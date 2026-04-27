-- FX.Cli.Main — the `fxi` command-line entry point.
--
-- Role: argv-parser and dispatcher for the `fxi` binary.  This is
-- the ONLY module in leanx that uses `IO` for command output, and
-- the ONLY module that owns the process exit code.  Every verb the
-- binary exposes to an agent starts here; every phase-deferred
-- subcommand funnels through `notImplemented` for a uniform 2-exit.
--
-- Design goals (tracked against fx_design.md §24 "Compiler Agent
-- Protocol"):
--   * Subcommands are verbs, flags are double-dashed long options or
--     single-dashed short aliases; FILE arguments are positional.
--   * Every subcommand has a dedicated `fxi help SUBCMD` screen.
--   * Exit codes are structured (0 success, 1 user error, 2 not-yet-
--     implemented, 3 internal error).
--   * Error output always goes to stderr; machine-readable output (AST
--     dumps, token streams, axiom lists) goes to stdout.
--   * No hidden state: every input comes through argv, every output
--     through a stream.  This is the contract an agent depends on.
--
-- Subcommands (cf. SPEC.md §9 and the agent-first REST analog in
-- fx_design.md §24):
--   fxi version [--json]             print version (JSON-or-plain) and exit
--   fxi self-test                    run axiom audit + smoke checks
--   fxi help [SUBCMD]                usage (global or per-subcommand)
--   fxi tokenize FILE.fx             dump lexer token stream
--   fxi parse    FILE.fx             dump parsed surface AST
--   fxi dump --tokens  FILE.fx       alias for `tokenize`
--   fxi dump --ast     FILE.fx       alias for `parse`
--   fxi dump --axioms                list the declared-axiom invariant
--   fxi dump --kernel  FILE.fx       emit kernel terms          (Phase 2+)
--   fxi check    FILE.fx             type-check only            (Phase 2+)
--   fxi show-axioms SYMBOL FILE.fx   walk dependency closure    (Phase 2+)
--   fxi run      FILE.fx             elaborate + evaluate       (Phase 3+)
--   fxi repl                         interactive REPL           (Phase 9+)
--   fxi test     DIR                 run conformance suite over directory
--
-- Also accepted: `--version` / `-V` / `--help` / `-h` as top-level
-- shorthand for the matching subcommand.

import FX.Core
import FX.Syntax.Lexer
import FX.Syntax.Parser
import FX.Elab.Elaborate
import FX.Elab.CheckFile
import FX.Eval.Interp
import FX.Eval.Pretty
import FX.Util.Diagnostic
import FX.Kernel.AxiomWalker

namespace FX.Cli

-- Structured exit codes.  Anything else is a bug.
namespace Exit
/-- Success. -/
def success           : UInt32 := 0
/-- User input was invalid: parse error, type error, missing file. -/
def userError      : UInt32 := 1
/-- The subcommand is deferred to a later phase. -/
def notImplemented : UInt32 := 2
/-- fxi itself hit a bug.  Report. -/
def internalError  : UInt32 := 3
end Exit

/-- The global `fxi --help` screen.  One-shot summary.  Per-subcommand
    details live in `helpFor`. -/
def usage : String :=
  "fxi — leanx reference interpreter for FX.\n" ++
  "\n" ++
  "USAGE:\n" ++
  "  fxi <SUBCMD> [ARGS...]\n" ++
  "  fxi --version | -V\n" ++
  "  fxi --help    | -h\n" ++
  "\n" ++
  "SUBCOMMANDS:\n" ++
  "  version [--json]     print the fxi version and exit\n" ++
  "  self-test            run built-in smoke checks (quick)\n" ++
  "  help [SUBCMD]        show help for a subcommand (or this screen)\n" ++
  "  tokenize FILE.fx     dump the lexer token stream (one token/line)\n" ++
  "  parse    FILE.fx     dump the parsed surface AST\n" ++
  "  dump     FLAGS       machine-readable dumps (see `fxi help dump`)\n" ++
  "  check    FILE.fx     type-check only                         (Phase 2+)\n" ++
  "  show-axioms SYMBOL FILE.fx\n" ++
  "                       walk transitive const-dep closure       (Phase 2+)\n" ++
  "  run      FILE.fx     elaborate + evaluate                    (Phase 3+)\n" ++
  "  repl                 interactive REPL                        (Phase 9+)\n" ++
  "  test     DIR         check every *.fx file under DIR recursively\n" ++
  "\n" ++
  "EXIT CODES:\n" ++
  "  0  success\n" ++
  "  1  user error (parse, type, I/O)\n" ++
  "  2  subcommand not implemented in this phase\n" ++
  "  3  internal error (report as a bug)\n" ++
  "\n" ++
  "See leanx/SPEC.md §9 and fx_design.md §24 for the full protocol.\n"

/-- Per-subcommand help.  Returned as `some` for known commands,
    `none` otherwise (the caller prints the global usage + error). -/
def helpFor : String → Option String
  | "version"    => some <|
      "fxi version [--json] — print the fxi semver and exit.\n" ++
      "\n" ++
      "  (no flag)   human-readable line: `fxi <semver>`\n" ++
      "  --json      machine-readable object: `{\"version\": \"<semver>\"}`\n" ++
      "\n" ++
      "Exits 0 on success.  The `--json` form is intended for agent\n" ++
      "consumption per fx_design.md §24 (Compiler Agent Protocol).\n"
  | "self-test"  => some <|
      "fxi self-test — run built-in smoke checks.\n" ++
      "Checks: CLI help renders, version string non-empty.\n" ++
      "Exits 0 if all checks pass, 3 otherwise.\n" ++
      "(Full invariants: run scripts/axiom-audit.sh and lake exe fxi-tests.)\n"
  | "help"       => some <|
      "fxi help [SUBCMD] — show help.\n" ++
      "With no argument, prints the global usage.\n"
  | "tokenize"   => some <|
      "fxi tokenize FILE.fx — dump the lexer token stream.\n" ++
      "Each line: LINE:COLUMN TOKEN  (one token per line).\n" ++
      "Errors go to stderr; exit 1 iff any lexical error was raised.\n"
  | "parse"      => some <|
      "fxi parse FILE.fx — lex and parse, then print the File AST.\n" ++
      "Uses Lean's `Repr` for the AST; intended for tooling, not humans.\n" ++
      "Errors go to stderr; exit 1 iff any lexer or parser error was raised.\n"
  | "dump"       => some <|
      "fxi dump FLAGS — machine-readable dumps.\n" ++
      "\n" ++
      "  --tokens FILE.fx   same as `fxi tokenize FILE.fx`\n" ++
      "  --ast    FILE.fx   same as `fxi parse    FILE.fx`\n" ++
      "  --axioms           print the axiom allowlist invariant as plain text\n" ++
      "  --kernel FILE.fx   emit elaborated kernel terms per decl\n" ++
      "                     (one block per decl: `NAME : TYPE\\n  := BODY`)\n"
  | "check"      => some <|
      "fxi check FILE.fx — lex + parse + elaborate + type-check.\n" ++
      "Prints one line per declaration:\n" ++
      "  ok        NAME   declaration elaborated and type-checked\n" ++
      "  elab-err  NAME   elaboration rejected it (E0xx code + span)\n" ++
      "  type-err  NAME   kernel checker rejected it (T0xx code)\n" ++
      "Exits 0 iff every declaration is ok, 1 otherwise.\n" ++
      "Phase 2.1 scope: fn declarations with oneLiner bodies, positional\n" ++
      "args, no spec clauses, no type parameters.  Other surface forms\n" ++
      "emit E020 / E030 diagnostics (not bugs — deferred to later phases).\n"
  | "show-axioms" => some <|
      "fxi show-axioms SYMBOL FILE.fx — print the §1.2 'enumerable\n" ++
      "trusted base' for SYMBOL.\n" ++
      "\n" ++
      "Two sections in the output:\n" ++
      "\n" ++
      "  (1) TRANSITIVE CLOSURE: every top-level symbol SYMBOL\n" ++
      "      references (self-inclusive), tagged by transparency:\n" ++
      "        transparent  — the body delta-unfolds at whnf / convEq\n" ++
      "        opaque       — the name stays a stuck const (default)\n" ++
      "        UNRESOLVED   — no body in scope (axiom, extern, or bug)\n" ++
      "\n" ++
      "  (2) KERNEL AXIOMS: the §31 Appendix-H axioms SYMBOL's\n" ++
      "      closure invokes, grouped by category:\n" ++
      "        H.1 Universes      H.2 Pi          H.3 Sigma\n" ++
      "        H.4 Inductive      H.5 Coinductive H.6 Identity\n" ++
      "        H.7 Quotient       H.8 Grade       H.9 Subsumption\n" ++
      "        H.10 Emit-table\n" ++
      "\n" ++
      "A summary line lists the always-applied axioms that fire at\n" ++
      "every elaboration without leaving kernel-term residue\n" ++
      "(T-conv, T-sub, Grade-algebra laws).\n" ++
      "\n" ++
      "Exit 0 on success; 1 if SYMBOL isn't registered in the\n" ++
      "elaborated file.  Agent-protocol transport per fx_design.md\n" ++
      "§24 is GET /axioms?symbol=...; this subcommand is its CLI\n" ++
      "twin.\n"
  | "run"        => some <|
      "fxi run FILE.fx — lex + parse + elaborate + type-check +\n" ++
      "evaluate every decl and print its normal form.\n" ++
      "Prints one line per decl: `NAME = <value>`.\n" ++
      "Exits 0 iff every decl elaborated, checked, and evaluated;\n" ++
      "1 on any diagnostic.  Phase 2.2 scope matches `fxi check`.\n"
  | "repl"       => some <|
      "fxi repl — launch the interactive REPL.\n" ++
      "Not yet implemented (Phase 9+).  Exits 2.\n"
  | "test"       => some <|
      "fxi test DIR — run fxi check on every '.fx' file under DIR\n" ++
      "recursively, reporting per-file pass/fail plus an aggregate\n" ++
      "summary.  Phase-2 scope matches `fxi check` semantics — no\n" ++
      "per-decl `test`/`bench`/`test_theory` block execution yet\n" ++
      "(arrives with Stream G's conformance suite drive).\n" ++
      "\n" ++
      "Exit 0 iff every file elaborates + checks cleanly; 1 if any\n" ++
      "file reports an error; 3 on I/O failure (directory unreadable,\n" ++
      "symlink loop).\n" ++
      "\n" ++
      "Output:\n" ++
      "  ok      relative/path/to/file.fx\n" ++
      "  fail    relative/path/to/broken.fx\n" ++
      "  ...\n" ++
      "  test: N of M files passed, K failed\n"
  | _            => none

/-- Emit a "not yet implemented" stub message.  Phase-deferred
    subcommands funnel through here so users get a single, uniform
    explanation rather than ad-hoc strings. -/
def notImplemented (subCmd : String) (phaseLabel : String) : IO UInt32 := do
  IO.eprintln s!"fxi: '{subCmd}' not yet implemented ({phaseLabel})."
  IO.eprintln "Run `fxi help` for the list of supported subcommands."
  return Exit.notImplemented

/-! ## Compact Term pretty-printer (for `fxi dump --kernel`)

`repr Term` renders every `Grade` field individually, producing
~30-line dumps for a two-binder function.  This compact
pretty-printer maps Term to a surface-adjacent syntax
(`Pi(x:A, B)`, `Lam(x:A, body)`, `f(a)`, etc.) and collapses
`Grade.default` / `Grade.ghost` to their named abbreviations.

Full de-Bruijn indices are kept as `#N` — the pretty-printer
is for auditing kernel output, not for round-tripping back to
surface syntax.  A future surface back-printer (Stream D
follow-up) would add named binders and concrete operator
syntax. -/

private def gradeShort (grade : FX.Kernel.Grade) : String :=
  if grade == FX.Kernel.Grade.default then "default"
  else if grade == FX.Kernel.Grade.ghost then "ghost"
  else s!"g({repr grade.usage})"

/-- Short rendering of an `Effect` record — emits the non-empty
    labels as a comma-separated list, or `Tot` for the empty row.
    Used by the Pi pretty-printer to surface kernel-level effect
    annotations at `fxi dump --kernel` time. -/
private def effectShort (effect : FX.Kernel.Effect) : String :=
  let labels : List String :=
    (if effect.io    then ["IO"]    else []) ++
    (if effect.div   then ["Div"]   else []) ++
    (if effect.ghost then ["Ghost"] else []) ++
    (if effect.exn   then ["Exn"]   else []) ++
    (if effect.alloc then ["Alloc"] else []) ++
    (if effect.read  then ["Read"]  else []) ++
    (if effect.write then ["Write"] else []) ++
    (if effect.async then ["Async"] else [])
  if labels.isEmpty then "Tot"
  else String.intercalate ", " labels

private def levelShort : FX.Kernel.Level → String
  | .zero        => "0"
  | .succ inner  => s!"(succ {levelShort inner})"
  | .max a b     => s!"(max {levelShort a} {levelShort b})"
  | .var index   => s!"lvl#{index}"

/-- Render a ctor label — look up the spec (user or prelude) for
    the PascalCase ctor name.  Falls back to `ctorN` when the spec
    isn't registered (shouldn't happen on ok-elab'd terms). -/
def ctorLabel (userSpecs : List FX.Kernel.IndSpec) (typeName : String)
    (ctorIndex : Nat) : String :=
  match FX.Kernel.Inductive.specByName? typeName userSpecs with
  | some indSpec =>
    match indSpec.ctorAt? ctorIndex with
    | some ctorSpec => ctorSpec.name
    | none          => s!"ctor{ctorIndex}"
  | none          => s!"ctor{ctorIndex}"

partial def termPrettyWith (userSpecs : List FX.Kernel.IndSpec)
    : FX.Kernel.Term → String
  | .var index                 => s!"#{index}"
  | .type level                => s!"Type<{levelShort level}>"
  | .const name                => name
  | .coind coindName coindArgs =>
    if coindArgs.isEmpty then
      coindName
    else
      let argStrings := coindArgs.map (termPrettyWith userSpecs)
      s!"{coindName}({", ".intercalate argStrings})"
  | .forallLevel body          => s!"∀lvl. {termPrettyWith userSpecs body}"
  | .app func arg              =>
    s!"{termPrettyWith userSpecs func}({termPrettyWith userSpecs arg})"
  | .lam grade domainType body =>
    s!"λ(_:{termPrettyWith userSpecs domainType} :_{gradeShort grade}). {termPrettyWith userSpecs body}"
  | .pi grade domainType codomainType returnEffect =>
    let effectSuffix :=
      if returnEffect == FX.Kernel.Effect.tot then ""
      else
        let labels := effectShort returnEffect
        " →{" ++ labels ++ "}"
    s!"Π(_:{termPrettyWith userSpecs domainType} :_{gradeShort grade}){effectSuffix}. {termPrettyWith userSpecs codomainType}"
  | .sigma grade domainType codomainType =>
    s!"Σ(_:{termPrettyWith userSpecs domainType} :_{gradeShort grade}). {termPrettyWith userSpecs codomainType}"
  | .ind typeName []           => typeName
  | .ind typeName args         =>
    let argStrs := args.map (termPrettyWith userSpecs)
    s!"{typeName}({String.intercalate ", " argStrs})"
  | .ctor typeName ctorIndex _typeArgs []  =>
    s!"{typeName}.{ctorLabel userSpecs typeName ctorIndex}"
  | .ctor typeName ctorIndex _typeArgs ctorArgs =>
    let argStrs := ctorArgs.map (termPrettyWith userSpecs)
    s!"{typeName}.{ctorLabel userSpecs typeName ctorIndex}({String.intercalate ", " argStrs})"
  | .indRec typeName _motive methods target =>
    let methodStrs := methods.map (termPrettyWith userSpecs)
    s!"indRec[{typeName}]({termPrettyWith userSpecs target}, methods=[{String.intercalate ", " methodStrs}])"
  | .id baseType leftEndpoint rightEndpoint =>
    s!"Id({termPrettyWith userSpecs baseType}, {termPrettyWith userSpecs leftEndpoint}, {termPrettyWith userSpecs rightEndpoint})"
  | .refl witness              => s!"refl({termPrettyWith userSpecs witness})"
  | .idJ _motive base eqProof  =>
    s!"idJ(base={termPrettyWith userSpecs base}, eq={termPrettyWith userSpecs eqProof})"
  | .quot baseType relation    =>
    s!"Quot({termPrettyWith userSpecs baseType}, {termPrettyWith userSpecs relation})"
  | .quotMk _relation witness  => s!"Quot.mk({termPrettyWith userSpecs witness})"
  | .quotLift lifted _respects target =>
    s!"Quot.lift({termPrettyWith userSpecs lifted}, {termPrettyWith userSpecs target})"
  | .coindUnfold typeName _typeArgs arms =>
    -- unfold<T>(head => e₁; tail => e₂; …) — arms listed in
    -- spec declaration order (CoindSpec.destructors).  Names
    -- would require CoindSpec lookup; we print by index until
    -- the lookup is wired the same way `ctorLabel` is.
    let armStrs := arms.mapIdx
      (fun idx arm => s!"#{idx} => {termPrettyWith userSpecs arm}")
    s!"unfold<{typeName}>({String.intercalate "; " armStrs})"
  | .coindDestruct typeName destructorIndex target =>
    s!"{typeName}.dtor{destructorIndex}({termPrettyWith userSpecs target})"

/-- Prelude-only alias for `termPrettyWith []` — maintained for
    callers that don't hold a GlobalEnv yet.  User ADT ctors
    render as `T.ctorN` under this entry point (fallback). -/
def termPretty (term : FX.Kernel.Term) : String := termPrettyWith [] term

/-! ## Structured-diagnostic emission (F6)

`ElabError` carries a source `Span`; `TypeError` carries an
optional `Term` but no `Span` (kernel operates on already-
elaborated terms).  Both fall through the same `Diagnostic`
renderer for consistent §10.10 formatting: a headline with
severity + code + source location, the explain footer
`[--explain CODE]`, and (future) goal/have/suggestion blocks.

The converters sit in the CLI rather than in
`FX/Util/Diagnostic.lean` because that module is a leaf — it
knows nothing about `ElabError` or `TypeError`.  Putting the
converters here keeps the trust layer free of diagnostic
dependencies. -/

/-- Map an `ElabError` to a renderable `Diagnostic`.
    Prepends the decl's display name to the summary for
    cross-decl output legibility ("decl: message" vs bare
    "message").  Span round-trips from the error. -/
def elabErrorToDiagnostic (displayName : String)
    (elabError : FX.Elab.ElabError) : FX.Util.Diagnostic :=
  FX.Util.Diagnostic.error
    elabError.code
    s!"{displayName}: {elabError.message}"
    elabError.span

/-- Map a `TypeError` to a renderable `Diagnostic`.  The kernel
    has no `Span` — it sees elaborated `Term`s, not source AST.
    We render with `Span.zero`, which `Diagnostic.toText`
    translates to "no source location" (the `<unknown>:1:1`
    placeholder is omitted).  The `elabDecl.name` prefix
    mirrors `elabErrorToDiagnostic` for consistent prefixes. -/
def typeErrorToDiagnostic (displayName : String)
    (typeError : FX.Kernel.TypeError) : FX.Util.Diagnostic :=
  FX.Util.Diagnostic.error
    typeError.code
    s!"{displayName}: {typeError.message}"
    FX.Syntax.Span.zero

/-- Read FILE.fx with a clear diagnostic on missing / directory /
    empty.  Returns the file contents on success; otherwise writes a
    diagnostic to stderr and returns the chosen exit code. -/
def readSourceFile (filePath : String) : IO (Except UInt32 String) := do
  let fsPath : System.FilePath := filePath
  let exists? ← fsPath.pathExists
  if !exists? then
    IO.eprintln s!"fxi: file not found: '{filePath}'"
    return .error Exit.userError
  let isDir? ← fsPath.isDir
  if isDir? then
    IO.eprintln s!"fxi: '{filePath}' is a directory, not a file."
    return .error Exit.userError
  try
    let sourceText ← IO.FS.readFile filePath
    if sourceText.isEmpty then
      IO.eprintln s!"fxi: '{filePath}' is empty."
      return .error Exit.userError
    return .ok sourceText
  catch ioError =>
    IO.eprintln s!"fxi: cannot read '{filePath}': {ioError}"
    return .error Exit.userError

/-- Read a file, run the lexer, and print every token one per line
    with its span.  Lexer errors are printed to stderr.  Exit code
    reflects the error count. -/
def tokenizeFile (filePath : String) : IO UInt32 := do
  match ← readSourceFile filePath with
  | .error exitCode => return exitCode
  | .ok sourceText =>
    let lexOutput := FX.Syntax.tokenize sourceText
    for locatedToken in lexOutput.tokens do
      let startPosition := locatedToken.span.start
      IO.println s!"{startPosition.line}:{startPosition.column} {repr locatedToken.token}"
    for lexError in lexOutput.errors do
      IO.eprintln (toString lexError)
    return (if lexOutput.errors.isEmpty then Exit.success else Exit.userError)

/-- Read a file, run the lexer + parser, and print the File AST
    via `Repr`.  Errors are printed to stderr.  Exit code reflects
    the error count. -/
def parseFileCmd (filePath : String) : IO UInt32 := do
  match ← readSourceFile filePath with
  | .error exitCode => return exitCode
  | .ok sourceText =>
    let lexOutput := FX.Syntax.tokenize sourceText
    for lexError in lexOutput.errors do
      IO.eprintln (toString lexError)
    let (parsedFile, parseErrors) := FX.Syntax.Parser.parseFile lexOutput.tokens
    IO.println (repr parsedFile.decls)
    for parseError in parseErrors do
      IO.eprintln (toString parseError)
    let allClean := lexOutput.errors.isEmpty ∧ parseErrors.isEmpty
    return (if allClean then Exit.success else Exit.userError)

/-- `fxi check FILE.fx` — lex + parse + elaborate + type-check.

Pipeline: `readSourceFile` → `FX.Syntax.tokenize` → `FX.Syntax.Parser.parseFile`
→ `FX.Elab.elabAndCheck` (per-decl).  Prints one summary line per
declaration and, for failures, a diagnostic block with the error
code + message.  Exit code: 0 iff every declaration reached
`okDecl`; 1 if any lex/parse/elab/type error occurred.

Phase-2.1 note: elaborator currently handles only `fn` declarations
with `oneLiner` bodies.  Other decl kinds and block bodies produce
`E020` / `E030` placeholders — these are deferred-phase markers,
not bugs, but for `fxi check` purposes they still flip exit to 1
(the file did not fully check).
-/
def checkFileCmd (filePath : String) : IO UInt32 := do
  match ← readSourceFile filePath with
  | .error exitCode => return exitCode
  | .ok sourceText =>
    let lexOutput := FX.Syntax.tokenize sourceText
    for lexError in lexOutput.errors do
      IO.eprintln (toString lexError)
    let (parsedFile, parseErrors) := FX.Syntax.Parser.parseFile lexOutput.tokens
    for parseError in parseErrors do
      IO.eprintln (toString parseError)
    let allClean := lexOutput.errors.isEmpty ∧ parseErrors.isEmpty
    -- Run elab + check on every decl.  `elabAndCheck` never throws —
    -- it returns a DeclResult variant.  Zip decls with results so we
    -- can pull a display name even when elaboration fails (`DeclResult.elabFail`
    -- only carries the error, not the source decl).
    let declResults := FX.Elab.checkFile parsedFile
    let mut anyFail := !allClean
    for (decl, declResult) in parsedFile.decls.zip declResults do
      let displayName := FX.Elab.Decl.nameHint decl
      match declResult with
      | .okDecl elabDecl =>
        IO.println s!"ok        {elabDecl.name}"
      | .elabFail elabError =>
        anyFail := true
        IO.println s!"elab-err  {displayName}"
        IO.eprintln ((elabErrorToDiagnostic displayName elabError).renderWithSource sourceText)
      | .typeFail elabDecl typeError =>
        anyFail := true
        IO.println s!"type-err  {elabDecl.name}"
        IO.eprintln ((typeErrorToDiagnostic elabDecl.name typeError).renderWithSource sourceText)
    return (if anyFail then Exit.userError else Exit.success)

/-- `fxi run FILE.fx` — lex + parse + elaborate + type-check +
    evaluate every declaration and print its normal form.

Pipeline:
  1. read source
  2. tokenize + report lex errors
  3. parse + report parse errors
  4. elab + check per decl (via `FX.Elab.checkFile` — threads a
     growing `GlobalEnv` across decls so later decls resolve to
     earlier ones)
  5. for each successful decl, evaluate its body under a runtime
     globalEnv seeded with the globals and print the result via
     `FX.Eval.Value.pretty`

Exit: 0 iff every decl reaches `okDecl` AND evaluates without a
runtime error; 1 otherwise.  Phase-2.2 note: the evaluator is
total on Phase-2.2-kernel terms (no non-terminating reduction
appears in practice for closed well-typed programs — but a `Div`
annotation will land with Stream C once the fuel-bounded variant
is wired). -/
def runFileCmd (filePath : String) : IO UInt32 := do
  match ← readSourceFile filePath with
  | .error exitCode => return exitCode
  | .ok sourceText =>
    let lexOutput := FX.Syntax.tokenize sourceText
    for lexError in lexOutput.errors do
      IO.eprintln (toString lexError)
    let (parsedFile, parseErrors) := FX.Syntax.Parser.parseFile lexOutput.tokens
    for parseError in parseErrors do
      IO.eprintln (toString parseError)
    let allClean := lexOutput.errors.isEmpty ∧ parseErrors.isEmpty
    -- Elab + check + thread globals through decl order.
    let declResults := FX.Elab.checkFile parsedFile
    -- Build the runtime globalEnv from every ok-decl.  Mirrors what
    -- `FX.Elab.checkFile` does for the Global registry.  User ADT
    -- specs (B9) are registered up-front via `elabTypeDeclSpec` so
    -- subsequent eval of fn bodies referencing those specs finds
    -- them at runtime via `iotaValue`'s `specByName?` lookup.  Q68:
    -- start from `emptyWithPrelude` so kernel-level prelude fns
    -- (nat_eq, ...) are available to `Term.const` lookups during
    -- evaluation — `checkFile` seeds its own env with the same
    -- prelude, so `fxi run` and `fxi check` agree on which names
    -- resolve.
    let mut globals : FX.Kernel.GlobalEnv :=
      FX.Derived.PreludeFn.emptyWithPrelude
    for decl in parsedFile.decls do
      match decl with
      | .typeDecl attrs declName typeParams ctors span =>
        match FX.Elab.elabTypeDeclSpec globals attrs declName typeParams ctors span with
        | .ok fullSpec => globals := globals.addUserSpec fullSpec
        | .error _err  => pure ()  -- surfaced through declResults below
      | _ => pure ()
    -- Q59/Q60: pre-register every ok-decl's body into `globals`
    -- before the display loop starts.  Without this, a zero-arg
    -- fn whose body references a fn declared LATER in the file
    -- evaluates against a `globals` that doesn't yet contain the
    -- referent — the `Term.const` resolves to a neutral form and
    -- the printed value looks like `?var0[Unit.tt]` instead of
    -- the actual number.  The subsequent display loop still
    -- updates `globals` per-iteration, but since we've already
    -- populated everything up front, re-addition is idempotent
    -- (newer entries shadow older with the same name, which is
    -- what `addDecl` does anyway).
    for (_decl, declResult) in parsedFile.decls.zip declResults do
      match declResult with
      | .okDecl elabDecl =>
        globals := globals.addDecl elabDecl.name elabDecl.type elabDecl.body
      | _ => pure ()
    let mut anyFail := !allClean
    for (decl, declResult) in parsedFile.decls.zip declResults do
      let displayName := FX.Elab.Decl.nameHint decl
      match declResult with
      | .okDecl elabDecl =>
        -- Type-check already ran inside checkFile; now evaluate.
        let evalEnv : FX.Eval.EvalEnv := FX.Eval.EvalEnv.ofGlobals globals
        -- Zero-arg fns elaborate to `Π (_ :_ghost Unit) → T`; the
        -- body is a closure wrapping an internal T expression.
        -- `evalDecl` applies `Unit.tt` for that shape so the
        -- printed value is the inner T, not `<closure>`.  Genuine
        -- fn values (non-zero-arg) still print as closures.
        let value := FX.Eval.evalDecl evalEnv elabDecl.body elabDecl.type
        IO.println s!"{elabDecl.name} = {FX.Eval.Value.prettyWith globals.userSpecs value}"
        globals := globals.addDecl elabDecl.name elabDecl.type elabDecl.body
      | .elabFail elabError =>
        anyFail := true
        IO.println s!"elab-err  {displayName}"
        IO.eprintln ((elabErrorToDiagnostic displayName elabError).renderWithSource sourceText)
      | .typeFail _elabDecl typeError =>
        anyFail := true
        IO.println s!"type-err  {displayName}"
        IO.eprintln ((typeErrorToDiagnostic displayName typeError).renderWithSource sourceText)
    return (if anyFail then Exit.userError else Exit.success)

/-! ## `fxi repl` — interactive REPL (F2)

Line-buffered interactive driver.  Each line is parsed as a
single decl (one-liner, no multi-line blocks), elaborated
against the accumulated `globalEnv`, type-checked, and — for
zero-arg fns — evaluated and printed.  The persistent env
lets subsequent lines reference prior decls by name.

**Input shape.**  Each non-meta input must be a single decl
ending in `;`:

  * `fn NAME() : T = expr;`
  * `fn NAME(x: U) : T = expr;`
  * `type NAME ctor1; ctor2; end type;`
  * `const NAME : T = expr;`
  * `val NAME : T;`

Multi-line `begin fn ... end fn` bodies don't compose with
line buffering — use `fxi run FILE.fx` for those.  The REPL
prints an error on any line that fails to parse/elab/check;
the env rolls forward only for successful decls.

**Meta commands.**

  * `:quit` / `:q` — exit (return code 0)
  * `:help` — print this list
  * `:decls` — list every registered global decl name
  * `:reset` — clear all registered decls (fresh env)

Blank lines and `//` comments are ignored.  EOF on stdin
exits cleanly.
-/

/-- Process one line of REPL input against the current state.
    Returns `(newGlobals, shouldQuit)` — on quit, the driver
    loop bails.  Non-fatal errors print to stderr/stdout and
    leave `globals` unchanged. -/
partial def replProcessLine
    (rawLine : String)
    (globals : FX.Kernel.GlobalEnv)
    : IO (FX.Kernel.GlobalEnv × Bool) := do
  let line := rawLine.trimAscii.toString
  -- Blank / comment lines: silently skip.
  if line.isEmpty || line.startsWith "//" then
    return (globals, false)
  -- Meta commands: `:quit`, `:help`, `:decls`, `:reset`.
  if line == ":quit" || line == ":q" then
    return (globals, true)
  if line == ":help" then
    IO.println "fxi repl commands:"
    IO.println "  :quit / :q   — exit"
    IO.println "  :help        — this message"
    IO.println "  :decls       — list registered global decls"
    IO.println "  :reset       — clear all registered decls"
    IO.println ""
    IO.println "Input each decl on one line, ending in `;`.  Example:"
    IO.println "  fn id<a: type>(x: a) : a = x;"
    IO.println "  fn main() : Nat = Nat.Succ(Nat.Zero);"
    IO.println ""
    IO.println "Multi-line `begin fn … end fn` bodies: use `fxi run FILE.fx`."
    return (globals, false)
  if line == ":decls" then
    let names := globals.names
    if names.isEmpty then
      IO.println "(no decls)"
    else
      for name in names.reverse do  -- oldest first (insertion order)
        match globals.lookup? name with
        | some entry =>
          IO.println s!"  {entry.name} : {termPretty entry.type}"
        | none        => IO.println s!"  {name} : <?>"
    return (globals, false)
  if line == ":reset" then
    IO.println "(env reset)"
    return (FX.Derived.PreludeFn.emptyWithPrelude, false)
  -- Otherwise treat as a decl.  Run the full lex → parse → elab
  -- → check → eval pipeline on this one line.
  let lexOutput := FX.Syntax.tokenize line
  if !lexOutput.errors.isEmpty then
    for err in lexOutput.errors do IO.eprintln (toString err)
    return (globals, false)
  let (parsedFile, parseErrors) := FX.Syntax.Parser.parseFile lexOutput.tokens
  if !parseErrors.isEmpty then
    for err in parseErrors do IO.eprintln (toString err)
    return (globals, false)
  if parsedFile.decls.isEmpty then
    IO.eprintln "repl: no decl recognized (input must be a single `fn`/`type`/`const`/`val` ending in `;`)"
    return (globals, false)
  -- Register type decls first so ctor args resolve during elab.
  let mut workingGlobals := globals
  for decl in parsedFile.decls do
    match decl with
    | .typeDecl attrs declName typeParams ctors span =>
      match FX.Elab.elabTypeDeclSpec workingGlobals attrs declName typeParams ctors span with
      | .ok fullSpec => workingGlobals := workingGlobals.addUserSpec fullSpec
      | .error _err  => pure ()  -- surfaced via declResults below
    | _ => pure ()
  -- The checkFile driver wants an AstFile carrying JUST the current
  -- line's decls but with `workingGlobals` primed — use the existing
  -- checkFile over the parsed file directly.  checkFile starts from
  -- empty globals internally, so we re-run the pipeline manually to
  -- preserve cross-line state.
  let declResults := FX.Elab.checkFileWithGlobals parsedFile workingGlobals
  for (decl, declResult) in parsedFile.decls.zip declResults do
    let displayName := FX.Elab.Decl.nameHint decl
    match declResult with
    | .okDecl elabDecl =>
      let evalEnv : FX.Eval.EvalEnv :=
        FX.Eval.EvalEnv.ofGlobals workingGlobals
      let value := FX.Eval.evalDecl evalEnv elabDecl.body elabDecl.type
      IO.println
        s!"{elabDecl.name} = {FX.Eval.Value.prettyWith workingGlobals.userSpecs value}"
      workingGlobals :=
        workingGlobals.addDecl elabDecl.name elabDecl.type elabDecl.body
    | .elabFail elabError =>
      IO.println s!"elab-err  {displayName}"
      IO.eprintln ((elabErrorToDiagnostic displayName elabError).renderWithSource line)
    | .typeFail _elabDecl typeError =>
      IO.println s!"type-err  {displayName}"
      IO.eprintln ((typeErrorToDiagnostic displayName typeError).renderWithSource line)
  return (workingGlobals, false)

/-- Count `begin`/`end` as whole-word tokens in `s`, after
    stripping `//` line comments.  Used by the REPL to decide
    whether an accumulated multi-line buffer is complete.

    The check is structural, not a full parse — a stray `begin`
    inside a string literal would fool it, but FX's Phase-2
    surface has no string-literal content that mentions these
    keywords, so in practice the heuristic is accurate.  A full
    implementation would tokenize + match, but that's
    disproportionate to the REPL's role as a quick-iteration
    tool. -/
partial def replKeywordBalance (buffer : String) : Int := Id.run do
  -- Strip line comments: anything after `//` to end-of-line.
  let stripped :=
    buffer.splitOn "\n" |>.map (fun line =>
      match line.splitOn "//" with
      | head :: _ => head
      | []        => line)
    |> String.intercalate "\n"
  let mut depth : Int := 0
  let words := stripped.splitOn " " |>.flatMap (·.splitOn "\n") |>.flatMap (·.splitOn "\t")
  for w in words do
    -- Strip trailing punctuation the tokenizer would split off
    -- but we didn't: `;`, `,`, `)`, `]`, `}`.  Keep only the
    -- alpha-numeric prefix for keyword matching.
    let core := (w.takeWhile Char.isAlphanum).toString
    if core == "begin" then
      depth := depth + 1
    else if core == "end" then
      depth := depth - 1
  return depth

/-- True iff the accumulated buffer is ready for parse: ends in
    `;` after trimming trailing whitespace AND every `begin` is
    matched by an `end`.  The `;` requirement matches every FX
    decl form — `fn ... = expr;`, `type ... end type;`,
    `const ... = expr;`, `val ... : T;`, `fn ... end fn;`. -/
partial def replBufferComplete (buffer : String) : Bool :=
  let trimmed := buffer.trimAscii.toString
  if trimmed.isEmpty then false
  else
    trimmed.endsWith ";" && replKeywordBalance trimmed == 0

/-- Main REPL driver.  Accumulates stdin lines into a buffer
    until the buffer is "complete" per `replBufferComplete`,
    then processes via `replProcessLine`.  Meta commands
    (starting with `:`) fire on the raw line — they don't
    accumulate.  Returns 0 on clean exit; per-input errors
    print and the loop continues. -/
partial def replCmd : IO UInt32 := do
  IO.println "fxi repl — type :help for commands, :quit to exit"
  IO.println "  (multi-line bodies accepted — buffer processes once a `;` terminates at begin/end balance)"
  let stdin ← IO.getStdin
  let rec loop (globals : FX.Kernel.GlobalEnv) (buffer : String) : IO UInt32 := do
    -- Prompt: `fx> ` at fresh input, `... ` while accumulating.
    IO.print (if buffer.isEmpty then "fx> " else "... ")
    (← IO.getStdout).flush
    let line ← stdin.getLine
    if line.isEmpty then
      -- EOF — process any outstanding buffer, then exit.
      if !buffer.isEmpty then
        let (_, _) ← replProcessLine buffer globals
      IO.println "(EOF, exiting)"
      return Exit.success
    let trimmedLine := line.trimAscii.toString
    -- Meta commands fire only at an empty-buffer prompt.  This
    -- avoids eating `:foo` appearing inside a string literal of
    -- a partially-typed decl (Phase-2 FX has no `:` in legal
    -- tokens outside type ascription, so this heuristic is
    -- safe for now).
    if buffer.isEmpty && trimmedLine.startsWith ":" then
      let (nextGlobals, shouldQuit) ← replProcessLine line globals
      if shouldQuit then return Exit.success
      loop nextGlobals ""
    else
      -- Accumulate.  Skip leading blank lines at an empty buffer.
      if buffer.isEmpty && trimmedLine.isEmpty then
        loop globals ""
      else
        let newBuffer :=
          if buffer.isEmpty then line else buffer ++ line
        if replBufferComplete newBuffer then
          let (nextGlobals, shouldQuit) ← replProcessLine newBuffer globals
          if shouldQuit then return Exit.success
          loop nextGlobals ""
        else
          loop globals newBuffer
  loop FX.Derived.PreludeFn.emptyWithPrelude ""

/-- `fxi dump --axioms` — print the trust-base invariant as plain text.
    This is the in-binary projection of AXIOMS.md §11 (totals) and is
    cheap enough to keep always available. -/
def dumpAxiomsInvariant : IO UInt32 := do
  IO.println "# fxi axiom-allowlist invariant (Phase 1)"
  IO.println "# See leanx/AXIOMS.md and fx_design.md Appendix H."
  IO.println ""
  IO.println "Total entries in allowlist: 33"
  IO.println "  H.1  Universes                5"
  IO.println "  H.2  Pi                       3"
  IO.println "  H.3  Sigma                    3"
  IO.println "  H.4  Inductive                4"
  IO.println "  H.5  Coinductive              4"
  IO.println "  H.6  Identity                 3"
  IO.println "  H.7  Quotient                 3"
  IO.println "  H.8  Grade algebra            5"
  IO.println "  H.9  Subsumption/conv.        2"
  IO.println "  H.10 Emit-table               1"
  IO.println ""
  IO.println "Trust invariant: at most 33 axioms; each declared `axiom` in"
  IO.println "FX/Kernel/** must match an entry in AXIOMS.md.  Enforced by"
  IO.println "scripts/axiom-audit.sh."
  return Exit.success

/-- `fxi self-test` — quick internal consistency checks.  Enough to
    tell an agent whether the binary is cooperative; does NOT replace
    the axiom audit or the runtime test suite. -/
def selfTest : IO UInt32 := do
  IO.println "fxi: self-test"
  -- Check 1: version string is non-empty.
  if FX.version.isEmpty then
    IO.eprintln "fxi: internal error: version string is empty."
    return Exit.internalError
  IO.println s!"  version:          {FX.version}  OK"
  -- Check 2: global usage renders.
  if usage.isEmpty then
    IO.eprintln "fxi: internal error: usage string is empty."
    return Exit.internalError
  IO.println "  help screen:      OK"
  -- Check 3: per-subcommand help covers every documented verb.
  let verbs := ["version", "self-test", "help", "tokenize", "parse",
                "dump", "check", "show-axioms", "run", "repl", "test"]
  for verbName in verbs do
    if (helpFor verbName).isNone then
      IO.eprintln s!"fxi: internal error: no help entry for '{verbName}'."
      return Exit.internalError
  IO.println s!"  help-for verbs:   {verbs.length} covered  OK"
  IO.println "fxi: self-test passed."
  return Exit.success

/-- Handle `fxi help [SUBCMD]`. -/
def helpCmd : List String → IO UInt32
  | []          => do IO.println usage; return Exit.success
  | [subCmd]    =>
    match helpFor subCmd with
    | some helpMessage => do IO.print helpMessage; return Exit.success
    | none             => do
        IO.eprintln s!"fxi: no help topic '{subCmd}'."
        IO.eprintln "Run `fxi help` for the list of supported subcommands."
        return Exit.userError
  | _ :: _ :: _ => do
    IO.eprintln "fxi: usage: fxi help [SUBCMD]"
    return Exit.userError

/-- `fxi dump --kernel FILE.fx` — print the elaborated kernel term
    for every decl in the file.  One block per decl:

    ```
    <name> : <elaborated-type-term>
      := <elaborated-body-term>
    ```

    Failures (elab or check) are reported to stderr with the
    error code and span; successful decls print to stdout.
    Exit 0 iff every decl elaborates and checks cleanly.

    Output uses `Repr` for the term — compact but not pretty.
    The surface FX back-printer (Q future) renders the term as
    FX source; this dump is the raw kernel projection per
    `fx_design.md` §31.2. -/
def dumpKernelFile (filePath : String) : IO UInt32 := do
  match ← readSourceFile filePath with
  | .error exitCode => return exitCode
  | .ok sourceText =>
    let lexOutput := FX.Syntax.tokenize sourceText
    for lexError in lexOutput.errors do
      IO.eprintln (toString lexError)
    let (parsedFile, parseErrors) := FX.Syntax.Parser.parseFile lexOutput.tokens
    for parseError in parseErrors do
      IO.eprintln (toString parseError)
    let allClean := lexOutput.errors.isEmpty ∧ parseErrors.isEmpty
    let declResults := FX.Elab.checkFile parsedFile
    -- Collect user-declared ADT specs so `termPrettyWith` renders
    -- user ctors by name rather than `ctorN` fallback.
    let mut userSpecs : List FX.Kernel.IndSpec := []
    for decl in parsedFile.decls do
      match decl with
      | .typeDecl attrs declName typeParams ctors span =>
        match FX.Elab.elabTypeDeclSpec
                FX.Kernel.GlobalEnv.empty attrs declName typeParams ctors span with
        | .ok spec => userSpecs := spec :: userSpecs
        | .error _ => pure ()
      | _ => pure ()
    let mut anyFail := !allClean
    for (decl, declResult) in parsedFile.decls.zip declResults do
      let displayName := FX.Elab.Decl.nameHint decl
      match declResult with
      | .okDecl elabDecl =>
        IO.println s!"{elabDecl.name} : {termPrettyWith userSpecs elabDecl.type}"
        IO.println s!"  := {termPrettyWith userSpecs elabDecl.body}"
      | .elabFail elabError =>
        anyFail := true
        IO.eprintln ((elabErrorToDiagnostic displayName elabError).renderWithSource sourceText)
      | .typeFail elabDecl typeError =>
        anyFail := true
        IO.eprintln ((typeErrorToDiagnostic elabDecl.name typeError).renderWithSource sourceText)
    return (if anyFail then Exit.userError else Exit.success)

/-- `fxi show-axioms SYMBOL FILE.fx` — print the §1.2 "enumerable
    trusted base" for `SYMBOL`.

    Two pieces of information:

      1. **Transitive `Term.const` closure** — every top-level
         symbol `SYMBOL` transitively references (self-inclusive),
         tagged by `transparent`/`opaque`/`UNRESOLVED`.  Same as
         Q44's carve-out.
      2. **Kernel axiom dependency** — the §31 Appendix-H axioms
         the elaborator invoked when accepting the closure.  Each
         decl's `type` and `body` are walked by
         `FX.Kernel.Term.collectAxioms`, and the union is printed
         sorted by `H.N.M` citation.

    Always-invoked axioms (T-conv H.9.1 and T-sub H.9.2 — fired
    at every conversion/subsumption check without leaving a kernel
    residue, plus universally-applied Grade-algebra axioms H.8.1
    through H.8.5) are listed in a summary line — they apply to
    every symbol by construction.

    Exit 0 iff the walk succeeds; `Exit.userError` if SYMBOL isn't
    registered in the elaborated file.  Suitable as the agent-
    protocol `GET /axioms?symbol=...` transport when F5 wires into
    §24.

    Phase-1 caveat: §H.10 U-emit and §H.5 Coinductive axioms fire
    only for hardware and codata terms not yet emitted by the
    elaborator — they will appear automatically once those
    terms land. -/
def showAxiomsFile (symbolName filePath : String) : IO UInt32 := do
  match ← readSourceFile filePath with
  | .error exitCode => return exitCode
  | .ok sourceText =>
    let lexOutput := FX.Syntax.tokenize sourceText
    for lexError in lexOutput.errors do
      IO.eprintln (toString lexError)
    let (parsedFile, parseErrors) := FX.Syntax.Parser.parseFile lexOutput.tokens
    for parseError in parseErrors do
      IO.eprintln (toString parseError)
    -- Rebuild the global env from checkFile's ok results — same
    -- shape `fxi dump --kernel` uses.
    let declResults := FX.Elab.checkFile parsedFile
    let env : FX.Kernel.GlobalEnv := declResults.foldl
      (init := FX.Kernel.GlobalEnv.empty)
      fun acc declResult =>
        match declResult with
        | .okDecl elaborated =>
          acc.addDecl elaborated.name elaborated.type elaborated.body
            (transparent := elaborated.transparent)
        | _ => acc
    if !env.contains symbolName then
      IO.eprintln s!"fxi show-axioms: '{symbolName}' not registered (typo or elab failure?)"
      return Exit.userError
    -- ===== Closure =====
    let deps := env.closureConstRefs symbolName
    IO.println s!"# dependency closure of '{symbolName}'"
    IO.println s!"# {deps.length} reachable symbol(s) (self-inclusive)"
    IO.println ""
    let mut unresolvedCount : Nat := 0
    for depName in deps do
      match env.lookup? depName with
      | some entry =>
        let tag := if entry.transparent then "transparent" else "opaque     "
        IO.println s!"  {tag}  {depName}"
      | none =>
        unresolvedCount := unresolvedCount + 1
        IO.println s!"  UNRESOLVED   {depName}"
    -- ===== Kernel axioms =====
    let kernelAxioms : List FX.Kernel.KernelAxiom :=
      deps.foldl (init := ([] : List FX.Kernel.KernelAxiom))
        fun axAcc depName =>
          match env.lookup? depName with
          | some entry =>
            let typeAx := FX.Kernel.Term.collectAxioms entry.type
            let bodyAx := FX.Kernel.Term.collectAxioms entry.body
            let combined := FX.Kernel.Term.unionAxioms typeAx bodyAx
            FX.Kernel.Term.unionAxioms axAcc combined
          | none => axAcc
    let sorted := FX.Kernel.Term.sortAxioms kernelAxioms
    IO.println ""
    IO.println s!"# kernel axioms invoked ({sorted.length} of 33)"
    IO.println ""
    -- Group by category header for readability.
    let mut currentCategory : String := ""
    for ax in sorted do
      let cat := FX.Kernel.KernelAxiom.category ax
      if cat != currentCategory then
        IO.println s!"## {cat}"
        currentCategory := cat
      let (citation, name) := FX.Kernel.KernelAxiom.tag ax
      -- Manual right-pad: longest citation is `H.10.1` (6 chars).
      let citationPadded :=
        if citation.length >= 6 then citation
        else citation ++ String.ofList (List.replicate (6 - citation.length) ' ')
      IO.println s!"  {citationPadded}  {name}"
    -- Always-applied axioms note.  T-conv / T-sub / Grade-algebra
    -- fire on every elaboration without leaving kernel-term
    -- residue; they're implicit in any successful elab.
    IO.println ""
    IO.println "# always-applied (every elaborated symbol implicitly invokes):"
    IO.println "  H.9.1   T-conv               (definitional equality at every check site)"
    IO.println "  H.9.2   T-sub                (subsumption at every grade / type slot)"
    IO.println "  H.8.1   Grade-semiring-laws  (per-dim; fires at every graded binder)"
    IO.println "  H.8.2   Grade-subsumption"
    IO.println "  H.8.3   Grade-division       (Pi-intro context division, Wood-Atkey)"
    IO.println "  H.8.4   Grade-zero           (ghost-erasure at compile time)"
    IO.println "  H.8.5   Grade-lattice        (Tier L validity at partial combines)"
    if unresolvedCount > 0 then
      IO.println ""
      IO.println s!"# warning: {unresolvedCount} unresolved reference(s) — would be user axioms if elaborated"
    return Exit.success

/-! ## `fxi test DIR` — conformance runner (F3)

Walks DIR recursively for `*.fx` files and runs `fxi check`'s
elaboration pipeline on each.  Phase-2 scope matches `fxi
check`: per-file pass/fail based on whether every decl reaches
`okDecl` without any `elabFail` / `typeFail` — no per-decl
`test` / `bench` / `test_theory` block execution yet (arrives
with Stream G's conformance suite drive).

Shape: `test` is quieter than `check` — it doesn't print per-decl
status, only per-file status.  On failure, the file's first
diagnostic is emitted so users get enough signal without wall-of-
text output for a suite with hundreds of files. -/

/-- Check one file silently for `fxi test DIR`.  Returns
    `(passedQ, firstDiagnostic?)` so the caller can summarize
    per-file status and emit one diagnostic per failing file. -/
def checkFileSilent (filePath : String) : IO (Bool × Option String) := do
  match ← readSourceFile filePath with
  | .error _ => return (false, some s!"cannot read '{filePath}'")
  | .ok sourceText =>
    let lexOutput := FX.Syntax.tokenize sourceText
    if let some firstError := lexOutput.errors.toList.head? then
      return (false, some (toString firstError))
    let (parsedFile, parseErrors) := FX.Syntax.Parser.parseFile lexOutput.tokens
    if let some firstError := parseErrors.toList.head? then
      return (false, some (toString firstError))
    let declResults := FX.Elab.checkFile parsedFile
    -- Return on first failing decl.  Iterate over (decl, result)
    -- pairs so we can report a proper diagnostic.
    for (decl, declResult) in parsedFile.decls.zip declResults do
      match declResult with
      | .okDecl _ => continue
      | .elabFail elabError =>
        let displayName := FX.Elab.Decl.nameHint decl
        let diag := elabErrorToDiagnostic displayName elabError
        return (false, some (diag.renderWithSource sourceText))
      | .typeFail elabDecl typeError =>
        let diag := typeErrorToDiagnostic elabDecl.name typeError
        return (false, some (diag.renderWithSource sourceText))
    return (true, none)

/-- Recursively walk `dirPath` collecting every `*.fx` file.  Paths
    returned are absolute (preserves what `readSourceFile` expects).
    Skips hidden entries (names starting with `.`) to avoid
    descending into `.git`, editor swap files, and similar.  IO
    failures propagate as `none` so the caller reports a single
    uniform error code. -/
partial def walkFxFiles (dirPath : System.FilePath) : IO (Option (Array System.FilePath)) := do
  try
    let entries ← dirPath.readDir
    let mut acc : Array System.FilePath := #[]
    for entry in entries do
      let entryName := entry.fileName
      -- Skip hidden entries and editor artifacts.
      if entryName.startsWith "." then continue
      let fullPath := entry.path
      let isDir ← fullPath.isDir
      if isDir then
        match ← walkFxFiles fullPath with
        | some children => acc := acc ++ children
        | none          => return none  -- bubble up I/O failure
      else if fullPath.extension == some "fx" then
        acc := acc.push fullPath
    -- Deterministic ordering (readDir doesn't guarantee order).
    return some (acc.qsort fun a b => toString a < toString b)
  catch ioError =>
    IO.eprintln s!"fxi test: cannot read directory '{dirPath}': {ioError}"
    return none

/-- `fxi test DIR` implementation. -/
def testDirCmd (dirPath : String) : IO UInt32 := do
  let fsPath : System.FilePath := dirPath
  let exists? ← fsPath.pathExists
  if !exists? then
    IO.eprintln s!"fxi test: directory not found: '{dirPath}'"
    return Exit.userError
  let isDir? ← fsPath.isDir
  if !isDir? then
    IO.eprintln s!"fxi test: '{dirPath}' is not a directory — use `fxi check FILE.fx` for single files."
    return Exit.userError
  match ← walkFxFiles fsPath with
  | none => return Exit.internalError  -- I/O failure already reported
  | some files =>
    if files.isEmpty then
      IO.eprintln s!"fxi test: no '.fx' files found under '{dirPath}'."
      return Exit.userError
    -- Pretty-print paths relative to DIR when possible — keeps
    -- output narrow in deep trees.
    let prefixStr := toString fsPath
    let stripPrefix (full : String) : String :=
      if full.startsWith prefixStr then
        let remainder := (full.drop prefixStr.length).toString
        -- strip a leading "/" from the remainder
        if remainder.startsWith "/" then (remainder.drop 1).toString else remainder
      else full
    let mut passed : Nat := 0
    let mut failed : Nat := 0
    for filePath in files do
      let (ok, diag?) ← checkFileSilent (toString filePath)
      let shortName := stripPrefix (toString filePath)
      if ok then
        passed := passed + 1
        IO.println s!"ok      {shortName}"
      else
        failed := failed + 1
        IO.println s!"fail    {shortName}"
        match diag? with
        | some d => IO.eprintln d
        | none   => pure ()
    let total := passed + failed
    IO.println ""
    IO.println s!"test: {passed} of {total} files passed, {failed} failed"
    return (if failed == 0 then Exit.success else Exit.userError)

/-- Handle `fxi dump FLAGS`. -/
def dumpCmd : List String → IO UInt32
  | ["--tokens", filePath]  => tokenizeFile filePath
  | ["--ast", filePath]     => parseFileCmd filePath
  | ["--axioms"]            => dumpAxiomsInvariant
  | ["--kernel", filePath]  => dumpKernelFile filePath
  | ["--kernel"]            => do
      IO.eprintln "fxi: usage: fxi dump --kernel FILE.fx"
      IO.eprintln "Run `fxi help dump` for details."
      return Exit.userError
  | "--kernel" :: _         => do
      IO.eprintln "fxi: 'dump --kernel' takes exactly one argument: FILE.fx"
      return Exit.userError
  | []                      => do
      IO.eprintln "fxi: usage: fxi dump (--tokens|--ast) FILE.fx | --axioms | --kernel FILE.fx"
      IO.eprintln "Run `fxi help dump` for details."
      return Exit.userError
  | args                    => do
      let joinedArgs := String.intercalate " " args
      IO.eprintln s!"fxi: 'dump': invalid arguments: {joinedArgs}"
      IO.eprintln "Run `fxi help dump` for usage."
      return Exit.userError

/-- Top-level dispatch. -/
def run : List String → IO UInt32
  | []                          => do IO.println usage; return Exit.userError
  -- Version (short/long flags AND the subcommand form).  The `--json`
  -- form is the agent-consumption variant per fx_design.md §24.
  | ["--version"]               => do IO.println s!"fxi {FX.version}"; return Exit.success
  | ["-V"]                      => do IO.println s!"fxi {FX.version}"; return Exit.success
  | ["version"]                 => do IO.println s!"fxi {FX.version}"; return Exit.success
  | ["version", "--json"]       => do
      IO.println s!"\{\"version\": \"{FX.version}\"}"
      return Exit.success
  | "version" :: _              => do
      IO.eprintln "fxi: usage: fxi version [--json]"
      IO.eprintln "Run `fxi help version` for details."
      return Exit.userError
  -- Help (short/long flags AND the subcommand form).
  | ["--help"]                  => do IO.println usage; return Exit.success
  | ["-h"]                      => do IO.println usage; return Exit.success
  | "help" :: restArgs          => helpCmd restArgs
  -- Smoke checks.
  | ["self-test"]               => selfTest
  -- Phase-1 subcommands.
  | ["tokenize", filePath]      => tokenizeFile filePath
  | ["parse", filePath]         => parseFileCmd filePath
  | "dump" :: restArgs          => dumpCmd restArgs
  -- Phase-2 subcommands.
  | ["check", filePath]         => checkFileCmd filePath
  | ["check"]                   => do
      IO.eprintln "fxi: usage: fxi check FILE.fx"
      IO.eprintln "Run `fxi help check` for details."
      return Exit.userError
  | "check"    :: _             => do
      IO.eprintln "fxi: 'check' takes exactly one argument: FILE.fx"
      return Exit.userError
  -- Transitive const-dependency walker (Q44; carve-out of F5).
  | ["show-axioms", symbolName, filePath] =>
      showAxiomsFile symbolName filePath
  | "show-axioms" :: _          => do
      IO.eprintln "fxi: usage: fxi show-axioms SYMBOL FILE.fx"
      return Exit.userError
  -- Phase-deferred subcommands.
  | ["run", filePath]           => runFileCmd filePath
  | ["run"]                     => do
      IO.eprintln "fxi: usage: fxi run FILE.fx"
      IO.eprintln "Run `fxi help run` for details."
      return Exit.userError
  | "run"      :: _             => do
      IO.eprintln "fxi: 'run' takes exactly one argument: FILE.fx"
      return Exit.userError
  | ["repl"]                    => replCmd
  | "repl"     :: _             => do
      IO.eprintln "fxi: 'repl' takes no arguments"
      return Exit.userError
  -- Phase-2 `fxi test DIR` (F3): walks DIR recursively for *.fx
  -- files, runs the elab pipeline on each, prints per-file pass/
  -- fail plus an aggregate summary.
  | ["test", dirPath]           => testDirCmd dirPath
  | ["test"]                    => do
      IO.eprintln "fxi: usage: fxi test DIR"
      IO.eprintln "Run `fxi help test` for details."
      return Exit.userError
  | "test"     :: _             => do
      IO.eprintln "fxi: 'test' takes exactly one argument: DIR"
      return Exit.userError
  -- Arity errors for known verbs (must come AFTER the positive matches).
  | ["tokenize"]                => do
      IO.eprintln "fxi: usage: fxi tokenize FILE.fx"
      IO.eprintln "Run `fxi help tokenize` for details."
      return Exit.userError
  | "tokenize" :: _             => do
      IO.eprintln "fxi: 'tokenize' takes exactly one argument: FILE.fx"
      return Exit.userError
  | ["parse"]                   => do
      IO.eprintln "fxi: usage: fxi parse FILE.fx"
      IO.eprintln "Run `fxi help parse` for details."
      return Exit.userError
  | "parse"    :: _             => do
      IO.eprintln "fxi: 'parse' takes exactly one argument: FILE.fx"
      return Exit.userError
  -- Unknown subcommand.
  | unknownCmd :: _             => do
      IO.eprintln s!"fxi: unknown subcommand '{unknownCmd}'"
      IO.eprintln "Run `fxi --help` for the list of supported subcommands."
      return Exit.userError

end FX.Cli

def main (argv : List String) : IO UInt32 :=
  FX.Cli.run argv
