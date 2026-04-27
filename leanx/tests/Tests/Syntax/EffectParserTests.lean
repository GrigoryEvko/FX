import FX.Syntax.Lexer
import FX.Syntax.Parser
import Tests.Framework

/-!
# Effect decl parser tests (task E-4, parser half)

Per `fx_grammar.md §5.12` / `fx_design.md §9.5`.  Exercises the
`effect NAME<typeParams>? op+ end effect;` surface form.

Scope (parser half):

  * Name parsing (PascalCase required; P040 on lower-case).
  * Type parameters (optional).
  * One or more operation signatures `fn op(params) : T with eff?;`.
  * `end effect;` closer.

Deferred to the elaborator half:

  * Registration of the effect name into a per-module registry.
  * Extending the kernel's `Effect` struct to hold user-declared
    labels (today's `FX.Kernel.Grade.Effect` is a fixed 8-field
    record; supporting new labels requires making it extensible).
  * `subsumes` relations — the grammar accepts them inside
    `effect` blocks, but this pass parses only operation
    signatures; `subsumes` lands with the elaborator half.

Split into its own file from `ParserTests.lean` because the
`run` do-block there already sits near Lean 4's elab-depth
ceiling (same rationale as `Tests.Syntax.TryParserTests`).
-/

namespace Tests.Syntax.EffectParserTests

open Tests FX.Syntax FX.Syntax.Ast

/-- Lex + parse; return decls plus any parse errors. -/
def parse (sourceText : String) : Array Decl × Array FX.Util.Error :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (fileResult, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  (fileResult.decls, lexOut.errors ++ parseErrs)

/-- Project an effect decl's name, or `"<not-effect>"` otherwise. -/
def effectName? (decls : Array Decl) : String :=
  match decls[0]? with
  | some (Decl.effectDecl declName _ _ _) => declName
  | _                                      => "<not-effect>"

/-- Project the effect decl's operation count. -/
def effectOpCount? (decls : Array Decl) : Nat :=
  match decls[0]? with
  | some (Decl.effectDecl _ _ ops _) => ops.size
  | _                                 => 0

/-- Project the first operation's name, or `"<no-op>"`. -/
def firstOpName? (decls : Array Decl) : String :=
  match decls[0]? with
  | some (Decl.effectDecl _ _ ops _) =>
    match ops[0]? with
    | some (EffectOp.mk opName _ _ _ _) => opName
    | none                               => "<no-op>"
  | _ => "<not-effect>"

/-- Project the i-th operation's name, or `"<oob>"`. -/
def opNameAt? (decls : Array Decl) (index : Nat) : String :=
  match decls[0]? with
  | some (Decl.effectDecl _ _ ops _) =>
    match ops[index]? with
    | some (EffectOp.mk opName _ _ _ _) => opName
    | none                               => "<oob>"
  | _ => "<not-effect>"

/-- Project the effect decl's type-parameter count. -/
def effectTypeParamCount? (decls : Array Decl) : Nat :=
  match decls[0]? with
  | some (Decl.effectDecl _ typeParams _ _) => typeParams.size
  | _                                        => 0

def run : IO Unit := do
  /- ## 1. Minimal single-op effect.  No type params, single op,
     no effect row on the op. -/
  let (decls, errs) := parse "effect Log fn write(msg: string) : unit; end effect;"
  check "1. minimal effect: no parse errors" 0 errs.size
  check "1. decl count == 1" 1 decls.size
  check "1. effectName == \"Log\"" "Log" (effectName? decls)
  check "1. op count == 1" 1 (effectOpCount? decls)
  check "1. first op name == \"write\"" "write" (firstOpName? decls)
  check "1. no type params" 0 (effectTypeParamCount? decls)

  /- ## 2. Type-parameterized effect per §9.5 `effect State<s: type>`. -/
  let (decls, errs) := parse
    "effect State<s: type> fn get() : s; fn put(new_state: s) : unit; end effect;"
  check "2. State<s>: no parse errors" 0 errs.size
  check "2. effectName == \"State\"" "State" (effectName? decls)
  check "2. two ops" 2 (effectOpCount? decls)
  check "2. first op: get" "get" (opNameAt? decls 0)
  check "2. second op: put" "put" (opNameAt? decls 1)
  check "2. one type param" 1 (effectTypeParamCount? decls)

  /- ## 3. Op with its own effect row (`with IO`) per §9.5
     FileSystem example — operations may declare effects. -/
  let (decls, errs) := parse
    "effect FileSystem fn read_file(path: string) : string with IO; end effect;"
  check "3. FileSystem: no parse errors" 0 errs.size
  check "3. one op" 1 (effectOpCount? decls)
  let firstOpHasEffect : Bool :=
    match decls[0]? with
    | some (Decl.effectDecl _ _ ops _) =>
      match ops[0]? with
      | some (EffectOp.mk _ _ _ effects _) => effects.size > 0
      | none                                => false
    | _ => false
  check "3. first op has an effect row" true firstOpHasEffect

  /- ## 4. Multiple ops in sequence — chains correctly. -/
  let (decls, errs) := parse
    "effect Reader<r: type> fn ask() : r; fn local(f: r, body: r) : r; end effect;"
  check "4. Reader: no parse errors" 0 errs.size
  check "4. Reader: two ops" 2 (effectOpCount? decls)
  check "4. Reader: op 0 name" "ask" (opNameAt? decls 0)
  check "4. Reader: op 1 name" "local" (opNameAt? decls 1)

  /- ## 5. Zero-op effect — unusual but grammar-valid.
     Accepted by `effectOpsLoop` (empty accumulator closes
     against `end effect;`). -/
  let (decls, errs) := parse "effect Empty end effect;"
  check "5. empty effect: no parse errors" 0 errs.size
  check "5. empty effect: zero ops" 0 (effectOpCount? decls)
  check "5. empty effect: name preserved" "Empty" (effectName? decls)

  /- ## 6. Missing `end effect;` closer — triggers recorded error
     but parse doesn't explode.  The closer-check lives at the
     end of `parseEffectDecl`, so a missing closer surfaces
     through `expectKw`'s diagnostic.  Pin: parse records at
     least one error, doesn't exceed its token stream. -/
  let (_, errs) := parse "effect Bad fn op() : unit;"  -- missing end
  check "6. missing end effect: error recorded" true (errs.size > 0)

  /- ## 7. Lower-case effect name — P040 warning, parse
     productive.  Effect names must be PascalCase per §2.3. -/
  let (_, errs) := parse "effect lowercase fn op() : unit; end effect;"
  let hasP040 : Bool := errs.any (·.code == "P040")
  check "7. lower-case effect name: P040 recorded" true hasP040

  /- ## 8. The canonical §9.5 Exception example — demonstrates
     the typical user-defined effect form with a never-returning
     operation. -/
  let (decls, errs) := parse
    "effect Exception<e: type> fn throw(err: e) : never; end effect;"
  check "8. Exception<e>: no parse errors" 0 errs.size
  check "8. Exception: one op" 1 (effectOpCount? decls)
  check "8. Exception: op name" "throw" (firstOpName? decls)
  check "8. Exception: type param count" 1 (effectTypeParamCount? decls)

end Tests.Syntax.EffectParserTests
