import FX.Syntax.Span

/-!
# Structured diagnostic

Per `fx_design.md` §10.10, every compiler error follows a fixed
shape:

```
error[CODE]: one-line summary at FILE:LINE:COL

  SOURCE_LINE
  ^^^^^^^^^ underline

  Goal:    what the compiler needs
  Have:    what facts are available
  Gap:     what is missing

  Suggestion:
    concrete FX code to fix the problem

  [--explain CODE for full documentation]
```

This file defines the structure behind that rendering.  Rendering
itself — resolving the span to a source line, composing the caret
underline, and formatting the block — lives in the `Diagnostic.
render` pass (Q28) which needs source-file access that this leaf
module deliberately does NOT import.

## Relationship to existing error types

Three error types in the tree — `FX.Util.Error` (lexer / parser
record-errors), `FX.Kernel.TypeError`, `FX.Elab.ElabError` — each
carry their own `code + message + span-or-term` fields.  They
survive as the direct throw targets of their respective layers
(kernel stays dependency-light, elaborator stays close to its
AST).  `Diagnostic` is the user-facing presentation layer: a
`toDiagnostic` converter from each layer's error type feeds into
one renderer, so the CLI, agent daemon, and LSP all consume the
same wire format regardless of which phase raised the error.

For Q27 this file only defines the structure + builders.  Per-
layer `toDiagnostic` helpers and the renderer itself land with
Q28 (F6 downstream).  Nothing in the compiler consumes
`Diagnostic` yet — the structure is a commitment to the §10.10
shape, not yet the pipeline's working currency.

## Why a separate type

Each layer's native error is tuned to what that layer has on
hand.  `ElabError` carries a `Span` because the elaborator
walks the AST.  `TypeError` carries an `Option Term` because
the kernel only sees terms.  `Error` carries a stringly-typed
`(file, line, col)` because the lexer runs before any AST.
Lifting all three into one structured `Diagnostic` — with
severity, explicit goal/have/gap, and a suggestion slot —
gives rendering one shape to target and gives agents one JSON
schema to parse.

## Severity

`fx_design.md` §10.6 / §10.12 define the tiers:

  * `error`   — rejects the program under the active profile.
                Sketch mode may downgrade some to warning; release
                mode rejects.
  * `warning` — does not reject; code starts with `W`.
  * `note`    — auxiliary context attached to an error or
                warning; never stands alone.

No `info` / `debug` tier — those are traces, not diagnostics.
-/

namespace FX.Util

open FX.Syntax

/-- Diagnostic severity per §10.6 / §10.12. -/
inductive Severity : Type where
  /-- Rejects the program.  Codes `T/R/E/M/S/I/P/N/L/CT`. -/
  | error
  /-- Does not reject.  Codes `W000+`. -/
  | warning
  /-- Auxiliary context attached to a parent error/warning. -/
  | note
  deriving Repr, BEq, DecidableEq

namespace Severity

/-- Lowercase surface spelling — matches `fx_design.md` §10.10
    sample output (`error[T001]`, `warning[W001]`). -/
def toString : Severity → String
  | .error   => "error"
  | .warning => "warning"
  | .note    => "note"

instance : ToString Severity := ⟨toString⟩

end Severity

/--
A structured compiler diagnostic matching `fx_design.md` §10.10.
Captures everything the renderer needs; rendering itself
lives elsewhere because producing the source-line extract + caret
requires file access.

Field semantics:

  * `code`       — canonical error-code string (`T001`, `E010`,
                   `W001`, …).  The registry is in
                   `docs/error-codes.md`.
  * `severity`   — `.error` / `.warning` / `.note`.  Release
                   builds reject on any `.error`.
  * `summary`    — one-line headline printed on the `error[CODE]:`
                   line.  No newlines.
  * `span`       — source range.  Rendering extracts the
                   surrounding line + builds the caret underline
                   from the byte offsets.
  * `goal`       — what the compiler needs (optional).
  * `have_`      — what facts are available (optional).  Trailing
                   underscore because `have` is a Lean tactic keyword.
  * `gap`        — what is missing (optional).  Usually the
                   synthesis of `goal` minus `have_`.
  * `suggestion` — concrete FX code fixing the problem (optional).
                   Per §10.10 this must be a valid FX fragment, not
                   a vague hint.
  * `notes`      — child diagnostics of `.note` severity attached
                   to this one.  Usage: cross-reference a prior
                   binding, point at an invariant declaration,
                   show where a conflicting import came from.
-/
structure Diagnostic : Type where
  code       : String
  severity   : Severity
  summary    : String
  span       : Span
  goal       : Option String := none
  have_      : Option String := none
  gap        : Option String := none
  suggestion : Option String := none
  notes      : Array Diagnostic := #[]
  deriving Repr

namespace Diagnostic

/-- Build a plain error diagnostic; `goal`/`have`/`gap`/
    `suggestion` default to `none` and can be added via the
    with-builders below. -/
def error (code summary : String) (span : Span := Span.zero) : Diagnostic :=
  { code, severity := .error, summary, span }

/-- Warning counterpart to `error`.  The renderer colors
    warnings differently but the fields are identical. -/
def warning (code summary : String) (span : Span := Span.zero) : Diagnostic :=
  { code, severity := .warning, summary, span }

/-- Note counterpart — always attaches to a parent via the
    parent's `notes` array rather than standing alone. -/
def note (code summary : String) (span : Span := Span.zero) : Diagnostic :=
  { code, severity := .note, summary, span }

/-- Attach the "Goal:" line. -/
def withGoal (diag : Diagnostic) (goalText : String) : Diagnostic :=
  { diag with goal := some goalText }

/-- Attach the "Have:" line. -/
def withHave (diag : Diagnostic) (haveText : String) : Diagnostic :=
  { diag with have_ := some haveText }

/-- Attach the "Gap:" line. -/
def withGap (diag : Diagnostic) (gapText : String) : Diagnostic :=
  { diag with gap := some gapText }

/-- Attach the "Suggestion:" line.  Must be a valid FX fragment
    (§10.10); callers should produce actual source, not a hint. -/
def withSuggestion (diag : Diagnostic) (fragment : String) : Diagnostic :=
  { diag with suggestion := some fragment }

/-- Append a note diagnostic to the parent.  Appends, so repeated
    calls produce `.notes = #[first, second, ...]`. -/
def addNote (parent : Diagnostic) (child : Diagnostic) : Diagnostic :=
  { parent with notes := parent.notes.push child }

/-- Is this an error severity (for exit-code / rejection
    decisions in release builds)?  Wraps the `.error` case so
    callers don't pattern-match severity directly. -/
def isError (diag : Diagnostic) : Bool :=
  diag.severity == .error

/-- Is this a warning?  Exists as the mirror of `isError` for
    callers that want to exclude warnings from a rejection
    count without pattern-matching. -/
def isWarning (diag : Diagnostic) : Bool :=
  diag.severity == .warning

/-- Two-space indent for the content lines under the headline.
    Matches the §10.10 sample output. -/
private def indent : String := "  "

/-- Location suffix `" at <source>:line:col"` or empty when span
    is zero.  Real file path plumbing lives in
    `renderWithSource` (future). -/
private def locationSuffix (span : FX.Syntax.Span) : String :=
  if span == FX.Syntax.Span.zero then ""
  else
    let startPos := span.start
    s!" at <source>:{startPos.line}:{startPos.column}"

/-- A single `Label:    value` line, indented.  `Option` so
    filterMap drops absent fields. -/
private def labelLine (label : String) : Option String → Option String
  | none      => none
  | some text => some s!"{indent}{label}:    {text}"

/-- Combine the Goal / Have / Gap lines into one block, separated
    by single newlines.  Returns `none` if all three are absent. -/
private def goalBlock (goal have_ gap : Option String) : Option String :=
  let lines := [labelLine "Goal" goal,
                labelLine "Have" have_,
                labelLine "Gap"  gap].filterMap id
  if lines.isEmpty then none
  else some (String.intercalate "\n" lines)

/-- Suggestion block — the label and the indented code fragment. -/
private def suggestionBlock : Option String → Option String
  | none       => none
  | some code  => some s!"{indent}Suggestion:\n{indent}{indent}{code}"

/-- Explain footer — always present on any diagnostic that
    renders.  Matches §10.10's closing line. -/
private def explainFooter (errorCode : String) : String :=
  s!"{indent}[--explain {errorCode} for full documentation]"

/-- Render a single Diagnostic to the `fx_design.md` §10.10
    text shape, modulo the source-line + caret block which
    needs file access (see `renderWithSource` once it lands).

    Current shape — each present block is separated from the
    next by one blank line (two consecutive `\n`):

    ```
    <sev>[<code>]: <summary> at <file>:<line>:<col>

      Goal:    <goal>
      Have:    <have>
      Gap:     <gap>

      Suggestion:
        <suggestion>

      [--explain <code> for full documentation]
    ```

    The file / line / col comes from the span; if the span is
    `Span.zero` the location suffix is omitted.  Goal/Have/Gap
    appear together as one block (all missing → the block is
    omitted); the Suggestion block is independent; the explain
    footer is always present.  Notes attached to the diagnostic
    are rendered in order, indented one more level than the
    parent — matching §10.10's implicit nesting. -/
partial def toText (diag : Diagnostic) : String :=
  let loc      := locationSuffix diag.span
  let headline := s!"{diag.severity}[{diag.code}]: {diag.summary}{loc}"
  let blocks : List String := [
    some headline,
    goalBlock diag.goal diag.have_ diag.gap,
    suggestionBlock diag.suggestion,
    some (explainFooter diag.code)
  ].filterMap id
  let body := String.intercalate "\n\n" blocks
  if diag.notes.isEmpty then body
  else body ++ "\n" ++ String.intercalate "\n"
                         (diag.notes.map renderNote).toList
where
  renderNote (child : Diagnostic) : String :=
    -- Prefix each line of the child's render with indent so the
    -- nesting is visually unambiguous.
    let rendered := toText child
    indent ++ rendered.replace "\n" ("\n" ++ indent)

instance : ToString Diagnostic where
  toString := Diagnostic.toText

/-! ## Source-line extract + caret underline (F6)

`toText` omits the §10.10 source-line + caret block because the
Diagnostic type itself holds only a `Span`, not the file bytes.
`renderWithSource` takes the source text alongside the diagnostic
and injects the missing rows under the headline:

```
error[T042]: ... at <source>:3:10

  let x : i64 = some_non_i64_value;
           ^^^^^^^^^^^^^^^^^^^^^^

  Goal:    i64
  Have:    i32
  ...
```

The extractor is best-effort: spans beyond the source's line
count, or zero spans, render without the source/caret block (just
the plain `toText`).  This keeps the renderer total — an
ill-formed span never blocks a diagnostic from reaching the user. -/

/-- Split a source text into lines by `\n`.  Preserves trailing
    newline behavior that `String.splitOn` gives: a trailing `\n`
    produces a trailing empty string, which is correct because
    a span ending at the last `\n` should still find the
    preceding line.  1-based line indexing at the output. -/
private def sourceLines (sourceText : String) : List String :=
  sourceText.splitOn "\n"

/-- Extract the source line at `span.start.line` (1-based) from
    `sourceText`, returning `none` when the line index is out of
    range.  Out-of-range = span is `Span.zero` OR the source has
    fewer lines than `span.start.line`. -/
private def extractSourceLine (span : FX.Syntax.Span) (sourceText : String) : Option String :=
  if span == FX.Syntax.Span.zero then none
  else
    let lineIndex := span.start.line
    if lineIndex == 0 then none
    else ((sourceLines sourceText).drop (lineIndex - 1)).head?

/-- Build the caret underline for a span on its own line.  `column`
    spaces, then `length` carets — clamped so we emit at least one
    caret (single-position spans still render a marker) and so a
    caret-count exceeding the line's length doesn't write past
    what the user sees. -/
private def caretUnderline (span : FX.Syntax.Span) (sourceLine : String) : String :=
  let startColumn := span.start.column
  let endColumn   := span.stop.column
  let lineLength  := sourceLine.length
  -- Cap startColumn against lineLength so a malformed span
  -- doesn't write a sea of spaces.
  let leading := min startColumn lineLength
  -- Caret length is the span width, but at least 1 (point spans
  -- still get a visible marker) and at most (lineLength -
  -- leading) so the underline stays within the source line.
  let rawWidth := endColumn - startColumn
  let width    := max 1 (min rawWidth (lineLength - leading + 1))
  let spaces := String.ofList (List.replicate leading ' ')
  let carets := String.ofList (List.replicate width '^')
  spaces ++ carets

/-- Render a Diagnostic with its source-line extract + caret
    underline per §10.10.  Uses `toText`'s blocks for Goal / Have /
    Gap / Suggestion / explain; the source+caret rows sit between
    the headline and the Goal block.

    When the span's line is out of range (or `Span.zero`), falls
    back to `toText`'s span-less shape — no source/caret block
    can be built without a resolvable line. -/
def renderWithSource (diag : Diagnostic) (sourceText : String) : String :=
  match extractSourceLine diag.span sourceText with
  | none => diag.toText  -- no resolvable source line; fall back
  | some sourceLine =>
    let loc      := locationSuffix diag.span
    let headline := s!"{diag.severity}[{diag.code}]: {diag.summary}{loc}"
    let srcBlock := s!"{indent}{sourceLine}\n{indent}{caretUnderline diag.span sourceLine}"
    let blocks : List String := [
      some headline,
      some srcBlock,
      goalBlock diag.goal diag.have_ diag.gap,
      suggestionBlock diag.suggestion,
      some (explainFooter diag.code)
    ].filterMap id
    let body := String.intercalate "\n\n" blocks
    if diag.notes.isEmpty then body
    else body ++ "\n" ++ String.intercalate "\n"
                           (diag.notes.map (fun child =>
                             indent ++ (toText child).replace "\n"
                                                              ("\n" ++ indent))).toList

end Diagnostic

end FX.Util

-- ── Compile-time sanity checks ──────────────────────────────────────

namespace FX.Util

open FX.Syntax

/-- `error` constructor produces severity `.error` and no
    extras. -/
example : (Diagnostic.error "T001" "bad").severity = .error := rfl
example : (Diagnostic.error "T001" "bad").goal     = none   := rfl

/-- Builders compose; `error |> withGoal |> withSuggestion`
    fills the corresponding fields and leaves the rest alone. -/
example :
    ((Diagnostic.error "T002" "mismatch").withGoal "T"
      |>.withSuggestion "let x : T = ...").goal       = some "T" := rfl
example :
    ((Diagnostic.error "T002" "mismatch").withGoal "T"
      |>.withSuggestion "let x : T = ...").suggestion = some "let x : T = ..." := rfl

/-- `isError` / `isWarning` discriminate without pattern-matching. -/
example : (Diagnostic.error   "T001" "bad").isError   = true  := by native_decide
example : (Diagnostic.warning "W001" "shadow").isError = false := by native_decide
example : (Diagnostic.warning "W001" "shadow").isWarning = true := by native_decide

/-- Notes attach to a parent; count and order preserved. -/
example :
    let parent := Diagnostic.error "T002" "mismatch"
    let note1  := Diagnostic.note  "T900" "previous binding here"
    let note2  := Diagnostic.note  "T901" "also relevant"
    (parent.addNote note1 |>.addNote note2).notes.size = 2 := rfl

/-- Minimal rendering — no optional fields — still emits
    headline + explain footer.  Shows the `error[CODE]: summary`
    line and the `[--explain CODE ...]` footer. -/
example :
    (Diagnostic.error "T001" "bad").toText =
    "error[T001]: bad\n\n  [--explain T001 for full documentation]" := by
  native_decide

/-- With a goal + suggestion, sections appear in §10.10 order. -/
example :
    (((Diagnostic.error "T002" "mismatch").withGoal "List Nat")
        |>.withSuggestion "let x : List Nat = ...").toText =
    "error[T002]: mismatch\n" ++
    "\n  Goal:    List Nat" ++
    "\n\n  Suggestion:\n    let x : List Nat = ..." ++
    "\n\n  [--explain T002 for full documentation]" := by
  native_decide

/-- Warning severity renders as `warning[CODE]` not `error[CODE]`. -/
example :
    ((Diagnostic.warning "W001" "unstable proof").toText).startsWith
      "warning[W001]" := by
  native_decide

/-! ## F6 — renderWithSource source-line + caret -/

/-- Build a span pointing at a specific (1-based) line / byte
    column, used to construct minimal-fixture diagnostics for
    the renderer tests. -/
private def pointSpan (line column offset length : Nat) : FX.Syntax.Span :=
  { start := { line := line, column := column, offset := offset }
  , stop  := { line := line, column := column + length, offset := offset + length } }

/-- Source line is extracted and shown; caret lines up under the
    span.  3-char wide span at column 4 of the second line. -/
example :
    let src := "fn foo() : Nat =\n  bad_body;"
    let diag := (Diagnostic.error "T042" "type mismatch" (pointSpan 2 2 19 3))
      |>.withGoal "Nat"
    (diag.renderWithSource src) =
    "error[T042]: type mismatch at <source>:2:2" ++
    "\n\n    bad_body;\n    ^^^" ++
    "\n\n  Goal:    Nat" ++
    "\n\n  [--explain T042 for full documentation]" := by
  native_decide

/-- Span at column 0 on first line — underline at far-left. -/
example :
    let src := "let x = 42;"
    let diag := Diagnostic.error "E020" "unsupported let-binding"
      (pointSpan 1 0 0 3)
    (diag.renderWithSource src) =
    "error[E020]: unsupported let-binding at <source>:1:0" ++
    "\n\n  let x = 42;\n  ^^^" ++
    "\n\n  [--explain E020 for full documentation]" := by
  native_decide

/-- Point span (stop = start) still emits a single `^` caret.
    Protects against spans produced by zero-width cursor positions
    (e.g., "expected token here" pointing at a gap). -/
example :
    let src := "fn foo()\n"
    let diag := Diagnostic.error "P001" "missing colon"
      { start := { line := 1, column := 8, offset := 8 }
      , stop  := { line := 1, column := 8, offset := 8 } }
    (diag.renderWithSource src).contains '^' = true := by
  native_decide

/-- Zero span falls back to plain `toText` — no source/caret block
    (there's no line to show). -/
example :
    let diag := Diagnostic.error "X000" "generic" Span.zero
    diag.renderWithSource "some source text" = diag.toText := by
  native_decide

/-- Out-of-range span (line beyond source's line count) also falls
    back to `toText`.  Keeps the renderer total on ill-formed
    spans. -/
example :
    let src := "only one line"
    let diag := Diagnostic.error "X001" "huh" (pointSpan 99 0 0 1)
    (diag.renderWithSource src) = diag.toText := by
  native_decide

end FX.Util
