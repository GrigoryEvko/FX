-- FX.Util.Basic — leaf utility layer for leanx.
--
-- Role: the error / result vocabulary that every other layer
-- (`Syntax`, `Kernel`, `Elab`, `Cli`) consumes.  Must stay a
-- dependency-free leaf — importing `FX.Kernel` or `FX.Syntax`
-- from here would cycle.
--
-- Phase-1 surface:
--   * `Error`            structured diagnostic  (code + message + span)
--   * `Error.make`       source-free constructor
--   * `Error.withSource` / `withoutSource` span tagging
--   * `Error.attach`     prepend context, format `"<ctx>: <msg>"`
--   * `Error.isWarning`  true when the code starts with `W`
--   * `Result valueType`         `Except (Array Error) valueType`, accumulates errors
--
-- Error codes follow `fx_design.md` §10.10 (Txxx/Rxxx/Exxx/Mxxx/
-- Sxxx/Ixxx/Pxxx/Nxxx/Wxxx).

namespace FX.Util

/-- A structured compile-time error carrying an error code and a
    message.  Code taxonomy matches `fx_design.md` §10.10:
      Txxx  type errors
      Rxxx  refinement errors
      Exxx  effect errors
      Mxxx  mode / ownership errors
      Sxxx  session type errors
      Ixxx  information flow errors
      Pxxx  proof errors
      Nxxx  precision errors
      Wxxx  warnings
-/
structure Error where
  code    : String
  message : String
  source  : Option (String × Nat × Nat) := none  -- (file, line, col)
  deriving Repr, DecidableEq

namespace Error

/-- Build a source-free error.  Prefer this over raw struct syntax
    so call sites read like prose and not like record literals. -/
def make (code message : String) : Error :=
  { code := code, message := message, source := none }

/-- Attach a source location to an existing error.  If the error
    already has a source, the new one replaces it — callers should
    attach at the outermost layer that knows the span. -/
def withSource (error : Error) (fileName : String) (lineNumber columnNumber : Nat)
    : Error :=
  { error with source := some (fileName, lineNumber, columnNumber) }

/-- Strip the source location.  Useful when testing equality modulo
    where the error was found. -/
def withoutSource (error : Error) : Error :=
  { error with source := none }

/-- Prepend context to an error's message, keeping the code and
    source.  The separator is the literal three characters `": "`
    (colon-space); callers rely on this being stable for agent
    parsing.  Do not change without bumping the CLI protocol version
    surfaced by `fxi version --json`.

    Example: `error.attach "while parsing Auth.fx"` produces
    `"while parsing Auth.fx: <original message>"`. -/
def attach (error : Error) (context : String) : Error :=
  { error with message := context ++ ": " ++ error.message }

/-- `true` iff the code is a warning (starts with `W`).  Everything
    else — errors proper — must be distinguishable because some
    pipelines want to emit warnings non-fatally. -/
def isWarning (error : Error) : Bool :=
  error.code.startsWith "W"

end Error

instance : ToString Error where
  toString error :=
    let locationPrefix := match error.source with
      | some (fileName, lineNumber, columnNumber) =>
        s!"{fileName}:{lineNumber}:{columnNumber}: "
      | none => ""
    s!"{locationPrefix}error[{error.code}]: {error.message}"

/-- Result of a fallible operation.  Carries a list of errors on
    failure because elaboration often wants to report several issues
    at once rather than stopping at the first. -/
abbrev Result (valueType : Type) := Except (Array Error) valueType

namespace Result

/-- Lift a value into the success branch. -/
def succeed {valueType : Type} (value : valueType) : Result valueType :=
  Except.ok value

/-- Fail with exactly one error. -/
def failOne {valueType : Type} (error : Error) : Result valueType :=
  Except.error #[error]

/-- Fail with a prepared array of errors. -/
def failMany {valueType : Type} (errors : Array Error) : Result valueType :=
  Except.error errors

/-- `true` iff the result is `Except.ok _`. -/
def isOk {valueType : Type} : Result valueType → Bool
  | .ok _    => true
  | .error _ => false

/-- `true` iff the result is `Except.error _`. -/
def isError {valueType : Type} : Result valueType → Bool
  | .ok _    => false
  | .error _ => true

/-- Project the error array, or `#[]` on success. -/
def errors {valueType : Type} : Result valueType → Array Error
  | .ok _     => #[]
  | .error es => es

end Result

end FX.Util

-- ── Compile-time sanity checks ──────────────────────────────────────
-- These `example` declarations verify the invariants that the CLI
-- and the agent protocol depend on.  They are elaborated during
-- `lake build` but produce no runtime artefacts.

namespace FX.Util

/-- `Error.attach` uses the literal separator `": "`.  The CLI and
    any agent consuming `fxi` output rely on this split token. -/
example :
    (Error.make "T001" "bad").attach "parsing" =
    { code := "T001", message := "parsing: bad", source := none } :=
  rfl

/-- Two errors with the same fields compare equal; two with different
    codes compare unequal.  Decidability is derived on `Error`. -/
example :
    decide (Error.make "T001" "x" = Error.make "T001" "x") = true := rfl
example :
    decide (Error.make "T001" "x" = Error.make "T002" "x") = false := rfl

/-- `Result.isOk` / `isError` agree with `Except` constructors; this
    is the discriminator the CLI uses to pick its exit code. -/
example : (Result.succeed (valueType := Nat) 7).isOk     = true  := rfl
example : (Result.succeed (valueType := Nat) 7).isError  = false := rfl
example : (Result.failOne (valueType := Nat) (Error.make "T001" "x")).isError = true := rfl
example : (Result.failOne (valueType := Nat) (Error.make "T001" "x")).isOk    = false := rfl

/-- `isWarning` fires exactly on the `W` prefix.  `String.startsWith`
    does not reduce at elaboration time, so we use `native_decide`. -/
example : (Error.make "W001" "shadow").isWarning = true  := by native_decide
example : (Error.make "T001" "bad").isWarning    = false := by native_decide

end FX.Util
