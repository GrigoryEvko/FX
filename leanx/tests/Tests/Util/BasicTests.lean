import FX.Util.Basic
import Tests.Framework

/-!
# Util.Basic runtime tests

Covers `FX/Util/Basic.lean`:

  * `Error` carries code + message + optional source
  * `ToString Error` formats `loc: error[CODE]: MESSAGE`
  * `Result.succeed` lifts a value
  * `Result.failOne` and `Result.failMany` wrap errors
-/

namespace Tests.Util.BasicTests

open Tests FX.Util

def typeMismatchError : Error :=
  { code := "T001", message := "type mismatch" }

def precondFailedError : Error :=
  { code := "R005"
  , message := "precondition failed"
  , source := some ("Foo.fx", 12, 4) }

def run : IO Unit := Tests.suite "Tests.Util.BasicTests" do
  -- Error fields.
  check "typeMismatchError.code"    "T001"          typeMismatchError.code
  check "typeMismatchError.message" "type mismatch" typeMismatchError.message
  check "typeMismatchError.source"
    (valueType := Option (String × Nat × Nat)) none typeMismatchError.source
  check "precondFailedError.source"
    (valueType := Option (String × Nat × Nat))
    (some ("Foo.fx", 12, 4)) precondFailedError.source

  -- ToString formatting.
  check "ToString Error without source"
    "error[T001]: type mismatch"
    (toString typeMismatchError)
  check "ToString Error with source"
    "Foo.fx:12:4: error[R005]: precondition failed"
    (toString precondFailedError)

  -- Result constructors.  `Except` doesn't derive DecidableEq in
  -- std4, so we project into Option / Array and compare those.
  let successResult : Result Nat := Result.succeed 42
  check "Result.succeed projects to some 42"
    (some 42) (successResult.toOption)

  let singleFailResult : Result Nat := Result.failOne typeMismatchError
  check "Result.failOne has exactly one error"
    1 (match singleFailResult with | .error errs => errs.size | _ => 0)

  let multiFailResult : Result Nat :=
    Result.failMany #[typeMismatchError, precondFailedError]
  check "Result.failMany preserves error array"
    #[typeMismatchError, precondFailedError]
    (match multiFailResult with | .error errs => errs | _ => #[])

end Tests.Util.BasicTests
