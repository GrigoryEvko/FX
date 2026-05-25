/-!
# CheckResult — Raw-to-Certified Rejection Reasons

This file defines the finite rejection vocabulary for the future computable
raw-to-certified PolyCell checker.  It does not accept any raw cell and does
not prove checker soundness; it only fixes the concrete reasons a checker must
return when raw input fails a certified-cell invariant.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Why raw PolyCell input failed certification. -/
inductive CellCheckRejection where
  /-- The raw generator or rule id is not present in the supported table. -/
  | unknownGenerator
  /-- The inferred sort is not the sort requested by an expected-shape check. -/
  | wrongSort
  /-- The raw payload does not decode according to the generator metadata. -/
  | badPayload
  /-- The decoded raw child count differs from the generator child specs. -/
  | wrongArity
  /-- A decoded child has the wrong sort, dimension, or shifted scope. -/
  | wrongChildShape
  /-- A source or target endpoint is not certified. -/
  | badBoundaryEndpoint
  /-- A vertical composite has mismatched middle endpoints. -/
  | badVerticalBoundary
  /-- Raw horizontal composition is not yet supported by certified PolyCell. -/
  | unsupportedCompH
  deriving DecidableEq

namespace CellCheckRejection

/-- Stable finite enumeration of rejection reasons. -/
def all : List CellCheckRejection :=
  [.unknownGenerator, .wrongSort, .badPayload, .wrongArity,
    .wrongChildShape, .badBoundaryEndpoint, .badVerticalBoundary,
    .unsupportedCompH]

/-- Stable numeric code for compact diagnostics. -/
def toCode : CellCheckRejection → Nat
  | .unknownGenerator => 0
  | .wrongSort => 1
  | .badPayload => 2
  | .wrongArity => 3
  | .wrongChildShape => 4
  | .badBoundaryEndpoint => 5
  | .badVerticalBoundary => 6
  | .unsupportedCompH => 7

/-- Decode a stable rejection code. -/
def ofCode? : Nat → Option CellCheckRejection
  | 0 => some .unknownGenerator
  | 1 => some .wrongSort
  | 2 => some .badPayload
  | 3 => some .wrongArity
  | 4 => some .wrongChildShape
  | 5 => some .badBoundaryEndpoint
  | 6 => some .badVerticalBoundary
  | 7 => some .unsupportedCompH
  | _ => none

/-- Encoding then decoding a rejection reason recovers the original reason. -/
theorem ofCode?_toCode (rejection : CellCheckRejection) :
    ofCode? rejection.toCode = some rejection := by
  cases rejection <;> rfl

/-- The rejection enumeration has exactly eight entries. -/
theorem all_length : all.length = 8 := rfl

end CellCheckRejection

end LeanFX2.Foundation.PolyCell.Core
