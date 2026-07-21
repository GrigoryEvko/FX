import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialRingWitness

/-! # IntPolynomialCharMinors — the k×k minors of `x·I − M` over ℤ[x]

The generic `SetoidMatrix.cofactorDet` is carrier-generic, so the minor selector lifts to any
`CommutativeRingWitness`: `submatrixByIndex` reindexes through row/column index functions, `minorDet` takes
the generic determinant of the selected square sub-block.  Instantiated at the ℤ[x] ring witness on the
characteristic matrix `charMatrix M = x·I − M`, `charMatrixMinor` yields a polynomial k×k minor — the raw
ingredient of the determinantal divisor `d_k = gcd of all k×k minors of x·I − M`, whose successive quotients
are the invariant factors classifying similarity.

At dimension 2 the distinguishing 1×1 minors already separate similarity classes the characteristic
polynomial cannot: `2·I` and the Jordan block `[[2,1],[0,2]]` share char poly `(x−2)²`, yet the `(0,1)`
minor is `0` for the scalar (so `d₁ = x−2`) and the unit `−1` for the Jordan block (so `d₁ = 1`).

`submatrixByIndex`/`minorDet`/`charMatrixMinor` are plain defs; groundings are `decide` over concrete
`polyTrim`med `List Int`.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`. -/

namespace FX1Poly.ComputerAlgebra

namespace SetoidMatrix

/-! ## The carrier-generic minor selector -/

/-- The submatrix reading through row/column index functions over any carrier: entry `(i, j)` is the
original entry at `(rowSelect i, colSelect j)`, with the caller's declared
`selectedRowCount × selectedColCount` shape.  Function-valued (not list-valued) so the substrate stays
propext-free — the carrier-generic lift of `selectSubmatrix`. -/
def submatrixByIndex {carrier : Type} (matrix : SetoidMatrix carrier)
    (selectedRowCount selectedColCount : Nat) (rowSelect colSelect : Nat → Nat) :
    SetoidMatrix carrier :=
  { rowCount := selectedRowCount
    colCount := selectedColCount
    entry := fun rowIndex colIndex => matrix.entry (rowSelect rowIndex) (colSelect colIndex) }

/-- The `k × k` minor determinant over any `CommutativeRingWitness`: pick `k` rows and `k` columns via
the selection functions, take the generic `cofactorDet` of the selected square sub-block.  The
carrier-generic lift of `intMinorDet`. -/
def minorDet {carrier : Type} (ring : CommutativeRingWitness carrier) (matrix : SetoidMatrix carrier)
    (minorSize : Nat) (rowSelect colSelect : Nat → Nat) : carrier :=
  cofactorDet ring minorSize (submatrixByIndex matrix minorSize minorSize rowSelect colSelect)

end SetoidMatrix

/-! ## The characteristic-matrix minors over ℤ[x] -/

/-- A `k × k` minor of the characteristic matrix `x·I − M`, valued in ℤ[x]: the generic minor selector
at the polynomial ring witness on `charMatrix matrix`.  This is a polynomial; the determinantal divisor
`d_k` is the ℤ[x] GCD of all such minors over the `k`-index selections. -/
def charMatrixMinor (minorSize : Nat) (matrix : SetoidMatrix Int)
    (rowSelect colSelect : Nat → Nat) : List Int :=
  SetoidMatrix.minorDet intPolynomialRingWitness (charMatrix matrix) minorSize rowSelect colSelect

/-! ## Index selections -/

/-- Select index `0` for every position (a singleton `{0}` selection). -/
def selectOnlyZero : Nat → Nat := fun _ => 0

/-- Select index `1` for every position (a singleton `{1}` selection). -/
def selectOnlyOne : Nat → Nat := fun _ => 1

/-- Select index `i` at position `i` (the identity — the full leading-block selection). -/
def selectIdentity : Nat → Nat := fun index => index

/-! ## A `2 × 2` integer matrix from its four entries -/

/-- The `2 × 2` integer matrix with the given entries, for grounding the char-matrix minors. -/
def twoByTwoMatrix (topLeft topRight bottomLeft bottomRight : Int) : SetoidMatrix Int :=
  { rowCount := 2, colCount := 2,
    entry := fun rowIndex colIndex =>
      if rowIndex = 0 then (if colIndex = 0 then topLeft else topRight)
      else (if colIndex = 0 then bottomLeft else bottomRight) }

/-! ## Groundings — char-matrix minors are genuine ℤ[x] polynomials -/

/-- The `(0,0)` 1×1 minor of `x·I − diag(2,3)` is `x − 2` (`[−2, 1]`). -/
theorem charMatrixMinorDiagTopLeftIsXMinusTwo :
    polyTrim (charMatrixMinor 1 (twoByTwoMatrix 2 0 0 3) selectOnlyZero selectOnlyZero) = [-2, 1] := by
  decide

/-- The `(1,1)` 1×1 minor of `x·I − diag(2,3)` is `x − 3` (`[−3, 1]`). -/
theorem charMatrixMinorDiagBottomRightIsXMinusThree :
    polyTrim (charMatrixMinor 1 (twoByTwoMatrix 2 0 0 3) selectOnlyOne selectOnlyOne) = [-3, 1] := by
  decide

/-- The full `2×2` minor of `x·I − diag(2,3)` is `(x−2)(x−3) = x² − 5x + 6` (`[6, −5, 1]`) — the
identity selection recovers the whole characteristic polynomial. -/
theorem charMatrixMinorDiagFullIsCharPoly :
    polyTrim (charMatrixMinor 2 (twoByTwoMatrix 2 0 0 3) selectIdentity selectIdentity) = [6, -5, 1] := by
  decide

/-- The distinguishing minor for the Jordan block `[[2,1],[0,2]]`: its `(0,1)` 1×1 minor is the unit `−1`
(`[−1]`), so the determinantal divisor `d₁` of `x·I − J` is a unit (`1`). -/
theorem charMatrixMinorJordanOffDiagIsUnit :
    polyTrim (charMatrixMinor 1 (twoByTwoMatrix 2 1 0 2) selectOnlyZero selectOnlyOne) = [-1] := by
  decide

/-- The corresponding minor for the scalar `2·I`: its `(0,1)` 1×1 minor is `0` (`[]`), so the
determinantal divisor `d₁` of `x·I − 2·I` is `gcd(x−2, x−2) = x−2`, not a unit — the minor-level witness
that `2·I` and the Jordan block, which share char poly `(x−2)²`, are not similar. -/
theorem charMatrixMinorScalarOffDiagIsZero :
    polyTrim (charMatrixMinor 1 (twoByTwoMatrix 2 0 0 2) selectOnlyZero selectOnlyOne) = [] := by
  decide

end FX1Poly.ComputerAlgebra
