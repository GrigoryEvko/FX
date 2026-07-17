import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialRingWitness

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialCharMinors — the k×k minors of `x·I − M` over ℤ[x]
(the second brick of the char-matrix → invariant-factors layer, WP-ENDO #2255)

The `EndomorphismMinorSelector` r2 minor selector (`selectSubmatrix`/`intMinorDet`) reads through
row/column index FUNCTIONS but is hard-wired to `Int`.  The generic `SetoidMatrix.cofactorDet` is
already carrier-generic, so the selector lifts to any `CommutativeRingWitness carrier` in one line:
`SetoidMatrix.submatrixByIndex` reindexes, `SetoidMatrix.minorDet` takes the generic determinant of
the selected square sub-block.

Instantiated at the ℤ[x] ring witness (`intPolynomialRingWitness`) on the characteristic matrix
`charMatrix M = x·I − M`, `charMatrixMinor` yields a **polynomial** k×k minor — the raw ingredient of
the determinantal divisor `d_k = gcd of all k×k minors of x·I − M`, whose successive quotients
`s_k = d_k / d_{k-1}` (via the shipped ℤ[x] GCD) are the invariant factors classifying similarity.

## Why the minors classify

The determinantal divisors already separate the three archetypes at dimension 2:

  * `diag(2,3)` — the two diagonal 1×1 minors are `x−2` and `x−3` (coprime), so `d₁ = 1`, `d₂ =
    (x−2)(x−3)`: one invariant factor, the char poly (non-derogatory, distinct eigenvalues).
  * `2·I` — the off-diagonal 1×1 minors are `0`, so `d₁ = gcd(x−2, x−2) = x−2`, `d₂ = (x−2)²`: two
    invariant factors `(x−2), (x−2)`.
  * the Jordan block `[[2,1],[0,2]]` — the `(0,1)` 1×1 minor is the **unit** `−1`, so `d₁ = 1`, `d₂ =
    (x−2)²`: one invariant factor `(x−2)²`.

`2·I` and the Jordan block share char poly `(x−2)²` yet differ in `d₁` (`x−2` vs the unit `1`) — the
minors of `x·I − M` see the similarity difference the char poly cannot.  The distinguishing 1×1 minors
are grounded here by `decide`; the GCD fold that turns them into `d_k` is the next brick.

## Zero-axiom design

`submatrixByIndex` is a structure literal, `minorDet` is a `cofactorDet` application, `charMatrixMinor`
specializes them at the polynomial witness — all plain defs.  Groundings are `decide` over concrete
`polyTrim`med `List Int`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in the audit twin.
-/

namespace FX1Poly.ComputerAlgebra

namespace SetoidMatrix

/-! ## The carrier-generic minor selector -/

/-- The submatrix reading through row/column index FUNCTIONS over ANY carrier: entry `(i, j)` is the
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

/-- ★ The distinguishing minor for the Jordan block `[[2,1],[0,2]]`: its `(0,1)` 1×1 minor is the
**unit** `−1` (`[−1]`), so the determinantal divisor `d₁` of `x·I − J` is a unit (`1`). -/
theorem charMatrixMinorJordanOffDiagIsUnit :
    polyTrim (charMatrixMinor 1 (twoByTwoMatrix 2 1 0 2) selectOnlyZero selectOnlyOne) = [-1] := by
  decide

/-- ★ The corresponding minor for the scalar `2·I`: its `(0,1)` 1×1 minor is `0` (`[]`), so the
determinantal divisor `d₁` of `x·I − 2·I` is `gcd(x−2, x−2) = x−2`, NOT a unit — the minor-level
witness that `2·I` and the Jordan block, which share char poly `(x−2)²`, are NOT similar. -/
theorem charMatrixMinorScalarOffDiagIsZero :
    polyTrim (charMatrixMinor 1 (twoByTwoMatrix 2 0 0 2) selectOnlyZero selectOnlyOne) = [] := by
  decide

/-! ## The marker -/

/-- ★ **The characteristic-matrix minors over ℤ[x] are shipped.**  `= true` records that the generic
minor selector (`SetoidMatrix.submatrixByIndex`/`minorDet`) instantiated at the polynomial ring witness
computes any `k×k` minor of `x·I − M` as a genuine ℤ[x] polynomial — the raw ingredient of the
determinantal divisors `d_k = gcd of the k×k minors`, whose quotients are the invariant factors.  The
off-diagonal 1×1 minor already separates the scalar `2·I` (`d₁ = x−2`) from the Jordan block `[[2,1],
[0,2]]` (`d₁ = unit`), which share a characteristic polynomial. -/
def fxIntPoly_hasCharMatrixMinors : Bool := true

end FX1Poly.ComputerAlgebra
