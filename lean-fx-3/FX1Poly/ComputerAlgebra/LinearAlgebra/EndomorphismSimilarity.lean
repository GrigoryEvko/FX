import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidMatrixRing
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntFractionFree

/-! # EndomorphismSimilarity — the walking-endomorphism linear model

The walking endomorphism is one object with one generating self-loop and no relations; its linear
model over a field is a square matrix `M` on a chosen basis, and two representations are isomorphic
exactly when the matrices are similar (`N = S⁻¹ M S` for invertible `S`).  This file is the
certificate producer for that classification over `SetoidMatrix Int`, whose setoid at ℤ is plain
`Eq`, so every check is an integer literal.

Similar integer matrices need not be integer-unimodular-conjugate (the conjugator lives over ℚ), and
a ℚ matrix carrier is undecidable.  Clearing denominators once, a witness carries `(P, Q, d)` with
`d ≠ 0` and the integer identities `P · Q = d · I` and `Q · (A · P) = d · B` (so `P⁻¹ A P = B` over
ℚ).  The adjugate construction `Q = adj(P)`, `d = det(P)` shows this covers every ℚ-similar integer
pair.  The lane contract is per-input: no general decision procedure is claimed.

Zero-axiom design: `agreeOnWindow` is a bounded double-`∀` over `Nat` decided by
`Nat.decidableBallLT` and `Int.decEq`, with no `Nat.min`/`Nat.sub` inside any decided expression.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`; gated per
declaration in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

open SetoidMatrix

/-! ## The windowed-equality substrate (the `DenoteSame`-avoidance pin) -/

/-- Two `SetoidMatrix Int` grids agree on the `height × width` window: entries match at every in-range
index.  A bounded double-`∀` so `Decidable` synthesis unfolds it to `Nat.decidableBallLT`, not the
undecidable `DenoteSame` (which quantifies over all `Nat`). -/
@[reducible] def agreeOnWindow (leftMatrix rightMatrix : SetoidMatrix Int) (height width : Nat) :
    Prop :=
  ∀ rowIndex : Nat, rowIndex < height → ∀ colIndex : Nat, colIndex < width →
    leftMatrix.entry rowIndex colIndex = rightMatrix.entry rowIndex colIndex

/-! ## The scaled-pair witness -/

/-- A certificate that `source` and `target` are ℚ-similar, presented over ℤ: `changeOfBasis` is `P`,
`scaledInverse` is `Q = d · P⁻¹`, `scale` is `d`, checked by `WitnessesSimilarity`. -/
structure EndomorphismSimilarityWitness where
  dimension : Nat
  source : SetoidMatrix Int
  target : SetoidMatrix Int
  changeOfBasis : SetoidMatrix Int
  scaledInverse : SetoidMatrix Int
  scale : Int

/-! ## Substrate truth-probe

The `d = 2` inverse window `P · Q = 2 · I` for `P = [[1,1],[0,2]]`, `Q = adj(P) = [[2,-1],[0,1]]`,
decided against `scalarMul 2 I`: the windowed check sees the real integer product. -/
theorem endomorphismScaledInverseWindowProbe :
    agreeOnWindow
      (mulMatrix intCommutativeRingWitness (setoidMatrixOfRows [[1, 1], [0, 2]])
        (setoidMatrixOfRows [[2, -1], [0, 1]]))
      (scalarMul intCommutativeRingWitness 2 (identityMatrix intCommutativeRingWitness 2)) 2 2 := by
  decide

/-- The checker: the `d ≠ 0` guard (`1 ≤ Int.natAbs d`) plus the two window identities `P · Q = d · I`
and `Q · (A · P) = d · B`.  Reducible, so each concrete instance closes by `decide`. -/
@[reducible] def EndomorphismSimilarityWitness.WitnessesSimilarity
    (witness : EndomorphismSimilarityWitness) : Prop :=
  1 ≤ Int.natAbs witness.scale
  ∧ agreeOnWindow
      (mulMatrix intCommutativeRingWitness witness.changeOfBasis witness.scaledInverse)
      (scalarMul intCommutativeRingWitness witness.scale
        (identityMatrix intCommutativeRingWitness witness.dimension))
      witness.dimension witness.dimension
  ∧ agreeOnWindow
      (mulMatrix intCommutativeRingWitness witness.scaledInverse
        (mulMatrix intCommutativeRingWitness witness.source witness.changeOfBasis))
      (scalarMul intCommutativeRingWitness witness.scale witness.target)
      witness.dimension witness.dimension

/-! ## Self-attack: singular-`P` and degenerate-`d` rejection

Two forgeries of a "universal" similarity are rejected by the checker, both targeting the dissimilar
pair `[[1,0],[0,0]]` (trace 1) vs `[[2,0],[0,0]]` (trace 2). -/

/-- A singular change of basis (`P = 0`) with a nonzero scale (`d = 1`).  The guard passes, but
`P · Q = 0 ≠ 1 · I` at entry `(0,0)` (`0 ≠ 1`), so the inverse window rejects it. -/
def endomorphismSingularBasisWitness : EndomorphismSimilarityWitness :=
  { dimension := 2
    source := setoidMatrixOfRows [[1, 0], [0, 0]]
    target := setoidMatrixOfRows [[2, 0], [0, 0]]
    changeOfBasis := setoidMatrixOfRows [[0, 0], [0, 0]]
    scaledInverse := setoidMatrixOfRows [[0, 0], [0, 0]]
    scale := 1 }

/-- The singular-`P` witness is rejected: no nonzero-scale inverse can hold for a zero basis. -/
theorem endomorphismSingularBasisRejected :
    ¬ endomorphismSingularBasisWitness.WitnessesSimilarity := by decide

/-- The degenerate `d = 0` forgery (`P = Q = 0`): without the guard this fakes similarity of any pair,
since `P · Q = 0 · I` and `Q · A · P = 0 · B` both hold.  The `d ≠ 0` guard rejects it. -/
def endomorphismDegenerateScaleWitness : EndomorphismSimilarityWitness :=
  { dimension := 2
    source := setoidMatrixOfRows [[1, 0], [0, 0]]
    target := setoidMatrixOfRows [[2, 0], [0, 0]]
    changeOfBasis := setoidMatrixOfRows [[0, 0], [0, 0]]
    scaledInverse := setoidMatrixOfRows [[0, 0], [0, 0]]
    scale := 0 }

/-- The degenerate `d = 0` witness is rejected by the `d ≠ 0` guard. -/
theorem endomorphismDegenerateScaleRejected :
    ¬ endomorphismDegenerateScaleWitness.WitnessesSimilarity := by decide

/-! ## Separator engine 1: the characteristic polynomial

`det(x·I − M)` as an ascending coefficient list, closed form at `n = 2, 3`; a `≠` certifies
dissimilarity.  `EndomorphismCharPolyThree` extends it to the principal-minor coefficient reading. -/

/-- The characteristic-polynomial coefficients of `matrix`, ascending (`[c₀, …, cₙ = 1]`), in closed
form at `n = 2` (`x² − tr·x + det`) and `n = 3` (`x³ − c₁x² + c₂x − c₃`); other sizes return `[]`. -/
def endomorphismCharPolyCoefficients (dimension : Nat) (matrix : SetoidMatrix Int) : List Int :=
  match dimension with
  | 2 =>
      let traceValue := matrix.entry 0 0 + matrix.entry 1 1
      [intCofactorDet 2 matrix, -traceValue, 1]
  | 3 =>
      let traceValue := matrix.entry 0 0 + matrix.entry 1 1 + matrix.entry 2 2
      let principalTwoMinorSum :=
        (matrix.entry 0 0 * matrix.entry 1 1 - matrix.entry 0 1 * matrix.entry 1 0)
          + (matrix.entry 0 0 * matrix.entry 2 2 - matrix.entry 0 2 * matrix.entry 2 0)
          + (matrix.entry 1 1 * matrix.entry 2 2 - matrix.entry 1 2 * matrix.entry 2 1)
      [-(intCofactorDet 3 matrix), principalTwoMinorSum, -traceValue, 1]
  | _ => []

/-- `source` and `target` are dissimilar because their characteristic polynomials differ. -/
@[reducible] def EndomorphismDissimilarByCharPoly (dimension : Nat)
    (source target : SetoidMatrix Int) : Prop :=
  endomorphismCharPolyCoefficients dimension source
    ≠ endomorphismCharPolyCoefficients dimension target

/-- Grounding: the `2×2` char-poly of `[[1,1],[0,3]]` is `x² − 4x + 3` (trace 4, det 3). -/
theorem endomorphismCharPolyTwoByTwoExample :
    endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[1, 1], [0, 3]]) = [3, -4, 1] := by decide

/-- Grounding: the `3×3` char-poly of `diag(2,3,4)` is `x³ − 9x² + 26x − 24`. -/
theorem endomorphismCharPolyThreeByThreeExample :
    endomorphismCharPolyCoefficients 3 (setoidMatrixOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]])
      = [-24, 26, -9, 1] := by decide

/-! ## Separator engine 2: the `2×2` rank (separates the equal-char-poly nilpotents)

Rank is a similarity invariant, so a `≠` between two ranks certifies dissimilarity, separating the
`0` vs Jordan-block pair that char poly cannot see.  Higher rank and the full nilpotent separator
(the rank sequence `rank(Mᵏ)`) are closed in `EndomorphismMinorSelector` and
`EndomorphismPowerZeroSeparator`. -/

/-- The rank of a `2×2` integer matrix (a similarity invariant): `2` if `det ≠ 0`, else `0`/`1`. -/
def endomorphismRank2 (matrix : SetoidMatrix Int) : Nat :=
  if intCofactorDet 2 matrix = 0 then
    (if matrix.entry 0 0 = 0 ∧ matrix.entry 0 1 = 0 ∧ matrix.entry 1 0 = 0 ∧ matrix.entry 1 1 = 0
      then 0 else 1)
  else 2

/-- `source` and `target` are dissimilar because their `2×2` ranks differ. -/
@[reducible] def EndomorphismDissimilarByRank (source target : SetoidMatrix Int) : Prop :=
  endomorphismRank2 source ≠ endomorphismRank2 target

/-- Grounding: the zero matrix has rank `0`. -/
theorem endomorphismRankZeroExample :
    endomorphismRank2 (setoidMatrixOfRows [[0, 0], [0, 0]]) = 0 := by decide

/-- Grounding: a single Jordan block `[[0,1],[0,0]]` has rank `1` (`det = 0`, not all-zero). -/
theorem endomorphismRankOneExample :
    endomorphismRank2 (setoidMatrixOfRows [[0, 1], [0, 0]]) = 1 := by decide

/-- Grounding: the identity has full rank `2` (`det = 1 ≠ 0`). -/
theorem endomorphismRankTwoExample :
    endomorphismRank2 (setoidMatrixOfRows [[1, 0], [0, 1]]) = 2 := by decide

/-! ## The decided instances

Two similar pairs with kernel-checked scaled-pair witnesses, and two dissimilar pairs with
kernel-checked separators, including the equal-char-poly pair that only rank tells apart. -/

/-- Similar #1, unimodular (`d = 1`): the nilpotent `[[0,1],[0,0]]` conjugated by `P = [[1,0],[1,1]]`
(`Q = P⁻¹`) to `[[1,1],[-1,-1]]` — the classical integer-unimodular case. -/
def endomorphismNilpotentConjugacyWitness : EndomorphismSimilarityWitness :=
  { dimension := 2
    source := setoidMatrixOfRows [[0, 1], [0, 0]]
    target := setoidMatrixOfRows [[1, 1], [-1, -1]]
    changeOfBasis := setoidMatrixOfRows [[1, 0], [1, 1]]
    scaledInverse := setoidMatrixOfRows [[1, 0], [-1, 1]]
    scale := 1 }

/-- The unimodular nilpotent conjugacy is machine-checked: `P · Q = I` and `Q · (A · P) = B`. -/
theorem endomorphismNilpotentConjugacyIsWitnessed :
    endomorphismNilpotentConjugacyWitness.WitnessesSimilarity := by decide

/-- Similar #2, the scaled trick (`d = 2`): `A = [[1,1],[0,3]]` and `B = [[1,0],[0,3]]` are ℚ-similar
but not integer-unimodular-conjugate.  Cleared to `P = [[1,1],[0,2]]`, `Q = adj(P) = [[2,-1],[0,1]]`,
`d = 2`, so `P · Q = 2·I` and `Q · (A · P) = 2·B`.  This exercises the scaled pair. -/
def endomorphismRationalConjugacyWitness : EndomorphismSimilarityWitness :=
  { dimension := 2
    source := setoidMatrixOfRows [[1, 1], [0, 3]]
    target := setoidMatrixOfRows [[1, 0], [0, 3]]
    changeOfBasis := setoidMatrixOfRows [[1, 1], [0, 2]]
    scaledInverse := setoidMatrixOfRows [[2, -1], [0, 1]]
    scale := 2 }

/-- The `d = 2` rational conjugacy is machine-checked: `P · Q = 2·I` and `Q · (A · P) = 2·B`. -/
theorem endomorphismRationalConjugacyIsWitnessed :
    endomorphismRationalConjugacyWitness.WitnessesSimilarity := by decide

/-- Dissimilar #1, char poly (trace differs): `[[1,0],[0,0]]` (char-poly `x² − x`) vs
`[[2,0],[0,0]]` (char-poly `x² − 2x`).  Distinct trace ⇒ distinct char-poly ⇒ dissimilar. -/
theorem endomorphismDistinctTraceDissimilar :
    EndomorphismDissimilarByCharPoly 2 (setoidMatrixOfRows [[1, 0], [0, 0]])
      (setoidMatrixOfRows [[2, 0], [0, 0]]) := by decide

/-- Dissimilar #2, equal char poly, rank-separated: the zero matrix vs the Jordan block
`[[0,1],[0,0]]`: both have char poly `x²`, so char poly is blind; rank `0` vs `1` separates them. -/
theorem endomorphismZeroVersusJordanDissimilar :
    EndomorphismDissimilarByRank (setoidMatrixOfRows [[0, 0], [0, 0]])
      (setoidMatrixOfRows [[0, 1], [0, 0]]) := by decide

/-- The zero-vs-Jordan pair SHARES a characteristic polynomial (`x²`), confirming char-poly cannot
separate it — the rank separator above is necessary. -/
theorem endomorphismZeroVersusJordanShareCharPoly :
    endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[0, 0], [0, 0]])
      = endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[0, 1], [0, 0]]) := by decide

/-! ## The walker tie-in

The walking endomorphism is the one-object, one-generating-1-cell, no-relation polygraph — the
delooping of the free monoid `ℕ`.  Its rewriting presentation is trivially convergent, so its content
is the linear model: iso-classification of representations `(V, f : V → V)` is similarity of `M`,
i.e. rational canonical form — the matrix-semantics axis, mirroring
`WalkingBunchedBimonoidMatrixSemantics`.  The sharper separators and the open invariant-factor wall
are summarized at `fxEndo_hasSeparatorSuite` below. -/

/-- The classification axis of the walking-endomorphism linear model: representations up to iso ⇔
matrices up to similarity ⇔ rational canonical form. -/
inductive WalkingEndomorphismClassification
  | similarByRationalCanonicalForm

/-- A census entry: the classification marker plus the counts of kernel-checked similar witnesses and
dissimilarity separators shipped as its grounding. -/
structure WalkingEndomorphismCensusEntry where
  classification : WalkingEndomorphismClassification
  decidedSimilarInstances : Nat
  decidedDissimilarInstances : Nat

/-- The census feed: two decided similar witnesses (`d = 1`, `d = 2`) and two decided separators
(char poly, rank). -/
def walkingEndomorphismCensusEntry : WalkingEndomorphismCensusEntry :=
  { classification := WalkingEndomorphismClassification.similarByRationalCanonicalForm
    decidedSimilarInstances := 2
    decidedDissimilarInstances := 2 }

/-- The census feed grounded: the two scaled-pair witnesses and the two dissimilarity separators
bundled into one certificate, so the counts are backed by machine-checked evidence. -/
theorem walkingEndomorphismCensusGrounded :
    endomorphismNilpotentConjugacyWitness.WitnessesSimilarity
      ∧ endomorphismRationalConjugacyWitness.WitnessesSimilarity
      ∧ EndomorphismDissimilarByCharPoly 2 (setoidMatrixOfRows [[1, 0], [0, 0]])
          (setoidMatrixOfRows [[2, 0], [0, 0]])
      ∧ EndomorphismDissimilarByRank (setoidMatrixOfRows [[0, 0], [0, 0]])
          (setoidMatrixOfRows [[0, 1], [0, 0]]) :=
  ⟨endomorphismNilpotentConjugacyIsWitnessed, endomorphismRationalConjugacyIsWitnessed,
    endomorphismDistinctTraceDissimilar, endomorphismZeroVersusJordanDissimilar⟩

/-! ## The separator-suite marker -/

/-- The walking-endomorphism separator suite: a family of decidable, eigenvalue-free dissimilarity
certificates over ℤ.  It ships the characteristic polynomial via principal minors
(`EndomorphismCharPolyThree`), the rank sequence `rank(Mᵏ)` at its rank-zero boundary
(`EndomorphismPowerZeroSeparator`), the general `k×k` minor rank (`EndomorphismMinorSelector`), the
minimal-polynomial degree at dimension `2` (`EndomorphismMinimalPolynomialTwoByTwo`), and the minimal
polynomial as a produced-and-checked annihilator (`EndomorphismMinimalPolynomial`), the top invariant
factor and the sharpest of the five.  The complete separator — the full invariant-factor list via
ℚ[x] Euclidean GCD — stays open. -/
def fxEndo_hasSeparatorSuite : Bool := true

end FX1Poly.ComputerAlgebra
