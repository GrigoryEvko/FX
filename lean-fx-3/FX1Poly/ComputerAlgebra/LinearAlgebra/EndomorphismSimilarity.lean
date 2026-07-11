import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidMatrixRing
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntFractionFree

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/EndomorphismSimilarity — the walking-endomorphism linear model

The walking endomorphism is one object with one generating self-loop and no relations; its linear
model over a field is a pair `(V, f : V -> V)`, i.e. on a chosen basis a square matrix `M`.  Two
representations are isomorphic exactly when the matrices are **similar** (`M ~ N` iff `N = S⁻¹ M S`
for some invertible `S`).  This file is the ComputerAlgebra-lane certificate producer for that
classification, over the shipped multiplicative carrier `SetoidMatrix Int` (whose setoid at ℤ is
plain `Eq`, so every check is an honest `Int` literal a reader can machine-check).

## The scaled-pair witness (the decidable route to ℚ-similarity)

Similar INTEGER matrices need not be conjugate by an integer-unimodular matrix — the conjugator
lives over ℚ.  Routing the checker through a ℚ matrix carrier is a trap: `RationalPair`'s setoid is a
cross-multiplication relation, so windowed equality there is undecidable.  Instead we clear
denominators once: a witness carries `(P, Q, d)` with `d : Int`, `d ≠ 0`, and the KERNEL-CHECKED
integer identities

  * `P · Q = d · I`  (so over ℚ, `P` is invertible with `P⁻¹ = Q / d`),
  * `Q · (A · P) = d · B`  (so `P⁻¹ A P = (1/d)(Q A P) = B`).

Soundness (checker holds ⇒ `A` and `B` are ℚ-similar) is the two lines above.  Completeness (every
ℚ-similar integer pair admits such a witness) is the adjugate construction: take `P = d₀ · S`
(`d₀` = common denominator of `S`), `Q = adj(P)`, `d = det(P) ≠ 0`; the adjugate identity gives
`P · Q = det(P) · I` over ℤ.  So the scaled pair covers ALL ℚ-similar integer pairs — a strict
generalization of the unimodular (`d = 1`) case.

## Lane contract (inherited from #2137)

The general Smith-driver totality was REFUTED (not walled) upstream; this lane successor inherits the
**per-input** contract only: `WitnessesSimilarity` is an untrusted producer's obligation whose sole
guarantee is the kernel-checked literal reductions on each shipped instance.  No general similarity
DECISION procedure is claimed — only that each concrete witness/separator is machine-verified.

## Zero-axiom design

`agreeOnWindow` is a bounded double-`∀` over `Nat` with `<` guards plus `DecidableEq Int`, decided by
`Nat.decidableBallLT` + `Int.decEq` — the exact `by decide` pattern the Smith `offDiagonalVanishes`
field uses.  No `Nat.min` / `Nat.sub` appears inside any decided expression (those taint `decide`
with `propext`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/EndomorphismSimilarity.lean`.
-/

namespace FX1Poly.ComputerAlgebra

open SetoidMatrix

/-! ## The windowed-equality substrate (the `DenoteSame`-avoidance pin) -/

/-- Two `SetoidMatrix Int` grids agree on the `height × width` window: entries match at every in-range
index.  Reducible and stated as a bounded double-`∀` so `Decidable` synthesis unfolds it to
`Nat.decidableBallLT` — NEVER the undecidable `DenoteSame` (which quantifies over all `Nat`). -/
@[reducible] def agreeOnWindow (leftMatrix rightMatrix : SetoidMatrix Int) (height width : Nat) :
    Prop :=
  ∀ rowIndex : Nat, rowIndex < height → ∀ colIndex : Nat, colIndex < width →
    leftMatrix.entry rowIndex colIndex = rightMatrix.entry rowIndex colIndex

/-! ## The scaled-pair witness -/

/-- A produced certificate that `source` and `target` are ℚ-similar, presented over ℤ by clearing
denominators.  `changeOfBasis` is `P`, `scaledInverse` is `Q = d · P⁻¹`, and `scale` is `d`; the
checker `WitnessesSimilarity` verifies `P · Q = d · I` and `Q · (A · P) = d · B` on the window. -/
structure EndomorphismSimilarityWitness where
  dimension : Nat
  source : SetoidMatrix Int
  target : SetoidMatrix Int
  changeOfBasis : SetoidMatrix Int
  scaledInverse : SetoidMatrix Int
  scale : Int

/-! ## Substrate truth-probe

The concrete `d = 2` rational-conjugacy inverse window `P · Q = 2 · I`, evaluated by hand
(`P = [[1,1],[0,2]]`, `Q = adj(P) = [[2,-1],[0,1]]`, `P · Q = [[2,0],[0,2]]`) and here decided against
`scalarMul 2 I`.  This anchors the substrate: the windowed check sees the real integer product. -/
theorem endomorphismScaledInverseWindowProbe :
    agreeOnWindow
      (mulMatrix intCommutativeRingWitness (setoidMatrixOfRows [[1, 1], [0, 2]])
        (setoidMatrixOfRows [[2, -1], [0, 1]]))
      (scalarMul intCommutativeRingWitness 2 (identityMatrix intCommutativeRingWitness 2)) 2 2 := by
  decide

/-! ## The certificate checker

`WitnessesSimilarity` is the produced-then-checked obligation: the load-bearing `d ≠ 0` guard
(stated `1 ≤ Int.natAbs d`, decided by `Nat.decLe`) plus the two kernel-checked window identities
`P · Q = d · I` and `Q · (A · P) = d · B`.  Reducible so `Decidable` synthesis unfolds it to the
`And` of decidable pieces — each concrete instance closes by `decide`. -/
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

Two ways an attacker could forge a "universal" similarity are structurally rejected by the checker.
Both target the genuinely DISSIMILAR pair `[[1,0],[0,0]]` (trace 1) vs `[[2,0],[0,0]]` (trace 2). -/

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

/-- The degenerate `d = 0` forgery (`P = Q = 0`, `d = 0`): without the guard this fakes similarity of
ANY pair (`P · Q = 0 · I` and `Q · A · P = 0 · B` both hold).  The `1 ≤ Int.natAbs 0` guard is false,
so the checker rejects it — the guard is load-bearing. -/
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

/-! ## Separator engine 1: the characteristic polynomial (equal char-poly is NECESSARY for similarity)

Ascending-coefficient list of `det(x·I − M)`, in closed form for the adjudicated sizes (`n = 2, 3`),
reusing the shipped exact cofactor determinant for the constant term.  A `≠` between two char-poly
lists is a machine-checked DISsimilarity certificate (contrapositive of "similar ⇒ equal char-poly").

Honest wall: the GENERAL `det(x·I − M)` over `ℚ[x]` — the complete invariant-factor separator — needs
a univariate polynomial matrix carrier that does NOT ship (no `IntPolynomial`, no `x·I − M`).  That,
and Smith-over-`ℚ[x]` when eigenvalues are irrational, is the r2 boundary. -/

/-- The characteristic-polynomial coefficients of `matrix`, ascending (`[c₀, c₁, …, cₙ = 1]`), in
closed form at `n = 2` (`x² − tr·x + det`) and `n = 3` (`x³ − c₁x² + c₂x − c₃`).  Other sizes return
`[]` (out of r1 scope). -/
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
def EndomorphismDissimilarByCharPoly (dimension : Nat) (source target : SetoidMatrix Int) : Prop :=
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

The rank at `2×2` in closed form via the shipped determinant: full rank `2` when `det ≠ 0`, else `0`
for the zero matrix and `1` otherwise.  A `≠` between two ranks is a machine-checked dissimilarity
certificate (rank is a similarity invariant), and it separates the subtle `0` vs Jordan-block pair
that char-poly cannot see.

Honest wall: `3×3` and higher rank needs a general `k×k` minor selector (the shipped determinant only
deletes row 0); the complete NILPOTENT separator is the rank sequence `rank(Mᵏ)`, which needs a matrix
power — both r1-stretch.  The smallest equal-char-poly, equal-`rank(M)`, still-dissimilar pair is
`4×4` (`J(2)⊕J(2)` vs `J(3)⊕J(1)`), separated only at `rank(M²)`; r1's `rank(M)` cannot see it. -/

/-- The rank of a `2×2` integer matrix (a similarity invariant): `2` if `det ≠ 0`, else `0`/`1`. -/
def endomorphismRank2 (matrix : SetoidMatrix Int) : Nat :=
  if intCofactorDet 2 matrix = 0 then
    (if matrix.entry 0 0 = 0 ∧ matrix.entry 0 1 = 0 ∧ matrix.entry 1 0 = 0 ∧ matrix.entry 1 1 = 0
      then 0 else 1)
  else 2

/-- `source` and `target` are dissimilar because their `2×2` ranks differ. -/
def EndomorphismDissimilarByRank (source target : SetoidMatrix Int) : Prop :=
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

end FX1Poly.ComputerAlgebra
