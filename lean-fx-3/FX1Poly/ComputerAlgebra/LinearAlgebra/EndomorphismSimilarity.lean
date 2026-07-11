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

end FX1Poly.ComputerAlgebra
