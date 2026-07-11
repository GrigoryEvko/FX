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

end FX1Poly.ComputerAlgebra
