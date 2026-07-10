import FX1Poly.Polygraph.Omega.InvertibilitySeed

/-! # Polygraph/Omega/InvertibilityReverseSeed — the REVERSE invertibility duality, classified
    (OMEGA-6 r2, B3)

★ **The reverse of the HL23 duality, classified three-ways honest — the reachable leg SHIPPED as a
machine-checked refutation, the rest WALLED by citation.**  r1 (`InvertibilitySeed.lean`) shipped the FORWARD
inclusion `omegaSnInvertible_subset_folkInvertible` (least ⊆ greatest, "SN-invertible ⇒ folk-invertible",
always true).  The REVERSE — "folk-invertible ⇒ SN-invertible", `coinductiveClosure ⊆ inductiveClosure` — is
the genuine content this round classifies.  The abstract engine
`coinductiveClosure_subset_inductiveClosure_of_wellFounded` (`FiniteNoGap.lean`, HL23 Cor 4.35) provides it,
but ONLY under a `WellFounded guard` premise.  The three honest verdicts:

## 1. The UNCONDITIONAL reverse (no guard) is provably FALSE — SHIPPED here

At the r1 identity-Skolem placeholder the object cell is folk-invertible (`objectCell_folkInvertible`) but NOT
SN-invertible (`objectCell_not_snInvertible`), because the pure invertibility operator has no identity base
case, so its least fixpoint is empty.  Hence the unconditional reverse `∀ cell, folk ⇒ SN` is FALSE — machine
checked as `reverseDuality_unconditional_false`, reusing the r1 `placeholderGap` witnesses, zero-axiom.  This
is a genuine instance of HL23 Prop 4.31 ("coinductive is strictly bigger without finiteness"), promoted from
r1's pointwise gap (`placeholderGap_folkStrictlyBiggerThanSn`) to the universally-quantified refutation.  We do
NOT ship a bare "reverse" theorem — that would be false.

## 2. The CONDITIONAL reverse (under `WellFounded guard`) — already in hand, NOT re-stated

r1 already shipped the guarded collapse as `omegaFixpointsAgree_of_wellFounded` (the HL23 Cor 4.35 recall over
the ω-carrier; its `→` half IS the conditional reverse).  The guard (`WellFounded` on cell-reduction) is
globally FALSE at the raw ω-layer (the F1 memo pin; its discharge lives Core-side at
`StrongNormalizationBridge.lean`, which is Tier0/Core — Polygraph may not import it, `FiniteNoGap.lean`: "Core
instantiates Polygraph, never the reverse").  So r2 gains NO new conditional theorem — re-stating it would
duplicate r1.  It is recalled here by name only.

## 3. The GENUINE ω reverse (real inverses / unit / counit) — WALL, Makkai-adjacent

The identity-Skolem placeholder makes folk invertibility trivial and SN invertibility empty.  A MEANINGFUL
reverse needs the genuine ω-categorical inverses + coherence witnesses + the identity base that seeds
`inductiveClosure` — the Mode / OmegaCategory substrate + weak-ω coherence machinery, undecidable in general
(Makkai).  Cited by the ledger markers `fxOmega6_genuineOmegaReverseModelled = false` and
`fxOmega6_weakOmegaCoherenceEqualityDecidable = false` (Makkai / SN-638).  NEVER axiomatized.

**Net r2 reverse deliverable:** the refutation `reverseDuality_unconditional_false` (reachable, zero-axiom);
the conditional reverse recalled by name (`omegaFixpointsAgree_of_wellFounded`, r1); the genuine ω reverse
walled by citation.  Everything else is honestly walled.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Invertibility

/-- ★ **THE UNCONDITIONAL REVERSE DUALITY IS FALSE (B3).**  There is NO guard-free implication
"folk-invertible ⇒ SN-invertible" at the ω-carrier: the object cell is folk-invertible
(`objectCell_folkInvertible`) yet not SN-invertible (`objectCell_not_snInvertible`), so the universal fails.
The machine-checked refutation of the naive reverse — the honest counterpart to the r1 forward inclusion
`omegaSnInvertible_subset_folkInvertible`, and the universally-quantified promotion of the r1 pointwise gap
`placeholderGap_folkStrictlyBiggerThanSn` (HL23 Prop 4.31).  A GENUINE reverse needs the well-founded guard
(recalled: `omegaFixpointsAgree_of_wellFounded`, globally false at the raw layer) or the genuine ω inverses
(walled: Makkai). -/
theorem reverseDuality_unconditional_false :
    ¬ (∀ cell : OmegaCell demoComputad,
        omegaFolkInvertible demoComputad cell → omegaSnInvertible demoComputad cell) := by
  intro hReverse
  exact objectCell_not_snInvertible (hReverse ⟨0, objectCell⟩ objectCell_folkInvertible)

end FX1Poly.Polygraph.Omega
