import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingEquivariantTransport

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingEquivariantTransport — zero-axiom gate

Per-declaration zero-axiom gate for the crossing EQUIVARIANCE TRANSPORT.  The faithful `2⇒2` crossing acts on
`extractArc` by the adjacent transposition `transposeAdjacent (bottomCount + position)` of the two crossed boundary
indices: per-index (`crossInternalEventCountAt_equivariant`), as the same-component conjugation
(`crossBoundarySameComponent_equivariant`), and — the headline — as the whole-list count swap
(`internalCupCounts_stepCrossArc_eq_swap` / `internalCapCounts_stepCrossArc_eq_swap`, witnessed by
`crossing_observable_internalCupCounts_isSwap`).  This holds for EVERY state; the cup/cap totals and loop count are
invariant.  The partner field is only regime-gated: `crossing_paired_partner_eq_conjugate` confirms the
σ-conjugation on a perfect matching, `crossing_triComponent_partner_ne_conjugate` REFUTES it on a three-port
component — so `fxMode_hasArcCrossingPartnerEquivariantTransport` stays `false`.  The pins record that the shipped
`fxMode_hasArcCrossingFaithfulStep` stays `true` and neither `fxMode_hasArcPeelGeneralSignature` nor
`fxMode_hasArcGodementSamePartitionFreshProof` is flipped.

The transposition `transposeAdjacent` is defined by joint STRUCTURAL recursion (no `==`, no `if`), so every
equational lemma is `rfl`-clean and `propext`-free; the whole-list forms close by list extensionality over the
per-index equivariance.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the adjacent transposition + its equational lemmas
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_pivot
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_succ
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_other
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_cases
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_lt
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_addLeft

-- the swap length + the anchors
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_length
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_natListSwapTwoAt
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_rangeAppend_pastRange
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_boundaryNodes_stepCrossArc

-- per-index equivariance
#assert_no_axioms FX1Poly.Polygraph.crossInternalEventCountAt_equivariant
#assert_no_axioms FX1Poly.Polygraph.crossBoundarySameComponent_equivariant

-- the whole-list count-field swap + invariants
#assert_no_axioms FX1Poly.Polygraph.internalCupCounts_stepCrossArc_eq_swap
#assert_no_axioms FX1Poly.Polygraph.internalCapCounts_stepCrossArc_eq_swap
#assert_no_axioms FX1Poly.Polygraph.cupCount_stepCrossArc_unchanged
#assert_no_axioms FX1Poly.Polygraph.capCount_stepCrossArc_unchanged
#assert_no_axioms FX1Poly.Polygraph.loops_stepCrossArc_unchanged

-- the partner-conjugation probes (the regime-gated arm)
#assert_no_axioms FX1Poly.Polygraph.conjugatePartner
#assert_no_axioms FX1Poly.Polygraph.crossing_observable_internalCupCounts_isSwap
#assert_no_axioms FX1Poly.Polygraph.crossing_observable_internalCupCounts_isSwap_atOne
#assert_no_axioms FX1Poly.Polygraph.crossingPairedState
#assert_no_axioms FX1Poly.Polygraph.crossing_paired_partner_eq_conjugate
#assert_no_axioms FX1Poly.Polygraph.crossingTriComponentState
#assert_no_axioms FX1Poly.Polygraph.crossing_triComponent_partner_ne_conjugate

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingCountEquivariantTransport
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingPartnerEquivariantTransport
#assert_no_axioms FX1Poly.Polygraph.arcCrossingEquivariant_faithfulStep_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingEquivariant_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingEquivariant_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.transposeAdjacent_addLeft
#print axioms FX1Poly.Polygraph.natListGetAt_natListSwapTwoAt
#print axioms FX1Poly.Polygraph.natListGetAt_boundaryNodes_stepCrossArc
#print axioms FX1Poly.Polygraph.crossInternalEventCountAt_equivariant
#print axioms FX1Poly.Polygraph.crossBoundarySameComponent_equivariant
#print axioms FX1Poly.Polygraph.internalCupCounts_stepCrossArc_eq_swap
#print axioms FX1Poly.Polygraph.internalCapCounts_stepCrossArc_eq_swap
#print axioms FX1Poly.Polygraph.crossing_observable_internalCupCounts_isSwap
#print axioms FX1Poly.Polygraph.crossing_paired_partner_eq_conjugate
#print axioms FX1Poly.Polygraph.crossing_triComponent_partner_ne_conjugate
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingCountEquivariantTransport
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingPartnerEquivariantTransport
#print axioms FX1Poly.Polygraph.arcCrossingEquivariant_faithfulStep_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingEquivariant_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingEquivariant_samePartitionFreshProof_stays_false

end FX1PolyAudit
