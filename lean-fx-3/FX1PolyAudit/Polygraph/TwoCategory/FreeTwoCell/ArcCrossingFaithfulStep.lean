import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingFaithfulStep

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingFaithfulStep — zero-axiom gate

Per-declaration zero-axiom gate for the CORRECTED crossing arm shipped as an additive sibling.  `stepCrossArc` /
`stepArcAtomFaithful` model a `2⇒2` symmetric crossing FAITHFULLY: on the r6 width-4 probe state the corrected
arm PRESERVES width (`crossAtom_stepArcAtomFaithful_openWires_widthPreserved`, `4 = 4`, contrast the box arm's
`4 ⇒ 2`), transposes the ids (`_openWires_transposed`: `[10,11,12,13] ⇒ [11,10,12,13]`), and leaves the forest
and `nextFresh` untouched for EVERY state (`_links_untouched` / `_nextFresh_untouched`).  Double crossing is the
identity (`stepCrossArc_involution_onProbe`, the symmetric R2 relation), and the crossing is observable exactly
up to same-component reordering (`crossing_observable_extract_ne` on different-component strands,
`crossing_sameComponent_extract_unchanged` on same-component ports).  The engine is a CONSERVATIVE refinement:
it agrees with the shipped one on every cup / cap (`stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap`) and at the
whole walking-adjunction seed (`arcStructureOfFaithful_eq_arcStructureOf_adjunction`).  The honesty marker records
the corrected engine; the pins record that the shipped box arm stays corrupt and neither
`fxMode_hasArcPeelGeneralSignature` nor `fxMode_hasArcGodementSamePartitionFreshProof` is flipped.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in `AuditAll` beyond the parent's unified
registration. -/

namespace FX1PolyAudit

-- the corrected definitions
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc
#assert_no_axioms FX1Poly.Polygraph.stepArcAtomFaithful
#assert_no_axioms FX1Poly.Polygraph.processArcSpineFaithful
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfSpineListFaithful
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfFaithful
#assert_no_axioms FX1Poly.Polygraph.crossingObservableState

-- width preservation + transposition + forest/nextFresh untouched
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_openWires_widthPreserved
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_openWires_transposed
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_links_untouched
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_nextFresh_untouched
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_recordsNoCupEvent
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_recordsNoCapEvent

-- the symmetric R2 involution
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_involution_onProbe

-- the observability witnesses
#assert_no_axioms FX1Poly.Polygraph.crossing_observable_internalCupCounts_before
#assert_no_axioms FX1Poly.Polygraph.crossing_observable_internalCupCounts_after
#assert_no_axioms FX1Poly.Polygraph.crossing_observable_extract_ne
#assert_no_axioms FX1Poly.Polygraph.crossing_sameComponent_extract_unchanged

-- the conservative-refinement agreement
#assert_no_axioms FX1Poly.Polygraph.stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap
#assert_no_axioms FX1Poly.Polygraph.processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfFaithful_eq_arcStructureOf_adjunction

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingFaithfulStep
#assert_no_axioms FX1Poly.Polygraph.arcCrossingFaithful_boxArmCorruption_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingFaithful_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingFaithful_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_openWires_widthPreserved
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_openWires_transposed
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_links_untouched
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_nextFresh_untouched
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_recordsNoCupEvent
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtomFaithful_recordsNoCapEvent
#print axioms FX1Poly.Polygraph.stepCrossArc_involution_onProbe
#print axioms FX1Poly.Polygraph.crossing_observable_internalCupCounts_before
#print axioms FX1Poly.Polygraph.crossing_observable_internalCupCounts_after
#print axioms FX1Poly.Polygraph.crossing_observable_extract_ne
#print axioms FX1Poly.Polygraph.crossing_sameComponent_extract_unchanged
#print axioms FX1Poly.Polygraph.stepArcAtomFaithful_eq_stepArcAtom_of_cupOrCap
#print axioms FX1Poly.Polygraph.processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap
#print axioms FX1Poly.Polygraph.arcStructureOfFaithful_eq_arcStructureOf_adjunction
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingFaithfulStep
#print axioms FX1Poly.Polygraph.arcCrossingFaithful_boxArmCorruption_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingFaithful_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingFaithful_samePartitionFreshProof_stays_false

end FX1PolyAudit
