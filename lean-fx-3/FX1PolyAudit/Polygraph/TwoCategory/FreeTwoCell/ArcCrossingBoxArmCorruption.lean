import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingBoxArmCorruption

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingBoxArmCorruption — zero-axiom gate

Per-declaration zero-axiom gate for the deepened arity wall: on the width-4 probe state
`crossingBoxProbeState`, `stepArcAtom`'s generic box arm CORRUPTS wire width on a `2⇒2` crossing
(`crossAtom_stepArcAtom_openWires_isFreshPair`: `[10,11,12,13] ⇒ [20,21]`;
`crossAtom_stepArcAtom_openWires_widthDeficit`: width `4 ⇒ 2`) and BYPASSES the union-find forest for every
state (`crossAtom_stepArcAtom_links_untouched` / `_nextFresh_bump`), while the crossing fails the peel's
`AtomHasCupOrCapArity` tracking premise (`crossAtom_failsTracksBoundaryPremise`).  The honesty marker records
the corruption; the pins record that neither `fxMode_hasArcPeelGeneralSignature` nor
`fxMode_hasArcGodementSamePartitionFreshProof` is flipped.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the
two are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in `AuditAll` beyond the
parent's unified registration. -/

namespace FX1PolyAudit

-- the concrete probe state
#assert_no_axioms FX1Poly.Polygraph.crossingBoxProbeState

-- the width-corruption facts
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_openWires_isFreshPair
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_openWires_widthDeficit

-- the forest-bypass facts
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_links_untouched
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_nextFresh_bump

-- the failed tracking-law premise
#assert_no_axioms FX1Poly.Polygraph.crossAtom_failsTracksBoundaryPremise

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingBoxArmCorruption
#assert_no_axioms FX1Poly.Polygraph.arcCrossing_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossing_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_openWires_isFreshPair
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_openWires_widthDeficit
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_links_untouched
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_nextFresh_bump
#print axioms FX1Poly.Polygraph.crossAtom_failsTracksBoundaryPremise
#print axioms FX1Poly.Polygraph.arcCrossing_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossing_samePartitionFreshProof_stays_false

end FX1PolyAudit
