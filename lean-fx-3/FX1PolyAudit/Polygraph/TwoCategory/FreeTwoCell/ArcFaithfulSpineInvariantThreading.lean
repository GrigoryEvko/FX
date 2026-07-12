import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulSpineInvariantThreading

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulSpineInvariantThreading — zero-axiom gate

Per-declaration zero-axiom gate for the r14 (I3) faithful-engine invariant threading twins:
`stepArcAtomFaithful_nextFresh_le` (one faithful step never lowers `nextFresh`),
`processArcSpineFaithful_nextFresh_le` (nor the whole faithful fold), and
`arcStateFresh_processArcSpineFaithful_of_allCupOrCap` (the faithful fold preserves `ArcStateFresh` on the
reachable all-cup/cap regime, via the shipped agreement + `arcStateFresh_processArcSpine`).  Plus the
reachable-seed non-vacuity witness and the honesty marker + pins.

The file flips ONLY its own marker `fxMode_hasArcFaithfulSpineInvariantThreading := true`; the permanent keystone
pins `fxMode_hasArcPeelGeneralSignature` and `fxMode_hasArcGodementSamePartitionFreshProof` stay `false`
(re-asserted by `rfl`), and the faithful-step marker stays `true`.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the invariant threading twins + non-vacuity witness
#assert_no_axioms FX1Poly.Polygraph.stepArcAtomFaithful_nextFresh_le
#assert_no_axioms FX1Poly.Polygraph.processArcSpineFaithful_nextFresh_le
#assert_no_axioms FX1Poly.Polygraph.arcStateFresh_processArcSpineFaithful_of_allCupOrCap
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulNextFresh_crossSeed_confirms

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulSpineInvariantThreading
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSpineInvariantThreading_faithfulStep_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSpineInvariantThreading_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSpineInvariantThreading_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.stepArcAtomFaithful_nextFresh_le
#print axioms FX1Poly.Polygraph.processArcSpineFaithful_nextFresh_le
#print axioms FX1Poly.Polygraph.arcStateFresh_processArcSpineFaithful_of_allCupOrCap
#print axioms FX1Poly.Polygraph.arcFaithfulNextFresh_crossSeed_confirms
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulSpineInvariantThreading
#print axioms FX1Poly.Polygraph.arcFaithfulSpineInvariantThreading_faithfulStep_stays_true
#print axioms FX1Poly.Polygraph.arcFaithfulSpineInvariantThreading_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulSpineInvariantThreading_samePartitionFreshProof_stays_false

end FX1PolyAudit
