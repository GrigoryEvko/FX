import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWellFormedStateBundle

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcWellFormedStateBundle — zero-axiom gate (MODE-COMMUTE r24)

Per-declaration zero-axiom gate for the r24 `WellFormedArcState` bundle: the carrier structure, its five
arc-step preservation lemmas, the r21 cyclic-forest-gap negative control, the below-base positive
control (freshness / forest / well-formedness + the three concrete preservation fires), the two
bundle-threaded joint-simulation re-exports, the compound-sigma joint per-step cup / cap levers, the
seam-satisfied joint fire + its three field snapshots, the seam-violation negative control, the shipped
marker, and the three untouched-false honesty pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.WellFormedArcState
#assert_no_axioms FX1Poly.Polygraph.wellFormedArcState_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.wellFormedArcState_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.wellFormedArcState_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.wellFormedArcState_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.wellFormedArcState_runArcCell
#assert_no_axioms FX1Poly.Polygraph.not_wellFormedArcState
#assert_no_axioms FX1Poly.Polygraph.arcBelowBaseForestState
#assert_no_axioms FX1Poly.Polygraph.arcBelowBaseForestState_isFresh
#assert_no_axioms FX1Poly.Polygraph.arcBelowBaseForestState_isForest
#assert_no_axioms FX1Poly.Polygraph.arcBelowBaseForestState_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcBelowBaseForestState_cupReduct_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcBelowBaseForestState_capReduct_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcBelowBaseForestState_runNilCell_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_processArcSpine_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_runArcCell_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_renameState_compoundTransposition
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_renameState_compoundTransposition
#assert_no_axioms FX1Poly.Polygraph.arcJointCupFire_seamSatisfied
#assert_no_axioms FX1Poly.Polygraph.arcJointCupFire_openWires
#assert_no_axioms FX1Poly.Polygraph.arcJointCupFire_nextFresh
#assert_no_axioms FX1Poly.Polygraph.arcJointCupFire_links
#assert_no_axioms FX1Poly.Polygraph.arcSeamViolatingFixture
#assert_no_axioms FX1Poly.Polygraph.arcSeamViolation_openWiresDiffer
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasWellFormedArcStateBundle
#assert_no_axioms FX1Poly.Polygraph.arcWellFormedStateBundle_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcWellFormedStateBundle_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcWellFormedStateBundle_samePartitionFresh_stays_false

end FX1PolyAudit
