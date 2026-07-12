import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWellFormedStateBundle

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcWellFormedStateBundleAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r24
`WellFormedArcState` bundle: the carrier structure, its five arc-step preservation lemmas, the r21
cyclic negative control, the below-base positive control + its three concrete preservation fires, the
two bundle-threaded joint-simulation re-exports, the compound-sigma joint cup / cap levers, the
seam-satisfied joint fire + its three field snapshots, the seam-violation negative control, the shipped
marker, and the three untouched-false honesty pins.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.WellFormedArcState
#print axioms FX1Poly.Polygraph.wellFormedArcState_stepCupArc
#print axioms FX1Poly.Polygraph.wellFormedArcState_stepCapArc
#print axioms FX1Poly.Polygraph.wellFormedArcState_stepArcAtom
#print axioms FX1Poly.Polygraph.wellFormedArcState_processArcSpine
#print axioms FX1Poly.Polygraph.wellFormedArcState_runArcCell
#print axioms FX1Poly.Polygraph.not_wellFormedArcState
#print axioms FX1Poly.Polygraph.arcBelowBaseForestState
#print axioms FX1Poly.Polygraph.arcBelowBaseForestState_isFresh
#print axioms FX1Poly.Polygraph.arcBelowBaseForestState_isForest
#print axioms FX1Poly.Polygraph.arcBelowBaseForestState_isWellFormed
#print axioms FX1Poly.Polygraph.arcBelowBaseForestState_cupReduct_isWellFormed
#print axioms FX1Poly.Polygraph.arcBelowBaseForestState_capReduct_isWellFormed
#print axioms FX1Poly.Polygraph.arcBelowBaseForestState_runNilCell_isWellFormed
end FX1PolyAudit
