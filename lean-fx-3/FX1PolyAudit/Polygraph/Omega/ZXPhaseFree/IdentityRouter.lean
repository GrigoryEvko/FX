import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.IdentityRouter

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.IdentityRouter — zero-axiom gate
(the feeding-comb atoms; the walled feeding-comb router and identity induction)

Per-declaration zero-axiom gate for the feeding-comb-router round: the target
denotation and identity-row/normal-form/whisker-form semantics pins, the five
feeding-comb atoms (state-copy duplication, state-merge collapse, X/Z create-kill
annihilation, state slide past a crossing), the whiskered create-kill and the
two-atom create-route-discard composite, the four atom span pins, the live
content marker, and the two owner-false router/identity-absorb markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiEmptyDiagramDenote
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiIdRowsOnePin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiIdRowsTwoPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiNormalFormLayersOnePin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiNormalFormLayersTwoPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiNormalFormLayersThreePin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiWhiskerFormSpanPin

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiStateCopyDuplicates
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiStateMergeAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiCreateKillAbsorbsX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiCreateKillAbsorbsZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiStateSlidesPastCrossing

#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiCreateKillAbsorbsXWhiskered
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiCreateCopyThenKillBoth

#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiStateCopyDuplicatesSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiStateMergeAbsorbsSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiCreateKillAbsorbsXSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiCreateCopyThenKillBothSpanPin

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiHasFeedingCombAtoms
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiHasFeedingCombRouter
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxiHasIdentityAbsorb

end FX1PolyAudit
