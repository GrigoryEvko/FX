import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutSaturatedDispatchClose

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutSaturatedDispatchClose — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the master flips (superseding content markers) and the seven live fires of
the saturated dispatch.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutMuCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutIdTCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutLeftUnitComposite
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightUnitComposite
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutAssocLeftComposite
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutAssocRightComposite
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerSandwichedAssocFirst
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerSandwichedAssocSecond
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mixedInterchangeFirst
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mixedInterchangeSecond
#assert_no_axioms FX1Poly.Polygraph.Amalgam.leftLetterWhiskerCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireVcompUnitVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireVcompChainVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireWhiskerSandwichVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireMixedInterchangeVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireLeftLetterVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireCrossPairVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireFaceFlipVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireVcompUnit_isTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireVcompChain_isTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireWhiskerSandwich_isTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireMixedInterchange_isTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireLeftLetter_isTrue
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireCrossPair_isFalse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedFireFaceFlip_isFalse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedDispatchFireConjunction
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedDispatchFrozenOwnersPinned
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSaturatedDispatchTheoremClosed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFullSaturatedPushoutDispatchClosed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasGeneralPushoutDispatchClosed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_realLawCompletenessDischarged
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutDispatchCloseCriterionSuperseding
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutDispatchCloseCriterionSuperseding_true
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushout2043CloseCriterionMet

end FX1PolyAudit
