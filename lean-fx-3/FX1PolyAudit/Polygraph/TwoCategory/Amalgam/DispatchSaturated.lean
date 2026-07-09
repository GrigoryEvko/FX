import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DispatchSaturated — zero-axiom gate for the pushout base
relation, the cross-component commutation, and the saturated dispatch through `mapCellAlong` (WP-AMALG r4, B + C)

Per-declaration zero-axiom gate for: the cast-congruence (`SaturatedConvOver.castBoundaryCongr`), the free
cross-component commutation (`crossComponentWhiskerCommute`), the pushout base relation
(`SaturatedConvOverPushout`), the soundness lift (`mapCellAlongCongruence` / `mapCellAlong_preservesConv`), the
general thin decider (`saturatedThinDeciderForAnyRel`), the thin dispatch at the new interface
(`saturatedPushoutThinDispatch` / `involutionSecondSaturatedPushoutDispatch` / `saturatedPushoutMixedVerdict`),
and the concrete commutation witness (`thinSPath` / `thinUPath` / `thinIdBody` / `crossComponentCommuteWitness`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.castBoundaryCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentWhiskerCommute
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOverPushout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_preservesConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedThinDeciderForAnyRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedPushoutThinDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionSecondSaturatedPushoutDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedPushoutMixedVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinSPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinUPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinIdBody
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentCommuteWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.innerPushoutRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.combinedDeciderIsComposable
#assert_no_axioms FX1Poly.Polygraph.Amalgam.threeWaySameModes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.threeWayThinFold
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSaturatedPushoutBaseRelation
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFullSaturatedPushoutDispatch

end FX1PolyAudit
