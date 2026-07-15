import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCrossComponentBlockDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCrossComponentBlockDispatch — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the cross-component block dispatch: the computable window
check with its guard discharge at unbridged seeds, THE NAMED CONSEQUENCE
(`pushoutCrossComponentBlockDispatch`), the double-adjunction fixtures + fire with its
order-invariance pins, and the honesty/adjudication pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.arcWindowsListDisjointCheck
#assert_no_axioms FX1Poly.Polygraph.Amalgam.natListAllTrueOfMem
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arcWindowsComponentDisjoint_ofEmptyLinksCheck
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutCrossComponentBlockDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadLeftOnlyPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadRightOnlyPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadSandwichedCounitCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadSandwichedCounitCell_isTurnbackOnly
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentFireSeed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentFireSeed_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.doubleAdjunctionPushoutNilBase
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_firedOnDoubleAdjunction
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentFireRedex
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentFireReduct
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentFire_orderInvariantData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCrossComponentBlockDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_saturatedDispatch_stays_false
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_closeCriterion_stays_false
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_bridgedSeedSharpnessStands

end FX1PolyAudit
