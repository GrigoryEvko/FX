import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchLocallyThin

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DispatchLocallyThin — zero-axiom gate for the locally-thin
component decider + the doubly-thin dispatch (WP-AMALG-2, LEG A partial + LEG B fragment)

Per-declaration zero-axiom gate for: the transported identity (`idTo` / `idTo_rfl`), the boundary collapse
(`boundaryEq_of_noGen`), the collapse steps (`vcompIdCollapse` / `whiskerLeftIdCollapse` /
`whiskerRightIdCollapse`) and the full collapse-to-identity (`collapseToId`), local thinness
(`allParallelConv_of_noGen`) and the FIRST genuine `DecidableTwoCellConvFor _.toModeSignature`
(`locallyThinDecider`), reading thinness off a computad (`noGen_of_twoGenLenZero` /
`pushout_twoGenLenZero_of_components`), the dispatch inhabitant (`locallyThinDispatch`), the concrete
walking-involution instantiations (`involution_noGen` / `involutionThinDecider` /
`involutionSecondDispatch`), the mixed-pair witness (`thinMixedPath` / `mixedThinVerdict`), and the honesty
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.idTo
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idTo_rfl
#assert_no_axioms FX1Poly.Polygraph.Amalgam.boundaryEq_of_noGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompIdCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftIdCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightIdCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.collapseToId
#assert_no_axioms FX1Poly.Polygraph.Amalgam.allParallelConv_of_noGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.locallyThinDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.noGen_of_twoGenLenZero
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushout_twoGenLenZero_of_components
#assert_no_axioms FX1Poly.Polygraph.Amalgam.locallyThinDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involution_noGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionThinDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.secondThinComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionSecondSameModes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinPushout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinPushout_profile
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinPushout_disjoint
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionSecondDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinSLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinULetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinMode
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinMixedPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinMixedAlpha
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinMixedBeta
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mixedThinVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasLocallyThinComponentDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasLocallyThinDispatch

end FX1PolyAudit
