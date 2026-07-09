import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.SaturatedDispatch — zero-axiom gate for the SATURATED categorical
Nelson-Oppen dispatch (WP-AMALG r3, piece 3)

Per-declaration zero-axiom gate for: the saturated dispatch statement (`SaturatedDispatchDecidability`), the thin
fragment inhabitant (`saturatedLocallyThinDispatch`), the concrete instantiation
(`involutionSecondSaturatedDispatch`), the mixed-pair saturated verdict (`saturatedMixedThinVerdict`), and the two
honesty markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedDispatchDecidability
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedLocallyThinDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionSecondSaturatedDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedMixedThinVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSaturatedThinDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSaturatedDispatchTheorem

end FX1PolyAudit
