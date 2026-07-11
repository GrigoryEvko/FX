import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeWhiskerCase

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFactorizeWhiskerCase — zero-axiom gate for the `whisker` cases
of the top factorization (the frame as an inert wall around a single body slot, WP-AMALG-2 r15, B2)

Per-declaration zero-axiom gate for the whisker-cast helper, the inner-gadget reduction, the `whiskerRight` /
`whiskerLeft` single-gap cases, the left-framed block, the two concrete `s`-frame witnesses, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftCastBoundaryEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.framedGapInnerConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeWhiskerRightGap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.leftFramedGapPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeWhiskerLeftGap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftSEtaFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightSEtaFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerFrameGapCase

end FX1PolyAudit
