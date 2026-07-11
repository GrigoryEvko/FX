import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeVcompCase

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFactorizeVcompCase — zero-axiom gate for the `vcomp` base case
of the top factorization (two cells in one gap's vertical split + the r8 seam re-probe, WP-AMALG-2 r15, B3)

Per-declaration zero-axiom gate for the nil-framed gadget reduction, the vcomp single-gap block and factorization,
the concrete `eta`-then-`delta_1` witness, the r8 composite seam re-probe, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.nilFramedGadgetConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompSingleGapPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeVcompSingleGap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutEtaThenFaceVcompFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.r8ComposedSeamProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasVcompSingleGapCase

end FX1PolyAudit
