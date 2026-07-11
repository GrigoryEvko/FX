import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeGenCase

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFactorizeGenCase — zero-axiom gate for the `gen` case of the
top factorization (the single canonical firing slot, WP-AMALG-2 r15, B1)

Per-declaration zero-axiom gate for the single-gap block, the single-gap convertibility, the generic single-gap
factorization, the `gen` case, the two concrete pushout-generator factorizations, the wall-free-slot truth-probes,
and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.singleGapPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.singleGapLayoutConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeSingleGap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutEtaFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutMultFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutEtaSlotWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutMultSlotWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutMultBoundaryWallCountEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasGenCaseFactorization

end FX1PolyAudit
