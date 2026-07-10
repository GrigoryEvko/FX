import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedMuInvertible

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedMuInvertible — zero-axiom gate

Per-declaration zero-axiom gate for the GENERIC-NATIVE mu-invertibility crux (POLY-TAB r4): the generic moves + the
mu-iso chase over `SaturatedConvOver monadModeSignature IdempotentLawRel`, no bespoke reference.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.idemStep
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idemFull
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idemLeftUnitLaw
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idemRightUnitLaw
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idemAssocLaw
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idemIdempotenceLaw
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mulThenUnitRightWhisker_conv_godement_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitRightWhiskerSquare_conv_unitLeftWhisker_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.godementUnitMul_conv_identity_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentMulRightInverse_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentMulRightInverse_leftWhisker_gen

end FX1PolyAudit
