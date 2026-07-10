import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedNormalizer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedNormalizer — zero-axiom gate

Per-declaration zero-axiom gate for the GENERIC-NATIVE boundary-determined normalizer (POLY-TAB r4): `normalizeFullGen`,
`idempotentLocalPosetalityGeneric`, and the BESPOKE-FREE native decider `decideSaturatedConvOverIdempotentNative`.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.idNFConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightPullConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftPullConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightWhiskerEqConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftWhiskerEqConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonThroughT_reindexSourceGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonThroughT_reindexTargetGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompCanonCollapseGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.repNFVcompCollapseGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.repNFWhiskerLeftBrickGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.repNFWhiskerRightBrickGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.toNFGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.normalizeFullGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentGenericThinness_ofNormalize
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentLocalPosetalityGeneric
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decideSaturatedConvOverIdempotentNative
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentNativeDecidesTrue_smoke_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentNativeAgreesOldOnRegression_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxIdempotentMonad_hasGenericNativeNormalizer

end FX1PolyAudit
