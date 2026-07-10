import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaGen — zero-axiom gate (Δ soundness, generic-native)

Per-declaration zero-axiom gate for the GENERIC-NATIVE Δ soundness leg (POLY-TAB r6 S2 + S3): the congruence
witness `monadIsMonotoneMapCongruence`, the born-generic soundness `monadMonotoneMapOf_mapEqOfConvGen`, and the
born-generic canonicalization / decision assembly.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadIsMonotoneMapCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadMonotoneMapOf_mapEqOfConvGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadDecideSaturatedConvOverGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadSaturatedGenDecisionModulo
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasGenericNativeSoundnessLeg

end FX1PolyAudit
