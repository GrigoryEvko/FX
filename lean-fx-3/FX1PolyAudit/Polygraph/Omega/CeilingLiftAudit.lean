import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CeilingLift

/-! # FX1PolyAudit.Polygraph.Omega.CeilingLiftAudit — zero-axiom gate for OMEGA-3 r1 ceiling lift (B4).

Per-declaration `#assert_no_axioms` on the suspended encoded convertibility, the preserve/reflect constructor
maps, the depth-parameterized FORM-A reduction, and the involution non-vacuity witnesses.  The transitive
check confirms the composition through the shipped Burroni bridge `semiThue_iff_encodedTwoCell` introduces no
axiom (`propext` / `Quot.sound` / `Classical.choice` / `sorry` / `native_decide` / `omega`). -/

namespace FX1PolyAudit

-- CeilingLift.lean — the suspended encoded convertibility + preserve/reflect (B4)
#assert_no_axioms FX1Poly.Polygraph.Omega.EncodedConvSusp
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendEncoded
#assert_no_axioms FX1Poly.Polygraph.Omega.reflectEncoded
#assert_no_axioms FX1Poly.Polygraph.Omega.encoded_iff_encodedSuspended

-- the FORM-A ceiling at dimension 2 + suspensionDepth (B4)
#assert_no_axioms FX1Poly.Polygraph.Omega.semiThue_iff_encodedTwoCellSuspended

-- non-vacuity at every suspended dimension (B4)
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionEncodedSusp_positive
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionEncodedSusp_separation

-- honesty markers (B4 + B5)
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_ceilingLiftEveryDimensionShippedR1
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_ceilingLiftUndecidableInstanceMechanized

end FX1PolyAudit
