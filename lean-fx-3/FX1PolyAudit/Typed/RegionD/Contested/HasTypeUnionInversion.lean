import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion

/-! # FX1PolyAudit.Typed.RegionD.Contested.HasTypeUnionInversion — zero-axiom gate (REGION-D contested-module mirror, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pathLamCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.natSuccCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pathAppCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtPathLamHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtLamHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtNatElimHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtNatElimHeadAllPremises
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtNatSuccHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.unionRejectsAffineDoubleUse
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.pathLamSubjectIsAffine
#assert_no_axioms FX1Poly.Typed.NativeUnionInversionCoverage
#assert_no_axioms FX1Poly.Typed.nativeUnionInversionCoverageWitness

end FX1PolyAudit
