import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.MechanizedProofCrossReference

/-! # FX1PolyAudit.Typed.RegionD.SelfVerification.MechanizedProofCrossReference — zero-axiom gate (REGION-D audit-lib self-verification mirror, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.polyCellSubstrate_isFxOriginal
#assert_no_axioms FX1Poly.Typed.crossRef_uniqueNormalForm
#assert_no_axioms FX1Poly.Typed.crossRef_decidableConversion
#assert_no_axioms FX1Poly.Typed.crossRef_newmanLemma

end FX1PolyAudit
