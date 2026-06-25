import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Cost.GradedLinearTimeBound

/-! # FX1PolyAudit.Dimensions.Cost.GradedLinearTimeBound — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.invertLam
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.invertApp
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.weakening
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.substitution
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.betaPreservation
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.subjectReduction
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.stepDecreasesSize
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.linearTime
#assert_no_axioms FX1Poly.Modal.identityApplication_linearTime
#assert_no_axioms FX1Poly.Modal.duplicatedArgument
#assert_no_axioms FX1Poly.Modal.duplicatorRedex_betaDoesNotShrink
#assert_no_axioms FX1Poly.Modal.omegaFunctionType
#assert_no_axioms FX1Poly.Modal.omegaDuplicatorLam_typedAtGradeOmega

end FX1PolyAudit
