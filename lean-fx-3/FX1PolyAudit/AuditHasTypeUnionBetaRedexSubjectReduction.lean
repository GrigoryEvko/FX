import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionBetaRedexSubjectReduction

/-! # FX1PolyAudit/AuditHasTypeUnionBetaRedexSubjectReduction — TYTAB-2 SRINV β-closer audit shard

Per-declaration zero-axiom gate for β subject reduction FROM THE REDEX TYPING (the unconditional
bundle-β closer the W5 obligation deferred).  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.betaRowFiringPinsRedex
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionBetaFromRedex
#assert_no_axioms FX1Poly.Typed.pathBetaRowFiringPinsRedex
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionEndpointBetaFromRedex

end FX1PolyAudit
