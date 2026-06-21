import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence

/-! # FX1PolyAudit/AuditElimOutputTypeCongruence — eliminator output-type congruence audit shard

Per-declaration zero-axiom gate for the output-type Conv-stability ingredient of the native eliminator
subject reduction (the `app`-row half of the TYTAB-2-FT eliminator-SR residual, #1697): the
substitution-argument congruence `subst0_isConvStableUnderArgumentStep` and its `appElimRule` specialization.
Each must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.subst0_isConvStableUnderArgumentStep
#assert_no_axioms FX1Poly.Typed.appElimRuleOutputType_isConvStableUnderArgumentStep

end FX1PolyAudit
