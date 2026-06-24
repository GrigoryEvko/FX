import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence

/-! # FX1PolyAudit/AuditElimOutputTypeCongruence — eliminator output-type congruence audit shard

Per-declaration zero-axiom gate for the output-type Conv-stability ingredient of the native eliminator
subject reduction (the eliminator-SR residual of TYTAB-2-FT, #1697): the substitution-argument congruence
`subst0_isConvStableUnderArgumentStep` and its `appElimRule` specialization (the `app` mixed-row half), plus
the substitution-BODY congruence `subst0_isConvStableUnderBodyStep` and the two dependent-eliminator output
halves (`...UnderMotiveStep` / `...UnderScrutineeStep`) that cover the six `subst0 motive scrutinee` rows,
plus the `idJ` output halves (`idJOutputType_isConvStableUnder{Motive,Witness}Step`) for the
`idJMotiveAt motive point path` row.  Each must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.subst0_isConvStableUnderArgumentStep
#assert_no_axioms FX1Poly.Typed.appElimRuleOutputType_isConvStableUnderArgumentStep
#assert_no_axioms FX1Poly.Typed.subst0_isConvStableUnderBodyStep
#assert_no_axioms FX1Poly.Typed.dependentEliminatorOutputType_isConvStableUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.dependentEliminatorOutputType_isConvStableUnderScrutineeStep
#assert_no_axioms FX1Poly.Typed.idJOutputType_isConvStableUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.idJOutputType_isConvStableUnderWitnessStep

end FX1PolyAudit
