import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableBetaEtaRootSubjectReduction

/-! # FX1PolyAudit/AuditTableBetaEtaRootSubjectReduction — ETA-T6
inc-5b shard

Per-declaration zero-axiom gate for the typed SR of the table
beta-eta-root union: the union relation, the root-eta preservation
(backward adequacy + the bespoke eta-SR dispatcher), the ★ union SR,
and the union-star SR.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByTableEtaRoot
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRoot
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRootStar

end FX1PolyAudit
