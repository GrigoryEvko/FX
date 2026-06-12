import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.HasTypeUnionSubjectReduction

/-! # FX1PolyAudit/AuditUnionSubjectReduction — NATIVE-37 part a audit shard (ROOT-redex subject
    reduction for the 24-arm native union)

Per-declaration zero-axiom gate for NATIVE-37 part a: the seven unconditional branch-selection /
projection ι subject-reduction theorems (boolElim true/false, natElim/natRec zero, listElim nil,
optionMatch none, idJ refl), the two conditional recursive-succ ι subject-reduction theorems (natElim /
natRec succ — re-exposing the shipped substitution-file theorems), the coverage record / witness, the
deferred-root-redex-shape predicate, and the total master dispatcher over `Step`
(`unionRootStepSubjectReduction`).  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The seven unconditional branch-selection / projection ι subject-reduction theorems -/

#assert_no_axioms FX1Poly.Typed.unionSubjectReductionBoolElimTrue
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionBoolElimFalse
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatElimZero
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatRecZero
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionListElimNil
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionOptionMatchNone
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionIdJRefl

/-! ## The two conditional recursive-succ ι subject-reduction theorems -/

#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatElimSucc
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatRecSucc

/-! ## Coverage record + witness -/

#assert_no_axioms FX1Poly.Typed.NativeUnionRootRedexSubjectReductionCoverage
#assert_no_axioms FX1Poly.Typed.nativeUnionRootRedexSubjectReductionCoverageWitness

/-! ## The deferred-shape predicate + the total master dispatcher over `Step` -/

#assert_no_axioms FX1Poly.Typed.IsDeferredRootRedexShape
#assert_no_axioms FX1Poly.Typed.unionRootStepSubjectReduction

end FX1PolyAudit
