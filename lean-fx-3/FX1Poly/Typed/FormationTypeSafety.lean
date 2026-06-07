import FX1Poly.Typed.FormationCanonicalForms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Core.ExistsStepOfNotNormal

/-! # FX1Poly/Typed/FormationTypeSafety — UNCONDITIONAL syntactic type safety for the formation engine
    `HasTypeDesc` (five-layer-defense L4, §27.3 — the formation half of the preservation/progress parity)

`GrownTypeSafety.lean` ships the §27.3 five-layer-defense L4 deliverable for the GROWN engine
`HasTypeDescPi`: progress is unconditional, but full type safety (the closed term *evaluates to a canonical
value*) is CONDITIONAL on `subjectReductionStar` — the iterated `↝*` preservation whose lone residual is the
grown context-conversion `piElim` arm (`GCC-5`/`#842`), the entangled mutual fundamental-metatheory bundle.

The FORMATION engine `HasTypeDesc` (the moonshot core: `var` / `conv` / `universeFormation` / the generic
`genFormation` former arm) has a parallel type-safety statement, and here it is **UNCONDITIONAL** — there is no
`subjectReductionStar` hypothesis to discharge.  The reason is structural: the formation engine types ONLY
normal forms (variables, universe codes, Π/Σ-former codes, and conversions thereof — no λ, no application, no
data constructor, no eliminator), so `HasTypeDesc.subjectAdmitsNoStep` already says EVERY formation-typed
subject is a normal form.  Preservation is therefore VACUOUS (nothing steps), and progress collapses to "the
subject already IS the canonical value": no evaluation, no SR, no SN needed.

  * `RawTerm.IsFormationCanonicalHead` — the formation canonical-value-head predicate: a Π / Σ / universe type
    code (the three shapes a closed formation-typed term can take — note NO `gen_lam`, unlike the grown
    `IsGrownCanonicalHead`, since the formation engine has no introduction form).

  * `HasTypeDesc.closedFormationSubjectIsNormal` — a closed formation-typed subject is a step-normal-form, the
    contrapositive of `exists_step_of_not_isStepNormalForm` against `subjectAdmitsNoStep` (no step ⟹ normal).

  * `HasTypeDesc.closedFormationProgress` — **PROGRESS (unconditional, and STRONGER than the grown engine's).**
    A closed formation-typed term is a canonical value: a canonical head AND a normal form.  Unlike the grown
    `closedProgress` there is NO "or it steps" disjunct — a formation-typed term never steps, so it is ALWAYS
    already a value.  Composes the closed canonical forms (`closedSubjectHeadIsFormerOrUniverse`) with normality.

  * `HasTypeDesc.closedFormationTypeSafety` — **TYPE SAFETY (unconditional).**  Every closed formation-typed
    term evaluates to a canonical value — and that value is the term ITSELF (`StepStar.refl`), since it is
    already normal and canonical.  The formation engine's analogue of
    `closedTypeSafetyOfSubjectReductionStar`, but with the SR hypothesis ELIMINATED: the formation engine is the
    unconditional half of the L4 preservation/progress parity, the grown engine the SR-gated half.

## Zero-axiom verification

`by_cases` on the decidable `isStepNormalForm` + `exists_step_of_not_isStepNormalForm` (the normality bridge);
the shipped closed canonical forms + `StepStar.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The formation canonical-value-head predicate.**  The four head shapes a closed formation-typed term can
take: a Π / Σ / list type code or a universe code.  Note there is NO `gen_lam` disjunct — the formation engine
has no introduction form, so (unlike the grown `IsGrownCanonicalHead`) every closed formation-typed value is a
type code, never a λ.  The `gen_listCode` disjunct is the forward-compatible slot for the data-type-code
formation row (GTL-11), widened one commit ahead of the row (sound but unreached until `gen_listCode` joins
`typingRuleDescOf`). -/
abbrev RawTerm.IsFormationCanonicalHead {scope : Nat} (term : RawTerm scope) : Prop :=
  RawTerm.headGenerator term = Generator.gen_piTyCode ∨
  RawTerm.headGenerator term = Generator.gen_sigmaTyCode ∨
  RawTerm.headGenerator term = Generator.gen_universeCode ∨
  RawTerm.headGenerator term = Generator.gen_listCode ∨
  RawTerm.headGenerator term = Generator.gen_optionCode

/-- **A closed formation-typed subject is a step-normal-form.**  The contrapositive of
`exists_step_of_not_isStepNormalForm` (not-normal ⟹ exists a step) against `HasTypeDesc.subjectAdmitsNoStep`
(a formation-typed subject admits no step): if the subject were not normal it would step, contradicting
no-step.  The normality half of formation progress. -/
theorem HasTypeDesc.closedFormationSubjectIsNormal {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    RawTerm.isStepNormalForm subject := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact isNormal
  · obtain ⟨reduct, step⟩ := exists_step_of_not_isStepNormalForm isNormal
    exact absurd step (HasTypeDesc.subjectAdmitsNoStep typed reduct)

/-- **Progress (unconditional, stronger than the grown engine).**  A closed formation-typed term is a canonical
value: a canonical head AND a normal form.  There is NO "or it steps" disjunct (the grown `closedProgress` has
one) — a formation-typed term never steps, so it is ALWAYS already a value.  Composes the closed canonical
forms (`closedSubjectHeadIsFormerOrUniverse`) with `closedFormationSubjectIsNormal`. -/
theorem HasTypeDesc.closedFormationProgress {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    RawTerm.IsFormationCanonicalHead subject ∧ RawTerm.isStepNormalForm subject :=
  ⟨HasTypeDesc.closedSubjectHeadIsFormerOrUniverse typed,
    HasTypeDesc.closedFormationSubjectIsNormal typed⟩

/-- **Type safety (unconditional).**  Every closed formation-typed term evaluates to a canonical value — and
that value is the term ITSELF (`StepStar.refl`), since it is already a canonical normal form.  The formation
engine's analogue of the grown `closedTypeSafetyOfSubjectReductionStar`, with the SR hypothesis ELIMINATED: the
formation engine is the unconditional half of the L4 preservation/progress parity. -/
theorem HasTypeDesc.closedFormationTypeSafety {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
      RawTerm.IsFormationCanonicalHead value :=
  ⟨subject, StepStar.refl subject,
    HasTypeDesc.closedFormationSubjectIsNormal typed,
    HasTypeDesc.closedSubjectHeadIsFormerOrUniverse typed⟩

end FX1Poly.Typed
