import FX1Poly.Typed.Metatheory.Canonicity.Consistency.EmptyTypeConsistencyNativeReducibility
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationSubst

/-! # FX1Poly/Typed/.../ClosedBoolCanonicityFromFundamental
    — UNCONDITIONAL closed bool canonicity via the reducibility bypass (FTGEN-14, the first data instance)

The bool generalization of `HasTypeUnion.emptyTypeConsistency`: a closed union-typed term at `boolTypeCell`
reduces to `boolTrue` or `boolFalse`, with NO hypotheses.  Same reducibility bypass — the generic fundamental
theorem lands a bounded-reducible member of the classifier at the closing weakening; here the classifier is
`boolTypeCell`, so the shipped bridge `boolMemberAtBounded_dataTaitCandidate` carries the member into
`dataTaitCandidate boolIsValue`, whose closed members reduce to a value-or-neutral normal form.  The neutral
disjunct is refuted exactly as in the empty case (`IsNeutral.noClosedSubstImage`), leaving a `boolIsValue`
normal form, which the closing-weakening reflection brings back to scope 0.

The empty type was the `isValue := fun _ => False` instance (no value survives, hence consistency); bool is the
first NON-trivial value predicate (`boolTrue`/`boolFalse` survive), so the conclusion is genuine canonicity
rather than refutation.  The two differ only in the final clause: empty kills both disjuncts, bool keeps the
value disjunct and reflects it back.

## The closing-weakening value reflection

The FT member lives at scope 1 (`subst (Fin.elim0 : RawTermSubst 0 1) subject`), so the `boolIsValue` it yields
is about the WEAKENED normal form.  `boolValueReflectThroughClosingWeakening` brings it back to scope 0: a closed
normal form whose closing-weakening image is `boolTrue`/`boolFalse` is itself `boolTrue`/`boolFalse`, because
those are nullary cells (`subst` preserves the non-variable root generator, and the empty payload/children pin
the cell).  This is the value-side analogue of the neutral reflection `IsNeutral.noClosedSubstImage`.

## Zero-axiom verification

`BoundExceedsUnion.existsBound` + `fundamentalAtBoundedSuccFromTableArms` + `boolMemberAtBounded_dataTaitCandidate`
+ `stronglyNormalizing_of_subst` + `exists_normalForm_of_isStronglyNormalizing` + `StepStar.subst` + the closing
weakening normal-form preservation + `IsNeutral.noClosedSubstImage` + the nullary value reflection.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax
open StepStar

/-- **The nullary bool-value reflection through the closing weakening.**  For a CLOSED normal form whose
closing-weakening image is a bool value, the normal form is itself a bool value.  `boolTrueCell`/`boolFalseCell`
are nullary (`mkGen .gen_boolTrue () .childNil`), so `subst` preserving the non-variable root generator
(`subst_rootGenerator_of_not_var`) pins the head, and the empty payload/children pin the cell — `rfl` closes it.
The value-side analogue of `IsNeutral.noClosedSubstImage`. -/
theorem boolValueReflectThroughClosingWeakening {normalForm : RawTerm 0}
    (isValue : boolIsValue (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) normalForm)) :
    boolIsValue normalForm := by
  rcases isValue with imageIsTrue | imageIsFalse
  · refine Or.inl ?_
    cases normalForm with
    | mkGen generator payload children =>
        by_cases isVariableHead : generator = Generator.gen_var
        · subst isVariableHead; exact payload.elim0
        · have rootPreserved := RawTerm.subst_rootGenerator_of_not_var (Fin.elim0 : RawTermSubst 0 1)
            (term := .mkGen generator payload children) isVariableHead
          rw [imageIsTrue] at rootPreserved
          have generatorEq : generator = Generator.gen_boolTrue := rootPreserved.symm
          subst generatorEq
          cases payload
          cases children
          rfl
  · refine Or.inr ?_
    cases normalForm with
    | mkGen generator payload children =>
        by_cases isVariableHead : generator = Generator.gen_var
        · subst isVariableHead; exact payload.elim0
        · have rootPreserved := RawTerm.subst_rootGenerator_of_not_var (Fin.elim0 : RawTermSubst 0 1)
            (term := .mkGen generator payload children) isVariableHead
          rw [imageIsFalse] at rootPreserved
          have generatorEq : generator = Generator.gen_boolFalse := rootPreserved.symm
          subst generatorEq
          cases payload
          cases children
          rfl

/-- **★★★ UNCONDITIONAL CLOSED BOOL CANONICITY (FTGEN-14, the first data instance).**  A closed union-typed
term at `boolTypeCell` reduces to `boolTrue` or `boolFalse`, with NO hypotheses.  The bool generalization of
`HasTypeUnion.emptyTypeConsistency` via the reducibility bypass:

  1. `BoundExceedsUnion.existsBound` supplies a concrete level bound + budget for the closed derivation.
  2. `fundamentalAtBoundedSuccFromTableArms` lands a bounded-reducible member of `boolTypeCell` at the closing
     weakening (scope 1).
  3. `boolMemberAtBounded_dataTaitCandidate` carries it into `dataTaitCandidate boolIsValue`.
  4. The weakened subject is strongly normalizing (SN reflects back through the weakening), so `subject` has a
     normal form; pushed forward through the weakening it is still normal, hence value-or-neutral by the
     candidate; the neutral disjunct is refuted by `IsNeutral.noClosedSubstImage`; the value disjunct reflects
     back to scope 0 by `boolValueReflectThroughClosingWeakening`.

The same machinery as consistency, with the value disjunct kept instead of refuted.  Pure composition —
zero-axiom. -/
theorem HasTypeUnion.closedBoolCanonicity {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (boolTypeCell (scope := 0))) :
    ∃ value : RawTerm 0, StepStar subject value ∧ boolIsValue value ∧ RawTerm.isStepNormalForm value := by
  obtain ⟨bound, budget⟩ := BoundExceedsUnion.existsBound (env := fun _ => 0) typed
  have member :
      IsReducibleMemberAtBounded (fun _ => 0) bound (boolTypeCell (scope := 1))
        (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject) :=
    HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms (fun _ => 0) bound
      (fundamentalFormationRowAtBoundedSucc (fun _ => 0) bound)
      (fundamentalIntroRowAtBoundedSucc (fun _ => 0) bound)
      (fundamentalElimRowAtBoundedSucc (fun _ => 0) bound) typed budget
      (targetScope := 0) (Fin.elim0 : RawTermSubst 0 1)
      (ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1))
  have candidate : dataTaitCandidate boolIsValue (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject) :=
    boolMemberAtBounded_dataTaitCandidate member
  have subjectStronglyNormalizing : StepStar.IsStronglyNormalizing subject :=
    StepStar.stronglyNormalizing_of_subst (Fin.elim0 : RawTermSubst 0 1) subject candidate.1
  obtain ⟨normalForm, subjectReachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing subjectStronglyNormalizing
  have weakenedReaches :
      StepStar (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject)
        (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) normalForm) :=
    StepStar.subst (Fin.elim0 : RawTermSubst 0 1) subjectReachesNormalForm
  have weakenedIsRename :
      RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) normalForm
        = RawTerm.rename (Fin.elim0 : RawRenaming 0 1) normalForm := by
    rw [RawTerm.rename_eq_subst_ofRenaming]
    exact RawTerm.subst_pointwise (fun position => position.elim0) normalForm
  have weakenedIsNormal :
      RawTerm.isStepNormalForm (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) normalForm) := by
    rw [weakenedIsRename]
    exact (RawTerm.isStepNormalForm_rename_iff (Fin.elim0 : RawRenaming 0 1) normalForm).mpr
      normalFormIsNormal
  rcases candidate.2 _ weakenedReaches weakenedIsNormal with imageIsValue | imageIsNeutral
  · exact ⟨normalForm, subjectReachesNormalForm,
      boolValueReflectThroughClosingWeakening imageIsValue, normalFormIsNormal⟩
  · exact (IsNeutral.noClosedSubstImage imageIsNeutral (Fin.elim0 : RawTermSubst 0 1) rfl).elim

end FX1Poly.Typed
