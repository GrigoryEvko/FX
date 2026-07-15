import FX1Poly.Typed.Metatheory.Reducibility.Fundamental.ClosedNativeStronglyNormalizing
import FX1Poly.Typed.Metatheory.Canonicity.Consistency.ConsistencyTargetSignature
import FX1Poly.Core.Metatheory.Reducibility.Candidates.EmptyTaitCandidate
import FX1Poly.Core.Substrate.Neutral.NeutralSubstReflection
import FX1Poly.Core.Metatheory.Normalization.Core.StronglyNormalizingSubst
import FX1Poly.Core.Metatheory.Normalization.Core.WeakNormalization
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst
import FX1Poly.Core.Rewriting.Conversion.ConvRenameEquivariance
import FX1Poly.Axis.Term.Rename.RawTermRenameAsSubst
import FX1Poly.Axis.Term.Subst.RawTermSubstPointwise
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnly

/-! # FX1Poly/Typed/.../EmptyTypeConsistencyNativeReducibility
    — UNCONDITIONAL native consistency via the reducibility candidate bridge (#1697, closed)

The native-union twin of `HasTypeDescPi.emptyTypeConsistency`, delivered by the **reducibility bypass** rather
than the subject-reduction / canonicity route.  The earlier native headline
(`HasTypeUnion.coreFragmentConsistencyFromElimCongruenceCloserSnDischarged`) discharged gate 1 (native SN) but
still carried gate 2 — the eliminator congruence closer `UnionElimCongruenceClosesToEmptyType` (#1740), which
bottlenecks on native universe-flag-uniqueness for the motive-congruence arms — plus `pathApp`/`pathLam`-free
bookkeeping.  The bypass removes BOTH residual gates.

## The bypass

The generic fundamental theorem (`fundamentalAtBoundedSuccFromTableArms`, three kernel-bundle row dischargers,
gate 1 unconditional via #1734) ALREADY produces a bounded-reducible MEMBER of the typing's classifier at the
closing weakening — `closedStronglyNormalizing` throws everything but SN away.  Instantiated at the empty type it
lands `IsReducibleMemberAtBounded … (emptyTypeCell) (subst (Fin.elim0 : RawTermSubst 0 1) subject)` (the
`emptyTypeCell` classifier is `subst Fin.elim0`-invariant by `rfl`).  The shipped candidate bridge
`emptyTypeCell_memberIsEmptyCandidate` carries it into the head-expansion-closed empty Tait candidate, and the
member is refuted:

  * SN of the weakened subject reflects (`stronglyNormalizing_of_subst`) to SN of the closed `subject` (scope 0);
  * `subject` reaches a normal form `normalForm` (`exists_normalForm_of_isStronglyNormalizing`);
  * the reduction lifts under the closing weakening (`StepStar.subst`) to a reduction of the weakened subject to
    the weakened normal form, which is again normal (the closing weakening is a renaming —
    `rename_eq_subst_ofRenaming` + `subst_pointwise` over the vacuous `Fin 0` — and renaming preserves normality,
    `isStepNormalForm_rename_iff`);
  * the candidate's neutrality clause classifies the weakened normal form as `IsNeutral`;
  * `IsNeutral.noClosedSubstImage` (the reverse neutral reflection) refutes it — no neutral term is the image of a
    CLOSED preimage under a substitution.

No subject reduction, no canonicity gate, no congruence closer, no path-free bookkeeping.

## Zero-axiom verification

`BoundExceedsUnion.existsBound` + `fundamentalAtBoundedSuccFromTableArms` + `emptyTypeCell_memberIsEmptyCandidate`
+ `stronglyNormalizing_of_subst` + `exists_normalForm_of_isStronglyNormalizing` + `StepStar.subst` +
`rename_eq_subst_ofRenaming` + `subst_pointwise` + `isStepNormalForm_rename_iff` + `IsNeutral.noClosedSubstImage`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax
open StepStar

/-- **★★★ UNCONDITIONAL NATIVE CONSISTENCY (consistency leg #1697, closed).**  No closed term is union-typed at
the empty type: `HasTypeUnion .empty subject emptyTypeCell → False`, with NO hypotheses.  The native twin of
`HasTypeDescPi.emptyTypeConsistency`, via the reducibility bypass (FT member at the empty type → empty Tait
candidate → reverse neutral reflection of the weakened normal form).  Strictly stronger than
`coreFragmentConsistencyFromElimCongruenceCloserSnDischarged`: that needed gate 2 (the eliminator congruence
closer / universe-flag-uniqueness mountain) plus path-free bookkeeping; this needs neither. -/
theorem HasTypeUnion.emptyTypeConsistency {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (emptyTypeCell (scope := 0))) :
    False := by
  obtain ⟨bound, budget⟩ := BoundExceedsUnion.existsBound (env := fun _ => 0) typed
  have member :
      IsReducibleMemberAtBounded (fun _ => 0) bound (emptyTypeCell (scope := 1))
        (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject) :=
    HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms (fun _ => 0) bound
      (fundamentalFormationRowAtBoundedSucc (fun _ => 0) bound)
      (fundamentalIntroRowAtBoundedSucc (fun _ => 0) bound)
      (fundamentalElimRowAtBoundedSucc (fun _ => 0) bound) typed budget
      (targetScope := 0) (Fin.elim0 : RawTermSubst 0 1)
      (ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1))
  have candidate : emptyTaitCandidate (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject) :=
    emptyTypeCell_memberIsEmptyCandidate (fun _ => 0) bound member
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
  have weakenedIsNeutral : IsNeutral (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) normalForm) :=
    candidate.2 _ weakenedReaches weakenedIsNormal
  exact IsNeutral.noClosedSubstImage weakenedIsNeutral (Fin.elim0 : RawTermSubst 0 1) rfl

/-- **★★★ UNCONDITIONAL NATIVE-ONLY CONSISTENCY (consistency leg #1697, closed).**  The `ofGrown`-free 6-arm
kernel's own consistency: no closed `HasTypeUnionNativeOnly` term is typed at the empty type.  The native-only
inhabitant is re-typed as a `HasTypeUnion` derivation (`.toUnion`) and refuted by
`HasTypeUnion.emptyTypeConsistency`.  The consistency the physical RETIRE (#1698) needs, now UNCONDITIONAL. -/
theorem HasTypeUnionNativeOnly.emptyTypeConsistency {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeUnionNativeOnly profile (TypingContext.empty : TypingContext profile 0)
      subject (emptyTypeCell (scope := 0))) :
    False :=
  HasTypeUnion.emptyTypeConsistency typed.toUnion

end FX1Poly.Typed
