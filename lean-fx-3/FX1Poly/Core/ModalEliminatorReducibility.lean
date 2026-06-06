import FX1Poly.Core.StrongNormalizationModalEliminators
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.ModIntroCanonicalFormsCandidate

/-! # FX1Poly/Core/ModalEliminatorReducibility
    — modal elimination + subsumption reducibility (SN-074 / SN-075), unconditional + zero-axiom

`ModIntroCanonicalFormsCandidate.lean` (SN-073) ships the modal box INTRODUCTION reducibility candidate, and
`StrongNormalizationModalEliminators.lean` (#722) ships the FORWARD strong-normalization closure for the two
one-child modal operators — `modElim`'s child SN lifts to `modElim`'s SN (`modElim_isStronglyNormalizing_of_child`),
likewise `subsume`.  This file completes the modal-core reducibility picture with the missing direction and the
candidate-framing: SN-074 (`modElim` reducibility) and its twin SN-075 (`subsume` reducibility).

## Why the strong-normalization candidate is the honest target

The modal eliminator `gen_modElim` is, by deliberate design (see `NeutralTerm.lean`'s "Scope boundary"), NOT a
neutral head and has NO β+ι ι-rule: its only collapse is the raw-η `modIntro (modElim m) ↝ m`, which lives in
the separate `Step.eta` relation with `modIntro` (not `modElim`) as the redex root.  Under the β+ι relation
`Step`, `modElim` is therefore purely CONGRUENCE — a reduction out of a `modElim`-rooted term reduces exactly its
single child, and `modElim (modIntro p)` is genuinely stuck (no β rule turns it into `p`).

Consequently `modElim m` cannot honestly be claimed a member of an ARBITRARY payload candidate via the Girard CR3
neutral-expansion route — CR3 demands `IsNeutral`, which `modElim` lacks by design.  The honest ceiling is the
strong-normalization candidate `IsStronglyNormalizing` itself (the base candidate of
`isStronglyNormalizing_isReducibilityCandidate`, whose membership IS SN and so needs no neutrality): `modElim`
sends every reducibility-candidate member to an SN-candidate member.  Full payload-candidate membership awaits
either a β/ι computation rule for `modElim` or its registration as a neutral head — both presently absent, both
flagged honestly in `NeutralTerm.lean`.

## What this file adds beyond the forward SN closure (#722)

* `isStronglyNormalizing_child_of_oneChildCong` — the REUSABLE converse of
  `isStronglyNormalizing_of_oneChildCong`: strong normalization REFLECTS through any one-child congruence wrapper.
  Given the forward congruence `Step child child' → Step (wrap child) (wrap child')`, accessibility of the wrapped
  parent descends to the child.  The `Acc`-descent idiom mirrors `headValue_isStronglyNormalizing_of_listCons`,
  generalized to an arbitrary wrapper.
* `modElim_isStronglyNormalizing_child_of_parent` / `subsume_…` — the reflection at the two modal operators.
* `modElim_isStronglyNormalizing_iff` / `subsume_…` — the biconditional `IsStronglyNormalizing (op child) ↔
  IsStronglyNormalizing child` (forward = #722, backward = the new reflection): the complete SN characterization.
* `modElim_isStronglyNormalizing_of_candidateMember` / `subsume_…` — the reducibility-framing: a member of any
  reducibility candidate is sent by `modElim` / `subsume` to an SN-candidate member (CR1 on the candidate, then
  the forward closure).
* `modElim_isStronglyNormalizing_ofBoxMember` — the concrete capstone tying `modElim` back to SN-073's shipped box
  candidate `modIntroCanonicalFormsCandidate`: `modElim` of a modal-box-candidate member is strongly normalizing.

## Zero-axiom verification

The reflection lemma is `Acc` well-founded recursion freed at the wrapper equation (the standard
reflect-accessibility pattern), each child step lifted through the wrapper by `Step.cong` / `StepChildren.here`;
everything else composes the forward closure with the candidate's CR1 field.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **Strong normalization REFLECTS through a one-child congruence wrapper.**  The reusable converse of
`isStronglyNormalizing_of_oneChildCong`: if the wrapped parent `wrapParent sourceChild` is strongly normalizing
and every child step lifts to a parent step (`congParentStep`), then the child `sourceChild` is strongly
normalizing.  An infinite reduction of the child would lift, step by step, to one of the parent, contradicting
the parent's accessibility.  Proved by `Acc` induction on the parent generalized over the wrapper equation —
each child reduct's accessibility is delivered by the parent's induction hypothesis at the lifted parent reduct.
This is the generic engine behind the modal-operator SN reflections below; it mirrors
`headValue_isStronglyNormalizing_of_listCons` at an arbitrary wrapper. -/
theorem isStronglyNormalizing_child_of_oneChildCong
    {childScope parentScope : Nat}
    (wrapParent : RawTerm childScope → RawTerm parentScope)
    (congParentStep :
      ∀ {sourceChild targetChild : RawTerm childScope},
        Step sourceChild targetChild →
          Step (wrapParent sourceChild) (wrapParent targetChild))
    {sourceChild : RawTerm childScope}
    (parentTerminates : IsStronglyNormalizing (wrapParent sourceChild)) :
    IsStronglyNormalizing sourceChild := by
  suffices general :
      ∀ {parentTerm : RawTerm parentScope}, Acc StepSuccessor parentTerm →
        ∀ {currentChild : RawTerm childScope},
          parentTerm = wrapParent currentChild →
          Acc StepSuccessor currentChild from
    general parentTerminates rfl
  intro parentTerm parentAccessible
  induction parentAccessible with
  | intro _parentWitness _parentPredecessors parentInductiveHypothesis =>
      intro currentChild witnessEq
      subst witnessEq
      apply Acc.intro
      intro childAfter childStep
      exact parentInductiveHypothesis
        (wrapParent childAfter) (congParentStep childStep) rfl

/-- **`modElim`'s child reflects strong normalization (SN-074, the new direction).**  Congruence-only under β+ι:
each child step lifts to a `modElim` step (`Step.cong` / `StepChildren.here`), so accessibility of `modElim
modalTerm` descends to `modalTerm`.  The converse of `modElim_isStronglyNormalizing_of_child` (#722). -/
theorem modElim_isStronglyNormalizing_child_of_parent {scope : Nat}
    {modalTerm : RawTerm scope}
    (modElimTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_modElim () (.childCons modalTerm .childNil) : RawTerm scope)) :
    IsStronglyNormalizing modalTerm :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentModal =>
      (.mkGen .gen_modElim () (.childCons currentModal .childNil) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_modElim ()
        (StepChildren.here (.childNil : RawTermChildren [] scope) childStep))
    modElimTerminates

/-- **`subsume`'s child reflects strong normalization (SN-075, the new direction).**  The modality-subsumption
twin of `modElim_isStronglyNormalizing_child_of_parent`, identical one-child congruence shape. -/
theorem subsume_isStronglyNormalizing_child_of_parent {scope : Nat}
    {subsumedTerm : RawTerm scope}
    (subsumeTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil) : RawTerm scope)) :
    IsStronglyNormalizing subsumedTerm :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentSubsumed =>
      (.mkGen .gen_subsume () (.childCons currentSubsumed .childNil) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_subsume ()
        (StepChildren.here (.childNil : RawTermChildren [] scope) childStep))
    subsumeTerminates

/-- **`modElim` strong-normalization characterization (SN-074).**  `modElim modalTerm` is strongly normalizing
iff `modalTerm` is — forward is the #722 closure, backward is the new reflection.  The complete SN picture for
the modal eliminator under β+ι. -/
theorem modElim_isStronglyNormalizing_iff {scope : Nat} {modalTerm : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_modElim () (.childCons modalTerm .childNil) : RawTerm scope)
      ↔ IsStronglyNormalizing modalTerm :=
  ⟨modElim_isStronglyNormalizing_child_of_parent,
   modElim_isStronglyNormalizing_of_child⟩

/-- **`subsume` strong-normalization characterization (SN-075).**  The subsumption twin of
`modElim_isStronglyNormalizing_iff`. -/
theorem subsume_isStronglyNormalizing_iff {scope : Nat} {subsumedTerm : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil) : RawTerm scope)
      ↔ IsStronglyNormalizing subsumedTerm :=
  ⟨subsume_isStronglyNormalizing_child_of_parent,
   subsume_isStronglyNormalizing_of_child⟩

/-- **`modElim` sends reducibility-candidate members to SN-candidate members (SN-074, the reducibility
framing).**  Given a reducibility candidate `memberPredicate` and a member `modalTerm`, CR1 makes `modalTerm`
strongly normalizing, so the forward closure makes `modElim modalTerm` strongly normalizing — i.e. a member of
the base SN reducibility candidate (`isStronglyNormalizing_isReducibilityCandidate`).  This is the honest
ceiling: the SN candidate, not an arbitrary payload candidate, since `modElim` is non-neutral with no ι-rule. -/
theorem modElim_isStronglyNormalizing_of_candidateMember {scope : Nat}
    {memberPredicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate memberPredicate)
    {modalTerm : RawTerm scope} (modalMember : memberPredicate modalTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_modElim () (.childCons modalTerm .childNil) : RawTerm scope) :=
  modElim_isStronglyNormalizing_of_child (candidate.stronglyNormalizing modalMember)

/-- **`subsume` sends reducibility-candidate members to SN-candidate members (SN-075, the reducibility
framing).**  The subsumption twin of `modElim_isStronglyNormalizing_of_candidateMember`. -/
theorem subsume_isStronglyNormalizing_of_candidateMember {scope : Nat}
    {memberPredicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate memberPredicate)
    {subsumedTerm : RawTerm scope} (subsumedMember : memberPredicate subsumedTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil) : RawTerm scope) :=
  subsume_isStronglyNormalizing_of_child (candidate.stronglyNormalizing subsumedMember)

/-- **`modElim` of a modal-box-candidate member is strongly normalizing (SN-074 capstone).**  The concrete
instance tying the modal eliminator back to SN-073's shipped box reducibility candidate
`modIntroCanonicalFormsCandidate`: any member of the modal box candidate `CanonicalFormsPredicate
isModIntroValue` is sent by `modElim` to a strongly-normalizing (SN-candidate) term.  The reducibility
counterpart of `modIntroCanonicalFormsCandidate` for the eliminator side of the modal core. -/
theorem modElim_isStronglyNormalizing_ofBoxMember {scope : Nat}
    {modalTerm : RawTerm scope}
    (boxMember : CanonicalFormsPredicate isModIntroValue modalTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_modElim () (.childCons modalTerm .childNil) : RawTerm scope) :=
  modElim_isStronglyNormalizing_of_candidateMember modIntroCanonicalFormsCandidate boxMember

end StepStar
end FX1Poly.Core
