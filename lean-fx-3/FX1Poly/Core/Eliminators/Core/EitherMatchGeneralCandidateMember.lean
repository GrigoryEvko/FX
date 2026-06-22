import FX1Poly.Core.Metatheory.Canonicity.EitherCanonicalFormsCandidate
import FX1Poly.Core.Eliminators.Core.DependentDataEliminatorMemberSkeleton
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Eliminators.Match.MatchClosedMembership
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep

/-! # FX1Poly/Core/EitherMatchGeneralCandidateMember
    — dependent `eitherMatch` over a `dataTaitCandidate` scrutinee lands in the motive candidate (sum instance)

The `eitherMatch` companion to `optionMatchDependentReducibleMember`: the native bounded data-eliminator FT rows
need `eitherMatch` to land in an ARBITRARY reducibility candidate (the dependent motive's instantiated output
type), with the scrutinee arriving as a member of the head-expansion-closed `dataTaitCandidate isEitherValue`.

The sum is the TWO-UNARY-BRANCH shape: BOTH `inl payload` and `inr payload` carry a payload, and BOTH branches are
APPLIED to it (`eitherMatch … inl(v) ↝ app leftBranch v`, `… inr(v) ↝ app rightBranch v`) — unlike `option`,
whose `none` branch is nullary.  So the member takes a left- AND a right-branch application-SN premise and a left-
AND right-conditioned branch-membership premise; there is no nullary-reaches case.  As with `option`, an
`inl(redex)` focus is a candidate member whose payload is a redex — not a value, not neutral, not weak-head
reducible — so the trichotomy's conclusion predicate is the CONSTRUCTOR-HEAD relaxation `isEitherConstructorHead`
(head `inl`/`inr`, payload arbitrary), recovered from the focus's root generator by
`isEitherConstructorHead_ofValueHead`.

This is the third dependent data-eliminator general-candidate member (after `bool` and `option`), driving the same
shared `dependentDataEliminatorMemberFromValueDispatch` + `dataTaitFocusTrichotomyOfValueHead`: the FTGEN-11
unification confirmed on a two-applied-branch eliminator.

## Zero-axiom verification

`isEitherConstructorHead_ofValueHead` mirrors `isOptionConstructorHead_ofValueHead`'s head-recovery idiom (match
the cell, `change` the root equation, `subst`), collapsing the `Unit` payload and the unary children GADT (`[0]`
for both `inl` and `inr`).  The member drives the shared skeleton with the either spine lemmas
(`eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches`, `WeakHeadStep.scrutineeEitherMatch`,
`IsNeutral.eitherMatch`) and fires `iotaEitherMatchInl` / `iotaEitherMatchInr`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace
sweep in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The either value-head generator predicate.**  The two sum data constructors. -/
def isEitherValueHead (generator : Generator) : Prop :=
  generator = .gen_eitherInl ∨ generator = .gen_eitherInr

/-- **The either constructor-head predicate.**  A term is sum-constructor-headed when it is `inl payload` or
`inr payload` with the payload ARBITRARY (no normality side-condition — unlike `isEitherValue`).  This is the
predicate the dependent-eliminator value dispatch fires the ι on (the ι fires on `inl(anything)` / `inr(anything)`)
and the trichotomy concludes; `isEitherValue ⊆ isEitherConstructorHead`. -/
def isEitherConstructorHead {scope : Nat} (term : RawTerm scope) : Prop :=
  (∃ payload : RawTerm scope, term = eitherInlCell payload)
    ∨ ∃ payload : RawTerm scope, term = eitherInrCell payload

/-- **An either value is either-constructor-headed.**  Drops the payload-normality side-condition of
`isEitherValue` — the easy inclusion the trichotomy's candidate-side bridge composes with. -/
theorem isEitherConstructorHead_ofIsEitherValue {scope : Nat} {term : RawTerm scope}
    (valueIsEither : isEitherValue term) : isEitherConstructorHead term := by
  rcases valueIsEither with ⟨payload, valueIsInl, _payloadNormal⟩ | ⟨payload, valueIsInr, _payloadNormal⟩
  · exact Or.inl ⟨payload, valueIsInl⟩
  · exact Or.inr ⟨payload, valueIsInr⟩

/-- **An either value's root generator is an either value head.**  The candidate-side trichotomy bridge: a normal
sum value's root is `gen_eitherInl` / `gen_eitherInr`. -/
theorem isEitherValueHead_ofIsEitherValue {scope : Nat} {term : RawTerm scope}
    (valueIsEither : isEitherValue term) : isEitherValueHead term.rootGenerator := by
  rcases valueIsEither with ⟨_payload, valueIsInl, _payloadNormal⟩ | ⟨_payload, valueIsInr, _payloadNormal⟩
  · exact Or.inl (congrArg RawTerm.rootGenerator valueIsInl)
  · exact Or.inr (congrArg RawTerm.rootGenerator valueIsInr)

/-- **★ Root-generator reconstruction for either.**  A term whose root generator is a sum constructor IS
either-constructor-headed — `inl payload` or `inr payload` structurally.  The conclusion-side trichotomy bridge,
recovering the focus's constructor shape from `reachesValueHead`'s root-generator output.  Mirrors
`isOptionConstructorHead_ofValueHead`'s head-recovery (match the cell, `change`+`subst` the root equation), then
collapses the `Unit` payload and the unary children (`[0]` for both arms — the sum is the symmetric option). -/
theorem isEitherConstructorHead_ofValueHead {scope : Nat} {term : RawTerm scope}
    (rootIsEither : isEitherValueHead term.rootGenerator) : isEitherConstructorHead term := by
  rcases rootIsEither with rootInl | rootInr
  · match term, rootInl with
    | .mkGen generator payload children, rootInl =>
        change generator = .gen_eitherInl at rootInl
        subst rootInl
        match payload, children with
        | (), .childCons value .childNil => exact Or.inl ⟨value, rfl⟩
  · match term, rootInr with
    | .mkGen generator payload children, rootInr =>
        change generator = .gen_eitherInr at rootInr
        subst rootInr
        match payload, children with
        | (), .childCons value .childNil => exact Or.inr ⟨value, rfl⟩

/-- **★ Dependent `eitherMatch` reducibility: the cell lands in the candidate of the motive at the scrutinee.**
The `eitherMatch` companion to `optionMatchDependentReducibleMember`.  The scrutinee arrives as a member of the
head-expansion-closed `dataTaitCandidate isEitherValue`; the left-branch APPLIED to a payload is a result member
WHEN the scrutinee reaches `inl payload`, the right-branch APPLIED to a payload is a result member WHEN the
scrutinee reaches `inr payload` (the conditioning the bounded row discharges from the motive's reducibility).
Each branch application's strong normalization is a SEPARATE premise (the cell's SN needs it, and it is NOT free
from the branches' SN — application does not preserve SN unconditionally), discharged by the bounded bridge from
each branch's Π membership.  Drives the shared `dependentDataEliminatorMemberFromValueDispatch`: the per-focus
classifier is `dataTaitFocusTrichotomyOfValueHead` at either's constructor-head set; the value handler fires
`iotaEitherMatchInl` / `iotaEitherMatchInr` and transports the matching conditioned branch. -/
theorem eitherMatchDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {scrutinee leftBranch rightBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (leftBranchStronglyNormalizing : IsStronglyNormalizing leftBranch)
    (rightBranchStronglyNormalizing : IsStronglyNormalizing rightBranch)
    (leftBranchApplicationStronglyNormalizing : ∀ value : RawTerm scope,
        IsStronglyNormalizing value → IsStronglyNormalizing (applicationCell leftBranch value))
    (rightBranchApplicationStronglyNormalizing : ∀ value : RawTerm scope,
        IsStronglyNormalizing value → IsStronglyNormalizing (applicationCell rightBranch value))
    (scrutineeMember : dataTaitCandidate isEitherValue scrutinee)
    (leftBranchMemberIfReachesInl : ∀ payload : RawTerm scope,
        StepStar scrutinee (eitherInlCell payload) → resultCandidate (applicationCell leftBranch payload))
    (rightBranchMemberIfReachesInr : ∀ payload : RawTerm scope,
        StepStar scrutinee (eitherInrCell payload) → resultCandidate (applicationCell rightBranch payload)) :
    resultCandidate
      (.mkGen .gen_eitherMatch ()
        (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))) :=
  dependentDataEliminatorMemberFromValueDispatch
    (isValue := isEitherConstructorHead)
    (scrutineeCandidate := dataTaitCandidate isEitherValue)
    (elimSpine := fun focus =>
      .mkGen .gen_eitherMatch ()
        (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons focus .childNil)))))
    (focusTrichotomy := fun focusMember =>
      dataTaitFocusTrichotomyOfValueHead
        (valueHead := isEitherValueHead) (candidateValue := isEitherValue)
        (conclusionValue := isEitherConstructorHead)
        (fun valueIsEither => isEitherValueHead_ofIsEitherValue valueIsEither)
        (fun rootIsEither => isEitherConstructorHead_ofValueHead rootIsEither)
        focusMember)
    (candidateStronglyNormalizing := fun focusMember => focusMember.stronglyNormalizing)
    (candidateClosedUnderStep := fun focusMember step => focusMember.closedUnderStep step)
    (spineStronglyNormalizing := fun focusStronglyNormalizing =>
      eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
        leftBranchApplicationStronglyNormalizing rightBranchApplicationStronglyNormalizing
        focusStronglyNormalizing motiveStronglyNormalizing
        leftBranchStronglyNormalizing rightBranchStronglyNormalizing)
    (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeEitherMatch focusWeakHead)
    (spineNeutral := fun focusNeutral => IsNeutral.eitherMatch focusNeutral)
    (headExpand := headExpand)
    (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
    (valueHandler := fun focusIsConstructorHead reaches cellStronglyNormalizing => by
      rcases focusIsConstructorHead with ⟨payload, focusIsInl⟩ | ⟨payload, focusIsInr⟩
      · subst focusIsInl
        exact headExpand IotaHeadStep.iotaEitherMatchInl.toWeakHeadStep
          (leftBranchMemberIfReachesInl payload reaches) cellStronglyNormalizing
      · subst focusIsInr
        exact headExpand IotaHeadStep.iotaEitherMatchInr.toWeakHeadStep
          (rightBranchMemberIfReachesInr payload reaches) cellStronglyNormalizing)
    (scrutineeMember := scrutineeMember)

end FX1Poly.Core
