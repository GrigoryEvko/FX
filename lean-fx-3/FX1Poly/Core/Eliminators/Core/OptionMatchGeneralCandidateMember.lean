import FX1Poly.Core.Metatheory.Canonicity.OptionCanonicalFormsCandidate
import FX1Poly.Core.Eliminators.Core.DependentDataEliminatorMemberSkeleton
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Eliminators.Match.MatchClosedMembership
import FX1Poly.Core.Eliminators.Match.MatchReductTrackingStrongNormalization
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep

/-! # FX1Poly/Core/OptionMatchGeneralCandidateMember
    — dependent `optionMatch` over a `dataTaitCandidate` scrutinee lands in the motive candidate (option instance)

The `optionMatch` companion to `boolElimDependentReducibleMember`: the native bounded data-eliminator FT rows
need `optionMatch` to land in an ARBITRARY reducibility candidate (the dependent motive's instantiated output
type), with the scrutinee arriving as a member of the head-expansion-closed `dataTaitCandidate isOptionValue`.

The general-candidate route classifies the FOCUS (not its normal form), and `some(redex)` — a candidate member
whose payload is a redex — is the awkward case: it is NOT `isOptionValue` (payload not normal), NOT neutral
(constructor head), NOT weak-head reducible (the redex sits in the child).  So the trichotomy's value predicate
must be the CONSTRUCTOR-HEAD relaxation `isOptionConstructorHead` (head `none`/`some`, payload arbitrary), and the
focus is recovered from its root generator by `isOptionConstructorHead_ofValueHead`.

This file is being built brick-by-brick; this first brick is the constructor-head predicate + the root-generator
reconstruction (the one genuinely-new ingredient).  The trichotomy instance and the dependent member follow.

## Zero-axiom verification

`isOptionConstructorHead_ofValueHead` mirrors `RawTerm.rename_eq_mkGen`'s head-recovery idiom (match the term,
`change` the root equation, `subst`), then collapses the `Unit` payload and the concrete-arity children GADT
(`[]` for `none`, `[0]` for `some`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace sweep in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The option value-head generator predicate.**  The two option data constructors. -/
def isOptionValueHead (generator : Generator) : Prop :=
  generator = .gen_optionNone ∨ generator = .gen_optionSome

/-- **The option constructor-head predicate.**  A term is option-constructor-headed when it is `none`, or
`some payload` with the payload ARBITRARY (no normality side-condition — unlike `isOptionValue`).  This is the
predicate the dependent-eliminator value dispatch fires the ι on (the ι fires on `some(anything)`), and the
trichotomy concludes; `isOptionValue ⊆ isOptionConstructorHead`. -/
def isOptionConstructorHead {scope : Nat} (term : RawTerm scope) : Prop :=
  term = optionNoneCell ∨ ∃ payload : RawTerm scope, term = optionSomeCell payload

/-- **An option value is option-constructor-headed.**  Drops the payload-normality side-condition of
`isOptionValue` — the easy inclusion the trichotomy's candidate-side bridge composes with. -/
theorem isOptionConstructorHead_ofIsOptionValue {scope : Nat} {term : RawTerm scope}
    (valueIsOption : isOptionValue term) : isOptionConstructorHead term := by
  rcases valueIsOption with valueIsNone | ⟨payload, valueIsSome, _payloadNormal⟩
  · exact Or.inl valueIsNone
  · exact Or.inr ⟨payload, valueIsSome⟩

/-- **An option value's root generator is an option value head.**  The candidate-side trichotomy bridge: a normal
option value's root is `gen_optionNone` / `gen_optionSome`. -/
theorem isOptionValueHead_ofIsOptionValue {scope : Nat} {term : RawTerm scope}
    (valueIsOption : isOptionValue term) : isOptionValueHead term.rootGenerator := by
  rcases valueIsOption with valueIsNone | ⟨_payload, valueIsSome, _payloadNormal⟩
  · exact Or.inl (congrArg RawTerm.rootGenerator valueIsNone)
  · exact Or.inr (congrArg RawTerm.rootGenerator valueIsSome)

/-- **★ Root-generator reconstruction for option.**  A term whose root generator is an option constructor IS
option-constructor-headed — `none` or `some payload` structurally.  The conclusion-side trichotomy bridge,
recovering the focus's constructor shape from `reachesValueHead`'s root-generator output.  Mirrors
`RawTerm.rename_eq_mkGen`'s head-recovery (match the cell, `change`+`subst` the root equation), then collapses the
`Unit` payload and the concrete-arity children (`[]` / `[0]`). -/
theorem isOptionConstructorHead_ofValueHead {scope : Nat} {term : RawTerm scope}
    (rootIsOption : isOptionValueHead term.rootGenerator) : isOptionConstructorHead term := by
  rcases rootIsOption with rootNone | rootSome
  · match term, rootNone with
    | .mkGen generator payload children, rootNone =>
        change generator = .gen_optionNone at rootNone
        subst rootNone
        match payload, children with
        | (), .childNil => exact Or.inl rfl
  · match term, rootSome with
    | .mkGen generator payload children, rootSome =>
        change generator = .gen_optionSome at rootSome
        subst rootSome
        match payload, children with
        | (), .childCons value .childNil => exact Or.inr ⟨value, rfl⟩

/-- **★ Dependent `optionMatch` reducibility: the cell lands in the candidate of the motive at the scrutinee.**
The `optionMatch` companion to `boolElimDependentReducibleMember`.  The scrutinee arrives as a member of the
head-expansion-closed `dataTaitCandidate isOptionValue`; the none-branch is a result member WHEN the scrutinee
reaches `none`, the some-branch APPLIED to a payload is a result member WHEN the scrutinee reaches `some payload`
(the conditioning the bounded row discharges from the motive's reducibility).  The some-branch application's
strong normalization is a SEPARATE premise (the cell's SN needs it, and it is NOT free from the branches' SN —
application does not preserve SN unconditionally), discharged by the bounded bridge from the some-branch's Π
membership.  Drives the shared `dependentDataEliminatorMemberFromValueDispatch`: the per-focus classifier is
`dataTaitFocusTrichotomyOfValueHead` at option's constructor-head set; the value handler fires
`iotaOptionMatchNone` / `iotaOptionMatchSome` and transports the matching conditioned branch. -/
theorem optionMatchDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {scrutinee noneBranch someBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (noneBranchStronglyNormalizing : IsStronglyNormalizing noneBranch)
    (someBranchStronglyNormalizing : IsStronglyNormalizing someBranch)
    (someBranchApplicationStronglyNormalizing : ∀ value : RawTerm scope,
        IsStronglyNormalizing value → IsStronglyNormalizing (applicationCell someBranch value))
    (scrutineeMember : dataTaitCandidate isOptionValue scrutinee)
    (noneBranchMemberIfReachesNone : StepStar scrutinee optionNoneCell → resultCandidate noneBranch)
    (someBranchMemberIfReachesSome : ∀ payload : RawTerm scope,
        StepStar scrutinee (optionSomeCell payload) → resultCandidate (applicationCell someBranch payload)) :
    resultCandidate
      (.mkGen .gen_optionMatch ()
        (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) :=
  dependentDataEliminatorMemberFromValueDispatch
    (isValue := isOptionConstructorHead)
    (scrutineeCandidate := dataTaitCandidate isOptionValue)
    (elimSpine := fun focus =>
      .mkGen .gen_optionMatch ()
        (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons focus .childNil)))))
    (focusTrichotomy := fun focusMember =>
      dataTaitFocusTrichotomyOfValueHead
        (valueHead := isOptionValueHead) (candidateValue := isOptionValue)
        (conclusionValue := isOptionConstructorHead)
        (fun valueIsOption => isOptionValueHead_ofIsOptionValue valueIsOption)
        (fun rootIsOption => isOptionConstructorHead_ofValueHead rootIsOption)
        focusMember)
    (candidateStronglyNormalizing := fun focusMember => focusMember.stronglyNormalizing)
    (candidateClosedUnderStep := fun focusMember step => focusMember.closedUnderStep step)
    (spineStronglyNormalizing := fun focusStronglyNormalizing =>
      optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
        someBranchApplicationStronglyNormalizing
        focusStronglyNormalizing motiveStronglyNormalizing
        noneBranchStronglyNormalizing someBranchStronglyNormalizing)
    (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeOptionMatch focusWeakHead)
    (spineNeutral := fun focusNeutral => IsNeutral.optionMatch focusNeutral)
    (headExpand := headExpand)
    (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
    (valueHandler := fun focusIsConstructorHead reaches cellStronglyNormalizing => by
      rcases focusIsConstructorHead with focusIsNone | ⟨payload, focusIsSome⟩
      · subst focusIsNone
        exact headExpand IotaHeadStep.iotaOptionMatchNone.toWeakHeadStep
          (noneBranchMemberIfReachesNone reaches) cellStronglyNormalizing
      · subst focusIsSome
        exact headExpand IotaHeadStep.iotaOptionMatchSome.toWeakHeadStep
          (someBranchMemberIfReachesSome payload reaches) cellStronglyNormalizing)
    (scrutineeMember := scrutineeMember)

/-- **★ Dependent `optionMatch` reducibility — SELF-CONTAINED cell SN (no false branch-application SN premise).**
The false-premise-free strengthening of `optionMatchDependentReducibleMember`: it DROPS the universally-false
bare-SN obligation `someBranchApplicationStronglyNormalizing` (false over arbitrary branches — applying a reducible
Pi-member to a merely-SN, non-member argument is not SN, the Omega counterexample) and instead derives cell SN at
each scrutinee focus from the SCRUTINEE-REDUCING four-fold engine
`optionMatchCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN`, fed through the
member-keyed dispatch `dependentDataEliminatorMemberFromValueDispatchMemberKeyed`.

The engine's `originalSomeContractumSN` obligation is supplied from the GENUINE reach-conditioned MEMBER residue:
the focus reaches `some payload` (composed with the outer `StepStar scrutinee focus`), so `someBranchMemberIfReaches\
Some` lands the applied contractum in the result candidate, whose CR1 (`candidateMembersSN`) is exactly the
contractum SN the engine needs.  The `none` arm lands directly on the (accessible) current `noneBranch`, carrying
no contractum premise.  The new `candidateMembersSN` premise (members of the result candidate are strongly
normalizing — true, the CR1 of the bounded candidate) REPLACES the false bare-SN premise: a strict honesty
improvement, the `optionMatch` twin of `listElimDependentReducibleMemberFamilySelfContained`.

## Zero-axiom verification

The same shared member-keyed dispatch as the listElim self-contained family, with the four-fold reduct-tracking SN
engine supplying cell SN from the reach-conditioned applied-contractum membership.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace
sweep in `FX1PolyAudit/`. -/
theorem optionMatchDependentReducibleMemberSelfContained {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {scrutinee noneBranch someBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (noneBranchStronglyNormalizing : IsStronglyNormalizing noneBranch)
    (someBranchStronglyNormalizing : IsStronglyNormalizing someBranch)
    (scrutineeMember : dataTaitCandidate isOptionValue scrutinee)
    (noneBranchMemberIfReachesNone : StepStar scrutinee optionNoneCell → resultCandidate noneBranch)
    (someBranchMemberIfReachesSome : ∀ payload : RawTerm scope,
        StepStar scrutinee (optionSomeCell payload) → resultCandidate (applicationCell someBranch payload)) :
    resultCandidate
      (.mkGen .gen_optionMatch ()
        (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) :=
  dependentDataEliminatorMemberFromValueDispatchMemberKeyed
    (isValue := isOptionConstructorHead)
    (scrutineeCandidate := dataTaitCandidate isOptionValue)
    (elimSpine := fun focus =>
      .mkGen .gen_optionMatch ()
        (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons focus .childNil)))))
    (focusTrichotomy := fun focusMember =>
      dataTaitFocusTrichotomyOfValueHead
        (valueHead := isOptionValueHead) (candidateValue := isOptionValue)
        (conclusionValue := isOptionConstructorHead)
        (fun valueIsOption => isOptionValueHead_ofIsOptionValue valueIsOption)
        (fun rootIsOption => isOptionConstructorHead_ofValueHead rootIsOption)
        focusMember)
    (candidateStronglyNormalizing := fun focusMember => focusMember.stronglyNormalizing)
    (candidateClosedUnderStep := fun focusMember step => focusMember.closedUnderStep step)
    (spineStronglyNormalizing := fun focusMember focusReaches =>
      optionMatchCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN
        focusMember.stronglyNormalizing motiveStronglyNormalizing
        noneBranchStronglyNormalizing someBranchStronglyNormalizing
        (fun payload focusReachesSome =>
          candidateMembersSN
            (someBranchMemberIfReachesSome payload (StepStar.trans_compose focusReaches focusReachesSome))))
    (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeOptionMatch focusWeakHead)
    (spineNeutral := fun focusNeutral => IsNeutral.optionMatch focusNeutral)
    (headExpand := headExpand)
    (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
    (valueHandler := fun focusIsConstructorHead reaches cellStronglyNormalizing => by
      rcases focusIsConstructorHead with focusIsNone | ⟨payload, focusIsSome⟩
      · subst focusIsNone
        exact headExpand IotaHeadStep.iotaOptionMatchNone.toWeakHeadStep
          (noneBranchMemberIfReachesNone reaches) cellStronglyNormalizing
      · subst focusIsSome
        exact headExpand IotaHeadStep.iotaOptionMatchSome.toWeakHeadStep
          (someBranchMemberIfReachesSome payload reaches) cellStronglyNormalizing)
    (scrutineeMember := scrutineeMember)

end FX1Poly.Core
