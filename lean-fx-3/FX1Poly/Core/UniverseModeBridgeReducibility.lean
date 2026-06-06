import FX1Poly.Core.StrongNormalizationUniverseModeBridges
import FX1Poly.Core.ModalEliminatorReducibility
import FX1Poly.Core.ReducibilityCandidate

/-! # FX1Poly/Core/UniverseModeBridgeReducibility
    — 2LTT universe-mode bridge reducibility (SN-077), unconditional + zero-axiom

`StrongNormalizationUniverseModeBridges.lean` ships the FORWARD strong-normalization closures for the two
universe-mode bridge operators of the 2-level type theory (2LTT) stack: the inner→outer lift
`gen_liftInnerToOuter` (one child, the inner term) and the outer→inner lower `gen_lowerOuterToInner` (two
children, the outer term + its cofibrancy witness).  This file completes their reducibility picture with the
REFLECTION direction and the candidate-framing — SN-077, the mode-bridge twin of SN-074/075
(`ModalEliminatorReducibility.lean`).

## Why the strong-normalization candidate is the honest target (same as SN-074)

Both bridges are CONGRUENCE-ONLY + NON-NEUTRAL under the β+ι relation `Step`, exactly like `gen_modElim`: their
mode-bridge computation rule `lower (lift x) ↝ x` is not part of the current β+ι substrate (it awaits the
mode-bridge ι-rule, M26-Z1 / `#434`), and neither operator is registered as a neutral head (`NeutralTerm.lean`).
So `lower (lift x)` is genuinely stuck, and neither bridge can be claimed a member of an arbitrary classifier
candidate via Girard CR3 (which demands `IsNeutral`).  The honest ceiling is the strong-normalization candidate
`IsStronglyNormalizing`: the bridges send candidate members to SN-candidate members.

## Contents

* `liftInnerToOuter_isStronglyNormalizing_child_of_parent` — the lift's reflection, via the reusable
  `isStronglyNormalizing_child_of_oneChildCong` (SN-074).
* `lowerOuterToInner_outer_…` / `lowerOuterToInner_cofibrancy_…` — the lower's two child reflections, each a
  one-child SLICE of the two-child operator (hold the other child fixed), instantiating the same generic
  one-child reflection lemma — mirroring how `listCons`'s head/tail SN projections slice the two-child cons.
* `liftInnerToOuter_isStronglyNormalizing_iff` / `lowerOuterToInner_isStronglyNormalizing_iff` — the
  biconditionals: lift SN ↔ inner SN, and lower SN ↔ (outer SN ∧ cofibrancy SN) (forward = the shipped #894
  closures, backward = these reflections).
* `liftInnerToOuter_isStronglyNormalizing_of_candidateMember` /
  `lowerOuterToInner_isStronglyNormalizing_of_candidateMembers` — the reducibility-framing: candidate members
  are sent by the bridges to SN-candidate members.

## Zero-axiom verification

Each reflection is an instance of `isStronglyNormalizing_child_of_oneChildCong` with the forward congruence
built by `Step.cong` / `StepChildren.here` (the cofibrancy slice threads `StepChildren.there` past the held
outer child, with the explicit `@`-form because `gen_lowerOuterToInner.binderShifts = [0, 0]` does not
auto-reduce — the same idiom as `tailValue_isStronglyNormalizing_of_listCons`).  Everything else composes the
shipped forward closures with the candidate's CR1 field.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The inner→outer lift's child reflects strong normalization (SN-077).**  Congruence-only under β+ι
(`Step.from_liftInnerToOuter`), so accessibility of `liftInnerToOuter innerTerm` descends to `innerTerm` via the
reusable one-child reflection lemma.  The converse of `liftInnerToOuter_isStronglyNormalizing_of_child`. -/
theorem liftInnerToOuter_isStronglyNormalizing_child_of_parent {scope : Nat}
    {innerTerm : RawTerm scope}
    (liftTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_liftInnerToOuter () (.childCons innerTerm .childNil) : RawTerm scope)) :
    IsStronglyNormalizing innerTerm :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentInner =>
      (.mkGen .gen_liftInnerToOuter () (.childCons currentInner .childNil) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_liftInnerToOuter ()
        (StepChildren.here (.childNil : RawTermChildren [] scope) childStep))
    liftTerminates

/-- **The outer→inner lower's OUTER child reflects strong normalization (SN-077).**  The one-child slice of the
two-child lower in the outer-term position (cofibrancy held fixed): each outer step lifts to a `lowerOuterToInner`
step via `StepChildren.here`, so accessibility descends to `outerTerm`. -/
theorem lowerOuterToInner_outer_isStronglyNormalizing_of_parent {scope : Nat}
    {outerTerm cofibrancy : RawTerm scope}
    (lowerTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_lowerOuterToInner ()
          (.childCons outerTerm (.childCons cofibrancy .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing outerTerm :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentOuter =>
      (.mkGen .gen_lowerOuterToInner ()
        (.childCons currentOuter (.childCons cofibrancy .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_lowerOuterToInner ()
        (StepChildren.here
          (.childCons cofibrancy .childNil : RawTermChildren [0] scope) childStep))
    lowerTerminates

/-- **The outer→inner lower's COFIBRANCY child reflects strong normalization (SN-077).**  The one-child slice in
the cofibrancy-witness position (outer term held fixed): each cofibrancy step lifts via the tail-then-head
congruence (`StepChildren.there ∘ StepChildren.here`), so accessibility descends to `cofibrancy`.  The `there`
binder shift is pinned with the explicit `@`-form because `gen_lowerOuterToInner.binderShifts = [0, 0]` does not
auto-reduce. -/
theorem lowerOuterToInner_cofibrancy_isStronglyNormalizing_of_parent {scope : Nat}
    {outerTerm cofibrancy : RawTerm scope}
    (lowerTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_lowerOuterToInner ()
          (.childCons outerTerm (.childCons cofibrancy .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing cofibrancy :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentCofibrancy =>
      (.mkGen .gen_lowerOuterToInner ()
        (.childCons outerTerm (.childCons currentCofibrancy .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_lowerOuterToInner ()
        (@StepChildren.there scope 0 [0] outerTerm _ _
          (StepChildren.here (.childNil : RawTermChildren [] scope) childStep)))
    lowerTerminates

/-- **The lift's strong-normalization characterization (SN-077).**  `liftInnerToOuter innerTerm` is strongly
normalizing iff `innerTerm` is — forward is the #894 closure, backward is the reflection. -/
theorem liftInnerToOuter_isStronglyNormalizing_iff {scope : Nat} {innerTerm : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_liftInnerToOuter () (.childCons innerTerm .childNil) : RawTerm scope)
      ↔ IsStronglyNormalizing innerTerm :=
  ⟨liftInnerToOuter_isStronglyNormalizing_child_of_parent,
   liftInnerToOuter_isStronglyNormalizing_of_child⟩

/-- **The lower's strong-normalization characterization (SN-077).**  `lowerOuterToInner outerTerm cofibrancy` is
strongly normalizing iff both children are — forward (both children SN) is the #894 two-child closure, backward
is the two child reflections. -/
theorem lowerOuterToInner_isStronglyNormalizing_iff {scope : Nat}
    {outerTerm cofibrancy : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_lowerOuterToInner ()
          (.childCons outerTerm (.childCons cofibrancy .childNil)) : RawTerm scope)
      ↔ (IsStronglyNormalizing outerTerm ∧ IsStronglyNormalizing cofibrancy) :=
  ⟨fun lowerTerminates =>
      ⟨lowerOuterToInner_outer_isStronglyNormalizing_of_parent lowerTerminates,
       lowerOuterToInner_cofibrancy_isStronglyNormalizing_of_parent lowerTerminates⟩,
   fun ⟨outerTerminates, cofibrancyTerminates⟩ =>
      lowerOuterToInner_isStronglyNormalizing_of_children outerTerminates cofibrancyTerminates⟩

/-- **The lift sends reducibility-candidate members to SN-candidate members (SN-077).**  Given a candidate and a
member `innerTerm`, CR1 makes `innerTerm` strongly normalizing, so the forward closure makes
`liftInnerToOuter innerTerm` strongly normalizing — a member of the base SN reducibility candidate.  The honest
ceiling, the bridge twin of `modElim_isStronglyNormalizing_of_candidateMember`. -/
theorem liftInnerToOuter_isStronglyNormalizing_of_candidateMember {scope : Nat}
    {memberPredicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate memberPredicate)
    {innerTerm : RawTerm scope} (innerMember : memberPredicate innerTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_liftInnerToOuter () (.childCons innerTerm .childNil) : RawTerm scope) :=
  liftInnerToOuter_isStronglyNormalizing_of_child (candidate.stronglyNormalizing innerMember)

/-- **The lower sends reducibility-candidate members to SN-candidate members (SN-077).**  Both children members
of (possibly distinct) candidates ⟹ the lower is strongly normalizing, via the two CR1 fields and the #894
two-child closure. -/
theorem lowerOuterToInner_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {outerPredicate cofibrancyPredicate : RawTerm scope → Prop}
    (outerCandidate : IsReducibilityCandidate outerPredicate)
    (cofibrancyCandidate : IsReducibilityCandidate cofibrancyPredicate)
    {outerTerm cofibrancy : RawTerm scope}
    (outerMember : outerPredicate outerTerm)
    (cofibrancyMember : cofibrancyPredicate cofibrancy) :
    IsStronglyNormalizing
      (.mkGen .gen_lowerOuterToInner ()
        (.childCons outerTerm (.childCons cofibrancy .childNil)) : RawTerm scope) :=
  lowerOuterToInner_isStronglyNormalizing_of_children
    (outerCandidate.stronglyNormalizing outerMember)
    (cofibrancyCandidate.stronglyNormalizing cofibrancyMember)

end StepStar
end FX1Poly.Core
