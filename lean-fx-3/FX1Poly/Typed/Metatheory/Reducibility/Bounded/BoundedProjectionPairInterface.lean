import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedProjectionCarrierObligations

/-! # FX1Poly/Typed/BoundedProjectionPairInterface
    — the projection-candidate interface at the bounded level (the `pairLike.assemble` swap's drop-in lemmas)

The projection-based Σ candidate `projectionPairCandidate` (`ProjectionPairCandidate.lean`) states each of its
properties GIVEN `CarrierObligations` on the two component carriers.  The bounded model recovers the components
as `ReducibleTypeAtBounded env bound firstCode firstCandidate` (the carrier-aware inversions), and
`boundedTypeCarrierObligations` (`BoundedProjectionCarrierObligations.lean`) turns each into the required
`CarrierObligations`.  This file composes the two into the projection interface stated DIRECTLY over the bounded
reducibles — the exact shape the forthcoming `pairLike` `CarrierCombinator.assemble` swap (assemble ↦
`projectionPairCandidate`) consumes at its use sites:

  * `_isReducibilityCandidate_ofBounded` — the model validity (the `dataFlatCarrierAware` arm's CR1/CR2/CR3);
  * `_headExpansionClosed_ofBounded` — the Π-codomain arm property;
  * `_closedUnderStep_ofBounded` / `_memberWeakHeadExpansion_ofBounded` — the two `assemble_*` lemmas that the
    swap must re-prove per-tag (they currently dispatch to `dataTaitCandidate.*`, which fails for a
    non-`dataTaitCandidate` `pairLike` arm);
  * `_reachableComponentMembers_ofBounded` — ★ the `fst` / `snd` residue discharge content, FORWARD, for
    arbitrary (Π-included) component carriers;
  * `_memberOfReducibleComponents_ofBounded` — the pair intro row's member builder.

`congr` needs no bounded premises (it takes `PointwiseIff`), so `projectionPairCandidate_congr` is used directly.

## Zero-axiom verification

Each is `projection_lemma (boundedTypeCarrierObligations firstReducible) (boundedTypeCarrierObligations
secondReducible) …` — a composition of two shipped zero-axiom carriers.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- **Model validity for the projection candidate, from the bounded component reducibles.** -/
theorem projectionPairCandidate_isReducibilityCandidate_ofBounded {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode : RawTerm (scope + 1)}
    {firstCandidate secondCandidate : RawTerm (scope + 1) → Prop}
    (firstReducible : ReducibleTypeAtBounded env bound firstCode firstCandidate)
    (secondReducible : ReducibleTypeAtBounded env bound secondCode secondCandidate) :
    IsReducibilityCandidate (projectionPairCandidate firstCandidate secondCandidate) :=
  projectionPairCandidate_isReducibilityCandidate
    (boundedTypeCarrierObligations firstReducible) (boundedTypeCarrierObligations secondReducible)

/-- **The Π-codomain head-expansion property for the projection candidate, from the bounded reducibles.** -/
theorem projectionPairCandidate_headExpansionClosed_ofBounded {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode : RawTerm (scope + 1)}
    {firstCandidate secondCandidate : RawTerm (scope + 1) → Prop}
    (firstReducible : ReducibleTypeAtBounded env bound firstCode firstCandidate)
    (secondReducible : ReducibleTypeAtBounded env bound secondCode secondCandidate) :
    HeadExpansionClosed (projectionPairCandidate firstCandidate secondCandidate) :=
  projectionPairCandidate_headExpansionClosed
    (boundedTypeCarrierObligations firstReducible) (boundedTypeCarrierObligations secondReducible)

/-- **Member-level CR2 for the projection candidate, from the bounded reducibles** (the
`assemble_closedUnderStep` analogue). -/
theorem projectionPairCandidate_closedUnderStep_ofBounded {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode : RawTerm (scope + 1)}
    {firstCandidate secondCandidate : RawTerm (scope + 1) → Prop}
    (firstReducible : ReducibleTypeAtBounded env bound firstCode firstCandidate)
    (secondReducible : ReducibleTypeAtBounded env bound secondCode secondCandidate)
    {term reduct : RawTerm (scope + 1)}
    (member : projectionPairCandidate firstCandidate secondCandidate term)
    (step : Step term reduct) :
    projectionPairCandidate firstCandidate secondCandidate reduct :=
  projectionPairCandidate_closedUnderStep
    (boundedTypeCarrierObligations firstReducible) (boundedTypeCarrierObligations secondReducible) member step

/-- **Member weak-head expansion for the projection candidate, from the bounded reducibles** (the
`assemble_memberWeakHeadExpansion` analogue). -/
theorem projectionPairCandidate_memberWeakHeadExpansion_ofBounded {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode : RawTerm (scope + 1)}
    {firstCandidate secondCandidate : RawTerm (scope + 1) → Prop}
    (firstReducible : ReducibleTypeAtBounded env bound firstCode firstCandidate)
    (secondReducible : ReducibleTypeAtBounded env bound secondCode secondCandidate)
    {source reduct : RawTerm (scope + 1)}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : projectionPairCandidate firstCandidate secondCandidate reduct) :
    projectionPairCandidate firstCandidate secondCandidate source :=
  projectionPairCandidate_memberWeakHeadExpansion
    (boundedTypeCarrierObligations firstReducible) (boundedTypeCarrierObligations secondReducible)
    weakHeadStep sourceStronglyNormalizing reductMember

/-- **★ The forward `fst` / `snd` residue discharge, from the bounded reducibles.**  A projection member of the
Σ candidate that reaches `pairCell first second` has each component reducible at the LITERAL reached component,
for arbitrary (Π-included) carriers — the Ω-fork-free discharge of `fstFirstMemberIfReachesPair` /
`sndSecondMemberIfReachesPair`. -/
theorem projectionPairCandidate_reachableComponentMembers_ofBounded {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode : RawTerm (scope + 1)}
    {firstCandidate secondCandidate : RawTerm (scope + 1) → Prop}
    (firstReducible : ReducibleTypeAtBounded env bound firstCode firstCandidate)
    (secondReducible : ReducibleTypeAtBounded env bound secondCode secondCandidate)
    {source first second : RawTerm (scope + 1)}
    (member : projectionPairCandidate firstCandidate secondCandidate source)
    (reaches : StepStar source (pairCell first second)) :
    firstCandidate first ∧ secondCandidate second :=
  projectionPairCandidate_reachableComponentMembers
    (boundedTypeCarrierObligations firstReducible) (boundedTypeCarrierObligations secondReducible) member reaches

/-- **The pair intro member builder, from the bounded reducibles** (the pair intro row's member). -/
theorem projectionPairCandidate_memberOfReducibleComponents_ofBounded {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {firstCode secondCode : RawTerm (scope + 1)}
    {firstCandidate secondCandidate : RawTerm (scope + 1) → Prop}
    (firstReducible : ReducibleTypeAtBounded env bound firstCode firstCandidate)
    (secondReducible : ReducibleTypeAtBounded env bound secondCode secondCandidate)
    {first second : RawTerm (scope + 1)}
    (firstMember : firstCandidate first) (secondMember : secondCandidate second) :
    projectionPairCandidate firstCandidate secondCandidate (pairCell first second) :=
  projectionPairCandidate_memberOfReducibleComponents
    (boundedTypeCarrierObligations firstReducible) (boundedTypeCarrierObligations secondReducible)
    firstMember secondMember

end FX1Poly.Typed
