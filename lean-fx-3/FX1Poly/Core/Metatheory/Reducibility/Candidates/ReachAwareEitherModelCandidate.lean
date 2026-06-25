import FX1Poly.Core.Metatheory.Canonicity.CarrierAwareReducibleComponentMembers
import FX1Poly.Core.Metatheory.Reducibility.Candidates.EitherMatchCandidate

/-! # FX1Poly/Core/ReachAwareEitherModelCandidate
    — the reach-aware coproduct candidate is MODEL-VIABLE: member-weak-head-expansion-closed, hence
      head-expansion-closed, congruent — the Ω-fork-free coproduct model candidate

`reachAwareEitherCandidate` (`CarrierAwareReducibleComponentMembers.lean`) strengthens the NF-value
`carrierAwareEitherCandidate` with two forward-closed clauses recording the payload's carrier membership at
EVERY reached `inl` / `inr` injection (not merely the normal form).  It already ships CR1/CR2/CR3 validity,
the reach projections (`reachableInlMember` / `reachableInrMember`), and the forward intros
(`memberOfReducibleInl` / `memberOfReducibleInr`).

This file supplies the THREE remaining model-interface properties the bounded reducibility model's
`dataFlatCarrierAware` coproduct arm demands — member weak-head expansion, head-expansion closure, and
carrier congruence — establishing that the reach-aware candidate is a drop-in model candidate at
`coproductLike`.

## The no-drift escape from the documented Ω-fork

The reach-aware section docstring (`CarrierAwareReducibleComponentMembers.lean`) flagged the reach clause as
NOT beta-head-expansion-closed, on the worry that a head-expanded term reaches injections whose payload is a
PREDECESSOR of the contractum's reached payload.  That worry is specific to recovering carrier membership at a
DRIFTED payload.  For the coproduct reach-to-injection clause it does NOT arise: an injection value is
weak-head normal, so the no-drift strip `weakHeadStripToReachedInl` / `weakHeadStripToReachedInr`
(`EitherMatchCandidate.lean`) carries a SOURCE reach `source ↝* inl payload` across a weak-head step
`source ↝ʰ reduct` to a REDUCT reach `reduct ↝* inl payload` at the SAME `payload` — no drift, no predecessor.
So the reduct's reach clause supplies `firstCandidate payload` directly, and the reach clause IS closed under
member weak-head expansion.  Head-expansion closure (the β-spine special case) follows.

## Why this is the right coproduct model candidate (vs the match-frame `eitherMatchCandidate`)

The match-frame `eitherMatchCandidate` is head-expansion-closed and forward-correct, but its second-order
universal demands an UNCONDITIONED branch premise `∀ payload, firstCandidate payload → resultCandidate
(app leftBranch payload)` at a FIXED result candidate — underivable for a DEPENDENT motive, whose branch lands
in `candidate (subst0 motive (inl payload))`, convertible to the eliminator's `candidate (subst0 motive
scrutinee)` only along the reach `scrutinee ↝* inl payload`.  The reach-aware candidate carries exactly that
reach-conditioned payload membership, which (composed with the branch's Π membership and the dependent codomain
conversion along the reach) discharges the dependent `eitherMatch` row's reach-conditioned branch residues at
the model level — the genuine dissolution the dependent case requires.

## Zero-axiom verification

The reach-clause member weak-head expansion is the no-drift strip composed with the reduct clause; the
`carrierAwareEitherCandidate` conjunct's member weak-head expansion is `dataTaitCandidate_memberWeakHead\
Expansion`; head-expansion closure is the β-spine corollary (`WeakHeadStep.betaSpine` + `betaSpineHead\
Expansion` for redex SN); congruence transports the conjuncts pointwise.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace
sweep in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **★ The reach-aware coproduct candidate is closed under member weak-head expansion.**  For any
`WeakHeadStep source reduct` with `source` strongly normalizing and `reduct` a reach-aware member, `source` is a
reach-aware member.  The `carrierAwareEitherCandidate` conjunct lifts by `dataTaitCandidate_memberWeakHead\
Expansion`; each reach clause lifts by the NO-DRIFT strip (`weakHeadStripToReachedInl` / `...Inr`): a `source`
reach to `inl` / `inr payload` strips across the weak-head step to a `reduct` reach at the SAME payload, whence
the reduct's clause supplies the carrier membership. -/
theorem reachAwareEitherCandidate_memberWeakHeadExpansion {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : reachAwareEitherCandidate firstCandidate secondCandidate reduct) :
    reachAwareEitherCandidate firstCandidate secondCandidate source := by
  obtain ⟨reductCarrierMember, reductInlClause, reductInrClause⟩ := reductMember
  refine ⟨dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing
    reductCarrierMember, ?_, ?_⟩
  · intro payload sourceReachesInl
    exact reductInlClause payload (weakHeadStripToReachedInl weakHeadStep sourceReachesInl)
  · intro payload sourceReachesInr
    exact reductInrClause payload (weakHeadStripToReachedInr weakHeadStep sourceReachesInr)

/-- **★★★ THE CRUX: the reach-aware coproduct candidate is APP-SPINE head-expansion-closed.**  The model's
`assembleModel_headExpansionClosed` consumes exactly `HeadExpansionClosed`: a spined β-redex inherits membership
from its contractum.  A β-redex weak-head-steps to its contractum (`WeakHeadStep.betaSpine`), so head-expansion
closure is the DERIVED special case of member weak-head expansion at that step, with the redex SN supplied by
`betaSpineHeadExpansion` from the contractum SN (the candidate's CR1, read off the `carrierAwareEitherCandidate`
conjunct).  This REFUTES the reach-aware section's documented β-head-expansion pessimism for the coproduct:
the no-drift strip closes it cleanly. -/
theorem reachAwareEitherCandidate_headExpansionClosed {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} :
    HeadExpansionClosed (reachAwareEitherCandidate firstCandidate secondCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  have contractumStronglyNormalizing : IsStronglyNormalizing
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
    (carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate).stronglyNormalizing
      contractumMember.1
  exact reachAwareEitherCandidate_memberWeakHeadExpansion WeakHeadStep.betaSpine
    (betaSpineHeadExpansion domainAnnSN argumentSN contractumStronglyNormalizing) contractumMember

/-- **The reach-aware coproduct candidate is forward-closed under one `Step`** (member CR2) — the candidacy
bundle's second leg, surfaced for the model interface's `closedUnderStep` dispatch. -/
theorem reachAwareEitherCandidate_closedUnderStep {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    {term reduct : RawTerm scope}
    (member : reachAwareEitherCandidate firstCandidate secondCandidate term)
    (step : Step term reduct) :
    reachAwareEitherCandidate firstCandidate secondCandidate reduct :=
  (reachAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate).closedUnderStep
    member step

/-- **The reach-aware coproduct candidate is congruent in its carriers** (the model's `assemble_congr`
analogue).  Pointwise-equivalent carriers yield pointwise-equivalent reach-aware candidates: the
`carrierAwareEitherCandidate` conjunct transports by `carrierAwareEitherCandidate_congr`; each reach clause
transports its payload membership by the corresponding carrier iff (COVARIANTLY — the clause CONCLUDES carrier
membership, unlike the match-frame candidate's contravariant branch premises). -/
theorem reachAwareEitherCandidate_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (reachAwareEitherCandidate firstCandidate1 secondCandidate1)
      (reachAwareEitherCandidate firstCandidate2 secondCandidate2) := by
  have carrierIff := carrierAwareEitherCandidate_congr firstIff secondIff
  intro term
  constructor
  · rintro ⟨carrierMember, inlClause, inrClause⟩
    exact ⟨(carrierIff term).mp carrierMember,
      fun payload reaches => (firstIff payload).mp (inlClause payload reaches),
      fun payload reaches => (secondIff payload).mp (inrClause payload reaches)⟩
  · rintro ⟨carrierMember, inlClause, inrClause⟩
    exact ⟨(carrierIff term).mpr carrierMember,
      fun payload reaches => (firstIff payload).mpr (inlClause payload reaches),
      fun payload reaches => (secondIff payload).mpr (inrClause payload reaches)⟩

/-- **A reach-aware coproduct member is a (weak) `dataTaitCandidate isEitherValue` member.**  The
`carrierAwareEitherCandidate` conjunct forgets to the content-free flat-either candidate via
`carrierAwareEitherCandidate_toWeakEitherCandidate` — the scrutinee bridge the dependent `eitherMatch` engine
consumes.  Unlike the match-frame candidate (which does NOT reduce to injection values), the reach-aware
candidate DOES carry the `dataTaitCandidate isEitherValue` trichotomy, so the existing eliminator engine is
preserved. -/
theorem reachAwareEitherCandidate_toWeakEitherCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : reachAwareEitherCandidate firstCandidate secondCandidate term) :
    dataTaitCandidate isEitherValue term :=
  carrierAwareEitherCandidate_toWeakEitherCandidate member.1

end FX1Poly.Core
