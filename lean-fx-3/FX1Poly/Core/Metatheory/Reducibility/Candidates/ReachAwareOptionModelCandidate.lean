import FX1Poly.Core.Metatheory.Canonicity.CarrierAwareReducibleComponentMembers
import FX1Poly.Core.Metatheory.Reducibility.Candidates.EitherMatchCandidate

/-! # FX1Poly/Core/ReachAwareOptionModelCandidate
    — the reach-aware OPTION candidate is MODEL-VIABLE: member-weak-head-expansion-closed, hence
      head-expansion-closed, congruent — the Ω-fork-free UNARY option model candidate

`reachAwareOptionCandidate` (`CarrierAwareReducibleComponentMembers.lean`) strengthens the NF-value
`carrierAwareOptionCandidate` with a forward-closed clause recording the payload's carrier membership at EVERY
reached `some` injection (not merely the normal form).  It already ships CR1/CR2/CR3 validity and the reach
projection (`reachableSomeMember`).  This file supplies the remaining model-interface properties the bounded
reducibility model's carrier-aware option arm demands — member weak-head expansion, head-expansion closure,
forward closure, the weak-candidate forget, and carrier congruence — establishing that the reach-aware option
candidate is a drop-in model candidate.

It is the UNARY twin of `ReachAwareEitherModelCandidate.lean`: option has one type parameter and its `none`
constructor carries no payload, so there is exactly ONE reach clause (vs the coproduct's inl/inr pair) and ONE
no-drift strip (`weakHeadStripToReachedSome`).

## The no-drift escape from the documented Ω-fork

A `some` injection value is weak-head normal, so the no-drift strip `weakHeadStripToReachedSome` carries a
SOURCE reach `source ↝* some payload` across a weak-head step `source ↝ʰ reduct` to a REDUCT reach
`reduct ↝* some payload` at the SAME `payload` — no drift, no predecessor.  So the reduct's reach clause supplies
`carrierCandidate payload` directly, and the reach clause IS closed under member weak-head expansion;
head-expansion closure (the β-spine special case) follows.  This is the same escape the coproduct twin uses,
specialized to the single `some` injection.

## Why this is the right option model candidate (vs the match-frame candidate)

A second-order match-frame option candidate would demand an UNCONDITIONED some-branch premise
`∀ payload, carrierCandidate payload → resultCandidate (app someBranch payload)` at a FIXED result candidate —
underivable for a DEPENDENT motive, whose branch lands in `candidate (subst0 motive (some payload))`,
convertible to the eliminator's `candidate (subst0 motive scrutinee)` only along the reach
`scrutinee ↝* some payload`.  The reach-aware candidate carries exactly that reach-conditioned payload
membership, which (composed with the some-branch's Π membership and the dependent codomain conversion along the
reach) discharges the dependent `optionMatch` row's reach-conditioned branch residue at the model level.

## Zero-axiom verification

The reach-clause member weak-head expansion is the no-drift strip composed with the reduct clause; the
`carrierAwareOptionCandidate` conjunct's member weak-head expansion is `dataTaitCandidate_memberWeakHead\
Expansion`; head-expansion closure is the β-spine corollary (`WeakHeadStep.betaSpine` + `betaSpineHead\
Expansion` for redex SN); congruence transports the conjuncts pointwise.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace
sweep in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **A no-drift weak-head strip to a reached `some` injection.**  The injection target admits no weak-head step
(`WeakHeadStep.not_from_optionSome`), so it is the `weakHeadStripToNormal` instance — the unary option twin of
`weakHeadStripToReachedInl` / `...Inr`.  A `source` reach to `optionSomeCell payload` strips across a weak-head
step `source ↝ʰ reduct` to a `reduct` reach at the SAME `payload`. -/
theorem weakHeadStripToReachedSome {scope : Nat} {source reduct payload : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (reaches : StepStar source (.mkGen .gen_optionSome () (.childCons payload .childNil))) :
    StepStar reduct (.mkGen .gen_optionSome () (.childCons payload .childNil)) :=
  weakHeadStripToNormal weakHeadStep reaches (fun _ => WeakHeadStep.not_from_optionSome)

/-- **★ The reach-aware option candidate is closed under member weak-head expansion.**  For any
`WeakHeadStep source reduct` with `source` strongly normalizing and `reduct` a reach-aware member, `source` is a
reach-aware member.  The `carrierAwareOptionCandidate` conjunct lifts by `dataTaitCandidate_memberWeakHead\
Expansion`; the reach clause lifts by the NO-DRIFT strip (`weakHeadStripToReachedSome`): a `source` reach to
`some payload` strips across the weak-head step to a `reduct` reach at the SAME payload, whence the reduct's
clause supplies the carrier membership. -/
theorem reachAwareOptionCandidate_memberWeakHeadExpansion {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : reachAwareOptionCandidate carrierCandidate reduct) :
    reachAwareOptionCandidate carrierCandidate source := by
  obtain ⟨reductCarrierMember, reductSomeClause⟩ := reductMember
  refine ⟨dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing
    reductCarrierMember, ?_⟩
  intro payload sourceReachesSome
  exact reductSomeClause payload (weakHeadStripToReachedSome weakHeadStep sourceReachesSome)

/-- **★★★ THE CRUX: the reach-aware option candidate is APP-SPINE head-expansion-closed.**  The model's
head-expansion-closure consumes exactly `HeadExpansionClosed`: a spined β-redex inherits membership from its
contractum.  A β-redex weak-head-steps to its contractum (`WeakHeadStep.betaSpine`), so head-expansion closure
is the DERIVED special case of member weak-head expansion at that step, with the redex SN supplied by
`betaSpineHeadExpansion` from the contractum SN (the candidate's CR1, read off the `carrierAwareOptionCandidate`
conjunct).  The unary twin of `reachAwareEitherCandidate_headExpansionClosed`. -/
theorem reachAwareOptionCandidate_headExpansionClosed {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} :
    HeadExpansionClosed (reachAwareOptionCandidate carrierCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  have contractumStronglyNormalizing : IsStronglyNormalizing
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
    (carrierAwareOptionCandidate_isReducibilityCandidate carrierCandidate).stronglyNormalizing
      contractumMember.1
  exact reachAwareOptionCandidate_memberWeakHeadExpansion WeakHeadStep.betaSpine
    (betaSpineHeadExpansion domainAnnSN argumentSN contractumStronglyNormalizing) contractumMember

/-- **The reach-aware option candidate is forward-closed under one `Step`** (member CR2) — the candidacy
bundle's second leg, surfaced for the model interface's `closedUnderStep` dispatch. -/
theorem reachAwareOptionCandidate_closedUnderStep {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    {term reduct : RawTerm scope}
    (member : reachAwareOptionCandidate carrierCandidate term)
    (step : Step term reduct) :
    reachAwareOptionCandidate carrierCandidate reduct :=
  (reachAwareOptionCandidate_isReducibilityCandidate carrierCandidate).closedUnderStep member step

/-- **The reach-aware option candidate is congruent in its carrier** (the model's `assemble_congr` analogue).
A pointwise-equivalent carrier yields pointwise-equivalent reach-aware option candidates: the
`carrierAwareOptionCandidate` conjunct transports by `carrierAwareOptionCandidate_congr`; the reach clause
transports its payload membership by the carrier iff (COVARIANTLY — the clause CONCLUDES carrier membership,
unlike a match-frame candidate's contravariant branch premise). -/
theorem reachAwareOptionCandidate_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (reachAwareOptionCandidate carrierCandidate1)
      (reachAwareOptionCandidate carrierCandidate2) := by
  have carrierAwareIff := carrierAwareOptionCandidate_congr carrierIff
  intro term
  constructor
  · rintro ⟨carrierMember, someClause⟩
    exact ⟨(carrierAwareIff term).mp carrierMember,
      fun payload reaches => (carrierIff payload).mp (someClause payload reaches)⟩
  · rintro ⟨carrierMember, someClause⟩
    exact ⟨(carrierAwareIff term).mpr carrierMember,
      fun payload reaches => (carrierIff payload).mpr (someClause payload reaches)⟩

/-- **A reach-aware option member is a (weak) `dataTaitCandidate isOptionValue` member.**  The
`carrierAwareOptionCandidate` conjunct forgets to the content-free flat-option candidate via
`carrierAwareOptionCandidate_toWeakOptionCandidate` — the scrutinee bridge the dependent `optionMatch` engine
consumes.  The reach-aware option candidate DOES carry the `dataTaitCandidate isOptionValue` trichotomy, so the
existing eliminator engine is preserved. -/
theorem reachAwareOptionCandidate_toWeakOptionCandidate {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : reachAwareOptionCandidate carrierCandidate term) :
    dataTaitCandidate isOptionValue term :=
  carrierAwareOptionCandidate_toWeakOptionCandidate member.1

end FX1Poly.Core
