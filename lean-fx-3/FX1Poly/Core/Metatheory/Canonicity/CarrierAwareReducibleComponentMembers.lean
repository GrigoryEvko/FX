import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareEitherCandidate

/-! # FX1Poly/Core/CarrierAwareReducibleComponentMembers
    — the general carrier-aware data-introduction members: a constructor of REDUCIBLE (not merely normal)
      carrier components is a carrier-aware member of its content-bearing candidate

`CarrierAwarePairCandidate.memberOfNormalPair` / `CarrierAwareEitherCandidate.memberOfNormalInl` consume
components that are already NORMAL FORMS.  The fundamental-theorem intro rows produce components that are
merely REDUCIBLE MEMBERS of their carrier candidates — strongly normalizing and reduction-closed, but not
normal.  This file ships the general builders that close that gap: a `pairCell` / `eitherInl` / `eitherInr`
of reducible carrier components is a carrier-aware member of the content-bearing flat candidate.

The construction mirrors `RecursiveDataIntroDataTaitMembers`'s `pairDataTaitMember` but carries the carrier
content: the constructor is SN from its components' SN (CR1), and every reachable normal form is the
constructor at NORMAL components (the constructor-reduction decomposition `stepStar_under_{unary,binary}Cell`)
which still lie in the carriers because the carriers are reduction-closed (CR2 iterated to `StepStar`).  So
the reachable normal form is a carrier-aware value, never the neutral disjunct.

These are scope-general (the carrier-aware product/either candidate is `RawTerm scope → Prop` at any scope),
so they apply directly under the bounded-reducibility intro rows' closing substitution at `targetScope + 1`.

## Zero-axiom verification

`pair_isStronglyNormalizing_of_components` / `eitherInl_isStronglyNormalizing_of_value` (CR1 of the cell from
the components), `stepStar_under_{unary,binary}Cell` (constructor reduction decomposition),
`closedUnderStepStar` (CR2 iterated), and the propext-clean Bool conjunction projections.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- Left projection of a Bool conjunction equal to `true`, by `cases` on the left flag (propext-clean; the
library `Bool.and_eq_true` leaks `propext`). -/
private theorem carrierBoolConjLeft {leftFlag rightFlag : Bool}
    (conjunction : (leftFlag && rightFlag) = true) : leftFlag = true := by
  cases leftFlag with
  | true => rfl
  | false => exact conjunction

/-- Right projection of a Bool conjunction equal to `true`, by `cases` on the left flag. -/
private theorem carrierBoolConjRight {leftFlag rightFlag : Bool}
    (conjunction : (leftFlag && rightFlag) = true) : rightFlag = true := by
  cases leftFlag with
  | true => exact conjunction
  | false => nomatch conjunction

/-- **CR2 iterated to `StepStar`.**  A reducibility candidate, closed under one `Step` (CR2), is closed under
multi-step reduction: structural `StepStar` induction threading the single-step closure.  The reduction-closure
the carrier-aware members consume to carry component membership from a constructor to its normal-form
components. -/
theorem closedUnderStepStar {scope : Nat} {predicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate predicate) {source target : RawTerm scope}
    (chain : StepStar source target) : predicate source → predicate target := by
  induction chain with
  | refl _ => exact fun member => member
  | trans firstStep _restChain restInductiveHypothesis =>
      exact fun member => restInductiveHypothesis (candidate.closedUnderStep member firstStep)

/-- **★ General carrier-aware Σ-introduction: a pair of reducible carrier components is a carrier-aware
member.**  Both components need only be reducible members of their carrier candidates (SN by CR1,
reduction-closed by CR2); the pair is SN, and every reachable normal form is `pairCell` at normal components
that still lie in the carriers — a carrier-aware pair value, never neutral.  The data-intro the bounded
`pair` FT row consumes (the SN-component generalization of `memberOfNormalPair`). -/
theorem carrierAwarePairCandidate.memberOfReducibleComponents {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstCandidateIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondCandidateIsCandidate : IsReducibilityCandidate secondCandidate)
    {first second : RawTerm scope}
    (firstMember : firstCandidate first) (secondMember : secondCandidate second) :
    carrierAwarePairCandidate firstCandidate secondCandidate (pairCell first second) := by
  refine ⟨pair_isStronglyNormalizing_of_components
      (firstCandidateIsCandidate.stronglyNormalizing firstMember)
      (secondCandidateIsCandidate.stronglyNormalizing secondMember), ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨firstAfter, secondAfter, targetEq, firstChain, secondChain⟩ :=
    stepStar_under_binaryCell pairCell Step.from_pair reaches first second rfl
  subst targetEq
  have folded : (RawTerm.isStepNormalFormBool firstAfter
      && (RawTerm.isStepNormalFormBool secondAfter && true)) = true := normalFormIsNormal
  have firstAfterNormal : RawTerm.isStepNormalForm firstAfter := carrierBoolConjLeft folded
  have secondAfterNormal : RawTerm.isStepNormalForm secondAfter :=
    carrierBoolConjLeft (carrierBoolConjRight folded)
  exact Or.inl ⟨firstAfter, secondAfter, rfl, firstAfterNormal, secondAfterNormal,
    closedUnderStepStar firstCandidateIsCandidate firstChain firstMember,
    closedUnderStepStar secondCandidateIsCandidate secondChain secondMember⟩

/-- **★ General carrier-aware coproduct introduction (left): `inl` of a reducible carrier payload is a
carrier-aware member.**  The payload need only be a reducible member of the first carrier candidate (SN by
CR1, reduction-closed by CR2); `eitherInl` is SN, and every reachable normal form is `eitherInl` at a normal
payload still in the first carrier — a carrier-aware left injection, never neutral.  The data-intro the
bounded `eitherInl` FT row consumes. -/
theorem carrierAwareEitherCandidate.memberOfReducibleInl {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstCandidateIsCandidate : IsReducibilityCandidate firstCandidate)
    {payload : RawTerm scope} (payloadMember : firstCandidate payload) :
    carrierAwareEitherCandidate firstCandidate secondCandidate (eitherInlCell payload) := by
  refine ⟨eitherInl_isStronglyNormalizing_of_value
      (firstCandidateIsCandidate.stronglyNormalizing payloadMember), ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨payloadAfter, targetEq, payloadChain⟩ :=
    stepStar_under_unaryCell eitherInlCell Step.from_eitherInl reaches payload rfl
  subst targetEq
  have folded : (RawTerm.isStepNormalFormBool payloadAfter && true) = true := normalFormIsNormal
  have payloadAfterNormal : RawTerm.isStepNormalForm payloadAfter := carrierBoolConjLeft folded
  exact Or.inl (Or.inl ⟨payloadAfter, rfl, payloadAfterNormal,
    closedUnderStepStar firstCandidateIsCandidate payloadChain payloadMember⟩)

/-- **★ General carrier-aware coproduct introduction (right): `inr` of a reducible carrier payload is a
carrier-aware member.**  The right-injection twin of `memberOfReducibleInl` — the data-intro the bounded
`eitherInr` FT row consumes. -/
theorem carrierAwareEitherCandidate.memberOfReducibleInr {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (secondCandidateIsCandidate : IsReducibilityCandidate secondCandidate)
    {payload : RawTerm scope} (payloadMember : secondCandidate payload) :
    carrierAwareEitherCandidate firstCandidate secondCandidate (eitherInrCell payload) := by
  refine ⟨eitherInr_isStronglyNormalizing_of_value
      (secondCandidateIsCandidate.stronglyNormalizing payloadMember), ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨payloadAfter, targetEq, payloadChain⟩ :=
    stepStar_under_unaryCell eitherInrCell Step.from_eitherInr reaches payload rfl
  subst targetEq
  have folded : (RawTerm.isStepNormalFormBool payloadAfter && true) = true := normalFormIsNormal
  have payloadAfterNormal : RawTerm.isStepNormalForm payloadAfter := carrierBoolConjLeft folded
  exact Or.inl (Or.inr ⟨payloadAfter, rfl, payloadAfterNormal,
    closedUnderStepStar secondCandidateIsCandidate payloadChain payloadMember⟩)

/-- **A neutral term's head is never the `pair` constructor** — the product ι-vacuity discriminator (the
`pairCell` analogue of `IsNeutral.rootGenerator_ne_optionSome`).  `cases` over the `IsNeutral` constructors
leaves every arm with a generator distinct from `gen_pair`, refuted by `Generator.noConfusion`; zero-axiom (no
`propext`, the constructors fix the head generator definitionally). -/
private theorem isNeutral_rootGenerator_ne_pair {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_pair := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **`pairCell` is injective** — two product cells are equal iff their components are.  The `mkGen` injection
exposes the children equality, then two `RawTermChildren.childCons.inj` drills project the first and second
component (the indices coincide on both sides, so each injection emits a plain `Eq` head component — the
`natSuccCell_inj` idiom over the two-child pair spine). -/
private theorem pairCell_inj {scope : Nat} {first1 second1 first2 second2 : RawTerm scope}
    (equal : pairCell first1 second1 = pairCell first2 second2) :
    first1 = first2 ∧ second1 = second2 := by
  injection equal with _scopeEq _generatorEq _payloadEq childrenEq
  refine ⟨(RawTermChildren.childCons.inj childrenEq).1, ?_⟩
  exact (RawTermChildren.childCons.inj (RawTermChildren.childCons.inj childrenEq).2).1

/-- **★ Inversion dual of `memberOfReducibleComponents`: a carrier-aware product member that REACHES a pair
extracts both components' carrier membership at their reachable normal forms.**  Where the intro builder takes
reducible components and produces a carrier-aware pair member, this inverts: a carrier-aware member of
`carrierAwarePairCandidate firstCandidate secondCandidate` that multi-step-reduces to `pairCell first second`
yields normal forms `firstNormal` / `secondNormal` of the two components, each a member of its carrier
candidate.  This is the "Girard Σ-candidate strengthening tracked separately" the bounded extractor
`productMemberAtBounded_carrierAware` names — the component-membership extraction at every reachable (not merely
already-normal) pair the `fst` / `snd` reach-conditioned elim-FT residues
(`firstMemberIfReachesPair` / `secondMemberIfReachesPair`) discharge against at the closed-canonical-forms leg.

The construction: membership transfers to the reached pair by CR2 iterated (`closedUnderStepStar`); the pair is
SN (CR1), so it reaches a normal form, which the binary-cell reduction decomposition forces to be
`pairCell firstNormal secondNormal` with `first ↝* firstNormal`, `second ↝* secondNormal`; the candidate's
value-or-neutral disjunct at that normal pair is the value side (a `pairCell` is never neutral,
`isNeutral_rootGenerator_ne_pair`), and `pairCell_inj` aligns the value predicate's recorded components with
`firstNormal` / `secondNormal`, transporting their carrier membership.  Injectivity-aware but propext-clean. -/
theorem carrierAwarePairCandidate.reachableComponentMembers {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    {source first second : RawTerm scope}
    (member : carrierAwarePairCandidate firstCandidate secondCandidate source)
    (reaches : StepStar source (pairCell first second)) :
    ∃ firstNormal secondNormal : RawTerm scope,
      StepStar first firstNormal ∧ StepStar second secondNormal ∧
      RawTerm.isStepNormalForm firstNormal ∧ RawTerm.isStepNormalForm secondNormal ∧
      firstCandidate firstNormal ∧ secondCandidate secondNormal := by
  have pairMember : carrierAwarePairCandidate firstCandidate secondCandidate (pairCell first second) :=
    closedUnderStepStar
      (carrierAwarePairCandidate_isReducibilityCandidate firstCandidate secondCandidate) reaches member
  obtain ⟨normalForm, pairReachesNF, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing pairMember.1
  obtain ⟨firstNormal, secondNormal, normalEq, firstChain, secondChain⟩ :=
    stepStar_under_binaryCell pairCell Step.from_pair pairReachesNF first second rfl
  subst normalEq
  rcases pairMember.2 (pairCell firstNormal secondNormal) pairReachesNF normalFormIsNormal with
    isCarrierPair | isNeutral
  · obtain ⟨valueFirst, valueSecond, cellEq, valueFirstNormal, valueSecondNormal,
        firstMember, secondMember⟩ := isCarrierPair
    obtain ⟨firstEq, secondEq⟩ := pairCell_inj cellEq
    refine ⟨firstNormal, secondNormal, firstChain, secondChain, ?_, ?_, ?_, ?_⟩
    · rw [firstEq]; exact valueFirstNormal
    · rw [secondEq]; exact valueSecondNormal
    · rw [firstEq]; exact firstMember
    · rw [secondEq]; exact secondMember
  · exact (isNeutral_rootGenerator_ne_pair isNeutral rfl).elim

end FX1Poly.Core
