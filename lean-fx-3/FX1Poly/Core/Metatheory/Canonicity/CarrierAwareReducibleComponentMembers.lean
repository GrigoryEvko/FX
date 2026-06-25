import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareEitherCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareOptionCandidate
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSubterm
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationMatch

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

/-- **A neutral term's head is never the `eitherInl` constructor** — the coproduct-left ι-vacuity discriminator
(reproved locally to keep this file's import surface minimal; same `cases`/`noConfusion` idiom as
`IsNeutral.rootGenerator_ne_eitherInl`). -/
private theorem isNeutral_rootGenerator_ne_eitherInl {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_eitherInl := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never the `eitherInr` constructor** — the coproduct-right ι-vacuity
discriminator. -/
private theorem isNeutral_rootGenerator_ne_eitherInr {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_eitherInr := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never the `optionSome` constructor** — the option ι-vacuity discriminator. -/
private theorem isNeutral_rootGenerator_ne_optionSome {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_optionSome := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **`eitherInlCell` is injective** — the `mkGen`/`childCons.inj` projection over the single-child injection
spine (the `natSuccCell_inj` idiom). -/
private theorem eitherInlCell_inj {scope : Nat} {payload1 payload2 : RawTerm scope}
    (equal : eitherInlCell payload1 = eitherInlCell payload2) : payload1 = payload2 := by
  injection equal with _scopeEq _generatorEq _payloadEq childrenEq
  exact (RawTermChildren.childCons.inj childrenEq).1

/-- **`eitherInrCell` is injective** — the right-injection twin of `eitherInlCell_inj`. -/
private theorem eitherInrCell_inj {scope : Nat} {payload1 payload2 : RawTerm scope}
    (equal : eitherInrCell payload1 = eitherInrCell payload2) : payload1 = payload2 := by
  injection equal with _scopeEq _generatorEq _payloadEq childrenEq
  exact (RawTermChildren.childCons.inj childrenEq).1

/-- **`optionSomeCell` is injective** — the option-injection twin of `eitherInlCell_inj`. -/
private theorem optionSomeCell_inj {scope : Nat} {payload1 payload2 : RawTerm scope}
    (equal : optionSomeCell payload1 = optionSomeCell payload2) : payload1 = payload2 := by
  injection equal with _scopeEq _generatorEq _payloadEq childrenEq
  exact (RawTermChildren.childCons.inj childrenEq).1

/-- **★ Inversion dual of `memberOfReducibleInl`: a carrier-aware coproduct member that REACHES a left
injection extracts its payload's first-carrier membership at the payload's reachable normal form.**  The
`eitherMatch` left-branch residue substrate: from a carrier-aware member of
`carrierAwareEitherCandidate firstCandidate secondCandidate` reducing to `eitherInlCell payload`, recover a
normal form `payloadNormal` of the payload in `firstCandidate`.  Membership transfers to the reached injection
(CR2 iterated); the injection is SN (CR1), reaches a normal form forced by the unary-cell decomposition to be
`eitherInlCell payloadNormal` with `payload ↝* payloadNormal`; the value-or-neutral disjunct is the value side
(`eitherInlCell` is never neutral), whose left disjunct aligns by `eitherInlCell_inj` and whose right disjunct
is ruled out by the `gen_eitherInl ≠ gen_eitherInr` head clash.  Propext-clean. -/
theorem carrierAwareEitherCandidate.reachableInlMember {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    {source payload : RawTerm scope}
    (member : carrierAwareEitherCandidate firstCandidate secondCandidate source)
    (reaches : StepStar source (eitherInlCell payload)) :
    ∃ payloadNormal : RawTerm scope,
      StepStar payload payloadNormal ∧ RawTerm.isStepNormalForm payloadNormal ∧
      firstCandidate payloadNormal := by
  have inlMember : carrierAwareEitherCandidate firstCandidate secondCandidate (eitherInlCell payload) :=
    closedUnderStepStar
      (carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate) reaches member
  obtain ⟨normalForm, inlReachesNF, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing inlMember.1
  obtain ⟨payloadNormal, normalEq, payloadChain⟩ :=
    stepStar_under_unaryCell eitherInlCell Step.from_eitherInl inlReachesNF payload rfl
  subst normalEq
  rcases inlMember.2 (eitherInlCell payloadNormal) inlReachesNF normalFormIsNormal with
    isCarrierEither | isNeutral
  · rcases isCarrierEither with ⟨valuePayload, cellEq, valueNormal, valueMember⟩
      | ⟨valuePayload, cellEq, _valueNormal, _valueMember⟩
    · have payloadEq := eitherInlCell_inj cellEq
      refine ⟨payloadNormal, payloadChain, ?_, ?_⟩
      · rw [payloadEq]; exact valueNormal
      · rw [payloadEq]; exact valueMember
    · have headEq : Generator.gen_eitherInl = Generator.gen_eitherInr :=
        congrArg RawTerm.rootGenerator cellEq
      exact Generator.noConfusion headEq
  · exact (isNeutral_rootGenerator_ne_eitherInl isNeutral rfl).elim

/-- **★ Inversion dual of `memberOfReducibleInr`: a carrier-aware coproduct member that REACHES a right
injection extracts its payload's second-carrier membership.**  The `eitherMatch` right-branch residue substrate;
the right-injection twin of `reachableInlMember` (the wrong disjunct is the left one, ruled out by
`gen_eitherInr ≠ gen_eitherInl`). -/
theorem carrierAwareEitherCandidate.reachableInrMember {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    {source payload : RawTerm scope}
    (member : carrierAwareEitherCandidate firstCandidate secondCandidate source)
    (reaches : StepStar source (eitherInrCell payload)) :
    ∃ payloadNormal : RawTerm scope,
      StepStar payload payloadNormal ∧ RawTerm.isStepNormalForm payloadNormal ∧
      secondCandidate payloadNormal := by
  have inrMember : carrierAwareEitherCandidate firstCandidate secondCandidate (eitherInrCell payload) :=
    closedUnderStepStar
      (carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate) reaches member
  obtain ⟨normalForm, inrReachesNF, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing inrMember.1
  obtain ⟨payloadNormal, normalEq, payloadChain⟩ :=
    stepStar_under_unaryCell eitherInrCell Step.from_eitherInr inrReachesNF payload rfl
  subst normalEq
  rcases inrMember.2 (eitherInrCell payloadNormal) inrReachesNF normalFormIsNormal with
    isCarrierEither | isNeutral
  · rcases isCarrierEither with ⟨valuePayload, cellEq, _valueNormal, _valueMember⟩
      | ⟨valuePayload, cellEq, valueNormal, valueMember⟩
    · have headEq : Generator.gen_eitherInr = Generator.gen_eitherInl :=
        congrArg RawTerm.rootGenerator cellEq
      exact Generator.noConfusion headEq
    · have payloadEq := eitherInrCell_inj cellEq
      refine ⟨payloadNormal, payloadChain, ?_, ?_⟩
      · rw [payloadEq]; exact valueNormal
      · rw [payloadEq]; exact valueMember
  · exact (isNeutral_rootGenerator_ne_eitherInr isNeutral rfl).elim

/-- **★ Inversion dual of `carrierAwareOptionCandidate.memberOfNormalSome`: a carrier-aware option member that
REACHES a `some` injection extracts its payload's carrier membership.**  The `optionMatch` some-branch residue
substrate.  Same construction as the coproduct extractions, over the unary `optionSomeCell` cell; the wrong
disjunct here is the `none` shape, ruled out by `gen_optionSome ≠ gen_optionNone`. -/
theorem carrierAwareOptionCandidate.reachableSomeMember {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {source payload : RawTerm scope}
    (member : carrierAwareOptionCandidate carrierCandidate source)
    (reaches : StepStar source (optionSomeCell payload)) :
    ∃ payloadNormal : RawTerm scope,
      StepStar payload payloadNormal ∧ RawTerm.isStepNormalForm payloadNormal ∧
      carrierCandidate payloadNormal := by
  have someMember : carrierAwareOptionCandidate carrierCandidate (optionSomeCell payload) :=
    closedUnderStepStar
      (carrierAwareOptionCandidate_isReducibilityCandidate carrierCandidate) reaches member
  obtain ⟨normalForm, someReachesNF, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing someMember.1
  obtain ⟨payloadNormal, normalEq, payloadChain⟩ :=
    stepStar_under_unaryCell optionSomeCell Step.from_optionSome someReachesNF payload rfl
  subst normalEq
  rcases someMember.2 (optionSomeCell payloadNormal) someReachesNF normalFormIsNormal with
    isCarrierOption | isNeutral
  · rcases isCarrierOption with noneEq | ⟨valuePayload, cellEq, valueNormal, valueMember⟩
    · have headEq : Generator.gen_optionSome = Generator.gen_optionNone :=
        congrArg RawTerm.rootGenerator noneEq
      exact Generator.noConfusion headEq
    · have payloadEq := optionSomeCell_inj cellEq
      refine ⟨payloadNormal, payloadChain, ?_, ?_⟩
      · rw [payloadEq]; exact valueNormal
      · rw [payloadEq]; exact valueMember
  · exact (isNeutral_rootGenerator_ne_optionSome isNeutral rfl).elim

/-- **★ Data-case component extraction: a carrier-aware product member over DATA carrier candidates that
REACHES a pair has both components reducible at the REACHED component, not merely at their normal forms.**
`reachableComponentMembers` extracts membership at the reachable NORMAL forms `firstNormal` / `secondNormal`;
when both carriers are `dataTaitCandidate` candidates, the data candidate's unrestricted multi-step
head-expansion (`dataTaitCandidate_memberStepStarExpansion`, free by confluence — the strength a structural
value predicate lacks) carries that membership back along `first ↝* firstNormal` / `second ↝* secondNormal`
to the reached components.  Component strong-normalization — the head-expansion's CR1 obligation — is the
subterm-SN reflection `first/secondComponent_isStronglyNormalizing_of_pair` of the reached pair's SN (the
pair is a member by CR2 iterated).

This is the closed-canonical-forms content the `fst` / `snd` reach-conditioned elim-FT residues
(`firstMemberIfReachesPair` / `secondMemberIfReachesPair`) discharge against when the projected Σ component
types are DATA types: whole-component membership `dataTaitCandidate firstValue first` at the reached pair,
no residual head-expansion interface — the data analogue of the cell-route projection members. -/
theorem carrierAwarePairCandidate.reachableComponentMembersData {scope : Nat}
    {firstValue secondValue : RawTerm scope → Prop} {source first second : RawTerm scope}
    (member :
      carrierAwarePairCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue) source)
    (reaches : StepStar source (pairCell first second)) :
    dataTaitCandidate firstValue first ∧ dataTaitCandidate secondValue second := by
  obtain ⟨firstNormal, secondNormal, firstChain, secondChain, _firstNF, _secondNF,
      firstMember, secondMember⟩ :=
    carrierAwarePairCandidate.reachableComponentMembers member reaches
  have pairMember :
      carrierAwarePairCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue)
        (pairCell first second) :=
    closedUnderStepStar
      (carrierAwarePairCandidate_isReducibilityCandidate (dataTaitCandidate firstValue)
        (dataTaitCandidate secondValue)) reaches member
  have firstSN : IsStronglyNormalizing first := firstComponent_isStronglyNormalizing_of_pair pairMember.1
  have secondSN : IsStronglyNormalizing second := secondComponent_isStronglyNormalizing_of_pair pairMember.1
  exact ⟨dataTaitCandidate_memberStepStarExpansion firstChain firstSN firstMember,
    dataTaitCandidate_memberStepStarExpansion secondChain secondSN secondMember⟩

/-- **★ Data-case left-payload extraction: a carrier-aware coproduct member over a DATA first carrier that
REACHES `inl` has its payload reducible at the REACHED payload.**  The `eitherMatch` left-branch data residue:
`reachableInlMember` gives membership at the reachable normal payload, and the data candidate's multi-step
head-expansion carries it back along `payload ↝* payloadNormal` to the reached payload, with payload SN
reflected from the reached injection's SN by `value_isStronglyNormalizing_of_eitherInl`. -/
theorem carrierAwareEitherCandidate.reachableInlMemberData {scope : Nat}
    {firstValue secondValue : RawTerm scope → Prop} {source payload : RawTerm scope}
    (member :
      carrierAwareEitherCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue) source)
    (reaches : StepStar source (eitherInlCell payload)) :
    dataTaitCandidate firstValue payload := by
  obtain ⟨payloadNormal, payloadChain, _payloadNF, payloadMember⟩ :=
    carrierAwareEitherCandidate.reachableInlMember member reaches
  have inlMember :
      carrierAwareEitherCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue)
        (eitherInlCell payload) :=
    closedUnderStepStar
      (carrierAwareEitherCandidate_isReducibilityCandidate (dataTaitCandidate firstValue)
        (dataTaitCandidate secondValue)) reaches member
  have payloadSN : IsStronglyNormalizing payload :=
    value_isStronglyNormalizing_of_eitherInl inlMember.1
  exact dataTaitCandidate_memberStepStarExpansion payloadChain payloadSN payloadMember

/-- **★ Data-case right-payload extraction: the `inr` twin of `reachableInlMemberData`.**  The `eitherMatch`
right-branch data residue — payload SN reflected by `value_isStronglyNormalizing_of_eitherInr`. -/
theorem carrierAwareEitherCandidate.reachableInrMemberData {scope : Nat}
    {firstValue secondValue : RawTerm scope → Prop} {source payload : RawTerm scope}
    (member :
      carrierAwareEitherCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue) source)
    (reaches : StepStar source (eitherInrCell payload)) :
    dataTaitCandidate secondValue payload := by
  obtain ⟨payloadNormal, payloadChain, _payloadNF, payloadMember⟩ :=
    carrierAwareEitherCandidate.reachableInrMember member reaches
  have inrMember :
      carrierAwareEitherCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue)
        (eitherInrCell payload) :=
    closedUnderStepStar
      (carrierAwareEitherCandidate_isReducibilityCandidate (dataTaitCandidate firstValue)
        (dataTaitCandidate secondValue)) reaches member
  have payloadSN : IsStronglyNormalizing payload :=
    value_isStronglyNormalizing_of_eitherInr inrMember.1
  exact dataTaitCandidate_memberStepStarExpansion payloadChain payloadSN payloadMember

/-- **★ Data-case some-payload extraction: a carrier-aware option member over a DATA carrier that REACHES
`some` has its payload reducible at the REACHED payload.**  The `optionMatch` some-branch data residue — the
option twin of `reachableInlMemberData`, payload SN reflected by `value_isStronglyNormalizing_of_optionSome`. -/
theorem carrierAwareOptionCandidate.reachableSomeMemberData {scope : Nat}
    {carrierValue : RawTerm scope → Prop} {source payload : RawTerm scope}
    (member : carrierAwareOptionCandidate (dataTaitCandidate carrierValue) source)
    (reaches : StepStar source (optionSomeCell payload)) :
    dataTaitCandidate carrierValue payload := by
  obtain ⟨payloadNormal, payloadChain, _payloadNF, payloadMember⟩ :=
    carrierAwareOptionCandidate.reachableSomeMember member reaches
  have someMember :
      carrierAwareOptionCandidate (dataTaitCandidate carrierValue) (optionSomeCell payload) :=
    closedUnderStepStar
      (carrierAwareOptionCandidate_isReducibilityCandidate (dataTaitCandidate carrierValue))
      reaches member
  have payloadSN : IsStronglyNormalizing payload :=
    value_isStronglyNormalizing_of_optionSome someMember.1
  exact dataTaitCandidate_memberStepStarExpansion payloadChain payloadSN payloadMember

end FX1Poly.Core
