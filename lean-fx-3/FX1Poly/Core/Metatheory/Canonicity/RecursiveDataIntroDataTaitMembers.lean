import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Metatheory.Canonicity.NatCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Canonicity.ListCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Canonicity.OptionCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Canonicity.EitherCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Canonicity.PairCanonicalFormsCandidate
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors

/-! # FX1Poly/Core/RecursiveDataIntroDataTaitMembers
    — the COMPLETE recursive data-introduction arm of the fundamental theorem (FTGEN-9 deeper), zero-axiom

The nullary / already-normal data-intro arm (`inductiveSaturatedIntro` / `dataTaitCandidate.memberOfValue`)
covers constructors whose argument is already a normal value (`natZero`/`boolTrue`/`optionNone`/`listNil`/…).
This file closes the RECURSIVE intro arm uniformly: a constructor applied to a non-normal but REDUCIBLE
argument is a member of its data candidate.  All six recursive data constructors of the kernel are covered:

  * `natSucc`     — recursive Nat (predecessor reducible)
  * `optionSome`  — structural Option (payload reducible)
  * `eitherInl` / `eitherInr` — structural Either (payload reducible)
  * `pair`        — structural Σ (both components reducible)
  * `listCons`    — recursive List (head reducible, tail reducible)

The structural value predicates (`isPairValue`/`isEitherValue`/`isOptionValue`) record only that the
children are NORMAL, so their intro arms need only the children's strong normalization.  The RECURSIVE value
predicates (`IsNatValue`/`IsListValue`) recurse into the value structure of the recursive child, so those
arms need the recursive child to be a candidate MEMBER and rule the closed neutral disjunct out
(`IsNeutral.noClosed`) — at scope 0 a `natSucc`/`listCons` of a stuck-neutral child would be neither a value
nor neutral, so closedness is genuinely load-bearing there.

  * **`stepStar_under_unaryCell` / `stepStar_under_binaryCell`** — generic reduction-under-a-constructor
    decompositions, parameterized by the constructor's single-step inversion (`Step.from_*`): every
    multi-step reduct of `C(children)` is `C(reduced children)`, the children evolving independently.
  * **The six `*DataTaitMember` arms** — each: SN-closure (`*_isStronglyNormalizing_of_*`) for the first
    conjunct; the decomposition routes each reachable normal form to reachable normal forms of the children,
    which the structural predicate accepts directly (children normal) or the recursive child's membership
    classifies as a value (neutral ruled out).

## Zero-axiom

Structural `StepStar` induction + the shipped `Step.from_*` / `*_isStronglyNormalizing_of_*` /
`IsNeutral.noClosed` + Bool conjunction projections for the children-normal extraction.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditRecursiveDataIntroDataTaitMembers.lean`. -/

namespace FX1Poly.Core

open StepStar

/-- Left projection of a Bool conjunction equal to `true`, by `cases` on the left flag (propext-clean;
the library `Bool.and_eq_true` leaks `propext`). -/
private theorem boolConjLeft {leftFlag rightFlag : Bool}
    (conjunction : (leftFlag && rightFlag) = true) : leftFlag = true := by
  cases leftFlag with
  | true => rfl
  | false => exact conjunction

/-- Right projection of a Bool conjunction equal to `true`, by `cases` on the left flag. -/
private theorem boolConjRight {leftFlag rightFlag : Bool}
    (conjunction : (leftFlag && rightFlag) = true) : rightFlag = true := by
  cases leftFlag with
  | true => exact conjunction
  | false => nomatch conjunction

/-- **Reduction under a one-child constructor decomposes.**  Every multi-step reduct of a unary cell
`C(child)` is `C(childAfter)` for a multi-step reduct `childAfter` of `child` — structural `StepStar`
induction, each step inverted by the constructor's single-step inversion. -/
theorem stepStar_under_unaryCell {scope : Nat} (cellOf : RawTerm scope → RawTerm scope)
    (stepInversion : ∀ {child reduct : RawTerm scope},
      Step (cellOf child) reduct →
        ∃ childAfter : RawTerm scope, reduct = cellOf childAfter ∧ Step child childAfter)
    {source target : RawTerm scope} (chain : StepStar source target) :
    ∀ child : RawTerm scope, source = cellOf child →
      ∃ childAfter : RawTerm scope, target = cellOf childAfter ∧ StepStar child childAfter := by
  induction chain with
  | refl currentTerm =>
      intro child sourceEq
      exact ⟨child, sourceEq, StepStar.refl child⟩
  | trans firstStep _restChain restInductiveHypothesis =>
      intro child sourceEq
      subst sourceEq
      obtain ⟨intermediateChild, intermediateEq, childStep⟩ := stepInversion firstStep
      obtain ⟨finalChild, targetEq, childChain⟩ :=
        restInductiveHypothesis intermediateChild intermediateEq
      exact ⟨finalChild, targetEq, StepStar.trans childStep childChain⟩

/-- **Reduction under a two-child constructor decomposes.**  Every multi-step reduct of a binary cell
`C(first, second)` is `C(firstAfter, secondAfter)` for multi-step reducts of each component — structural
`StepStar` induction, each step inverted to a step on exactly one of the two children. -/
theorem stepStar_under_binaryCell {scope : Nat}
    (cellOf : RawTerm scope → RawTerm scope → RawTerm scope)
    (stepInversion : ∀ {firstChild secondChild reduct : RawTerm scope},
      Step (cellOf firstChild secondChild) reduct →
        (∃ firstAfter : RawTerm scope,
            reduct = cellOf firstAfter secondChild ∧ Step firstChild firstAfter) ∨
        (∃ secondAfter : RawTerm scope,
            reduct = cellOf firstChild secondAfter ∧ Step secondChild secondAfter))
    {source target : RawTerm scope} (chain : StepStar source target) :
    ∀ firstChild secondChild : RawTerm scope,
      source = cellOf firstChild secondChild →
      ∃ firstAfter secondAfter : RawTerm scope,
        target = cellOf firstAfter secondAfter ∧
        StepStar firstChild firstAfter ∧ StepStar secondChild secondAfter := by
  induction chain with
  | refl currentTerm =>
      intro firstChild secondChild sourceEq
      exact ⟨firstChild, secondChild, sourceEq, StepStar.refl firstChild, StepStar.refl secondChild⟩
  | trans firstStep _restChain restInductiveHypothesis =>
      intro firstChild secondChild sourceEq
      subst sourceEq
      cases stepInversion firstStep with
      | inl firstBranch =>
          obtain ⟨intermediateFirst, intermediateEq, firstStepChild⟩ := firstBranch
          obtain ⟨finalFirst, finalSecond, targetEq, firstChain, secondChain⟩ :=
            restInductiveHypothesis intermediateFirst secondChild intermediateEq
          exact ⟨finalFirst, finalSecond, targetEq,
            StepStar.trans firstStepChild firstChain, secondChain⟩
      | inr secondBranch =>
          obtain ⟨intermediateSecond, intermediateEq, secondStepChild⟩ := secondBranch
          obtain ⟨finalFirst, finalSecond, targetEq, firstChain, secondChain⟩ :=
            restInductiveHypothesis firstChild intermediateSecond intermediateEq
          exact ⟨finalFirst, finalSecond, targetEq,
            firstChain, StepStar.trans secondStepChild secondChain⟩

/-- **★ Recursive Nat intro: `natSucc` of a reducible predecessor is reducible.**  Recursive value
predicate — the predecessor must be a member (its reachable numeral lifts through `IsNatValue.succ`); the
closed neutral disjunct is impossible. -/
theorem natSuccDataTaitMember {predecessor : RawTerm 0}
    (predecessorMember : dataTaitCandidate IsNatValue predecessor) :
    dataTaitCandidate IsNatValue (natSuccCell predecessor) := by
  refine ⟨natSucc_isStronglyNormalizing_of_predecessor predecessorMember.1, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨predecessorAfter, targetEq, predecessorChain⟩ :=
    stepStar_under_unaryCell natSuccCell Step.from_natSucc reaches predecessor rfl
  subst targetEq
  have predecessorAfterNormal : RawTerm.isStepNormalForm predecessorAfter := by
    have folded : (RawTerm.isStepNormalFormBool predecessorAfter && true) = true := normalFormIsNormal
    rw [Bool.and_true] at folded
    exact folded
  rcases predecessorMember.2 predecessorAfter predecessorChain predecessorAfterNormal with
      predecessorIsValue | predecessorIsNeutral
  · exact Or.inl (IsNatValue.succ predecessorIsValue)
  · exact (IsNeutral.noClosed predecessorIsNeutral).elim

/-- **★ Structural Option intro: `optionSome` of a reducible payload is reducible.**  Structural value
predicate — the payload need only strongly normalize; its reachable normal form witnesses the value.
Open-scope (the intro FT member rows instantiate it at `targetScope + 1`): nothing in the construction
pins the scope to `0`. -/
theorem optionSomeDataTaitMember {scope : Nat} {payload : RawTerm scope}
    (payloadStronglyNormalizing : IsStronglyNormalizing payload) :
    dataTaitCandidate isOptionValue (optionSomeCell payload) := by
  refine ⟨optionSome_isStronglyNormalizing_of_value payloadStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨payloadAfter, targetEq, _payloadChain⟩ :=
    stepStar_under_unaryCell optionSomeCell Step.from_optionSome reaches payload rfl
  subst targetEq
  have payloadAfterNormal : RawTerm.isStepNormalForm payloadAfter := by
    have folded : (RawTerm.isStepNormalFormBool payloadAfter && true) = true := normalFormIsNormal
    rw [Bool.and_true] at folded
    exact folded
  exact Or.inl (Or.inr ⟨payloadAfter, rfl, payloadAfterNormal⟩)

/-- **★ Structural Either intro (left): `eitherInl` of a reducible payload is reducible.** -/
theorem eitherInlDataTaitMember {payload : RawTerm 0}
    (payloadStronglyNormalizing : IsStronglyNormalizing payload) :
    dataTaitCandidate isEitherValue (eitherInlCell payload) := by
  refine ⟨eitherInl_isStronglyNormalizing_of_value payloadStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨payloadAfter, targetEq, _payloadChain⟩ :=
    stepStar_under_unaryCell eitherInlCell Step.from_eitherInl reaches payload rfl
  subst targetEq
  have payloadAfterNormal : RawTerm.isStepNormalForm payloadAfter := by
    have folded : (RawTerm.isStepNormalFormBool payloadAfter && true) = true := normalFormIsNormal
    rw [Bool.and_true] at folded
    exact folded
  exact Or.inl (Or.inl ⟨payloadAfter, rfl, payloadAfterNormal⟩)

/-- **★ Structural Either intro (right): `eitherInr` of a reducible payload is reducible.** -/
theorem eitherInrDataTaitMember {payload : RawTerm 0}
    (payloadStronglyNormalizing : IsStronglyNormalizing payload) :
    dataTaitCandidate isEitherValue (eitherInrCell payload) := by
  refine ⟨eitherInr_isStronglyNormalizing_of_value payloadStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨payloadAfter, targetEq, _payloadChain⟩ :=
    stepStar_under_unaryCell eitherInrCell Step.from_eitherInr reaches payload rfl
  subst targetEq
  have payloadAfterNormal : RawTerm.isStepNormalForm payloadAfter := by
    have folded : (RawTerm.isStepNormalFormBool payloadAfter && true) = true := normalFormIsNormal
    rw [Bool.and_true] at folded
    exact folded
  exact Or.inl (Or.inr ⟨payloadAfter, rfl, payloadAfterNormal⟩)

/-- **★ Structural Σ intro: `pair` of two reducible components is reducible.**  Both components need only
strongly normalize; their reachable normal forms witness the structural pair value. -/
theorem pairDataTaitMember {firstComponent secondComponent : RawTerm 0}
    (firstStronglyNormalizing : IsStronglyNormalizing firstComponent)
    (secondStronglyNormalizing : IsStronglyNormalizing secondComponent) :
    dataTaitCandidate isPairValue (pairCell firstComponent secondComponent) := by
  refine ⟨pair_isStronglyNormalizing_of_components firstStronglyNormalizing
    secondStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨firstAfter, secondAfter, targetEq, _firstChain, _secondChain⟩ :=
    stepStar_under_binaryCell pairCell Step.from_pair reaches firstComponent secondComponent rfl
  subst targetEq
  have firstAfterNormal : RawTerm.isStepNormalForm firstAfter := by
    have folded : (RawTerm.isStepNormalFormBool firstAfter &&
        (RawTerm.isStepNormalFormBool secondAfter && true)) = true := normalFormIsNormal
    exact boolConjLeft folded
  have secondAfterNormal : RawTerm.isStepNormalForm secondAfter := by
    have folded : (RawTerm.isStepNormalFormBool firstAfter &&
        (RawTerm.isStepNormalFormBool secondAfter && true)) = true := normalFormIsNormal
    exact boolConjLeft (boolConjRight folded)
  exact Or.inl ⟨firstAfter, secondAfter, rfl, firstAfterNormal, secondAfterNormal⟩

/-- **★ Recursive List intro: `listCons` of a reducible head onto a reducible tail is reducible.**  Mixed:
the head is structural (need only its reachable normal form), while the tail is recursive — it must be a
member, its reachable list value lifting through `IsListValue.cons`; the closed neutral tail is impossible. -/
theorem listConsDataTaitMember {headValue tailValue : RawTerm 0}
    (headStronglyNormalizing : IsStronglyNormalizing headValue)
    (tailMember : dataTaitCandidate IsListValue tailValue) :
    dataTaitCandidate IsListValue (listConsCell headValue tailValue) := by
  refine ⟨listCons_isStronglyNormalizing_of_head_tail headStronglyNormalizing tailMember.1, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨headAfter, tailAfter, targetEq, _headChain, tailChain⟩ :=
    stepStar_under_binaryCell listConsCell Step.from_listCons reaches headValue tailValue rfl
  subst targetEq
  have headAfterNormal : RawTerm.isStepNormalForm headAfter := by
    have folded : (RawTerm.isStepNormalFormBool headAfter &&
        (RawTerm.isStepNormalFormBool tailAfter && true)) = true := normalFormIsNormal
    exact boolConjLeft folded
  have tailAfterNormal : RawTerm.isStepNormalForm tailAfter := by
    have folded : (RawTerm.isStepNormalFormBool headAfter &&
        (RawTerm.isStepNormalFormBool tailAfter && true)) = true := normalFormIsNormal
    exact boolConjLeft (boolConjRight folded)
  rcases tailMember.2 tailAfter tailChain tailAfterNormal with tailIsValue | tailIsNeutral
  · exact Or.inl (IsListValue.cons headAfterNormal tailIsValue)
  · exact (IsNeutral.noClosed tailIsNeutral).elim

end FX1Poly.Core
