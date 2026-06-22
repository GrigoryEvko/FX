import FX1Poly.Core.Eliminators.Core.ClosedEliminatorDataTaitMembers
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate

/-! # FX1Poly/Core/Eliminators/Core/CarrierAwareProjectionMembers
    — the Σ projections over the CARRIER-AWARE product candidate (FTGEN-5.1, brick 2)

`fstDataTaitMember` / `sndDataTaitMember` (the shipped open-scope projection arms) take their first/second
component membership as an ASSUMED universal premise — `∀ first second, StepStar scrutinee (pairCell first
second) → dataTaitCandidate isValue first` — because the content-free weak product candidate
(`dataTaitCandidate isPairValue`) does not record component reducibility.  That assumed premise is exactly the
obligation the native fundamental theorem must DISCHARGE at the data-projection elim arm, and the placeholder
the content-free `dataFlat` arm cannot supply.

This file discharges it from the CARRIER-AWARE product candidate (`carrierAwarePairCandidate`, brick 1): a
scrutinee that is a carrier-aware product member ALREADY records, at every reachable normal form that is a
pair, that the components lie in the carrier candidates.  So the projection's contractum membership is read
DIRECTLY off the normal-form disjunct — NO assumed universal premise, no pair-StepStar decomposition, no
component head-expansion threading.  The proof is otherwise the verbatim value/neutral dispatch of
`fstDataTaitMember` (`StepStar.fstScrutinee` congruence + `IotaHeadStep.iotaFstPair` ι row on a pair value;
`IsNeutral.fst` + `memberOfStronglyNormalizingNeutral` on a neutral; both lifted back by
`dataTaitCandidate_memberStepStarExpansion`), with the value-case component membership coming from the
carrier-aware predicate instead of the premise.

These are the eliminator-level payoff of the carrier-aware candidate: `fst scrutinee ∈ ⟦A⟧` and
`snd scrutinee ∈ ⟦B⟧` hold for ANY carrier-aware product member, at arbitrary scope — exactly what the native
FT's projection arms need once the `dataFlat` type-reducibility arm denotes `carrierAwarePairCandidate`.

## Zero-axiom verification

Direct composition of the shipped audited Core projection machinery with the brick-1 carrier-aware candidate;
the value-case membership is the fourth conjunct of `pairValueWithMembers`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **★ FTGEN-5.1 — open `fst` over the CARRIER-AWARE product candidate.**  The first projection of a
carrier-aware product member is a member of the first carrier candidate `dataTaitCandidate firstValue` — with
NO assumed component-membership premise.  The scrutinee's strongly-normalizing normal form is a carrier-aware
pair value or neutral (`carrierAwarePairCandidate`'s second conjunct): a carrier-aware pair value
ι-projects to its first component (`StepStar.fstScrutinee` then `IotaHeadStep.iotaFstPair`), whose carrier
membership is recorded IN the normal-form disjunct (`pairValueWithMembers`'s fourth conjunct), while a
neutral normal form leaves the projection cell neutral (`IsNeutral.fst` +
`memberOfStronglyNormalizingNeutral`); both lift back through the scrutinee congruence by
`dataTaitCandidate_memberStepStarExpansion`. -/
theorem fstCarrierAwareMember {scope : Nat} {firstValue secondValue : RawTerm scope → Prop}
    {scrutinee : RawTerm scope}
    (scrutineeMember :
      carrierAwarePairCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue) scrutinee) :
    dataTaitCandidate firstValue (.mkGen .gen_fst () (.childCons scrutinee .childNil)) := by
  have member :
      dataTaitCandidate
        (pairValueWithMembers (dataTaitCandidate firstValue) (dataTaitCandidate secondValue)) scrutinee :=
    scrutineeMember
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_fst () (.childCons scrutinee .childNil)) :=
    fst_isStronglyNormalizing_of_argument member.stronglyNormalizing
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing member.stronglyNormalizing
  have cellToNormalFormCell :
      StepStar (.mkGen .gen_fst () (.childCons scrutinee .childNil))
        (.mkGen .gen_fst () (.childCons scrutineeNormalForm .childNil)) :=
    StepStar.fstScrutinee scrutineeToNormalForm
  rcases member.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    normalFormIsPair | normalFormIsNeutral
  · obtain ⟨firstComponent, secondComponent, normalFormEq, _firstNormal, _secondNormal,
      firstComponentMember, _secondComponentMember⟩ := normalFormIsPair
    subst normalFormEq
    have fstReducesToFirst :
        StepStar (.mkGen .gen_fst () (.childCons scrutinee .childNil)) firstComponent :=
      StepStar.transLast (StepStar.fstScrutinee scrutineeToNormalForm) IotaHeadStep.iotaFstPair.toStep
    exact dataTaitCandidate_memberStepStarExpansion fstReducesToFirst cellStronglyNormalizing
      firstComponentMember
  · have normalFormCellStronglyNormalizing :
        IsStronglyNormalizing (.mkGen .gen_fst () (.childCons scrutineeNormalForm .childNil)) :=
      isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      (dataTaitCandidate.memberOfStronglyNormalizingNeutral normalFormCellStronglyNormalizing
        (IsNeutral.fst normalFormIsNeutral))

/-- **★ FTGEN-5.1 — open `snd` over the CARRIER-AWARE product candidate.**  Symmetric to
`fstCarrierAwareMember`: the second projection of a carrier-aware product member is a member of the second
carrier candidate `dataTaitCandidate secondValue`, reading the second component's membership off the
carrier-aware normal-form disjunct (`pairValueWithMembers`'s fifth conjunct), ι-selecting via
`IotaHeadStep.iotaSndPair`, staying neutral on a neutral scrutinee (`IsNeutral.snd`), with NO assumed
component-membership premise. -/
theorem sndCarrierAwareMember {scope : Nat} {firstValue secondValue : RawTerm scope → Prop}
    {scrutinee : RawTerm scope}
    (scrutineeMember :
      carrierAwarePairCandidate (dataTaitCandidate firstValue) (dataTaitCandidate secondValue) scrutinee) :
    dataTaitCandidate secondValue (.mkGen .gen_snd () (.childCons scrutinee .childNil)) := by
  have member :
      dataTaitCandidate
        (pairValueWithMembers (dataTaitCandidate firstValue) (dataTaitCandidate secondValue)) scrutinee :=
    scrutineeMember
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_snd () (.childCons scrutinee .childNil)) :=
    snd_isStronglyNormalizing_of_argument member.stronglyNormalizing
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing member.stronglyNormalizing
  have cellToNormalFormCell :
      StepStar (.mkGen .gen_snd () (.childCons scrutinee .childNil))
        (.mkGen .gen_snd () (.childCons scrutineeNormalForm .childNil)) :=
    StepStar.sndScrutinee scrutineeToNormalForm
  rcases member.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    normalFormIsPair | normalFormIsNeutral
  · obtain ⟨firstComponent, secondComponent, normalFormEq, _firstNormal, _secondNormal,
      _firstComponentMember, secondComponentMember⟩ := normalFormIsPair
    subst normalFormEq
    have sndReducesToSecond :
        StepStar (.mkGen .gen_snd () (.childCons scrutinee .childNil)) secondComponent :=
      StepStar.transLast (StepStar.sndScrutinee scrutineeToNormalForm) IotaHeadStep.iotaSndPair.toStep
    exact dataTaitCandidate_memberStepStarExpansion sndReducesToSecond cellStronglyNormalizing
      secondComponentMember
  · have normalFormCellStronglyNormalizing :
        IsStronglyNormalizing (.mkGen .gen_snd () (.childCons scrutineeNormalForm .childNil)) :=
      isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      (dataTaitCandidate.memberOfStronglyNormalizingNeutral normalFormCellStronglyNormalizing
        (IsNeutral.snd normalFormIsNeutral))

end FX1Poly.Core
