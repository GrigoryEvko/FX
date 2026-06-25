import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Metatheory.Reducibility.Core.HeadExpansionClosure
import FX1Poly.Core.Metatheory.Canonicity.SigmaProjectionCanonicalComputation
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationIotaRedexes
import FX1Poly.Core.Substrate.Neutral.NeutralStepClosure
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationDeterminism

/-! # FX1Poly/Core/ProjectionPairCandidate
    — the projection-based Girard Σ candidate (Geuvers TYPES'94), the model-viable Σ reducibility candidate

The carrier-aware product candidate `carrierAwarePairCandidate` records each component's reducibility only at
NORMAL pairs (`pairValueWithMembers` requires `isStepNormalForm`); recovering component membership at the
LITERAL reached component needs backward expansion of the component candidate.  For a DATA carrier that is free
(confluence, `dataTaitCandidate_memberStepStarExpansion`), but for a FUNCTION (Π) carrier it is the
Ω-OBSTRUCTION: the arrow candidate is closed only under one-step / weak-head expansion, and arbitrary-position
expansion would demand `app(first, arg)` strongly normalizing — false because SUBSTITUTION DOES NOT PRESERVE
SN.  (Documented in `CarrierAwareReducibleComponentMembers.lean`; the reach-aware candidate there is NOT
beta-head-expansion-closed, so it cannot be the model candidate.)

This file ships the genuinely model-viable strengthening — the **projection-based Girard candidate**
(Geuvers TYPES'94 "A short and flexible proof of strong normalization for the Calculus of Constructions";
Casinghino arXiv:2210.11240 §6, the "Small Σ-types" `X ⊗ Y := { t | fst t ∈ X ∧ snd t ∈ Y }`):

    projectionPairCandidate fc sc t := IsStronglyNormalizing t ∧ fc (fst t) ∧ sc (snd t)

It is forward-correct (a reached pair projects to its literal components by ι + carrier CR2-forward, NO
expansion, NO Ω-fork) AND — the crux — it satisfies the model's APP-SPINE `HeadExpansionClosed` VERBATIM.  The
earlier worry that "the projection redex sits under `fst`, outside the app-spine form" is dissolved: the redex
`R` weak-head-steps to its contractum `C` (`WeakHeadStep.betaSpine`), so `fst R ↝wh fst C` via
`WeakHeadStep.scrutineeFst` (already a `WeakHeadStep` constructor), and `fc (fst R)` follows from the carrier's
own MEMBER WEAK-HEAD EXPANSION (`dataTaitCandidate_memberWeakHeadExpansion`) with `fst R` strongly normalizing.
So the app-spine `HeadExpansionClosed` is the DERIVED special case (instantiate the `WeakHeadStep` with
`betaSpine`); no generalized `HeadExpansionClosed` notion is required, and its type is unchanged.

The carrier interface the candidate needs is `CarrierObligations`: a reducibility candidate PLUS member
weak-head expansion under any `WeakHeadStep`.  Every `dataTaitCandidate` satisfies it
(`dataTaitCarrierObligations`), and the carrier-aware candidates the model threads ARE `dataTaitCandidate`s, so
the obligations are met by the existing model carriers.

`reachableComponentMembers` discharges the `fst` / `snd` reach-conditioned elim-FT residues
(`fstFirstMemberIfReachesPair` / `sndSecondMemberIfReachesPair`) FORWARD, for ARBITRARY carriers (Π included) —
2 of the 6 `fundamentalElimRowAtBoundedSucc` residues, toward the clean `elimFundamental` the closed-term SN
consistency leg (#1697) consumes.  Wiring (swap the `pairLike` arm of `CarrierCombinator.assemble` to this
candidate) is the follow-up; this file is the additive substrate.

## Zero-axiom verification

CR1/CR2/CR3 over `IsReducibilityCandidate` (fst/snd `Step.cong` congruence, `IsNeutral.fst`/`.snd` + the
`Step.from_fst` ι-vs-congruence dispatch refuting the ι by the neutral-vs-pair head clash); the forward
reach-projection via `StepStar.fstScrutinee` + `IotaHeadStep.iotaFstPair.toStep` + `closedUnderStepStar`; the
head-expansion crux via `WeakHeadStep.scrutineeFst` + the carrier's member weak-head expansion.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the
`FX1Poly.Core` namespace sweep in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `fst` projection cell over its sole child. -/
abbrev fstSpineCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_fst () (.childCons scrutinee .childNil)

/-- The `snd` projection cell over its sole child. -/
abbrev sndSpineCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_snd () (.childCons scrutinee .childNil)

/-- **The projection-based Girard Σ candidate.**  A term is reducible at the product of two carrier candidates
when it is strongly normalizing AND its two projections lie in the carrier candidates.  The model-viable
strengthening: forward-correct (a reached pair projects to its components) and app-spine head-expansion-closed,
provided the carriers are themselves candidates closed under member weak-head expansion (every
`dataTaitCandidate` is). -/
def projectionPairCandidate {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) (term : RawTerm scope) : Prop :=
  IsStronglyNormalizing term ∧
    firstCandidate (fstSpineCell term) ∧ secondCandidate (sndSpineCell term)

/-- **The carrier obligations the projection candidate needs of each component.**  A reducibility candidate
(CR1/CR2/CR3) PLUS member weak-head expansion under any `WeakHeadStep` (`WeakHeadStep source reduct → SN source
→ candidate reduct → candidate source`).  This is the right abstraction — NOT "the carrier is app-spine
`HeadExpansionClosed`" — because the projection frames `scrutineeFst`/`scrutineeSnd` are `WeakHeadStep`s. -/
structure CarrierObligations {scope : Nat} (candidate : RawTerm scope → Prop) : Prop where
  isCandidate : IsReducibilityCandidate candidate
  memberWeakHeadExpansion : ∀ {source reduct : RawTerm scope},
    WeakHeadStep source reduct → IsStronglyNormalizing source → candidate reduct → candidate source

/-- **Every `dataTaitCandidate` satisfies the carrier obligations.**  Its candidacy is
`dataTaitCandidate_isReducibilityCandidate`; its member weak-head expansion is
`dataTaitCandidate_memberWeakHeadExpansion` (for ANY `WeakHeadStep`).  Since the carrier-aware candidates the
model threads ARE `dataTaitCandidate`s, the obligations are met by the existing model carriers. -/
theorem dataTaitCarrierObligations {scope : Nat} (isValue : RawTerm scope → Prop) :
    CarrierObligations (dataTaitCandidate isValue) where
  isCandidate := dataTaitCandidate_isReducibilityCandidate
  memberWeakHeadExpansion := fun weakHeadStep sourceSN reductMember =>
    dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceSN reductMember

/-- **CR1: a projection member is strongly normalizing** — directly the first conjunct. -/
theorem projectionPairCandidate_stronglyNormalizing {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : projectionPairCandidate firstCandidate secondCandidate term) :
    IsStronglyNormalizing term :=
  member.1

/-- **CR2 (forward): a projection member's reduct is a projection member.**  SN forward by accessibility; each
projection's carrier membership forward by the carrier's CR2 along the `fst`/`snd` scrutinee congruence step
(`Step.cong … (StepChildren.here … step)`). -/
theorem projectionPairCandidate_closedUnderStep {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstObligations : CarrierObligations firstCandidate)
    (secondObligations : CarrierObligations secondCandidate)
    {term reduct : RawTerm scope}
    (member : projectionPairCandidate firstCandidate secondCandidate term)
    (step : Step term reduct) :
    projectionPairCandidate firstCandidate secondCandidate reduct := by
  obtain ⟨termSN, fstMember, sndMember⟩ := member
  refine ⟨isStronglyNormalizing_isReducibilityCandidate.closedUnderStep termSN step, ?_, ?_⟩
  · exact firstObligations.isCandidate.closedUnderStep fstMember
      (Step.cong .gen_fst () (StepChildren.here _ step))
  · exact secondObligations.isCandidate.closedUnderStep sndMember
      (Step.cong .gen_snd () (StepChildren.here _ step))

/-- **CR3 (neutral): a neutral term whose every one-step reduct is a projection member is a projection
member.**  SN of the term from the reducts; each projection `fst term` / `snd term` is neutral
(`IsNeutral.fst`/`.snd`), and its reducts are carrier members — a step from `fst term` is either the ι (forces
`term` a pair, impossible since `term` is neutral, refuted by the root-generator clash) or a scrutinee
congruence (the reduct's projection), so the carrier's CR3 applies. -/
theorem projectionPairCandidate_neutralExpansion {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstObligations : CarrierObligations firstCandidate)
    (secondObligations : CarrierObligations secondCandidate)
    {term : RawTerm scope}
    (termIsNeutral : IsNeutral term)
    (reductsMembers : ∀ reduct : RawTerm scope, Step term reduct →
      projectionPairCandidate firstCandidate secondCandidate reduct) :
    projectionPairCandidate firstCandidate secondCandidate term := by
  have termSN : IsStronglyNormalizing term :=
    Acc.intro term (fun reduct step => (reductsMembers reduct step).1)
  refine ⟨termSN, ?_, ?_⟩
  · apply firstObligations.isCandidate.neutralExpansion (IsNeutral.fst termIsNeutral)
    intro fstReduct fstStep
    cases Step.from_fst fstStep with
    | inl iotaProjection =>
        obtain ⟨firstValue, _secondValue, termIsPair, _⟩ := iotaProjection
        exact absurd (termIsPair ▸ rfl : term.rootGenerator = Generator.gen_pair)
          (by cases termIsNeutral <;> exact fun shapeEq => Generator.noConfusion shapeEq)
    | inr scrutineeCong =>
        obtain ⟨termReduct, fstReductEq, termStep⟩ := scrutineeCong
        rw [fstReductEq]
        exact (reductsMembers termReduct termStep).2.1
  · apply secondObligations.isCandidate.neutralExpansion (IsNeutral.snd termIsNeutral)
    intro sndReduct sndStep
    cases Step.from_snd sndStep with
    | inl iotaProjection =>
        obtain ⟨_firstValue, secondValue, termIsPair, _⟩ := iotaProjection
        exact absurd (termIsPair ▸ rfl : term.rootGenerator = Generator.gen_pair)
          (by cases termIsNeutral <;> exact fun shapeEq => Generator.noConfusion shapeEq)
    | inr scrutineeCong =>
        obtain ⟨termReduct, sndReductEq, termStep⟩ := scrutineeCong
        rw [sndReductEq]
        exact (reductsMembers termReduct termStep).2.2

/-- **The projection candidate IS a Girard reducibility candidate** (CR1+CR2+CR3), given the carrier
obligations on both components. -/
theorem projectionPairCandidate_isReducibilityCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstObligations : CarrierObligations firstCandidate)
    (secondObligations : CarrierObligations secondCandidate) :
    IsReducibilityCandidate (projectionPairCandidate firstCandidate secondCandidate) :=
  ⟨projectionPairCandidate_stronglyNormalizing,
   projectionPairCandidate_closedUnderStep firstObligations secondObligations,
   projectionPairCandidate_neutralExpansion firstObligations secondObligations⟩

/-- **★ The forward reach-projection — the `fst` / `snd` residue content, Ω-fork-free.**  A projection member
that reaches `pairCell first second` has `firstCandidate first` and `secondCandidate second` AT THE LITERAL
reached components, for ARBITRARY carriers (no data restriction, no normal-form detour, no expansion).
`fst source ↝* fst (pairCell first second) ↝ first` (scrutinee congruence `StepStar.fstScrutinee` then the ι
`IotaHeadStep.iotaFstPair`), then carrier CR2-forward (`closedUnderStepStar`).  This is the genuine forward
discharge the carrier-aware route could not give for Π component types. -/
theorem projectionPairCandidate_reachableComponentMembers {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstObligations : CarrierObligations firstCandidate)
    (secondObligations : CarrierObligations secondCandidate)
    {source first second : RawTerm scope}
    (member : projectionPairCandidate firstCandidate secondCandidate source)
    (reaches : StepStar source (pairCell first second)) :
    firstCandidate first ∧ secondCandidate second := by
  obtain ⟨_sourceSN, fstMember, sndMember⟩ := member
  have fstReachesFirst : StepStar (fstSpineCell source) first :=
    StepStar.transLast (StepStar.fstScrutinee reaches) IotaHeadStep.iotaFstPair.toStep
  have sndReachesSecond : StepStar (sndSpineCell source) second :=
    StepStar.transLast (StepStar.sndScrutinee reaches) IotaHeadStep.iotaSndPair.toStep
  exact ⟨firstObligations.isCandidate.closedUnderStepStar fstReachesFirst fstMember,
         secondObligations.isCandidate.closedUnderStepStar sndReachesSecond sndMember⟩

/-- **★ The intro: a pair of carrier members is a projection member.**  SN of the pair from the components' SN
(`pair_isStronglyNormalizing_of_components`); `fst (pairCell first second) ↝wh first` is a single ι, so
`firstCandidate (fst (pairCell first second))` follows from `firstCandidate first` by the carrier's member
weak-head expansion (with the projection cell SN). -/
theorem projectionPairCandidate_memberOfReducibleComponents {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstObligations : CarrierObligations firstCandidate)
    (secondObligations : CarrierObligations secondCandidate)
    {first second : RawTerm scope}
    (firstMember : firstCandidate first) (secondMember : secondCandidate second) :
    projectionPairCandidate firstCandidate secondCandidate (pairCell first second) := by
  have firstSN : IsStronglyNormalizing first := firstObligations.isCandidate.stronglyNormalizing firstMember
  have secondSN : IsStronglyNormalizing second := secondObligations.isCandidate.stronglyNormalizing secondMember
  have pairSN : IsStronglyNormalizing (pairCell first second) :=
    pair_isStronglyNormalizing_of_components firstSN secondSN
  refine ⟨pairSN, ?_, ?_⟩
  · have fstCellSN : IsStronglyNormalizing (fstSpineCell (pairCell first second)) :=
      fst_isStronglyNormalizing_of_argument pairSN
    exact firstObligations.memberWeakHeadExpansion
      (WeakHeadStep.rootIota IotaHeadStep.iotaFstPair) fstCellSN firstMember
  · have sndCellSN : IsStronglyNormalizing (sndSpineCell (pairCell first second)) :=
      snd_isStronglyNormalizing_of_argument pairSN
    exact secondObligations.memberWeakHeadExpansion
      (WeakHeadStep.rootIota IotaHeadStep.iotaSndPair) sndCellSN secondMember

/-- **★★★ THE CRUX: the projection candidate is APP-SPINE head-expansion-closed.**  The model's
`assemble_headExpansionClosed` consumes exactly `HeadExpansionClosed` (the app-spine form: a spined β-redex
inherits membership from its contractum).  The under-`fst` redex is NOT an obstruction: the redex `R`
weak-head-steps to its contractum `C` (`WeakHeadStep.betaSpine`), so `fst R ↝wh fst C` via
`WeakHeadStep.scrutineeFst` (already a `WeakHeadStep` constructor), and `firstCandidate (fst R)` follows from
`firstCandidate (fst C)` by the carrier's member weak-head expansion (with `fst R` SN).  So the app-spine form
holds VERBATIM — no generalized `HeadExpansionClosed` notion, its type unchanged. -/
theorem projectionPairCandidate_headExpansionClosed {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstObligations : CarrierObligations firstCandidate)
    (secondObligations : CarrierObligations secondCandidate) :
    HeadExpansionClosed (projectionPairCandidate firstCandidate secondCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  obtain ⟨contractumSN, fstContractumMember, sndContractumMember⟩ := contractumMember
  have redexSN : IsStronglyNormalizing
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        spine) :=
    betaSpineHeadExpansion domainAnnSN argumentSN contractumSN
  have betaWHS : WeakHeadStep
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        spine)
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
    WeakHeadStep.betaSpine
  refine ⟨redexSN, ?_, ?_⟩
  · have fstRedexSN : IsStronglyNormalizing (fstSpineCell _) :=
      fst_isStronglyNormalizing_of_argument redexSN
    exact firstObligations.memberWeakHeadExpansion
      (WeakHeadStep.scrutineeFst betaWHS) fstRedexSN fstContractumMember
  · have sndRedexSN : IsStronglyNormalizing (sndSpineCell _) :=
      snd_isStronglyNormalizing_of_argument redexSN
    exact secondObligations.memberWeakHeadExpansion
      (WeakHeadStep.scrutineeSnd betaWHS) sndRedexSN sndContractumMember

/-- **★ Member weak-head expansion** (the model's `assemble_memberWeakHeadExpansion` analogue).  The projection
candidate is closed under member weak-head expansion for ANY `WeakHeadStep`, reducing to the carrier's member
weak-head expansion under the `scrutineeFst`/`scrutineeSnd` frame. -/
theorem projectionPairCandidate_memberWeakHeadExpansion {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstObligations : CarrierObligations firstCandidate)
    (secondObligations : CarrierObligations secondCandidate)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceSN : IsStronglyNormalizing source)
    (reductMember : projectionPairCandidate firstCandidate secondCandidate reduct) :
    projectionPairCandidate firstCandidate secondCandidate source := by
  obtain ⟨_reductSN, fstReductMember, sndReductMember⟩ := reductMember
  refine ⟨sourceSN, ?_, ?_⟩
  · have fstSourceSN : IsStronglyNormalizing (fstSpineCell source) :=
      fst_isStronglyNormalizing_of_argument sourceSN
    exact firstObligations.memberWeakHeadExpansion
      (WeakHeadStep.scrutineeFst weakHeadStep) fstSourceSN fstReductMember
  · have sndSourceSN : IsStronglyNormalizing (sndSpineCell source) :=
      snd_isStronglyNormalizing_of_argument sourceSN
    exact secondObligations.memberWeakHeadExpansion
      (WeakHeadStep.scrutineeSnd weakHeadStep) sndSourceSN sndReductMember

/-- **The projection candidate is congruent in its carriers** (the model's `assemble_congr` analogue).  The
`fst`/`snd` cells are untouched; each projection's carrier membership swaps under the carrier `PointwiseIff`.
The `deterministic` finisher needs this without `funext`. -/
theorem projectionPairCandidate_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (projectionPairCandidate firstCandidate1 secondCandidate1)
      (projectionPairCandidate firstCandidate2 secondCandidate2) := by
  intro term
  constructor
  · rintro ⟨termSN, fstMember, sndMember⟩
    exact ⟨termSN, (firstIff _).mp fstMember, (secondIff _).mp sndMember⟩
  · rintro ⟨termSN, fstMember, sndMember⟩
    exact ⟨termSN, (firstIff _).mpr fstMember, (secondIff _).mpr sndMember⟩

end FX1Poly.Core
