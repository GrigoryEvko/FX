import FX1Poly.Core.Metatheory.Reducibility.Candidates.ProjectionPairCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DependentArrowReducibilityCandidate
import FX1Poly.Core.Eliminators.Core.EitherMatchGeneralCandidateMember
import FX1Poly.Core.Eliminators.Match.MatchReductTrackingStrongNormalization
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepCommute
import FX1Poly.Core.Rewriting.Normalize.WeakHeadStepNormalForms

/-! # FX1Poly/Core/EitherMatchCandidate
    — the match-frame Girard coproduct candidate (Geuvers TYPES'94), the model-viable + candidate

This is the COPRODUCT analogue of `projectionPairCandidate` (`ProjectionPairCandidate.lean`): the second
instance of the uniform Geuvers eliminator-candidate technique catalogued in that file's docstring (§ "the
plan for ALL six residues").  Where Σ uses the PROJECTION frame, the coproduct uses the MATCH frame: the
head-expansion-closed candidate is the eliminator-applied form

    eitherMatchCandidate fc sc term :=
      IsStronglyNormalizing term ∧
        ∀ motive resultCandidate (CarrierObligations resultCandidate) leftBranch rightBranch,
          SN motive → SN leftBranch → SN rightBranch →
            (∀ p, fc p → resultCandidate (app leftBranch p)) →
            (∀ p, sc p → resultCandidate (app rightBranch p)) →
              resultCandidate (eitherMatch motive leftBranch rightBranch term)

It is forward-correct (a reached `inl`/`inr` matches its branch by ι + scrutinee `StepStar` congruence + the
result candidate's CR2-forward, NO expansion, NO Ω-fork — `eitherMatchCandidate_reachableBranchMembers`,
mirroring `projectionPairCandidate_reachableComponentMembers`) AND app-spine `HeadExpansionClosed` VERBATIM.

The candidate is SECOND-ORDER: `resultCandidate` is universally quantified and FIXED across the quantified
motive/branch arguments, so — unlike the dependent arrow candidate — there is NO `convTransfer` step in CR3
(the codomain candidate does not move with the quantified argument).  The reach-vs-content reconciliation that
breaks the carrier-aware reach candidate (NOT head-expansion-closed, `CarrierAwareEitherCandidate.lean`) is
dissolved exactly because the match-frame eliminator form — not the reach form — is the one that lands.

The carrier interface for the result candidate is `CarrierObligations` (reused from `ProjectionPairCandidate`):
a reducibility candidate PLUS member weak-head expansion under any `WeakHeadStep`.  The branch-premise carriers
`firstCandidate`/`secondCandidate` appear only as antecedents in the branch premises (CONTRAVARIANTLY in the
congruence), so they need no obligations.

## Zero-axiom verification

CR1 = `member.1`; CR2 = scrutinee `Step.cong` transport of the result candidate via the FIXED result
obligations; CR3 = a THREE-FOLD nested `Acc StepSuccessor` induction over the motive, left- and right-branch
accessibilities (the coproduct cost over the arrow template's single-argument induction), dispatching the
neutral eliminator cell's reducts by `Step.from_eitherMatch` (the two ι cases refuted by the neutral-vs-`inl`/
`inr` root-generator clash, the four congruence cases threaded through the matching IH / outer member /
branch-premise reproof).  The reach-projection via `StepStar.eitherMatchScrutinee` + the ι +
`closedUnderStepStar`; the head-expansion crux via `WeakHeadStep.scrutineeEitherMatch` + the result obligations'
member weak-head expansion, the cell SN supplied by the reduct-tracking scrutinee-reducing engine whose reach
premise is discharged from the contractum cell's reach-projection across a no-drift weak-head strip
(`WeakHeadStep.commuteWithStep` lifted, closed by `inl`/`inr` weak-head normality).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the
`FX1Poly.Core` namespace sweep in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `eitherMatch` eliminator cell over its four children — Phase-Z spine `(motive, leftBranch, rightBranch,
scrutinee)`, the motive a term under one binder.  Names the raw `mkGen` the inversion / congruence / ι lemmas
are stated against. -/
abbrev eitherMatchSpineCell {scope : Nat} (motive : RawTerm (scope + 1))
    (leftBranch rightBranch scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons motive
      (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))

/-- **The match-frame Girard coproduct candidate.**  A term is reducible at the sum of two branch-premise
carrier candidates when it is strongly normalizing AND, for every motive, result candidate (with its carrier
obligations), and pair of branches whose applications to carrier members land in the result candidate, the
`eitherMatch` cell over the term lands in the result candidate.  The model-viable strengthening: forward-correct
(a reached injection matches its branch) and app-spine head-expansion-closed. -/
def eitherMatchCandidate {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) (term : RawTerm scope) : Prop :=
  IsStronglyNormalizing term ∧
    ∀ (motive : RawTerm (scope + 1)) (resultCandidate : RawTerm scope → Prop)
      (resultObligations : CarrierObligations resultCandidate)
      (leftBranch rightBranch : RawTerm scope),
      IsStronglyNormalizing motive → IsStronglyNormalizing leftBranch → IsStronglyNormalizing rightBranch →
      (∀ payload : RawTerm scope, firstCandidate payload →
          resultCandidate (applicationCell leftBranch payload)) →
      (∀ payload : RawTerm scope, secondCandidate payload →
          resultCandidate (applicationCell rightBranch payload)) →
      resultCandidate (eitherMatchSpineCell motive leftBranch rightBranch term)

/-- **A no-drift weak-head strip to any weak-head-normal target.**  If `source` reduces (multi-step) to a
`target` that admits NO weak-head step, and `source` weak-head-steps to `reduct`, then `reduct` reaches the SAME
`target`.  Stated with a FREE `target` (a variable, so the `StepStar` induction is well-formed — the fixed-injection
specializations below were the non-variable-index trap): the reach chain is non-empty (`source` weak-head-steps but
`target` does not), so its first step either IS the weak-head reduct or commutes with it
(`WeakHeadStep.commuteWithStep`), and the strip recurses with no drift. -/
theorem weakHeadStripToNormal {scope : Nat} {source reduct target : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (reaches : StepStar source target)
    (targetNoWeakHeadStep : ∀ r : RawTerm scope, ¬ WeakHeadStep target r) :
    StepStar reduct target := by
  induction reaches generalizing reduct with
  | refl _ => exact absurd weakHeadStep (targetNoWeakHeadStep reduct)
  | trans firstStep _restChain restInductiveHypothesis =>
      rcases weakHeadStep.commuteWithStep _ firstStep with
        otherEqualsReduct | ⟨otherReduct, otherWeakHeadStep, reductToOtherReduct⟩
      · exact otherEqualsReduct ▸ _restChain
      · exact StepStar.trans_compose reductToOtherReduct
          (restInductiveHypothesis otherWeakHeadStep targetNoWeakHeadStep)

/-- **A no-drift weak-head strip to a reached `inl` injection.**  The injection target admits no weak-head step
(`WeakHeadStep.not_from_eitherInl`), so it is the `weakHeadStripToNormal` instance.  Discharges the
scrutinee-reducing SN engine's reach-keyed contractum-SN obligation under head expansion. -/
theorem weakHeadStripToReachedInl {scope : Nat} {source reduct payload : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (reaches : StepStar source (.mkGen .gen_eitherInl () (.childCons payload .childNil))) :
    StepStar reduct (.mkGen .gen_eitherInl () (.childCons payload .childNil)) :=
  weakHeadStripToNormal weakHeadStep reaches (fun _ => WeakHeadStep.not_from_eitherInl)

/-- **A no-drift weak-head strip to a reached `inr` injection.**  The right-injection twin, closed by
`WeakHeadStep.not_from_eitherInr`. -/
theorem weakHeadStripToReachedInr {scope : Nat} {source reduct payload : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (reaches : StepStar source (.mkGen .gen_eitherInr () (.childCons payload .childNil))) :
    StepStar reduct (.mkGen .gen_eitherInr () (.childCons payload .childNil)) :=
  weakHeadStripToNormal weakHeadStep reaches (fun _ => WeakHeadStep.not_from_eitherInr)

/-- **CR1: a coproduct member is strongly normalizing** — directly the first conjunct. -/
theorem eitherMatchCandidate_stronglyNormalizing {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : eitherMatchCandidate firstCandidate secondCandidate term) :
    IsStronglyNormalizing term :=
  member.1

/-- **CR2 (forward): a coproduct member's reduct is a coproduct member.**  SN forward by accessibility; the
universal part transports the result candidate along the scrutinee congruence step
`eitherMatch … term ↝ eitherMatch … reduct` (`Step.cong … (StepChildren.here …)` at the LAST child) by the
result obligations' own CR2. -/
theorem eitherMatchCandidate_closedUnderStep {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    {term reduct : RawTerm scope}
    (member : eitherMatchCandidate firstCandidate secondCandidate term)
    (step : Step term reduct) :
    eitherMatchCandidate firstCandidate secondCandidate reduct := by
  obtain ⟨termSN, universal⟩ := member
  refine ⟨isStronglyNormalizing_isReducibilityCandidate.closedUnderStep termSN step, ?_⟩
  intro motive resultCandidate resultObligations leftBranch rightBranch
    motiveSN leftBranchSN rightBranchSN leftPremise rightPremise
  have cellMember :
      resultCandidate (eitherMatchSpineCell motive leftBranch rightBranch term) :=
    universal motive resultCandidate resultObligations leftBranch rightBranch
      motiveSN leftBranchSN rightBranchSN leftPremise rightPremise
  exact resultObligations.isCandidate.closedUnderStep cellMember
    (Step.cong .gen_eitherMatch ()
      (StepChildren.there _
        (StepChildren.there _
          (StepChildren.there _ (StepChildren.here _ step)))))

/-- **CR3 (neutral): a neutral term whose every one-step reduct is a coproduct member is a coproduct member.**
SN of the term from the reducts; the universal part proceeds by a THREE-FOLD nested `Acc StepSuccessor`
induction over the motive and both branches.  At the core the eliminator cell `eitherMatch motive l r term` is
neutral (`IsNeutral.eitherMatch`), so the result obligations' CR3 applies: each reduct of the cell is dispatched
by `Step.from_eitherMatch` — the two ι cases force `term` to be `inl`/`inr` (impossible, `term` neutral, refuted
by the root-generator clash), and the four congruence cases thread the matching nested IH (motive / left / right)
or the outer `reductsMembers` (scrutinee), reproving the branch premises for a stepped branch by the result
obligations' own CR2 along the application-head congruence. -/
theorem eitherMatchCandidate_neutralExpansion {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    {term : RawTerm scope}
    (termIsNeutral : IsNeutral term)
    (reductsMembers : ∀ reduct : RawTerm scope, Step term reduct →
      eitherMatchCandidate firstCandidate secondCandidate reduct) :
    eitherMatchCandidate firstCandidate secondCandidate term := by
  have termSN : IsStronglyNormalizing term :=
    Acc.intro term (fun reduct step => (reductsMembers reduct step).1)
  refine ⟨termSN, ?_⟩
  intro motive resultCandidate resultObligations leftBranch rightBranch
    motiveSN leftBranchSN rightBranchSN leftPremise rightPremise
  -- Generalize the motive and both branches over their accessibilities (= strong normalization) so the cell's
  -- congruence reducts (which move ONE of motive / leftBranch / rightBranch) land at the matching smaller
  -- induction hypothesis.  Each focus's reconstructed accessibility (`Acc.intro …`) IS its SN, threaded into the
  -- outer `reductsMembers` universal at the scrutinee-congruence reduct.
  suffices general :
      ∀ {currentMotive : RawTerm (scope + 1)}, IsStronglyNormalizing currentMotive →
        ∀ {currentLeft : RawTerm scope}, IsStronglyNormalizing currentLeft →
          ∀ {currentRight : RawTerm scope}, IsStronglyNormalizing currentRight →
            (∀ payload : RawTerm scope, firstCandidate payload →
                resultCandidate (applicationCell currentLeft payload)) →
            (∀ payload : RawTerm scope, secondCandidate payload →
                resultCandidate (applicationCell currentRight payload)) →
            resultCandidate (eitherMatchSpineCell currentMotive currentLeft currentRight term) from
    general motiveSN leftBranchSN rightBranchSN leftPremise rightPremise
  intro currentMotive motiveAccessible
  induction motiveAccessible with
  | intro motiveFocus motivePredecessors motiveInductiveHypothesis =>
      intro currentLeft leftAccessible
      have motiveFocusSN : IsStronglyNormalizing motiveFocus := Acc.intro motiveFocus motivePredecessors
      induction leftAccessible with
      | intro leftFocus leftPredecessors leftInductiveHypothesis =>
          intro currentRight rightAccessible
          have leftFocusSN : IsStronglyNormalizing leftFocus := Acc.intro leftFocus leftPredecessors
          induction rightAccessible with
          | intro rightFocus rightPredecessors rightInductiveHypothesis =>
              intro leftFocusPremise rightFocusPremise
              have rightFocusSN : IsStronglyNormalizing rightFocus := Acc.intro rightFocus rightPredecessors
              apply resultObligations.isCandidate.neutralExpansion
                (IsNeutral.eitherMatch termIsNeutral)
              intro cellReduct cellStep
              rcases Step.from_eitherMatch cellStep with
                ⟨_value, termIsInl, _⟩ | ⟨_value, termIsInr, _⟩ |
                ⟨motiveAfter, cellReductEq, motiveStep⟩ |
                ⟨leftAfter, cellReductEq, leftStep⟩ |
                ⟨rightAfter, cellReductEq, rightStep⟩ |
                ⟨scrutineeAfter, cellReductEq, scrutineeStep⟩
              · exact absurd
                  (termIsInl ▸ rfl : term.rootGenerator = Generator.gen_eitherInl)
                  (by cases termIsNeutral <;> exact fun shapeEq => Generator.noConfusion shapeEq)
              · exact absurd
                  (termIsInr ▸ rfl : term.rootGenerator = Generator.gen_eitherInr)
                  (by cases termIsNeutral <;> exact fun shapeEq => Generator.noConfusion shapeEq)
              · rw [cellReductEq]
                exact motiveInductiveHypothesis motiveAfter motiveStep
                  leftFocusSN rightFocusSN leftFocusPremise rightFocusPremise
              · rw [cellReductEq]
                have leftAfterPremise : ∀ payload : RawTerm scope, firstCandidate payload →
                    resultCandidate (applicationCell leftAfter payload) := by
                  intro payload payloadMember
                  exact resultObligations.isCandidate.closedUnderStep
                    (leftFocusPremise payload payloadMember)
                    (Step.cong .gen_app () (StepChildren.here _ leftStep))
                exact leftInductiveHypothesis leftAfter leftStep
                  rightFocusSN leftAfterPremise rightFocusPremise
              · rw [cellReductEq]
                have rightAfterPremise : ∀ payload : RawTerm scope, secondCandidate payload →
                    resultCandidate (applicationCell rightAfter payload) := by
                  intro payload payloadMember
                  exact resultObligations.isCandidate.closedUnderStep
                    (rightFocusPremise payload payloadMember)
                    (Step.cong .gen_app () (StepChildren.here _ rightStep))
                exact rightInductiveHypothesis rightAfter rightStep leftFocusPremise rightAfterPremise
              · rw [cellReductEq]
                exact (reductsMembers scrutineeAfter scrutineeStep).2
                  motiveFocus resultCandidate resultObligations leftFocus rightFocus
                  motiveFocusSN leftFocusSN rightFocusSN leftFocusPremise rightFocusPremise

/-- **The match-frame coproduct candidate IS a Girard reducibility candidate** (CR1+CR2+CR3) — the bundle of the
three preceding lemmas.  Needs no obligations on the branch-premise carriers: CR1/CR2/CR3 are all carried by the
result candidate's own obligations threaded through the quantifier (the member weak-head expansion is only needed by
the intro / head-expansion lemmas). -/
theorem eitherMatchCandidate_isReducibilityCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} :
    IsReducibilityCandidate (eitherMatchCandidate firstCandidate secondCandidate) :=
  ⟨fun member => eitherMatchCandidate_stronglyNormalizing member,
   fun member step => eitherMatchCandidate_closedUnderStep member step,
   fun termIsNeutral reductsMembers => eitherMatchCandidate_neutralExpansion termIsNeutral reductsMembers⟩

/-- **The match-frame coproduct candidate is congruent in its carriers** (the model's `assemble_congr` analogue).
The branch-premise carriers appear CONTRAVARIANTLY (as antecedents of the branch premises), so the carrier
`PointwiseIff` is applied in the OPPOSITE direction to the projection candidate's covariant case: forward transport
of the candidate feeds the universal a premise reproved by `.mp`, backward by `.mpr`.  The `deterministic` finisher
needs this without `funext`. -/
theorem eitherMatchCandidate_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (eitherMatchCandidate firstCandidate1 secondCandidate1)
      (eitherMatchCandidate firstCandidate2 secondCandidate2) := by
  intro term
  constructor
  · rintro ⟨termSN, universal⟩
    refine ⟨termSN, ?_⟩
    intro motive resultCandidate resultObligations leftBranch rightBranch
      motiveSN leftBranchSN rightBranchSN leftPremise rightPremise
    exact universal motive resultCandidate resultObligations leftBranch rightBranch
      motiveSN leftBranchSN rightBranchSN
      (fun payload payloadMember => leftPremise payload ((firstIff payload).mp payloadMember))
      (fun payload payloadMember => rightPremise payload ((secondIff payload).mp payloadMember))
  · rintro ⟨termSN, universal⟩
    refine ⟨termSN, ?_⟩
    intro motive resultCandidate resultObligations leftBranch rightBranch
      motiveSN leftBranchSN rightBranchSN leftPremise rightPremise
    exact universal motive resultCandidate resultObligations leftBranch rightBranch
      motiveSN leftBranchSN rightBranchSN
      (fun payload payloadMember => leftPremise payload ((firstIff payload).mpr payloadMember))
      (fun payload payloadMember => rightPremise payload ((secondIff payload).mpr payloadMember))

end FX1Poly.Core
