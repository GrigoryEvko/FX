import LeanFX2.Foundation.PolyCell.Core.StepEtaCriticalPairs

/-! # Foundation/PolyCell/Core/StepEtaEtaCriticalPairs

Eta-vs-eta local joins for the current root-only eta relation.

The task text lists nested eta examples, but the current formal relation is
deliberately root-only: `Step.eta` has no congruence constructor.  Therefore
eta/eta one-step branchings can only happen when two root eta constructors
match the same source term.  This file proves that the current root eta
relation is deterministic and uses that to close the eta/eta quadrant of the
betaEta local Church-Rosser theorem.
-/

namespace LeanFX2.Foundation.PolyCell.Core

namespace RawTerm

/-- Lambda eta sources are injective in the represented function. -/
theorem etaLamSource_injective {scope : Nat}
    {firstFunction secondFunction : RawTerm scope}
    (sourceEq :
      RawTerm.etaLamSource firstFunction =
        RawTerm.etaLamSource secondFunction) :
    firstFunction = secondFunction := by
  unfold RawTerm.etaLamSource at sourceEq
  injection sourceEq with _ _ _ lamChildrenEq
  injection lamChildrenEq with _ _ _ appEq _
  injection appEq with _ _ _ appChildrenEq
  injection appChildrenEq with _ _ _ weakenedEq _
  have strengthenedEq : some firstFunction = some secondFunction := by
    rw [← RawTerm.strengthen_weaken firstFunction]
    rw [weakenedEq]
    rw [RawTerm.strengthen_weaken secondFunction]
  injection strengthenedEq

/-- Pair eta sources are injective in the represented pair term. -/
theorem etaPairSource_injective {scope : Nat}
    {firstPair secondPair : RawTerm scope}
    (sourceEq :
      RawTerm.etaPairSource firstPair =
        RawTerm.etaPairSource secondPair) :
    firstPair = secondPair := by
  unfold RawTerm.etaPairSource at sourceEq
  injection sourceEq with _ _ _ pairChildrenEq
  injection pairChildrenEq with _ _ _ firstProjectionEq _
  injection firstProjectionEq with _ _ _ projectionChildrenEq
  injection projectionChildrenEq with _ _ _ pairEq _

/-- Path eta sources are injective in the represented path term. -/
theorem etaPathLamSource_injective {scope : Nat}
    {firstPath secondPath : RawTerm scope}
    (sourceEq :
      RawTerm.etaPathLamSource firstPath =
        RawTerm.etaPathLamSource secondPath) :
    firstPath = secondPath := by
  unfold RawTerm.etaPathLamSource at sourceEq
  injection sourceEq with _ _ _ lamChildrenEq
  injection lamChildrenEq with _ _ _ appEq _
  injection appEq with _ _ _ appChildrenEq
  injection appChildrenEq with _ _ _ weakenedEq _
  have strengthenedEq : some firstPath = some secondPath := by
    rw [← RawTerm.strengthen_weaken firstPath]
    rw [weakenedEq]
    rw [RawTerm.strengthen_weaken secondPath]
  injection strengthenedEq

/-- Modal eta sources are injective in the represented modal term. -/
theorem etaModIntroSource_injective {scope : Nat}
    {firstModal secondModal : RawTerm scope}
    (sourceEq :
      RawTerm.etaModIntroSource firstModal =
        RawTerm.etaModIntroSource secondModal) :
    firstModal = secondModal := by
  unfold RawTerm.etaModIntroSource at sourceEq
  injection sourceEq with _ _ _ introChildrenEq
  injection introChildrenEq with _ _ _ elimEq _
  injection elimEq with _ _ _ elimChildrenEq
  injection elimChildrenEq with _ _ _ modalEq _

/-- Glue eta sources are injective in the represented glued term. -/
theorem etaGlueIntroSource_injective {scope : Nat}
    {firstGlue secondGlue : RawTerm scope}
    (sourceEq :
      RawTerm.etaGlueIntroSource firstGlue =
        RawTerm.etaGlueIntroSource secondGlue) :
    firstGlue = secondGlue := by
  unfold RawTerm.etaGlueIntroSource at sourceEq
  injection sourceEq with _ _ _ introChildrenEq
  injection introChildrenEq with _ _ _ _ tailEq
  injection tailEq with _ _ _ glueEq _

end RawTerm

namespace Step.eta

/-- Any eta step from a lambda eta source targets that source's represented
function. -/
theorem from_etaLamSource {scope : Nat}
    {innerFunction rightReduct : RawTerm scope}
    (rightStep :
      Step.eta (RawTerm.etaLamSource innerFunction) rightReduct) :
    rightReduct = innerFunction := by
  generalize sourceEq :
    RawTerm.etaLamSource innerFunction = sourceTerm at rightStep
  cases rightStep with
  | etaLam =>
      exact (RawTerm.etaLamSource_injective sourceEq).symm
  | etaPair =>
      cases sourceEq
  | etaPathLam =>
      cases sourceEq
  | etaModIntro =>
      cases sourceEq
  | etaGlueIntro =>
      cases sourceEq

/-- Any eta step from a pair eta source targets that source's represented
pair term. -/
theorem from_etaPairSource {scope : Nat}
    {pairTerm rightReduct : RawTerm scope}
    (rightStep : Step.eta (RawTerm.etaPairSource pairTerm) rightReduct) :
    rightReduct = pairTerm := by
  generalize sourceEq :
    RawTerm.etaPairSource pairTerm = sourceTerm at rightStep
  cases rightStep with
  | etaLam =>
      cases sourceEq
  | etaPair =>
      exact (RawTerm.etaPairSource_injective sourceEq).symm
  | etaPathLam =>
      cases sourceEq
  | etaModIntro =>
      cases sourceEq
  | etaGlueIntro =>
      cases sourceEq

/-- Any eta step from a path eta source targets that source's represented
path term. -/
theorem from_etaPathLamSource {scope : Nat}
    {innerPath rightReduct : RawTerm scope}
    (rightStep :
      Step.eta (RawTerm.etaPathLamSource innerPath) rightReduct) :
    rightReduct = innerPath := by
  generalize sourceEq :
    RawTerm.etaPathLamSource innerPath = sourceTerm at rightStep
  cases rightStep with
  | etaLam =>
      cases sourceEq
  | etaPair =>
      cases sourceEq
  | etaPathLam =>
      exact (RawTerm.etaPathLamSource_injective sourceEq).symm
  | etaModIntro =>
      cases sourceEq
  | etaGlueIntro =>
      cases sourceEq

/-- Any eta step from a modal eta source targets that source's represented
modal term. -/
theorem from_etaModIntroSource {scope : Nat}
    {modalTerm rightReduct : RawTerm scope}
    (rightStep :
      Step.eta (RawTerm.etaModIntroSource modalTerm) rightReduct) :
    rightReduct = modalTerm := by
  generalize sourceEq :
    RawTerm.etaModIntroSource modalTerm = sourceTerm at rightStep
  cases rightStep with
  | etaLam =>
      cases sourceEq
  | etaPair =>
      cases sourceEq
  | etaPathLam =>
      cases sourceEq
  | etaModIntro =>
      exact (RawTerm.etaModIntroSource_injective sourceEq).symm
  | etaGlueIntro =>
      cases sourceEq

/-- Any eta step from a Glue eta source targets that source's represented
glued term. -/
theorem from_etaGlueIntroSource {scope : Nat}
    {gluedTerm rightReduct : RawTerm scope}
    (rightStep :
      Step.eta (RawTerm.etaGlueIntroSource gluedTerm) rightReduct) :
    rightReduct = gluedTerm := by
  generalize sourceEq :
    RawTerm.etaGlueIntroSource gluedTerm = sourceTerm at rightStep
  cases rightStep with
  | etaLam =>
      cases sourceEq
  | etaPair =>
      cases sourceEq
  | etaPathLam =>
      cases sourceEq
  | etaModIntro =>
      cases sourceEq
  | etaGlueIntro =>
      exact (RawTerm.etaGlueIntroSource_injective sourceEq).symm

/-- Root eta is deterministic in the current calculus.  There is no eta
congruence constructor, so two eta steps from the same source must contract
the same root eta redex. -/
theorem deterministic {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step.eta sourceTerm leftReduct)
    (rightStep : Step.eta sourceTerm rightReduct) :
    leftReduct = rightReduct := by
  cases leftStep with
  | etaLam innerFunction =>
      exact (from_etaLamSource rightStep).symm
  | etaPair pairTerm =>
      exact (from_etaPairSource rightStep).symm
  | etaPathLam innerPath =>
      exact (from_etaPathLamSource rightStep).symm
  | etaModIntro modalTerm =>
      exact (from_etaModIntroSource rightStep).symm
  | etaGlueIntro gluedTerm =>
      exact (from_etaGlueIntroSource rightStep).symm

end Step.eta

/-- Eta-vs-eta local Church-Rosser statement for the root-only eta
relation. -/
def CdLemmaStatementEtaEta : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    (leftStep : Step.eta sourceTerm leftReduct) →
    (rightStep : Step.eta sourceTerm rightReduct) →
    BetaEtaPairJoin (Or.inr leftStep) (Or.inr rightStep)

namespace BetaEtaPairJoin

/-- Eta-vs-eta local joins close by deterministic same-reduct equality. -/
theorem cd_lemma_eta_eta : CdLemmaStatementEtaEta := by
  intro scope sourceTerm leftReduct rightReduct leftStep rightStep
  apply ofReductsEqual
  exact Step.eta.deterministic leftStep rightStep

/-- Full local Church-Rosser dispatcher for the current beta+iota+root-eta
single-step relation. -/
theorem cd_lemma_betaEta : CdLemmaStatementBetaEta := by
  intro scope sourceTerm leftReduct rightReduct leftStep rightStep
  cases leftStep with
  | inl leftStepOnly =>
      cases rightStep with
      | inl rightStepOnly =>
          exact ofCdLemmaForStepSteps leftStepOnly rightStepOnly
      | inr rightEtaOnly =>
          exact cd_lemma_step_eta leftStepOnly rightEtaOnly
  | inr leftEtaOnly =>
      cases rightStep with
      | inl rightStepOnly =>
          exact cd_lemma_eta_step leftEtaOnly rightStepOnly
      | inr rightEtaOnly =>
          exact cd_lemma_eta_eta leftEtaOnly rightEtaOnly

end BetaEtaPairJoin

end LeanFX2.Foundation.PolyCell.Core
