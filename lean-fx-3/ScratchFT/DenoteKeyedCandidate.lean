import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Core.StratifiedReducibleTypeReducibilityCandidate

/-! Scratch: the arrow CR + parametric isReducibilityCandidate for the denote-keyed relation.
Verbatim ports of isDependentArrowReducibleStep_isReducibilityCandidate / ReducibleTypeStep.isReducibilityCandidate,
with ReducibleTypeStep.convTransfer → ReducibleTypeStepDenote.convTransfer, and the universe arm reusing the
fuel universeCandidateIsReducibilityCandidate via the defeq
universeDenotePredicate env lowerAt levelExpr = universeReducibilityPredicate (lowerAt (denote levelExpr env)).
The interface legs are now per-level (∀ lvl) since the universe arm decodes at denote levelExpr env. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- The dependent-arrow construction is a reducibility candidate (denote-keyed). Verbatim port; CR3's
argument-reduction case uses ReducibleTypeStepDenote.convTransfer. -/
theorem isDependentArrowReducibleStepDenote_isReducibilityCandidate {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {domainPredicate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : IsReducibilityCandidate domainPredicate)
    (codomainCandidateHood : ∀ argument : RawTerm scope, domainPredicate argument →
      IsReducibilityCandidate (codomainCandidate argument))
    (codomainReducible : ∀ argument : RawTerm scope, domainPredicate argument →
      ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    (reducibleWitness : RawTerm scope)
    (witnessReducible : domainPredicate reducibleWitness) :
    IsReducibilityCandidate (IsDependentArrowReducible domainPredicate codomainCandidate) := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro function functionArrowReducible
    have applicationReducible :
        codomainCandidate reducibleWitness
          (.mkGen .gen_app ()
            (.childCons function (.childCons reducibleWitness .childNil))) :=
      functionArrowReducible reducibleWitness witnessReducible
    exact appHead_isStronglyNormalizing_of_app
      ((codomainCandidateHood reducibleWitness witnessReducible).stronglyNormalizing
        applicationReducible)
  case closedUnderStep =>
    intro function functionAfter functionArrowReducible functionStep argument argumentReducible
    have applicationStep :
        Step
          (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
          (.mkGen .gen_app () (.childCons functionAfter (.childCons argument .childNil))) :=
      Step.cong .gen_app ()
        (StepChildren.here
          (.childCons argument .childNil : RawTermChildren [0] scope)
          functionStep)
    exact (codomainCandidateHood argument argumentReducible).closedUnderStep
      (functionArrowReducible argument argumentReducible) applicationStep
  case neutralExpansion =>
    intro function functionIsNeutral reductsArrowReducible
    suffices general :
        ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
          domainPredicate currentArgument →
            codomainCandidate currentArgument
              (.mkGen .gen_app ()
                (.childCons function (.childCons currentArgument .childNil))) from
      fun argument argumentReducible =>
        general (domainCandidate.stronglyNormalizing argumentReducible) argumentReducible
    intro currentArgument argumentAccessible
    induction argumentAccessible with
    | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
        intro argumentFocusReducible
        refine (codomainCandidateHood argumentFocus argumentFocusReducible).neutralExpansion
          (IsNeutral.app functionIsNeutral) ?_
        intro reduct reductionStep
        rcases Step.from_app reductionStep with
          ⟨_body, functionEqualsLam, _targetEq⟩ |
          ⟨functionAfter, reductEquals, functionStep⟩ |
          ⟨argumentAfter, reductEquals, argumentStep⟩
        · exact (IsNeutral.not_lam (functionEqualsLam ▸ functionIsNeutral)).elim
        · rw [reductEquals]
          exact reductsArrowReducible functionAfter functionStep
            argumentFocus argumentFocusReducible
        · rw [reductEquals]
          have argumentAfterReducible :=
            domainCandidate.closedUnderStep argumentFocusReducible argumentStep
          exact ReducibleTypeStepDenote.convTransfer
            (codomainReducible argumentAfter argumentAfterReducible)
            (codomainReducible argumentFocus argumentFocusReducible)
            ⟨_, StepStar.refl _, Step.subst0Argument codomainCode argumentStep⟩
            (argumentInductiveHypothesis argumentAfter argumentStep argumentAfterReducible)

/-- Every denote-keyed reducibility candidate is a Girard reducibility candidate (parametric). The universe
arm reuses the fuel universeCandidateIsReducibilityCandidate at the decoded level via defeq; interface legs
are per-level. -/
theorem ReducibleTypeStepDenote.isReducibilityCandidate {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm (scope + 1) → (RawTerm (scope + 1) → Prop) → Prop}
    (lowerForwardStep : ∀ (lvl : Nat) {typeCode reduct : RawTerm (scope + 1)}
        {candidate : RawTerm (scope + 1) → Prop},
      lowerAt lvl typeCode candidate → Step typeCode reduct → lowerAt lvl reduct candidate)
    (lowerNeutralInclusion : ∀ (lvl : Nat) {typeCode : RawTerm (scope + 1)}, IsNeutral typeCode →
      (∀ reduct : RawTerm (scope + 1), Step typeCode reduct →
        ∃ candidate : RawTerm (scope + 1) → Prop, lowerAt lvl reduct candidate) →
      ∃ candidate : RawTerm (scope + 1) → Prop, lowerAt lvl typeCode candidate)
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    IsReducibilityCandidate candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse =>
      exact isStronglyNormalizing_isReducibilityCandidate
  | piType codomainCandidate _domainReducible codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      exact isDependentArrowReducibleStepDenote_isReducibilityCandidate
        domainInductiveHypothesis codomainInductiveHypothesis codomainReducible
        (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
        (domainInductiveHypothesis.containsVariable ⟨0, Nat.succ_pos scope⟩)
  | universeCode levelExpr _flag =>
      exact ReducibleTypeStep.universeCandidateIsReducibilityCandidate
        (lowerForwardStep (LevelExpr.denote levelExpr env))
        (lowerNeutralInclusion (LevelExpr.denote levelExpr env))
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis.respectsPointwiseIff (fun term => pointwiseIff term)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.isDependentArrowReducibleStepDenote_isReducibilityCandidate
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.isReducibilityCandidate
