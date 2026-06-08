import FX1Poly.Core.StratifiedReducibleTypeHeadExpansion
import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch SN-D1: port the spine-general head-expansion closure from the fuel/stratified relation
(`ReducibleTypeStep.headExpansionClosed`) onto the denote relation `ReducibleTypeStepDenote`. 5-arm induction,
verbatim structure; only the universe arm's `lowerHeadExpand` leg is keyed to `LevelExpr.denote levelExpr env`.
The unconditional corollary discharges the leg via the shipped `denoteBelowFamily_backwardWeakHeadStep` +
`WeakHeadStep.betaSpine`. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem ReducibleTypeStepDenote.headExpansionClosed {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerHeadExpand : ∀ (lvl : Nat) {body : RawTerm (scope + 1)} {argument : RawTerm scope}
      {spine : List (RawTerm scope)} {lowerCandidate : RawTerm scope → Prop},
      lowerAt lvl (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) lowerCandidate →
      lowerAt lvl (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine) lowerCandidate)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    HeadExpansionClosed candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse =>
      exact isStronglyNormalizing_headExpansionClosed
  | @piType _domainCode _codomainCode _domainCandidate codomainCandidate _domainReducible
      _codomainReducible _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro body argument spine argumentSN contractumReducible extraArgument extraArgumentReducible
      have contractumAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp (RawTerm.subst0 body argument) (spine ++ [extraArgument])) := by
        rw [applySpineApp_append]
        exact contractumReducible extraArgument extraArgumentReducible
      have redexAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp
              (.mkGen .gen_app ()
                (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
                  (.childCons argument .childNil)))
              (spine ++ [extraArgument])) :=
        (codomainInductiveHypothesis extraArgument extraArgumentReducible)
          argumentSN contractumAtExtendedSpine
      rw [applySpineApp_append] at redexAtExtendedSpine
      exact redexAtExtendedSpine
  | universeCode levelExpr _flag =>
      intro _body _argument _spine argumentSN contractumMember
      obtain ⟨contractumStronglyNormalizing, lowerCandidate, lowerContractum⟩ := contractumMember
      exact ⟨betaSpineHeadExpansion argumentSN contractumStronglyNormalizing,
        lowerCandidate, lowerHeadExpand (LevelExpr.denote levelExpr env) lowerContractum⟩
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis.respectsPointwiseIff (fun term => pointwiseIff term)

theorem ReducibleTypeAtDenote.headExpansionClosed {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtDenote env level typeCode candidate) :
    HeadExpansionClosed candidate := by
  refine ReducibleTypeStepDenote.headExpansionClosed ?leg reducible
  intro lvl _body _argument _spine _lowerCandidate contractumMember
  exact denoteBelowFamily_backwardWeakHeadStep env level lvl contractumMember WeakHeadStep.betaSpine

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.headExpansionClosed
#print axioms FX1Poly.Typed.ReducibleTypeAtDenote.headExpansionClosed
