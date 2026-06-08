import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch: member-level CR2 (forward closure) for the denote relation — UNCONDITIONAL (only the lowerForwardStep
leg, never the bounded neutralInclusion). Every denote-reducible type's candidate is forward-closed under Step. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem ReducibleTypeStepDenote.memberForwardClosed {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerForwardStep : ∀ (lvl : Nat) {typeCode reduct : RawTerm scope}
        {candidate : RawTerm scope → Prop},
      lowerAt lvl typeCode candidate → Step typeCode reduct → lowerAt lvl reduct candidate)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {term reduct : RawTerm scope}, candidate term → Step term reduct → candidate reduct := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse =>
      intro term reduct memberStronglyNormalizing step
      exact isStronglyNormalizing_isReducibilityCandidate.closedUnderStep memberStronglyNormalizing step
  | @piType domainCode codomainCode domainCandidate codomainCandidate _domainReducible
      _codomainReducible _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro function functionAfter functionMember functionStep argument argumentInDomain
      exact codomainInductiveHypothesis argument argumentInDomain
        (functionMember argument argumentInDomain)
        (Step.cong .gen_app ()
          (StepChildren.here (.childCons argument .childNil : RawTermChildren [0] scope) functionStep))
  | universeCode levelExpr _flag =>
      intro term reduct member step
      exact ⟨isStronglyNormalizing_isReducibilityCandidate.closedUnderStep member.1 step,
        match member.2 with
        | ⟨lowerCandidate, lowerMember⟩ =>
            ⟨lowerCandidate, lowerForwardStep (LevelExpr.denote levelExpr env) lowerMember step⟩⟩
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro term reduct member step
      exact (pointwiseIff reduct).mp
        (innerInductiveHypothesis ((pointwiseIff term).mpr member) step)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.memberForwardClosed
