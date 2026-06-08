import FX1Poly.Core.BetaRedexStrongNormalization
import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch: the member weak-head expansion induction over ReducibleTypeStepDenote, GENERAL form
(WeakHeadStep source reduct + SN source), isolating the Π arm as an explicit hypothesis (the
ofReducibleTypeStepDenote pattern). Neutral = SN source (trivial); universe = backward leg; whnf/ofPointwiseIff
= IH. The lambda FT arm instantiates with source = app (lam body) arg + SN source via
appLam_isStronglyNormalizing_of_contractum. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem ReducibleTypeStepDenote.memberWeakHeadExpansionModuloPi {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerBackwardWeakHeadStep : ∀ (lvl : Nat) {typeCode reduct : RawTerm scope}
        {candidate : RawTerm scope → Prop},
      lowerAt lvl reduct candidate → WeakHeadStep typeCode reduct → lowerAt lvl typeCode candidate)
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        (∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
          domainCandidate reduct → domainCandidate source) →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
            codomainCandidate argument reduct → codomainCandidate argument source) →
        ∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
          (∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons reduct (.childCons argument .childNil)))) →
          ∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons source (.childCons argument .childNil))))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {source reduct : RawTerm scope}, WeakHeadStep source reduct → IsStronglyNormalizing source →
      candidate reduct → candidate source := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse =>
      intro source _reduct _whStep sourceStronglyNormalizing _member
      exact sourceStronglyNormalizing
  | @piType domainCode codomainCode domainCandidate codomainCandidate _domainReducible
      _codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      intro source reduct whStep sourceStronglyNormalizing member
      exact piArm codomainCandidate _domainReducible _codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis whStep sourceStronglyNormalizing member
  | universeCode levelExpr _flag =>
      intro source reduct whStep sourceStronglyNormalizing member
      exact ⟨sourceStronglyNormalizing,
        match member.2 with
        | ⟨lowerCandidate, lowerMember⟩ =>
            ⟨lowerCandidate, lowerBackwardWeakHeadStep (LevelExpr.denote levelExpr env) lowerMember whStep⟩⟩
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro source reduct whStep sourceStronglyNormalizing member
      exact (pointwiseIff source).mp
        (innerInductiveHypothesis whStep sourceStronglyNormalizing ((pointwiseIff reduct).mpr member))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.memberWeakHeadExpansionModuloPi
