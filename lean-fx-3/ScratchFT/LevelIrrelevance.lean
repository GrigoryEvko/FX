import FX1Poly.Core.StratifiedReducibleType
import FX1Poly.Core.StratifiedReducibleMember

/-! # ScratchFT/LevelIrrelevance — the master unlock: stratified reducibility is level-irrelevant (WIP) -/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Candidate-congruence of the reducibility step-functor under lower-existence-equivalence.**  If two
lower relations assign reducibility to the SAME type-codes (existence-equivalent), then `ReducibleTypeStep`
over them assigns POINTWISE-EQUAL candidates.  The Π case closes choice-free via the `ofPointwiseIff` arm:
each per-argument codomain candidate is transported back to the original by its induction hypothesis's
equivalence.  The universe case's candidate equality is exactly the lower-existence-equivalence. -/
theorem ReducibleTypeStep.existsCongr {scope : Nat}
    {lower lower' : RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerEquiv : ∀ subType : RawTerm scope, (∃ c, lower subType c) ↔ (∃ c, lower' subType c))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lower typeCode candidate) :
    ∃ candidate' : RawTerm scope → Prop,
      ReducibleTypeStep lower' typeCode candidate' ∧ (∀ term, candidate' term ↔ candidate term) := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible reductInductiveHypothesis =>
      obtain ⟨candidate', reducible', equivalence'⟩ := reductInductiveHypothesis
      exact ⟨candidate', .whnfExpand weakHeadStep reducible', equivalence'⟩
  | neutral noWeakHeadStep notPiType notUniverse =>
      exact ⟨IsStronglyNormalizing, .neutral noWeakHeadStep notPiType notUniverse, fun _ => Iff.rfl⟩
  | @piType domainCode codomainCode domainCandidate codomainCandidate _domainReducible _codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      obtain ⟨domainCandidate', domainReducible', domainEquivalence⟩ := domainInductiveHypothesis
      refine ⟨fun functionTerm => ∀ argument : RawTerm scope, domainCandidate' argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))),
        ReducibleTypeStep.piType codomainCandidate domainReducible' ?_, ?_⟩
      · intro argument argumentInDomain'
        have argumentInDomain : domainCandidate argument := (domainEquivalence argument).mp argumentInDomain'
        obtain ⟨codCandArg, codReducibleArg, codEquivArg⟩ :=
          codomainInductiveHypothesis argument argumentInDomain
        exact ReducibleTypeStep.ofPointwiseIff codReducibleArg (fun term => (codEquivArg term))
      · intro functionTerm
        constructor
        · intro membership argument argumentInDomain
          exact membership argument ((domainEquivalence argument).mpr argumentInDomain)
        · intro membership argument argumentInDomain'
          exact membership argument ((domainEquivalence argument).mp argumentInDomain')
  | universeCode levelExpr flag =>
      refine ⟨universeReducibilityPredicate lower', .universeCode levelExpr flag, ?_⟩
      intro term
      show (IsStronglyNormalizing term ∧ ∃ c, lower' term c) ↔ (IsStronglyNormalizing term ∧ ∃ c, lower term c)
      exact and_congr_right (fun _ => (lowerEquiv term).symm)
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      obtain ⟨candidate', reducible', equivalence'⟩ := innerInductiveHypothesis
      exact ⟨candidate', reducible', fun term => (equivalence' term).trans (pointwiseIff term)⟩

end FX1Poly.Core
