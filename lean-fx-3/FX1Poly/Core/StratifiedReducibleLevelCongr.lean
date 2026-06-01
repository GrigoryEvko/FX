import FX1Poly.Core.StratifiedReducibleType
import FX1Poly.Core.StratifiedReducibleMember

/-! # FX1Poly/Core/StratifiedReducibleLevelCongr
    — candidate-congruence of the stratified reducibility step-functor under lower-existence-equivalence

The stratified reducibility relation `ReducibleTypeAt` recurses on a `Nat` fuel level (level `0` over the
empty lower relation, level `n+1` over `ReducibleTypeAt n` — `StratifiedReducibleType.lean`).  The dependent
fundamental theorem's binder arms (piIntro / genFormation) would close trivially if this relation were
LEVEL-IRRELEVANT (a reducible type / member at one positive level is one at every positive level), because
then the `var` arm's conclusion level and the binder-deposited level could be reconciled freely.

This file ships the INDUCTIVE STEP of any such level argument: `ReducibleTypeStep.existsCongr`.  Given two
lower relations that agree on EXISTENCE (`∃ candidate, lower _ candidate`), the step-functor over them assigns
POINTWISE-EQUAL candidates to every type-code.  The proof is an induction on the `ReducibleTypeStep` derivation
whose only non-obvious case is the dependent arrow: each per-argument codomain candidate is transported back to
the original by its induction hypothesis's equivalence through the `ofPointwiseIff` arm — choice-free, no
canonical-candidate construction.  The universe case's candidate equality is exactly the lower-existence
equivalence (`universeReducibilityPredicate` conjoins strong normalization with lower-existence).

## What this does and does NOT yet give (honest scope)

`existsCongr` is the inductive STEP `(IsReducibleTypeAt L ≡ IsReducibleTypeAt L') → (candidates at L+1 ≡
candidates at L'+1)`.  It does NOT by itself bootstrap full level-irrelevance, because the chain bottoms out at
a DEGENERATE base: at level `0` the lower relation is `fun _ _ => False`, so the universe candidate
`universeReducibilityPredicate (fun _ _ => False)` is empty — `IsReducibleTypeAt 0 (Type@k)` exists but with an
empty candidate, NOT existence-equivalent to `IsReducibleTypeAt 0`'s lower (`False`).  So the bidirectional
hypothesis `existsCongr` needs (`∀ S, (∃c, lower S c) ↔ (∃c, lower' S c)`) is unavailable at the `0 ↔ 1`
boundary, and monotonicity in EITHER single direction also fails (the universe arm forces forward
candidate-containment while the Π arm forces reverse — only the bidirectional `PointwiseIff` satisfies both).
Bootstrapping past the degenerate base is the open obstruction — it likely requires a well-formedness
restriction on `S` (the equivalence holds for well-typed types, where level 0's vacuous-codomain permissiveness
coincides with the higher levels) or a non-fuel reformulation of the relation.  `existsCongr` is nonetheless
the reusable hard core: any future irrelevance / monotonicity result threads it as its inductive step.

## Zero-axiom verification

Induction on `ReducibleTypeStep`; the Π case rebuilds via the `piType` + `ofPointwiseIff` arms, the universe
case via `and_congr_right` on the lower-existence equivalence, the others by reconstruction.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Candidate-congruence of the reducibility step-functor under lower-existence-equivalence.**  If two lower
relations assign reducibility to the SAME type-codes (existence-equivalent), then `ReducibleTypeStep` over them
assigns POINTWISE-EQUAL candidates.  The Π case closes choice-free via `ofPointwiseIff`; the universe case's
candidate equality is the lower-existence equivalence.  The inductive step of level-irrelevance (see the module
docstring for the degenerate-base obstruction to bootstrapping it). -/
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
        exact ReducibleTypeStep.ofPointwiseIff codReducibleArg (fun term => codEquivArg term)
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
