import FX1Poly.Core.CandidateInterpretation

/-! # Foundation/PolyCell/Core/CandidateInterpretationDeterminism
    — the candidate-environment interpretation is functional (deterministic up to pointwise iff)

`InterpretsType` (`CandidateInterpretation`) is a relation, not a function — that is what lets it
sidestep the propext-leaking generator-dispatch recursion.  The price is that "the interpretation of
a type-code" is only meaningful once the relation is shown to be **functional**: a type-code
interprets to at most one candidate.  Because candidates are predicates, the right notion of
"one candidate" is **pointwise logical equivalence** (`∀ term, candidate₁ term ↔ candidate₂ term`),
which avoids `funext`/`propext` entirely.

The headline `InterpretsType.deterministic` is the reflexive instance of a stronger congruence:
`InterpretsType.pointwiseIff_of_envPointwiseIff` — interpreting one type-code under two
**pointwise-equivalent environments** yields pointwise-equivalent candidates.  That stronger form is
what the Π case needs (the codomain is interpreted under the environment extended by the domain
candidate, so the two extended environments are only equivalent, not equal) and what the upcoming
semantic substitution lemma will consume.

## Zero-axiom verification

Induction on the first interpretation, inverting the second by `cases` at each concrete generator
head (var / piTyCode / other) — propext-clean, as for `ErasesTo`.  Equivalences are threaded through
`isArrowReducible_pointwiseIff` and `pointwiseIffEnv_cons`; no predicate equality, hence no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- Pointwise logical equivalence of two candidate predicates. -/
def PointwiseIff {targetScope : Nat} (candidateA candidateB : RawTerm targetScope → Prop) : Prop :=
  ∀ term : RawTerm targetScope, candidateA term ↔ candidateB term

/-- Pointwise equivalence of two candidate environments — every entry is pointwise-equivalent. -/
def PointwiseIffEnv {scope targetScope : Nat}
    (env1 env2 : CandidateEnv scope targetScope) : Prop :=
  ∀ index : Fin scope, PointwiseIff (env1 index) (env2 index)

/-- A candidate environment is pointwise-equivalent to itself. -/
theorem PointwiseIffEnv.refl {scope targetScope : Nat}
    (env : CandidateEnv scope targetScope) : PointwiseIffEnv env env :=
  fun _index _term => Iff.rfl

/-- The arrow construction respects pointwise equivalence of its domain and codomain candidates. -/
theorem isArrowReducible_pointwiseIff {targetScope : Nat}
    {domain1 domain2 codomain1 codomain2 : RawTerm targetScope → Prop}
    (domainIff : PointwiseIff domain1 domain2)
    (codomainIff : PointwiseIff codomain1 codomain2) :
    PointwiseIff (IsArrowReducible domain1 codomain1) (IsArrowReducible domain2 codomain2) := by
  intro function
  constructor
  · intro arrowReducible1 argument argumentInDomain2
    exact (codomainIff _).mp (arrowReducible1 argument ((domainIff argument).mpr argumentInDomain2))
  · intro arrowReducible2 argument argumentInDomain1
    exact (codomainIff _).mpr (arrowReducible2 argument ((domainIff argument).mp argumentInDomain1))

/-- Consing pointwise-equivalent heads onto pointwise-equivalent tails preserves environment
equivalence. -/
theorem pointwiseIffEnv_cons {scope targetScope : Nat}
    {headCandidate1 headCandidate2 : RawTerm targetScope → Prop}
    {tailEnv1 tailEnv2 : CandidateEnv scope targetScope}
    (headIff : PointwiseIff headCandidate1 headCandidate2)
    (tailIff : PointwiseIffEnv tailEnv1 tailEnv2) :
    PointwiseIffEnv (CandidateEnv.cons headCandidate1 tailEnv1)
      (CandidateEnv.cons headCandidate2 tailEnv2) := by
  intro index
  match index with
  | ⟨0, _⟩ => exact headIff
  | ⟨priorValue + 1, hBound⟩ => exact tailIff ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- **Generalized determinism**: interpreting one type-code under two pointwise-equivalent candidate
environments yields pointwise-equivalent candidates.  Induction on the first interpretation, inverting
the second at each generator head: a type variable reads pointwise-equivalent environment entries, a
Π-code's arrow candidates are equivalent by `isArrowReducible_pointwiseIff` (the codomain environments
stay equivalent by `pointwiseIffEnv_cons` from the domain equivalence), and the SN candidate is
equivalent to itself. -/
theorem InterpretsType.pointwiseIff_of_envPointwiseIff {targetScope scope : Nat}
    {env1 : CandidateEnv scope targetScope} {typeCode : RawTerm scope}
    {candidate1 : RawTerm targetScope → Prop}
    (interpretation1 : InterpretsType env1 typeCode candidate1) :
    ∀ {env2 : CandidateEnv scope targetScope} {candidate2 : RawTerm targetScope → Prop},
      InterpretsType env2 typeCode candidate2 →
      PointwiseIffEnv env1 env2 →
      PointwiseIff candidate1 candidate2 := by
  induction interpretation1 with
  | typeVariable environment1 index =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | typeVariable environment2 index2 => exact envIff index
      | baseType _environment notVariable _notPiType => exact absurd rfl notVariable
  | piType _domainInterp1 _codomainInterp1 domainInductiveHypothesis
      codomainInductiveHypothesis =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | piType domainInterp2 codomainInterp2 =>
          have domainEquivalence := domainInductiveHypothesis domainInterp2 envIff
          exact isArrowReducible_pointwiseIff domainEquivalence
            (codomainInductiveHypothesis codomainInterp2
              (pointwiseIffEnv_cons domainEquivalence envIff))
      | baseType _environment _notVariable notPiType => exact absurd rfl notPiType
  | baseType environment1 notVariable1 notPiType1 =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | typeVariable _environment _index => exact absurd rfl notVariable1
      | piType _domainInterp2 _codomainInterp2 => exact absurd rfl notPiType1
      | baseType _environment _notVariable _notPiType => intro _term; exact Iff.rfl

/-- **Determinism**: a type-code interprets to at most one candidate (up to pointwise equivalence)
under a fixed environment.  The reflexive instance of `pointwiseIff_of_envPointwiseIff`. -/
theorem InterpretsType.deterministic {targetScope scope : Nat}
    {env : CandidateEnv scope targetScope} {typeCode : RawTerm scope}
    {candidate1 candidate2 : RawTerm targetScope → Prop}
    (interpretation1 : InterpretsType env typeCode candidate1)
    (interpretation2 : InterpretsType env typeCode candidate2) :
    PointwiseIff candidate1 candidate2 :=
  interpretation1.pointwiseIff_of_envPointwiseIff interpretation2 (PointwiseIffEnv.refl env)

end FX1Poly.Core
