import FX1Poly.Core.WhnfInterpretation
import FX1Poly.Core.CandidateInterpretationDeterminism

/-! # Foundation/PolyCell/Core/WhnfInterpretationDeterminism
    — the weak-head interpretation is functional (deterministic up to pointwise iff)

`InterpretsWhnf` (`WhnfInterpretation`) is a relation; "the interpretation of a type-code" is only
meaningful once it is shown FUNCTIONAL — a type-code interprets to at most one candidate (up to
pointwise logical equivalence, the funext-free notion reused from
`CandidateInterpretationDeterminism`).

The proof is the payoff of the weak-head design.  Inverting the second derivation, the five arms are
mutually exclusive on a fixed code by the partition (head generator, has-weak-head-step):

  * a `gen_var` head forces `typeVariable`;
  * a `gen_piTyCode` head forces `piType`;
  * any other NON-`gen_app` head forces `baseNormal`;
  * a `gen_app` head with no step forces `neutralApp`, with a step forces `headExpand`.

`HeadStep.subjectRootIsApp` (a weak-head step only fires on an application head) discharges the
cross-arm impossibilities, and `HeadStep.deterministic` equates the two reducts in the
`headExpand`/`headExpand` case — NO confluence needed, the whole reason the relation dispatches on
weak-head reduction rather than an arbitrary `StepStar` closure.

## Zero-axiom verification

Induction on the first interpretation, inverting the second by `cases`; concrete-non-application heads
close their stray `headExpand` by `cases` on the impossible `HeadStep` (the `not_from_lam` pattern),
free heads by `subjectRootIsApp` against the stored `≠ gen_app` / `no step` hypotheses.  Equivalences
threaded through `isArrowReducible_pointwiseIff` / `pointwiseIffEnv_cons`; no predicate equality, hence
no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- A weak-head step only fires on an application-headed term: both `HeadStep` constructors conclude a
`gen_app`-rooted subject. -/
theorem HeadStep.subjectRootIsApp {scope : Nat} {term reduct : RawTerm scope}
    (headStep : HeadStep term reduct) : term.rootGenerator = Generator.gen_app := by
  cases headStep with
  | beta => rfl
  | appCongruence _functionStep => rfl

/-- **Generalized determinism**: interpreting one type-code under two pointwise-equivalent candidate
environments yields pointwise-equivalent candidates.  The stronger form the Π case needs (the codomain
is interpreted under the environment extended by the domain candidate) and the upcoming substitution
lemma will consume. -/
theorem InterpretsWhnf.pointwiseIff_of_envPointwiseIff {targetScope scope : Nat}
    {env1 : CandidateEnv scope targetScope} {typeCode : RawTerm scope}
    {candidate1 : RawTerm targetScope → Prop}
    (interpretation1 : InterpretsWhnf env1 typeCode candidate1) :
    ∀ {env2 : CandidateEnv scope targetScope} {candidate2 : RawTerm targetScope → Prop},
      InterpretsWhnf env2 typeCode candidate2 →
      PointwiseIffEnv env1 env2 →
      PointwiseIff candidate1 candidate2 := by
  induction interpretation1 with
  | typeVariable environment1 index =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | typeVariable environment2 index2 => exact envIff index
      | baseNormal _environment notVariable _notPiType _notApp => exact absurd rfl notVariable
      | headExpand headStep _reductInterprets => cases headStep
  | piType _domainInterp1 _codomainInterp1 domainInductiveHypothesis codomainInductiveHypothesis =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | piType domainInterp2 codomainInterp2 =>
          have domainEquivalence := domainInductiveHypothesis domainInterp2 envIff
          exact isArrowReducible_pointwiseIff domainEquivalence
            (codomainInductiveHypothesis codomainInterp2
              (pointwiseIffEnv_cons domainEquivalence envIff))
      | baseNormal _environment _notVariable notPiType _notApp => exact absurd rfl notPiType
      | headExpand headStep _reductInterprets => cases headStep
  | baseNormal environment1 notVariable1 notPiType1 notApp1 =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | typeVariable _environment _index => exact absurd rfl notVariable1
      | piType _domainInterp2 _codomainInterp2 => exact absurd rfl notPiType1
      | baseNormal _environment _notVariable _notPiType _notApp => intro _term; exact Iff.rfl
      | neutralApp _environment _noHeadStep => exact absurd rfl notApp1
      | headExpand headStep _reductInterprets =>
          exact absurd (HeadStep.subjectRootIsApp headStep) notApp1
  | neutralApp environment1 noHeadStep1 =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | baseNormal _environment _notVariable _notPiType notApp => exact absurd rfl notApp
      | neutralApp _environment _noHeadStep => intro _term; exact Iff.rfl
      | headExpand headStep _reductInterprets => exact absurd headStep (noHeadStep1 _)
  | headExpand headStep1 _reductInterprets1 reductInductiveHypothesis =>
      intro env2 candidate2 interpretation2 envIff
      cases interpretation2 with
      | typeVariable _environment _index => cases headStep1
      | piType _domainInterp2 _codomainInterp2 => cases headStep1
      | baseNormal _environment _notVariable _notPiType notApp =>
          exact absurd (HeadStep.subjectRootIsApp headStep1) notApp
      | neutralApp _environment noHeadStep => exact absurd headStep1 (noHeadStep _)
      | headExpand headStep2 reductInterprets2 =>
          have reductEquation := HeadStep.deterministic headStep1 headStep2
          subst reductEquation
          exact reductInductiveHypothesis reductInterprets2 envIff

/-- **Determinism**: a type-code interprets to at most one candidate (up to pointwise equivalence)
under a fixed environment.  The reflexive instance of `pointwiseIff_of_envPointwiseIff`. -/
theorem InterpretsWhnf.deterministic {targetScope scope : Nat}
    {env : CandidateEnv scope targetScope} {typeCode : RawTerm scope}
    {candidate1 candidate2 : RawTerm targetScope → Prop}
    (interpretation1 : InterpretsWhnf env typeCode candidate1)
    (interpretation2 : InterpretsWhnf env typeCode candidate2) :
    PointwiseIff candidate1 candidate2 :=
  interpretation1.pointwiseIff_of_envPointwiseIff interpretation2 (PointwiseIffEnv.refl env)

end FX1Poly.Core
