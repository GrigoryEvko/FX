import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.WhnfInterpretationDeterminism
import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.WeakHeadStepDeterministic

/-! # Foundation/PolyCell/Core/ReducibleType
    — the dependent reducibility relation (Girard-Tait, made dependent)

`InterpretsWhnf` (`WhnfInterpretation`) is conversion-invariant but FIRST-ORDER: its environment maps
each type variable to a fixed candidate, so it cannot interpret a type-FAMILY variable `F` applied to
an argument (the substitution lemma fails — substituting a `lam` for a neutral application head turns
it into a redex that re-interprets to a different candidate).

`ReducibleType` is the DEPENDENT fix: a type-code denotes a reducibility candidate, dispatching after
weak-head reduction, with the Π codomain candidate a *function of the argument term* — so it
RE-INTERPRETS a substituted codomain rather than transporting a fixed candidate, which is exactly what
term-indexed families (`F : (n : A) → Type`) need.  Three arms:

  * `headExpand` — a redex-type inherits its weak-head contractum's candidate (conversion-invariance
    under weak-head reduction, via `HeadStep`);
  * `neutral` — every weak-head-normal NON-Π type (a variable, a stuck/neutral application — a neutral
    type family — a universe code, any other former) denotes the strong-normalization candidate.  This
    is correct for SN and is why no higher-kinded environment is needed: a neutral type family is SN;
  * `piType` — the DEPENDENT arrow: a Π-code denotes
      `fun functionTerm => ∀ argument, domainCandidate argument →
         codomainCandidate argument (functionTerm applied to argument)`,
    where `codomainCandidate argument` is obtained by interpreting `subst0 codomainCode argument` for
    each reducible argument.  This directly classifies `piElim` (`app f a : subst0 codomainCode a`).

`HeadStep` is DETERMINISTIC, so the relation is functional: the three arms are mutually exclusive on a
fixed code by the partition (has-weak-head-step, root = `gen_piTyCode`?), and `HeadStep.deterministic`
equates the two weak-head reducts — NO confluence needed.  `ReducibleType.deterministic` is that
functionality (up to pointwise iff, the funext-free notion reused from
`CandidateInterpretationDeterminism`).

This brick ships the inductive and its determinism.  Strict positivity holds (`ReducibleType` occurs
only positively, as the conclusion of the codomain premise's implication); the stored
`codomainCandidate` function and the `∀`-quantified premise are constructor data in a `Prop`, eliminated
only into `Prop`.

## Zero-axiom verification

A plain inductive `Prop` + induction inverting the second derivation by `cases`, cross-arm
impossibilities discharged by `HeadStep.subjectRootIsApp` (a weak-head step is `gen_app`-rooted, so a
`gen_piTyCode` code never steps) and `Generator.noConfusion`; the weak-head reducts equated by
`HeadStep.deterministic`.  Pointwise-iff, no predicate equality, hence no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- The dependent reducibility relation: a type-code denotes a reducibility candidate, dispatching
after weak-head reduction, with the Π codomain candidate a function of the argument term. -/
inductive ReducibleType {scope : Nat} : RawTerm scope → (RawTerm scope → Prop) → Prop where
  /-- A redex-type inherits its WEAK-HEAD contractum's candidate (conversion-invariance under the
  complete weak-head reduction `WeakHeadStep` = β at the head + root-ι + scrutinee-congruence).  This
  single arm subsumes β-expansion, root-ι expansion (eliminator-on-constructor, large-elimination-ready),
  AND scrutinee reduction (an eliminator whose scrutinee is itself reducible), so the `neutral` arm's
  guard can be the honest fully-stuck `¬ WeakHeadStep`. -/
  | whnfExpand {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop} :
      WeakHeadStep typeCode reduct → ReducibleType reduct candidate → ReducibleType typeCode candidate
  /-- A WEAK-HEAD-NORMAL non-Π type denotes the strong-normalization candidate (a variable, a
  stuck/neutral application or eliminator, a universe code, any non-Π former).  "Weak-head normal" is
  the honest `¬ WeakHeadStep`: no β head step, no root ι, AND no reducible scrutinee — genuinely stuck.
  This is what makes weak-head-normal forms closed under arbitrary internal reduction, hence
  conversion-invariance UNCONDITIONAL (not merely fragment-restricted). -/
  | neutral {typeCode : RawTerm scope} :
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct) →
      typeCode.rootGenerator ≠ Generator.gen_piTyCode →
      ReducibleType typeCode IsStronglyNormalizing
  /-- The dependent arrow: a Π-code denotes the dependent function-space candidate, the codomain
  candidate varying with the argument term. -/
  | piType {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainCandidate : RawTerm scope → Prop}
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)) :
      ReducibleType domainCode domainCandidate →
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleType (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) →
      ReducibleType
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))))
  /-- **Pointwise-congruence closure.**  A reducible type at one candidate is reducible at any
  pointwise-equivalent candidate.  Closing the relation under `PointwiseIff` (which it is otherwise
  functional up to but not closed under) is what lets the fundamental theorem feed the Π codomain the
  FIXED canonical member-predicate `fun arg => IsReducibleMember (subst0 cod arg)` WITHOUT choice: the
  per-argument premise is discharged from per-argument existence, then transported onto the fixed
  predicate here.  Positivity holds — the recursive premise is strictly positive, `canonicalCandidate` is
  a non-uniform index, and `PointwiseIff` has no recursive occurrence. -/
  | ofPointwiseIff {typeCode : RawTerm scope} {candidate canonicalCandidate : RawTerm scope → Prop} :
      ReducibleType typeCode candidate →
      PointwiseIff candidate canonicalCandidate →
      ReducibleType typeCode canonicalCandidate

/-- **Weak-head peel.**  A reducible type that weak-head-steps inherits the SAME candidate at its
contractum.  Induction (subject generic): `whnfExpand` equates the two reducts by
`WeakHeadStep.deterministic`; `neutral` has no weak-head step; the `piType` leaf is weak-head normal
(`rootIota` then the impossible `IotaHeadStep`); the `ofPointwiseIff` arm recurses by its induction
hypothesis and re-wraps the stored pointwise equivalence.  The inversion `deterministic`'s `whnfExpand`
cross-arm consumes (mirrors the stratified `ReducibleTypeStep.candidateAtWhnfReduct`). -/
theorem ReducibleType.candidateAtWhnfReduct {scope : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop} (reducible : ReducibleType typeCode candidate) :
    ∀ {reduct : RawTerm scope}, WeakHeadStep typeCode reduct → ReducibleType reduct candidate := by
  induction reducible with
  | whnfExpand weakHeadStep0 reductReducible0 _reductInductiveHypothesis =>
      intro reduct weakHeadStep
      have reductEquation := WeakHeadStep.deterministic weakHeadStep0 weakHeadStep
      subst reductEquation
      exact reductReducible0
  | neutral noWeakHeadStep _notPiType =>
      intro reduct weakHeadStep
      exact absurd weakHeadStep (noWeakHeadStep reduct)
  | piType _codomainCandidate _domainReducible _codomainReducible =>
      intro reduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro reduct weakHeadStep
      exact ReducibleType.ofPointwiseIff (innerInductiveHypothesis weakHeadStep) pointwiseIff

/-- **Π-shape inversion (up to pointwise iff).**  A reducible Π-code recovers its domain candidate, its
per-argument codomain candidate, their reducibility, and the pointwise equivalence of its candidate with
the dependent-arrow candidate.  `whnfExpand` (a Π-code is weak-head normal) and `neutral` (its root IS
`gen_piTyCode`) are impossible; `piType` reads off the data (its candidate IS the dependent-arrow candidate,
`Iff.rfl`); `ofPointwiseIff` recurses by its induction hypothesis and composes its stored equivalence.  The
inversion `deterministic`'s `piType` cross-arm consumes (mirrors the stratified
`ReducibleTypeStep.candidatePiShape`). -/
theorem ReducibleType.candidatePiShape {scope : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop} (reducible : ReducibleType typeCode candidate) :
    ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
      typeCode = (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) →
      ∃ (domainCandidate : RawTerm scope → Prop)
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleType domainCode domainCandidate ∧
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleType (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) ∧
        PointwiseIff candidate
          (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible _reductInductiveHypothesis =>
      intro _domainCode _codomainCode shapeEquation; subst shapeEquation
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | neutral _noWeakHeadStep notPiType =>
      intro _domainCode _codomainCode shapeEquation; subst shapeEquation
      exact absurd rfl notPiType
  | piType codomainCandidate domainReducible codomainReducible =>
      intro _domainCode _codomainCode shapeEquation; cases shapeEquation
      exact ⟨_, codomainCandidate, domainReducible, codomainReducible, fun _term => Iff.rfl⟩
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro _domainCode _codomainCode shapeEquation
      obtain ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible,
        pointwiseInner⟩ := innerInductiveHypothesis shapeEquation
      exact ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible,
        fun term => ((pointwiseIff term).symm).trans (pointwiseInner term)⟩

/-- **A weak-head-normal non-Π type's candidate is pointwise strong normalization.**  The candidate-level
neutral characterization: any candidate a weak-head-normal non-Π type-code denotes coincides pointwise with
`IsStronglyNormalizing`.  Induction: `whnfExpand` contradicts weak-head normality; `neutral` gives `SN` on
the nose (`Iff.rfl`); `piType` contradicts the non-Π root guard; `ofPointwiseIff` composes its stored
equivalence with the induction hypothesis.  The inversion the fundamental theorem's type-formation
`neutral` arm reads, and the helper `deterministic`'s `neutral` cross-arm consumes (mirrors the stratified
`ReducibleTypeStep.candidateIffStronglyNormalizing`); deterministic-independent so `deterministic` may call
it. -/
theorem ReducibleType.candidateIffStronglyNormalizing {scope : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop} (reducible : ReducibleType typeCode candidate)
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode) :
    PointwiseIff candidate IsStronglyNormalizing := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible _reductInductiveHypothesis =>
      exact absurd weakHeadStep (noWeakHeadStep _)
  | neutral _noWeakHeadStep _notPiType => intro _term; exact Iff.rfl
  | piType _codomainCandidate _domainReducible _codomainReducible => exact absurd rfl notPiType
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro term
      exact (pointwiseIff term).symm.trans (innerInductiveHypothesis noWeakHeadStep notPiType term)

/-- **The dependent reducibility relation is functional** (up to pointwise iff): a type-code denotes at
most one candidate.  Induction on the first derivation, inverting the second with the shape helpers that
ABSORB the `ofPointwiseIff` arm (`candidateAtWhnfReduct` / `candidateIffStronglyNormalizing` /
`candidatePiShape`): `whnfExpand` peels the second to the shared reduct; `neutral` reads the second's
strong-normalization candidate; `piType` inverts the second's arrow shape and equates domain (IH) +
codomain (IH, pointwise per argument); `ofPointwiseIff` recurses and composes.  Mirrors the stratified
`ReducibleTypeStep.deterministic`. -/
theorem ReducibleType.deterministic {scope : Nat} {typeCode : RawTerm scope}
    {candidate1 : RawTerm scope → Prop} (reducible1 : ReducibleType typeCode candidate1) :
    ∀ {candidate2 : RawTerm scope → Prop},
      ReducibleType typeCode candidate2 → PointwiseIff candidate1 candidate2 := by
  induction reducible1 with
  | whnfExpand weakHeadStep1 _reductReducible1 reductInductiveHypothesis =>
      intro candidate2 reducible2
      exact reductInductiveHypothesis (reducible2.candidateAtWhnfReduct weakHeadStep1)
  | neutral noWeakHeadStep1 notPiType1 =>
      intro candidate2 reducible2 term
      exact (reducible2.candidateIffStronglyNormalizing noWeakHeadStep1 notPiType1 term).symm
  | piType _codomainCandidate1 _domainReducible1 _codomainReducible1
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro candidate2 reducible2
      obtain ⟨_domainCandidate2, _codomainCandidate2, domainReducible2, codomainReducible2,
        pointwiseIff2⟩ := reducible2.candidatePiShape rfl
      refine fun functionTerm => Iff.trans ?_ (pointwiseIff2 functionTerm).symm
      constructor
      · intro membership1 argument domain2Argument
        have domain1Argument := (domainInductiveHypothesis domainReducible2 argument).mpr domain2Argument
        have codomainEquivalence :=
          codomainInductiveHypothesis argument domain1Argument
            (codomainReducible2 argument domain2Argument)
        exact (codomainEquivalence _).mp (membership1 argument domain1Argument)
      · intro membership2 argument domain1Argument
        have domain2Argument := (domainInductiveHypothesis domainReducible2 argument).mp domain1Argument
        have codomainEquivalence :=
          codomainInductiveHypothesis argument domain1Argument
            (codomainReducible2 argument domain2Argument)
        exact (codomainEquivalence _).mpr (membership2 argument domain2Argument)
  | ofPointwiseIff _innerReducible1 pointwiseIff1 innerInductiveHypothesis1 =>
      intro candidate2 reducible2 term
      exact (pointwiseIff1 term).symm.trans (innerInductiveHypothesis1 reducible2 term)

end FX1Poly.Core
