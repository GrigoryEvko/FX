import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.WhnfInterpretationDeterminism
import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.IotaHeadStepDisjoint

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
  /-- A redex-type inherits its weak-head β contractum's candidate (conversion-invariance under
  weak-head β reduction). -/
  | headExpand {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop} :
      HeadStep typeCode reduct → ReducibleType reduct candidate → ReducibleType typeCode candidate
  /-- A redex-type inherits its root-ι contractum's candidate (conversion-invariance under root-ι
  reduction) — the large-elimination-ready companion of `headExpand`: an eliminator-headed type-code
  (`natRec`-at-a-universe, …) is `gen_natRec`-rooted, not `gen_app`-rooted, so it is NOT `HeadStep`-
  reducible yet root-ι-reduces, possibly to a Π; `iotaExpand` gives it its contractum's candidate
  rather than the (wrong) strong-normalization candidate the `neutral` arm would assign. -/
  | iotaExpand {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop} :
      IotaHeadStep typeCode reduct → ReducibleType reduct candidate → ReducibleType typeCode candidate
  /-- A weak-head-NORMAL non-Π type denotes the strong-normalization candidate (a variable, a
  stuck/neutral application, a universe code, any non-Π former).  "Weak-head normal" now means no β
  head step AND no root ι step — the strengthened guard that keeps the relation a partial function once
  `iotaExpand` classifies eliminator-on-constructor redexes (otherwise a root-ι redex would satisfy the
  old `¬ HeadStep` guard yet also fire `iotaExpand`, breaking determinism). -/
  | neutral {typeCode : RawTerm scope} :
      (∀ reduct : RawTerm scope, ¬ HeadStep typeCode reduct) →
      (∀ reduct : RawTerm scope, ¬ IotaHeadStep typeCode reduct) →
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

/-- **The dependent reducibility relation is functional** (up to pointwise iff): a type-code denotes at
most one candidate.  Induction on the first derivation, inverting the second; a weak-head step forces
`headExpand` on both (reducts equated by `HeadStep.deterministic`), a `gen_piTyCode` root forces
`piType` on both (domain candidates equivalent by the induction hypothesis, codomain candidates
equivalent pointwise at each reducible argument), and the remaining cross-arm pairs are impossible. -/
theorem ReducibleType.deterministic {scope : Nat} {typeCode : RawTerm scope}
    {candidate1 : RawTerm scope → Prop} (reducible1 : ReducibleType typeCode candidate1) :
    ∀ {candidate2 : RawTerm scope → Prop},
      ReducibleType typeCode candidate2 → PointwiseIff candidate1 candidate2 := by
  induction reducible1 with
  | headExpand headStep1 _reductReducible1 reductInductiveHypothesis =>
      intro candidate2 reducible2
      cases reducible2 with
      | headExpand headStep2 reductReducible2 =>
          have reductEquation := HeadStep.deterministic headStep1 headStep2
          subst reductEquation
          exact reductInductiveHypothesis reductReducible2
      | iotaExpand iotaStep2 _reductReducible2 =>
          exact (HeadStep.not_iotaHeadStep headStep1 iotaStep2).elim
      | neutral noHeadStep2 _noIotaHeadStep2 _notPiType2 => exact absurd headStep1 (noHeadStep2 _)
      | piType _codomainCandidate2 _domainReducible2 _codomainReducible2 =>
          exact Generator.noConfusion (HeadStep.subjectRootIsApp headStep1)
  | iotaExpand iotaStep1 _reductReducible1 reductInductiveHypothesis =>
      intro candidate2 reducible2
      cases reducible2 with
      | headExpand headStep2 _reductReducible2 =>
          exact (HeadStep.not_iotaHeadStep headStep2 iotaStep1).elim
      | iotaExpand iotaStep2 reductReducible2 =>
          have reductEquation := IotaHeadStep.deterministic iotaStep1 iotaStep2
          subst reductEquation
          exact reductInductiveHypothesis reductReducible2
      | neutral _noHeadStep2 noIotaHeadStep2 _notPiType2 =>
          exact absurd iotaStep1 (noIotaHeadStep2 _)
      | piType _codomainCandidate2 _domainReducible2 _codomainReducible2 =>
          cases iotaStep1
  | neutral noHeadStep1 noIotaHeadStep1 notPiType1 =>
      intro candidate2 reducible2
      cases reducible2 with
      | headExpand headStep2 _reductReducible2 => exact absurd headStep2 (noHeadStep1 _)
      | iotaExpand iotaStep2 _reductReducible2 => exact absurd iotaStep2 (noIotaHeadStep1 _)
      | neutral _noHeadStep2 _noIotaHeadStep2 _notPiType2 => intro _term; exact Iff.rfl
      | piType _codomainCandidate2 _domainReducible2 _codomainReducible2 =>
          exact absurd rfl notPiType1
  | piType _codomainCandidate1 _domainReducible1 _codomainReducible1
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro candidate2 reducible2
      cases reducible2 with
      | headExpand headStep2 _reductReducible2 =>
          exact Generator.noConfusion (HeadStep.subjectRootIsApp headStep2)
      | iotaExpand iotaStep2 _reductReducible2 => cases iotaStep2
      | neutral _noHeadStep2 _noIotaHeadStep2 notPiType2 => exact absurd rfl notPiType2
      | piType _codomainCandidate2 domainReducible2 codomainReducible2 =>
          have domainEquivalence := domainInductiveHypothesis domainReducible2
          intro functionTerm
          constructor
          · intro membership1 argument domain2Argument
            have domain1Argument := (domainEquivalence argument).mpr domain2Argument
            have codomainEquivalence :=
              codomainInductiveHypothesis argument domain1Argument
                (codomainReducible2 argument domain2Argument)
            exact (codomainEquivalence _).mp (membership1 argument domain1Argument)
          · intro membership2 argument domain1Argument
            have domain2Argument := (domainEquivalence argument).mp domain1Argument
            have codomainEquivalence :=
              codomainInductiveHypothesis argument domain1Argument
                (codomainReducible2 argument domain2Argument)
            exact (codomainEquivalence _).mpr (membership2 argument domain2Argument)

end FX1Poly.Core
