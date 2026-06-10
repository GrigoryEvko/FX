import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/ReducibilityCandidateArrow
    — the function-space reducibility candidate (Girard's arrow construction)

The keystone of the Tait/Girard strong-normalization argument
(polycell.md §11.8.5).  From a candidate `domainPredicate` for the argument
position and a candidate `codomainPredicate` for the result position, the
**arrow predicate**

  `IsArrowReducible domainPredicate codomainPredicate function`
    := ∀ argument, domainPredicate argument →
         codomainPredicate (function applied to argument)

is itself a reducibility candidate.  Application is the only place the three CR
conditions interact across a reduction boundary; every higher former's
candidate (Σ, Nat, …) is assembled by the same template, so this is the load
arm of the whole `SN` development.

## The three CR proofs, each from a shipped ingredient

* **CR1** (reducible ⟹ SN): apply the function to a supplied reducible
  argument; the application is reducible in the codomain candidate, hence SN
  (`codomainCandidate.stronglyNormalizing`), and SN descends to the function
  through `appHead_isStronglyNormalizing_of_app` (the application-head sub-term
  projection).  The reducible-argument witness is an explicit hypothesis — the
  arrow candidate is SN-inhabited exactly when its domain is, so CR1 is honest
  about needing one.
* **CR2** (forward closure): a head step `function ↝ functionAfter` lifts to
  `app function argument ↝ app functionAfter argument` via `Step.cong`, and the
  codomain candidate is forward-closed under that step.
* **CR3** (neutral expansion): for a neutral `function` whose every reduct is
  arrow-reducible, `app function argument` is neutral (`IsNeutral.app`).  Its
  reducts are enumerated by `Step.from_app`: the β arm is impossible
  (`IsNeutral.not_lam` — a neutral term is never a λ), the head arm lands in the
  reduct hypothesis, the argument arm in the inner `Acc` induction on
  `SN argument`.  The codomain candidate's own CR3 then re-forms the
  application.

This is the non-dependent (simply-typed) arrow; the dependent-Π generalization
additionally tracks the codomain candidate varying with the argument and is
built on top of this construction.

## Zero-axiom verification

`Acc` induction + `Step.from_app` inversion + `Generator.noConfusion`
(λ-vs-neutral head disjointness) — no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The head generator of a raw term — the single `mkGen` constructor's
`generator` field.  Core-local; the Typed layer's `RawTerm.headGenerator` is the
same projection one layer up, unreachable from Core.  Used to refute
constructor-disjointness equalities via `congrArg … |>.noConfusion`. -/
def RawTerm.rootGenerator {scope : Nat} : RawTerm scope → Generator
  | .mkGen generator _payload _children => generator

/-- A neutral term is never a λ-abstraction.  Every `IsNeutral` arm builds its
subject as `mkGen generator …` with `generator` drawn from the elimination set
(`gen_var`, `gen_app`, `gen_fst`, …), none of which is `gen_lam`.  Casing the
neutrality witness with the subject free (the propext-safe direction) sends each
arm's `rootGenerator` to a concrete generator, refuted against `gen_lam` by
`Generator.noConfusion`.  This rules out the β reduct of a neutral application
in the arrow candidate's CR3. -/
theorem IsNeutral.not_lam {scope : Nat}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (lambdaIsNeutral :
      IsNeutral
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))) :
    False := by
  suffices neutralIsNeverLam :
      ∀ {subject : RawTerm scope}, IsNeutral subject →
        subject =
            .mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)) →
          False from
    neutralIsNeverLam lambdaIsNeutral rfl
  intro subject subjectIsNeutral
  cases subjectIsNeutral
  all_goals
    intro shapeEquation
    exact Generator.noConfusion (congrArg RawTerm.rootGenerator shapeEquation)

/-- A neutral term's head is never the Π-type former.  Every `IsNeutral` arm fixes the root to an
elimination generator (`gen_var`, `gen_app`, `gen_fst`, …); casing the neutrality witness with the
subject free sends each arm's `rootGenerator` to that concrete generator, refuted against `gen_piTyCode`
by `Generator.noConfusion`.  This is the `notPiType` obligation of the first-order simply-typed `leaf`
constructor, discharged uniformly for the whole neutral family (not just variables). -/
theorem IsNeutral.rootGenerator_ne_piTyCode {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_piTyCode := by
  cases neutral <;>
    exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- A neutral term's head is never the universe-code former (dual of `rootGenerator_ne_piTyCode`).  This
is the `notUniverse` obligation of the first-order simply-typed `leaf`, again uniform over the neutral
family. -/
theorem IsNeutral.rootGenerator_ne_universeCode {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_universeCode := by
  cases neutral <;>
    exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- The function-space reducibility predicate: `function` is arrow-reducible
when applying it to any `domainPredicate`-reducible argument yields a
`codomainPredicate`-reducible application. -/
def IsArrowReducible {scope : Nat}
    (domainPredicate codomainPredicate : RawTerm scope → Prop)
    (function : RawTerm scope) : Prop :=
  ∀ argument : RawTerm scope, domainPredicate argument →
    codomainPredicate
      (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))

/-- **The arrow construction.**  `IsArrowReducible` over two reducibility
candidates is again a reducibility candidate (Girard's function-space
candidate).  `reducibleWitness` supplies the SN-inhabitedness witness CR1
consumes. -/
theorem isArrowReducible_isReducibilityCandidate {scope : Nat}
    {domainPredicate codomainPredicate : RawTerm scope → Prop}
    (domainCandidate : IsReducibilityCandidate domainPredicate)
    (codomainCandidate : IsReducibilityCandidate codomainPredicate)
    (reducibleWitness : RawTerm scope)
    (witnessReducible : domainPredicate reducibleWitness) :
    IsReducibilityCandidate
      (IsArrowReducible domainPredicate codomainPredicate) := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro function functionArrowReducible
    have applicationReducible :
        codomainPredicate
          (.mkGen .gen_app ()
            (.childCons function (.childCons reducibleWitness .childNil))) :=
      functionArrowReducible reducibleWitness witnessReducible
    exact appHead_isStronglyNormalizing_of_app
      (codomainCandidate.stronglyNormalizing applicationReducible)
  case closedUnderStep =>
    intro function functionAfter functionArrowReducible functionStep
    intro argument argumentReducible
    have applicationStep :
        Step
          (.mkGen .gen_app ()
            (.childCons function (.childCons argument .childNil)))
          (.mkGen .gen_app ()
            (.childCons functionAfter (.childCons argument .childNil))) :=
      Step.cong .gen_app ()
        (StepChildren.here
          (.childCons argument .childNil : RawTermChildren [0] scope)
          functionStep)
    exact codomainCandidate.closedUnderStep
      (functionArrowReducible argument argumentReducible) applicationStep
  case neutralExpansion =>
    intro function functionIsNeutral reductsArrowReducible
    suffices general :
        ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
          domainPredicate currentArgument →
            codomainPredicate
              (.mkGen .gen_app ()
                (.childCons function (.childCons currentArgument .childNil))) from
      fun argument argumentReducible =>
        general (domainCandidate.stronglyNormalizing argumentReducible)
          argumentReducible
    intro currentArgument argumentAccessible
    induction argumentAccessible with
    | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
        intro argumentFocusReducible
        refine codomainCandidate.neutralExpansion
          (IsNeutral.app functionIsNeutral) ?_
        intro reduct reductionStep
        rcases Step.from_app reductionStep with
          ⟨_domainAnn, _body, functionEqualsLam, _targetEq⟩ |
          ⟨functionAfter, reductEquals, functionStep⟩ |
          ⟨argumentAfter, reductEquals, argumentStep⟩
        · exact (IsNeutral.not_lam (functionEqualsLam ▸ functionIsNeutral)).elim
        · rw [reductEquals]
          exact reductsArrowReducible functionAfter functionStep
            argumentFocus argumentFocusReducible
        · rw [reductEquals]
          exact argumentInductiveHypothesis argumentAfter argumentStep
            (domainCandidate.closedUnderStep argumentFocusReducible argumentStep)

end FX1Poly.Core
