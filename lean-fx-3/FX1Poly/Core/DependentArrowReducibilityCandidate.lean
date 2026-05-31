import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.ReducibleTypeConvInvariance
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst

/-! # Foundation/PolyCell/Core/DependentArrowReducibilityCandidate
    — the DEPENDENT function-space is a reducibility candidate (Girard CR3 via conversion-invariance)

`isArrowReducible_isReducibilityCandidate` (`ReducibilityCandidateArrow`) proves Girard's function-space
construction is a reducibility candidate, but only for a NON-dependent codomain (a fixed predicate).  The
`ReducibleType.piType` candidate is DEPENDENT: the codomain candidate `codomainCandidate argument` varies
with the argument (it is the interpretation of `subst0 codomainCode argument`).  This file proves the
dependent generalization.

The two of the three CR conditions adapt verbatim (just thread `codomainCandidate argument` where the
non-dependent proof used the fixed codomain).  The third, CR3 (neutral expansion), gains ONE new step —
and it is exactly what conversion-invariance was built for.  In the argument-reduction case of CR3 (the
neutral `function` applied to a reducing argument `argumentFocus ↝ argumentAfter`), the accessibility
induction hypothesis lands membership in `codomainCandidate argumentAfter`, but the goal is membership in
`codomainCandidate argumentFocus`.  Those two candidates interpret `subst0 codomainCode argumentAfter` and
`subst0 codomainCode argumentFocus`, which are CONVERTIBLE (`argumentFocus ↝ argumentAfter` lifts through
`subst0` to a `StepStar`, so they join), so `ReducibleType.convTransfer` ports the membership across.  The
non-dependent proof never needs this because its codomain does not move.

## Zero-axiom verification

The Girard candidate-construction proof (`refine ⟨…⟩`; CR1 = apply to the witness + `appHead` SN descent;
CR2 = function-congruence + codomain CR2; CR3 = accessibility induction on the argument + `Step.from_app`
inversion + codomain CR3), with the argument-reduction sub-case bridged by `ReducibleType.convTransfer`
over the `subst0`-argument `StepStar` (`Step.subst0Argument`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- The DEPENDENT function-space reducibility predicate: `function` is dependent-arrow-reducible when
applying it to any `domainPredicate`-reducible `argument` lands in `codomainCandidate argument` — the
candidate INDEXED by that argument (the `ReducibleType.piType` candidate's body). -/
def IsDependentArrowReducible {scope : Nat}
    (domainPredicate : RawTerm scope → Prop)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (function : RawTerm scope) : Prop :=
  ∀ argument : RawTerm scope, domainPredicate argument →
    codomainCandidate argument
      (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))

/-- **The dependent arrow construction is a reducibility candidate.**  Given a domain candidate, a family
of codomain candidates `codomainCandidate argument` each a reducibility candidate, the `ReducibleType`
witnesses that interpret them (`codomainReducible`, supplying conversion-invariance), and an SN-
inhabitedness witness in the domain, the dependent function-space predicate satisfies CR1/CR2/CR3.  CR3's
argument-reduction case is the only place the dependence bites: it is bridged by `ReducibleType.convTransfer`
across the convertible reduced codomain codes. -/
theorem isDependentArrowReducible_isReducibilityCandidate {scope : Nat}
    {domainPredicate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : IsReducibilityCandidate domainPredicate)
    (codomainCandidateHood : ∀ argument : RawTerm scope, domainPredicate argument →
      IsReducibilityCandidate (codomainCandidate argument))
    (codomainReducible : ∀ argument : RawTerm scope, domainPredicate argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainCandidate argument))
    (reducibleWitness : RawTerm scope)
    (witnessReducible : domainPredicate reducibleWitness) :
    IsReducibilityCandidate (IsDependentArrowReducible domainPredicate codomainCandidate) := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro function functionArrowReducible
    have applicationReducible :
        codomainCandidate reducibleWitness
          (.mkGen .gen_app ()
            (.childCons function (.childCons reducibleWitness .childNil))) :=
      functionArrowReducible reducibleWitness witnessReducible
    exact appHead_isStronglyNormalizing_of_app
      ((codomainCandidateHood reducibleWitness witnessReducible).stronglyNormalizing
        applicationReducible)
  case closedUnderStep =>
    intro function functionAfter functionArrowReducible functionStep argument argumentReducible
    have applicationStep :
        Step
          (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
          (.mkGen .gen_app () (.childCons functionAfter (.childCons argument .childNil))) :=
      Step.cong .gen_app ()
        (StepChildren.here
          (.childCons argument .childNil : RawTermChildren [0] scope)
          functionStep)
    exact (codomainCandidateHood argument argumentReducible).closedUnderStep
      (functionArrowReducible argument argumentReducible) applicationStep
  case neutralExpansion =>
    intro function functionIsNeutral reductsArrowReducible
    suffices general :
        ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
          domainPredicate currentArgument →
            codomainCandidate currentArgument
              (.mkGen .gen_app ()
                (.childCons function (.childCons currentArgument .childNil))) from
      fun argument argumentReducible =>
        general (domainCandidate.stronglyNormalizing argumentReducible) argumentReducible
    intro currentArgument argumentAccessible
    induction argumentAccessible with
    | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
        intro argumentFocusReducible
        refine (codomainCandidateHood argumentFocus argumentFocusReducible).neutralExpansion
          (IsNeutral.app functionIsNeutral) ?_
        intro reduct reductionStep
        rcases Step.from_app reductionStep with
          ⟨_body, functionEqualsLam, _targetEq⟩ |
          ⟨functionAfter, reductEquals, functionStep⟩ |
          ⟨argumentAfter, reductEquals, argumentStep⟩
        · exact (IsNeutral.not_lam (functionEqualsLam ▸ functionIsNeutral)).elim
        · rw [reductEquals]
          exact reductsArrowReducible functionAfter functionStep
            argumentFocus argumentFocusReducible
        · rw [reductEquals]
          have argumentAfterReducible :=
            domainCandidate.closedUnderStep argumentFocusReducible argumentStep
          exact ReducibleType.convTransfer
            (codomainReducible argumentAfter argumentAfterReducible)
            (codomainReducible argumentFocus argumentFocusReducible)
            ⟨_, StepStar.refl _, Step.subst0Argument codomainCode argumentStep⟩
            (argumentInductiveHypothesis argumentAfter argumentStep argumentAfterReducible)

end FX1Poly.Core
