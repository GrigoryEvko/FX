import FX1Poly.Core.ReducibleType
import FX1Poly.Core.StrongNormalizationSubterm

/-! # Foundation/PolyCell/Core/ReducibleTypeArrowCandidate
    — CR1 and CR2 for the dependent-arrow candidate of `ReducibleType.piType`

`ReducibleType.piType` (`ReducibleType.lean`) denotes the DEPENDENT arrow candidate

  `fun functionTerm => ∀ argument, domainCandidate argument →
     codomainCandidate argument (app functionTerm argument)`

with `codomainCandidate` a *function of the argument term*.  Proving this candidate is a genuine
reducibility candidate (`IsReducibilityCandidate`, the missing half of
`ReducibleType.isReducibilityCandidate`) needs all three CR conditions.  This file ships the two that
are UNBLOCKED:

  * **CR1** (`stronglyNormalizing`): a member of the arrow candidate is strongly normalizing — apply it
    to ANY reducible domain witness, land in that argument's codomain candidate (which is a candidate,
    so its members are SN), and descend `SN (app f witness)` to `SN f` by
    `appHead_isStronglyNormalizing_of_app`.  The domain witness is taken as a hypothesis (a variable
    when the scope is non-empty, via `containsVariable`); the *argument is fixed*, so no
    conversion-invariance is involved.
  * **CR2** (`closedUnderStep`): the arrow candidate is forward-closed under a function-position step —
    a step `f → f'` lifts to `app f arg → app f' arg` (`Step.cong gen_app`), and the codomain
    candidate's own CR2 carries membership across.  Again the *argument is fixed*.

CR3 (`neutralExpansion`) is NOT here: it is the precisely-localized wall (see the module docstring of
`ReducibleType.lean` and the project notes).  Its application-step subcase needs
`codomainCandidate argAfter X → codomainCandidate argFocus X` when `argFocus →Step argAfter` —
conversion-stability of the codomain candidate under ARGUMENT reduction — which `ReducibleType` does
not supply (it is closed only under weak-head reduction).  That is the Adjedj/Abel hard heart and is
left for the conversion-invariance development.

## Zero-axiom verification

CR1 is a direct application of `appHead_isStronglyNormalizing_of_app` to the codomain candidate's CR1;
CR2 lifts a function step by `Step.cong gen_app` / `StepChildren.here` and applies the codomain
candidate's `closedUnderStep`.  No induction, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- The dependent-arrow candidate produced by `ReducibleType.piType`: a function is reducible when it
sends every reducible argument into that argument's codomain candidate. -/
def DependentArrowCandidate {scope : Nat}
    (domainCandidate : RawTerm scope → Prop)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)) :
    RawTerm scope → Prop :=
  fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
    codomainCandidate argument
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))

/-- **CR1 for the dependent arrow**: a member of the dependent-arrow candidate is strongly normalizing.
Apply it to a reducible domain witness to land in that witness's codomain candidate — strongly
normalizing by the codomain candidate's CR1 — then descend `SN (app f witness)` to `SN f`.  The
argument is FIXED throughout, so this is conversion-invariance-free. -/
theorem DependentArrowCandidate.stronglyNormalizing {scope : Nat}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    (domainWitness : RawTerm scope) (witnessReducible : domainCandidate domainWitness)
    (codomainIsCandidate : IsReducibilityCandidate (codomainCandidate domainWitness))
    {functionTerm : RawTerm scope}
    (functionReducible :
      DependentArrowCandidate domainCandidate codomainCandidate functionTerm) :
    IsStronglyNormalizing functionTerm :=
  appHead_isStronglyNormalizing_of_app
    (codomainIsCandidate.stronglyNormalizing (functionReducible domainWitness witnessReducible))

/-- **CR2 for the dependent arrow**: the dependent-arrow candidate is forward-closed under a step in
the function position.  A function step `functionTerm → functionAfter` lifts to the application step
`app functionTerm argument → app functionAfter argument` (`Step.cong gen_app`), and the codomain
candidate's own CR2 (`closedUnderStep`) carries membership across.  The argument is FIXED, so this is
conversion-invariance-free. -/
theorem DependentArrowCandidate.closedUnderStep {scope : Nat}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    (codomainIsCandidate :
      ∀ argument : RawTerm scope, domainCandidate argument →
        IsReducibilityCandidate (codomainCandidate argument))
    {functionTerm functionAfter : RawTerm scope}
    (functionReducible :
      DependentArrowCandidate domainCandidate codomainCandidate functionTerm)
    (functionStep : Step functionTerm functionAfter) :
    DependentArrowCandidate domainCandidate codomainCandidate functionAfter := by
  intro argument argumentReducible
  have membership := functionReducible argument argumentReducible
  have applicationStep :
      Step
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))
        (.mkGen .gen_app () (.childCons functionAfter (.childCons argument .childNil))) :=
    Step.cong .gen_app ()
      (StepChildren.here (.childCons argument .childNil : RawTermChildren [0] scope) functionStep)
  exact (codomainIsCandidate argument argumentReducible).closedUnderStep membership applicationStep

end FX1Poly.Core
