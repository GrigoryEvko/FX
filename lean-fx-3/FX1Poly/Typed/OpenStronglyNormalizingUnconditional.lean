import FX1Poly.Typed.OpenStronglyNormalizing
import FX1Poly.Typed.ReducibleEnvOfWfContext

/-! # FX1Poly/Typed/OpenStronglyNormalizingUnconditional
    — ★ SN-FOR-WELL-TYPED, the OPEN case: every well-typed grown term is strongly normalizing

`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`: for any WELL-FORMED context `Γ` (arbitrary scope, well-formed
per the formation predicate `WfContextDesc`) and any grown derivation `HasTypeDescPi Γ subject classifier`,
`subject` is strongly normalizing — UNCONDITIONALLY, zero-axiom.  The open generalization of the closed capstone
`closedStronglyNormalizing` from `Γ = .empty` to an arbitrary well-formed context.

## The wire

The conditional open SN (`HasTypeDescPi.stronglyNormalizingOfReducibleEnv`, OpenStronglyNormalizing.lean)
gives SN GIVEN a `BoundExceedsPi` budget + a bound-reducible closing environment — reflecting SN through the
substitution INTERNALLY.  This theorem discharges both inputs:

  1. `BoundExceedsPi.existsBound` budgets the derivation at `boundDerivation`;
  2. `reducibleEnvOfWfContextDesc` supplies the reducible closing environment at `boundEnvironment` (its
     "every variable to `var 0`" substitution, built from the variable-membership leaf + binding-type
     reducibility);
  3. both lift to the common SUM bound `boundDerivation + boundEnvironment` (`BoundExceedsPi.monotoneInBound` +
     `IsReducibleMemberAtBounded.cumulative`; SUM not `max`, since `Nat.le_max_*` depend on `propext`);
  4. `stronglyNormalizingOfReducibleEnv` then yields `IsStronglyNormalizing subject` directly.

The universe valuation `env` is irrelevant to SN, so it is fixed to `fun _ => 0` (as in the closed capstone).

## What this route does not need

The bounded route reaches open SN with NONE of: a fuel-stability gate, a merged-candidate construction, or
bounded reducibility-under-renaming — the "var 0 head" trick in `reducibleEnvOfWfContextDesc` sidesteps the
last.  The closed case additionally has an independent second proof (`ValidTyping.closedStronglyNormalizing`).

## Honest scope: WfContextDesc-hypothesized

The statement carries `WfContextDesc Γ` as a hypothesis — the honest form, since an ill-formed context can type
nonsense.  Dropping it (if the grown engine presupposes context well-formedness) is a separate step.
Closed-term canonicity and consistency use the closed instance (`Γ = .empty`,
`WfContextDesc.emptyIsWellFormed` trivial); the conversion-decidability qualifier-drops use this open form.

## Zero-axiom verification

A four-step composition of shipped zero-axiom results.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **★ Open SN: every well-typed grown term in a well-formed context is strongly normalizing.**
`WfContextDesc Γ → HasTypeDescPi Γ subject classifier → IsStronglyNormalizing subject`, unconditionally and
zero-axiom.  Four-step composition: the reducible closing environment comes from
`reducibleEnvOfWfContextDesc`, so the whole open-SN capstone routes through the `HasTypeDesc`-defined
context-wellformedness predicate.  The derivation budget comes from `BoundExceedsPi.existsBound`; both
lift to a common SUM bound (`monotoneInBound` + `cumulative`) and feed `stronglyNormalizingOfReducibleEnv`,
which reflects SN through the substitution internally.  The `WfContextDesc Γ` hypothesis is genuinely external
(since `HasTypeDescPi Γ t T → WfContextDesc Γ` provably FAILS, `ContextValidityFails`), so it is supplied
externally rather than derived.  The open generalization of `closedStronglyNormalizing`; the target the
conversion-decidability qualifier-drops use. -/
theorem HasTypeDescPi.stronglyNormalizingOfWfContextDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (d : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨boundDerivation, budgetDerivation⟩ := BoundExceedsPi.existsBound (env := fun _ => 0) d
  obtain ⟨boundEnvironment, substitution, environmentReducible⟩ :=
    reducibleEnvOfWfContextDesc (fun _ => 0) context contextWellFormed
  exact d.stronglyNormalizingOfReducibleEnv
    (BoundExceedsPi.monotoneInBound (Nat.le_add_right boundDerivation boundEnvironment) budgetDerivation)
    (fun index => (environmentReducible index).cumulative
      (Nat.le_add_left boundEnvironment boundDerivation))

end FX1Poly.Typed
