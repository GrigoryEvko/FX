import FX1Poly.Typed.OpenStronglyNormalizing
import FX1Poly.Typed.ReducibleEnvOfWfContext

/-! # FX1Poly/Typed/OpenStronglyNormalizingUnconditional
    — ★ SN-FOR-WELL-TYPED, the OPEN case: every well-typed grown term is strongly normalizing (SN-043, OB-5)

`HasTypeDescPi.stronglyNormalizingOfWfContext`: for any WELL-FORMED context `Γ` (arbitrary scope) and any grown
derivation `HasTypeDescPi Γ subject classifier`, `subject` is strongly normalizing — UNCONDITIONALLY, zero-axiom.
This is **SN-043** (#546): the open generalization of the closed capstone `closedStronglyNormalizing` (BFT-14)
from `Γ = .empty` to an arbitrary well-formed context.

## The wire (the OB-1..OB-5 chain bottoms out here)

The conditional open SN (`HasTypeDescPi.stronglyNormalizingOfReducibleEnv`, OpenStronglyNormalizing.lean) already
gives SN GIVEN a `BoundExceedsPi` budget + a bound-reducible closing environment — reflecting SN through the
substitution INTERNALLY.  This theorem discharges both inputs:

  1. `BoundExceedsPi.existsBound` budgets the derivation at `boundDerivation`;
  2. `reducibleEnvOfWfContext` (OB-3) supplies the reducible closing environment at `boundEnvironment` (its
     "every variable to `var 0`" substitution, built from OB-1's variable-membership leaf + OB-2's binding-type
     reducibility);
  3. both lift to the common SUM bound `boundDerivation + boundEnvironment` (`BoundExceedsPi.monotoneInBound` +
     `IsReducibleMemberAtBounded.cumulative`; SUM not `max`, since `Nat.le_max_*` depend on `propext`);
  4. `stronglyNormalizingOfReducibleEnv` then yields `IsStronglyNormalizing subject` directly.

The universe valuation `env` is irrelevant to SN, so it is fixed to `fun _ => 0` (as in the closed capstone).

## What this route did NOT need

The BFT bounded route reaches SN-043 with NONE of: the fuel-stability gate #672
(`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`), the KB merged-candidate construction, or
bounded reducibility-under-renaming (the SN-040 analogue) — the "var 0 head" trick in OB-3 sidesteps the last.
The closed case additionally has an independent second proof (`ValidTyping.closedStronglyNormalizing`, route A).

## Honest scope: WfContext-hypothesized

The statement carries `WfContext Γ` as a hypothesis — the honest form, since an ill-formed context can type
nonsense.  Dropping it (if the grown engine presupposes context well-formedness) is the separate OB-6 (#795).
What the milestone consumes — closed-term canonicity (SN-047/048/049) and consistency (SN-050) — uses the closed
instance (`Γ = .empty`, `WfContext.empty` trivial); the qualifier-drops (SN-051/052/055) use this open form.

## Zero-axiom verification

A four-step composition of shipped zero-axiom results.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **★ SN-043 (open): every well-typed grown term in a well-formed context is strongly normalizing.**
`WfContext Γ → HasTypeDescPi Γ subject classifier → IsStronglyNormalizing subject`, unconditionally and
zero-axiom.  Composes `BoundExceedsPi.existsBound` (the derivation budget) + `reducibleEnvOfWfContext` (OB-3, the
reducible closing environment) at a common SUM bound, fed to `stronglyNormalizingOfReducibleEnv` (which reflects
SN through the substitution internally).  The open generalization of `closedStronglyNormalizing` (BFT-14); the
capstone of the OB-1..OB-5 chain. -/
theorem HasTypeDescPi.stronglyNormalizingOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (d : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨boundDerivation, budgetDerivation⟩ := BoundExceedsPi.existsBound (env := fun _ => 0) d
  obtain ⟨boundEnvironment, substitution, environmentReducible⟩ :=
    reducibleEnvOfWfContext (fun _ => 0) context contextWellFormed
  exact d.stronglyNormalizingOfReducibleEnv
    (BoundExceedsPi.monotoneInBound (Nat.le_add_right boundDerivation boundEnvironment) budgetDerivation)
    (fun index => (environmentReducible index).cumulative
      (Nat.le_add_left boundEnvironment boundDerivation))

end FX1Poly.Typed
