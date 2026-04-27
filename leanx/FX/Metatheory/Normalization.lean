import FX.Kernel.Typing
import FX.Kernel.Reduction

/-!
# Strong Normalization — kernel metatheory stub

Per `fx_design.md` §27.4 and §31.  **Theorem statement only — no
proof.**

## Statement

Every well-typed term has a finite reduction sequence reaching
a normal form.  Equivalently: there is no infinite reduction
chain starting from a well-typed term.

Formally, using the kernel's fuel-bounded `normalize`:

```
∀ (term expectedType : Term) (globalEnv : GlobalEnv),
  Term.check (TypingContext.empty) term expectedType globalEnv = .ok () →
  ∃ (normalForm : Term) (fuel : Nat),
    Term.normalize fuel term = normalForm ∧
    Term.betaStep? normalForm = none
```

## Scope deferral

Strong normalization proofs for MLTT-family calculi typically
run 10-30 kLOC of Lean/Coq/Agda.  Girard's candidates of
reducibility (semantic argument), or Tait-style strong
normalization via saturated sets, or the recent structural
approach via big-step evaluation — any of these is a
multi-person-month undertaking.

**Explicitly deferred to Phase 8+ per the interpreter plan.**
The interpreter ships with Preservation + Progress as the
immediate correctness guarantees; SN is a longer-horizon
project.

## What we get without SN

  * Preservation + Progress → type safety (no stuck non-canonical
    well-typed terms).
  * Fuel-bounded normalize → termination in practice for
    every program we ship; `R_fuel` surfaces hangs as typing
    errors.
  * The emit-table axiom (`U-emit`, Appendix H.10) is the one
    non-reducing rule; SN is over the pure fragment only.

## What SN enables (future)

  * Consistency as a theorem rather than an argument.
  * Decidable type checking (currently fuel-dependent).
  * Soundness of decision procedures for equality.
  * Removal of `defaultFuel` as a trusted constant.
-/

namespace FX.Metatheory

open FX.Kernel

/-- Every well-typed closed term normalizes in finite fuel.

    Unproved.  Deferred to Phase 8+ per `SPEC.md` §7 SN
    deferral.  The interpreter's current correctness argument
    rests on Preservation + Progress. -/
def StrongNormalization : Prop :=
  ∀ (term expectedType : Term) (globalEnv : GlobalEnv),
    Term.check (TypingContext.empty) term expectedType globalEnv = .ok () →
    ∃ (normalForm : Term) (fuel : Nat),
      Term.normalize fuel term = normalForm ∧
      Term.betaStep? normalForm = none

end FX.Metatheory
