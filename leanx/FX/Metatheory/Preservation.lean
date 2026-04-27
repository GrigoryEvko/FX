import FX.Kernel.Typing
import FX.Kernel.Reduction

/-!
# Preservation — kernel metatheory stub

Per `fx_design.md` §27.4 and §31.  **Theorem statement only — no
proof.**  The proof is the load-bearing correctness commitment
of the graded kernel; mechanization lives in a later phase
(see `docs/metatheory-status.md` when it exists).

## Statement

If a term is well-typed and takes a beta or iota reduction
step, the reduct is still well-typed at the same type.

Formally, using the concrete kernel API:

```
∀ (context : TypingContext) (term reduct : Term) (expectedType : Term)
  (globalEnv : GlobalEnv),
  Term.check context term expectedType globalEnv = .ok () →
  Term.betaStep? term = some reduct →
  Term.check context reduct expectedType globalEnv = .ok ()
```

## Scope notes

  * Covers β (app-lam) and ι (indRec-ctor) — the two head rules
    in `Term.betaStep?`.
  * η and ν reduction: preservation for these lands when
    `Conversion.convEq` and coinductive reduction respectively
    gain real content.
  * The graded extension: preservation must also preserve the
    grade vector up to subsumption (Wood-Atkey 2022).  Stated
    separately in `GradePreservation` once the usage checker
    exits its Phase-2 "advisory" mode.
-/

namespace FX.Metatheory

open FX.Kernel

/-- Well-typed terms stay well-typed under one head reduction step.

    Unproved.  Intended for mechanization via structural induction
    on the reduction rule used, with cases for β (Pi-elim +
    openWith substitution preserves typing) and ι (indRec-ctor
    picks the method whose type matches the ctor's image under
    the motive). -/
def Preservation : Prop :=
  ∀ (context : TypingContext) (term reduct expectedType : Term)
    (globalEnv : GlobalEnv),
    Term.check context term expectedType globalEnv = .ok () →
    Term.betaStep? term = some reduct →
    Term.check context reduct expectedType globalEnv = .ok ()

end FX.Metatheory
