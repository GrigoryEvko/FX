import FX.Kernel.Typing
import FX.Kernel.Reduction

/-!
# Progress — kernel metatheory stub

Per `fx_design.md` §27.4 and §31.  **Theorem statement only — no
proof.**

## Statement

Every closed, well-typed term is either a canonical form (a
`type`, `pi`, `sigma`, `lam`, `ind`, `ctor`, `id`, or `quot`) or
can take a head-reduction step.

Formally:

```
∀ (term expectedType : Term) (globalEnv : GlobalEnv),
  Term.check (TypingContext.empty) term expectedType globalEnv = .ok () →
  isCanonical term ∨ (Term.betaStep? term).isSome
```

Where `isCanonical` distinguishes head-values from reducible
applications.

## Scope notes

  * "Closed" means empty `TypingContext` — the standard
    formulation.  Open terms with free variables satisfy a
    progress variant that reduces to the var itself as a neutral.
  * `neutral` / `stuck` forms (free var in head position under
    applications / eliminators) are a separate category that
    Progress over open terms must account for.  Our canonical
    Progress for closed terms doesn't need them.
  * The kernel's `coind` is a stub — progress over codata is
    the `Coind-ν` unfolding rule in a later phase.
-/

namespace FX.Metatheory

open FX.Kernel

/-- Predicate: `term` is a canonical head-value.  Mirrors the
    "values don't reduce further" side of progress.  Kept as a
    stub — the real metatheory layer will define the full
    canonical-form relation via strict-positivity-respecting
    cases. -/
def isCanonical : Term → Bool
  | .type _                  => true
  | .forallLevel _           => true
  | .pi _ _ _ _              => true
  | .sigma _ _ _             => true
  | .lam _ _ _               => true
  | .ind _ _                 => true
  | .ctor _ _ _ _            => true
  | .id _ _ _                => true
  | .refl _                  => true
  | .quot _ _                => true
  | .quotMk _ _              => true
  | .coind _ _               => true
  | _                        => false

/-- Closed well-typed terms either are canonical or can reduce.

    Unproved.  The proof proceeds by inversion on the typing
    derivation: each syntactic form is either inherently
    canonical or has its head pattern-matched by `betaStep?`
    into a reduct. -/
def Progress : Prop :=
  ∀ (term expectedType : Term) (globalEnv : GlobalEnv),
    Term.check (TypingContext.empty) term expectedType globalEnv = .ok () →
    isCanonical term = true ∨ (Term.betaStep? term).isSome

end FX.Metatheory
