import FX.Kernel.Typing

/-!
# Consistency — kernel metatheory stub

Per `fx_design.md` §27.4 and §31.  **Theorem statement only — no
proof.**

## Statement

No closed term has type `∀ (P : Type<0>). P` — the universal
quantifier.  Equivalently: the kernel-as-logic is consistent; no
proof of False (encoded as `∀ P. P`) exists.

Formally:

```
¬ ∃ (witness : Term) (globalEnv : GlobalEnv),
  Term.check (TypingContext.empty) witness
    (Term.pi Grade.default (Term.type .zero) (Term.var 0))
    globalEnv = .ok ()
```

## Why it matters

Consistency is the load-bearing meta-theorem for FX's
"verification works" claim.  Every `sorry`-free, `axiom`-free
program whose typing check succeeds corresponds to a genuine
proof of its declared postconditions.  If consistency fails
(some witness inhabits False), every postcondition vacuously
holds and the type-check is worthless.

## Proof path

Consistency follows from two lemmas:

  1. **Strong normalization** (`FX.Metatheory.Normalization`) —
     every well-typed term reduces to a normal form.
  2. **Canonicity** — the only closed normal form of type
     `∀ P, P` would have to be a `lam` whose body is a closed
     normal form of type `P` under `P : Type<0>`, which by
     inversion must itself be canonical.  Case analysis over
     closed canonical forms of universally-quantified types
     yields contradiction.

Both steps are standard for pure MLTT-style calculi.  The
graded extension (§6.3) doesn't interfere with the pure-type
reasoning — grades are either erased (usage 0) or preserved
through subsumption, neither introducing new value
inhabitations.
-/

namespace FX.Metatheory

open FX.Kernel

/-- No closed term inhabits the universal type `∀ P : Type<0>, P`.

    Unproved.  Proven via Normalization + Canonicity in the
    full metatheory layer. -/
def Consistency : Prop :=
  ¬ ∃ (witness : Term) (globalEnv : GlobalEnv),
    Term.check (TypingContext.empty) witness
      (Term.pi Grade.default (Term.type .zero) (Term.var 0) Effect.tot)
      globalEnv = .ok ()

end FX.Metatheory
