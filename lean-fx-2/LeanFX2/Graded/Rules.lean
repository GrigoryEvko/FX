import LeanFX2.Graded.Ctx
import LeanFX2.Term

/-! # Graded/Rules — graded typing rules

Implements the graded MLTT calculus per `fx_design.md` §6.2:

* **Var**: `Γ, x :_r A |- x : A` with grade `r` at position `x`,
  zero everywhere else
* **App**: `Γ |-_p1 f : (x :_r A) → B    Γ |-_p2 a : A` →
          `Γ |-_(p1 + r * p2) f a : B[a/x]`
* **Lam (Wood/Atkey 2022, corrected)**: `Γ/p, x :_r A |-_1 b : B` →
                                        `Γ |-_p (fn(x) => b) : (x :_r A) → B`
* **Let**: `Γ |-_p1 e : A    Γ, x :_r A |-_p2 body : B` →
           `Γ |-_(r * p1 + p2) (let x = e; body) : B`
* **If**: join is worst-case grade across branches
* **Subsumption**: weaken grade `r ≤ s`

## Why Wood/Atkey context division

Atkey 2018's Lam rule was UNSOUND — allowed linear variables to be
captured in unrestricted closures (use multiple times).  The
canonical witness:

```
fn higher_order(f: i64 -> i64) : i64 -> i64 = fn(x) => f(f(x))
```

Wood/Atkey 2022 fixed this with **context division**.  In the rule
above, `Γ/p` divides every binding's grade by `p` (the result
lambda's grade).  For usage semiring's `1/ω = 0`, linearly-graded
captured variables become unavailable (grade 0) when capturing
into a replicable (ω-graded) closure.

## Modality interaction (Layer 6 + 7)

`fx_design.md` §6.3.1: a modality `m₁ ⤳ m₂` scales the grade
vector when crossing modal boundaries.  E.g., `▶` (Later) modality
might force every grade to 0 inside `▶ A` (gradients suspended).

```lean
def Modality.scale (modality : Modality m₁ m₂) (gv : GradeVector dims) : GradeVector dims := ...
```

Captured at the type-level: `Term.modIntro` uses `Modality.scale`
on the inner term's grade vector.

## Dependencies

* `Graded/Ctx.lean`
* `Term.lean`

## Downstream

* `Algo/Check.lean` — bidirectional checker uses graded rules
* `Algo/Soundness.lean` — soundness theorem against graded rules

## Implementation plan (Phase 8)

1. State each typing rule as a Prop / inductive case
2. Verify Wood-Atkey context division with usage semiring instance
3. Smoke: Atkey 2018 witness rejected (linear-double-use term)
4. Smoke: canonical linear/affine examples typecheck

Target: ~400 lines.
-/

namespace LeanFX2.Graded

-- TODO Phase 8: WellTyped predicate or graded Term inductive
-- TODO Phase 8: each typing rule as case
-- TODO Phase 8: Wood-Atkey context division application
-- TODO Phase 8: modality scale rule

end LeanFX2.Graded
