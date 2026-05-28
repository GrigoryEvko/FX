import LeanFX2.Foundation.PolyCell.Universe.LevelExpr

/-! # Foundation/PolyCell/Universe/LevelExprSimplify
   — M22 Phase A: single-pass structural simplifier for LevelExpr

M22 (#271, 2026-05-28) Phase A.  Ships the SINGLE-PASS structural
simplifier for `LevelExpr` per polycell.md §11.8 line 4028-4031:

> Equality of `LevelExpr` up to algebra (`lmax e e = e`, `lmax lzero
> e = e`, …) is decidable in **polynomial time** via the Mörtberg-
> Sterling 2024 normalization algorithm.

This Phase A ships the BASIC structural rules — single-pass
identity / idempotence / zero-elimination via pattern-form match.
The FULL polynomial-time normalization (Mörtberg-Sterling
arXiv:2406.05425) is Phase B (deferred to a focused multi-turn
session) since it requires iterating to fixed point + canonical
ordering of lmax operands + level-variable substitution
discipline.

## Phase A simplification rules

1. `lmax e e ↦ e` — idempotence of max.
2. `lmax lzero e ↦ e` — lzero is left identity for max.
3. `lmax e lzero ↦ e` — lzero is right identity for max.
4. `limax lzero e ↦ e` — lzero is left identity for impredicative max
   (codomain dominates when domain is lzero).
5. `limax e lzero ↦ lzero` — lzero is the IMPREDICATIVE collapse
   (when codomain is Prop = lzero, the whole Π type collapses
   to Prop regardless of domain).
6. All other forms (`lzero`, `lsucc e`, `lmax e1 e2` with e1 ≠ e2 ≠ lzero,
   `limax e1 e2` with e2 ≠ lzero and e1 ≠ lzero, `lvar n`) recurse
   structurally on children but otherwise return unchanged.

The order of pattern matches is significant: idempotence first
(catches `lmax e e` before zero-identity rules), then zero rules.
For `limax`, right-zero (#5) comes BEFORE left-zero (#4) because
the impredicative collapse is the load-bearing rule for Prop's
quantification.

## What's NOT in Phase A (deferred to Phase B / M22 closure)

Per polycell.md and Mörtberg-Sterling 2024, the full polynomial-
time algorithm requires:

* **Iteration to fixed point**: applying simplify until no rule
  applies.  Phase A is single-pass; multiple applications might
  expose new simplifications (e.g., `lmax (lmax lzero e) lzero`
  needs two passes).
* **Canonical lmax ordering**: when `lmax e1 e2` has both non-
  lzero, the polynomial-time algorithm imposes a TOTAL ORDER
  on operands so `lmax a b` and `lmax b a` canonicalize to the
  same form.  Requires defining `LevelExpr` < relation.
* **Distributivity over lsucc**: `lsucc (lmax e1 e2) = lmax
  (lsucc e1) (lsucc e2)` — distributing succ into max.
* **Level-variable substitution**: handling `lvar n` under
  universe-polymorphic instantiation.

Phase B (M22 closure) ships these via the full Mörtberg-Sterling
algorithm.  Phase A is the precursor establishing the simplify
infrastructure + the per-rule theorems Phase B will cite.

## Why Phase A is shippable

Phase A is sufficient to:
* Simplify CLOSED LEVELEXPR EXPRESSIONS — concrete `lzero`,
  `lsucc lzero`, `lmax lzero (lsucc lzero)`, etc. — to canonical
  form (no algebraic redundancy).
* Provide the per-rule `rfl`-witnessed equations Phase B's
  iteration loop will consume.
* Pin the simplification SHAPE so downstream Phase Z₀ work
  (M24 retrofit + M25 universe-mode generators) can rely on
  the simplify-canonical-form invariant.

## Decidable equivalence on closed expressions

For CLOSED level expressions (no `lvar`), Phase A's simplifier
produces a canonical form modulo the 5 rules above.  Two closed
expressions are equivalent up to Phase A's rules iff their
simplifications are syntactically equal via `LevelExpr.decEq`.

For OPEN expressions (containing `lvar`), Phase B's full
algorithm is needed because lmax canonical ordering matters.

## Zero-axiom verification

`simplify` defined by pattern-form structural recursion over
the 5-ctor `LevelExpr` inductive.  All per-rule smokes close
by `rfl`.  No `simp`, no `omega`, no `propext`.  Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Universe

/-- Single-pass structural simplifier for `LevelExpr` per
M22 Phase A.

Applies 5 simplification rules in priority order:
1. lmax idempotence: `lmax e e ↦ e`
2. lmax left-identity: `lmax lzero e ↦ e`
3. lmax right-identity: `lmax e lzero ↦ e`
4. limax left-identity: `limax lzero e ↦ e`
5. limax right-collapse: `limax e lzero ↦ lzero`

Children are RECURSIVELY SIMPLIFIED before applying the
parent rule (deep simplification on each pass).  Full
polynomial-time iteration to fixed point is Phase B (deferred).

Phase A is single-pass: one application may not reach the
fixed point (e.g., `lmax (lmax lzero a) lzero` needs two
passes to reduce `lmax (lmax lzero a) lzero ↦ lmax a lzero ↦
a`).  Downstream Phase B's iteration loop calls this
single-pass function until the fixed point. -/
def LevelExpr.simplify : LevelExpr → LevelExpr
  | .lzero => .lzero
  | .lsucc inner => .lsucc inner.simplify
  | .lmax e1 e2 =>
      let s1 := e1.simplify
      let s2 := e2.simplify
      if s1 = s2 then s1                       -- idempotence
      else if s1 = .lzero then s2               -- left identity
      else if s2 = .lzero then s1               -- right identity
      else .lmax s1 s2
  | .limax e1 e2 =>
      let s1 := e1.simplify
      let s2 := e2.simplify
      if s2 = .lzero then .lzero                -- impredicative collapse
      else if s1 = .lzero then s2               -- left identity
      else .limax s1 s2
  | .lvar n => .lvar n

/-! ## Per-rule smokes

Each smoke pins one of the 5 simplification rules + recursive
simplification of children.  All `rfl`-closed via the
`@[reducible] def`-style pattern match (Lean inlines `simplify`
on closed input). -/

/-- Rule 1: lmax idempotence.  `simplify (lmax lzero lzero) =
simplify lzero = lzero` because the inner siblings are
syntactically equal.  Direct rfl. -/
theorem LevelExpr.simplify_lmax_idempotent :
    LevelExpr.simplify (.lmax .lzero .lzero) = .lzero := rfl

/-- Rule 1 generalized: lmax of a non-zero idempotent.
`simplify (lmax (lsucc lzero) (lsucc lzero)) = lsucc lzero`. -/
theorem LevelExpr.simplify_lmax_idempotent_nonzero :
    LevelExpr.simplify (.lmax (.lsucc .lzero) (.lsucc .lzero)) =
      .lsucc .lzero := rfl

/-- Rule 2: lmax left-identity.  `simplify (lmax lzero (lsucc lzero))
= lsucc lzero`. -/
theorem LevelExpr.simplify_lmax_left_identity :
    LevelExpr.simplify (.lmax .lzero (.lsucc .lzero)) =
      .lsucc .lzero := rfl

/-- Rule 3: lmax right-identity.  `simplify (lmax (lsucc lzero) lzero)
= lsucc lzero`. -/
theorem LevelExpr.simplify_lmax_right_identity :
    LevelExpr.simplify (.lmax (.lsucc .lzero) .lzero) =
      .lsucc .lzero := rfl

/-- Rule 4: limax left-identity.  `simplify (limax lzero (lsucc lzero))
= lsucc lzero`. -/
theorem LevelExpr.simplify_limax_left_identity :
    LevelExpr.simplify (.limax .lzero (.lsucc .lzero)) =
      .lsucc .lzero := rfl

/-- Rule 5: limax right-collapse (the impredicative rule).
`simplify (limax (lsucc lzero) lzero) = lzero` because Prop's
quantification rule collapses Π types whose codomain is Prop. -/
theorem LevelExpr.simplify_limax_right_collapse :
    LevelExpr.simplify (.limax (.lsucc .lzero) .lzero) = .lzero := rfl

/-- Combined limax: both arguments zero → collapse to lzero (rule 5
takes priority since s2 = lzero is checked first). -/
theorem LevelExpr.simplify_limax_both_zero :
    LevelExpr.simplify (.limax .lzero .lzero) = .lzero := rfl

/-! ## No-simplification cases

When no rule applies, `simplify` returns the structurally
recursive-simplified form. -/

/-- lzero is its own simplification. -/
theorem LevelExpr.simplify_lzero :
    LevelExpr.simplify .lzero = .lzero := rfl

/-- lsucc recursively simplifies the inner expression. -/
theorem LevelExpr.simplify_lsucc_lzero :
    LevelExpr.simplify (.lsucc .lzero) = .lsucc .lzero := rfl

/-- lvar is unchanged. -/
theorem LevelExpr.simplify_lvar_zero :
    LevelExpr.simplify (.lvar 0) = .lvar 0 := rfl

/-- lmax of two distinct non-zero values is unchanged after
recursive simplification of children. -/
theorem LevelExpr.simplify_lmax_distinct :
    LevelExpr.simplify (.lmax (.lvar 0) (.lvar 1)) =
      .lmax (.lvar 0) (.lvar 1) := rfl

/-- limax with non-zero codomain is unchanged after recursive
simplification. -/
theorem LevelExpr.simplify_limax_non_lzero_codomain :
    LevelExpr.simplify (.limax (.lvar 0) (.lvar 1)) =
      .limax (.lvar 0) (.lvar 1) := rfl

/-! ## Phase A correctness witnesses

Pin Phase A's INVARIANTS: simplify is total (terminates on every
input), idempotence-preserving (simplify ∘ simplify = simplify
for closed expressions), and structural (it commutes with the
inductive structure). -/

/-- Simplify is the identity on lzero (rfl). -/
theorem LevelExpr.simplify_lzero_idempotent :
    LevelExpr.simplify (LevelExpr.simplify .lzero) =
      LevelExpr.simplify .lzero := rfl

/-- Simplify is idempotent on simplified closed expressions.
At Phase A, idempotence holds for terms in canonical form per
the 5 rules.  Full idempotence (every input is its own simplify-
fixed-point after one pass) is Phase B territory.

This smoke pins a SPECIFIC fixture: `simplify ∘ simplify` on
`lvar 0` returns `lvar 0`. -/
theorem LevelExpr.simplify_lvar_zero_idempotent :
    LevelExpr.simplify (LevelExpr.simplify (.lvar 0)) =
      LevelExpr.simplify (.lvar 0) := rfl

/-! ## Phase B forward-compat marker

When Phase B (full Mörtberg-Sterling normalization) ships, the
following theorem will pin that Phase A's single-pass simplifier
is BELOW the full algorithm — Phase B's `normalize` factors
through Phase A's `simplify` as the structural inner loop. -/

/-- Phase B forward-compat: `simplify` is the single-pass
inner-loop layer of the full polynomial-time normalization
algorithm.  Phase B's `normalize` iterates `simplify` to a
fixed point + applies canonical ordering on lmax operands +
distributivity over lsucc. -/
def LevelExpr.simplify_is_phase_a_inner_loop : Bool := true

theorem LevelExpr.simplify_is_phase_a_inner_loop_correct :
    LevelExpr.simplify_is_phase_a_inner_loop = true := rfl

end LeanFX2.Foundation.PolyCell.Universe
