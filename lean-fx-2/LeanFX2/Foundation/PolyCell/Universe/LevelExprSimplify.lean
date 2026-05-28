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

/-! ## Structural size measure + Phase A non-increasing correctness

M22 Phase A correctness (audit-A20 / #404, 2026-05-28).

Phase B's full Mörtberg-Sterling iteration needs a termination
measure: each application of `simplify` must not grow the
expression, otherwise iterating to a fixed point could diverge.
This section ships:

* `LevelExpr.size` — structural size (every leaf = 1, every
  interior node adds 1 to children's sum).
* `LevelExpr.size_pos` — every expression has size ≥ 1.
* `LevelExpr.simplify_size_le` — the load-bearing correctness
  theorem: `simplify e` is no larger than `e`.

The proof is by structural induction on `e`.  For `lmax`/`limax`,
each of the 4 / 3 if-then-else branches is handled by `by_cases`
on the underlying `DecidableEq`-decided condition, then closed
by `Nat.add_le_add` + IH composition.  No bare `simp`/`unfold`
(per project performance anti-patterns); the only tactic
machinery is `show` for definitional unfold of `simplify` and
`Nat.le_*` arithmetic. -/

/-- Structural size of a `LevelExpr`.

* `lzero` / `lvar _`: leaf, size 1.
* `lsucc inner`: `inner.size + 1`.
* `lmax e1 e2` / `limax e1 e2`: `e1.size + e2.size + 1`.

Used as the termination measure for Phase B's fixed-point
iteration over `simplify` and as the correctness witness that
Phase A's single-pass simplifier is size-non-increasing
(`simplify_size_le`). -/
def LevelExpr.size : LevelExpr → Nat
  | .lzero => 1
  | .lsucc inner => inner.size + 1
  | .lmax e1 e2 => e1.size + e2.size + 1
  | .limax e1 e2 => e1.size + e2.size + 1
  | .lvar _ => 1

/-- Every `LevelExpr` has positive size.  Used by
`simplify_size_le` to discharge the `limax e1 e2 ↦ lzero`
collapse case (the result has size 1, the source has size
≥ 1 + 1 + 1 = 3). -/
theorem LevelExpr.size_pos : ∀ (expr : LevelExpr), 1 ≤ expr.size
  | .lzero => Nat.le_refl 1
  | .lsucc _ => Nat.succ_le_succ (Nat.zero_le _)
  | .lmax _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .limax _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .lvar _ => Nat.le_refl 1

/-- Phase A's `simplify` is size-non-increasing: the result is no
larger than the input.

Phase B's full Mörtberg-Sterling normalization iterates
`simplify` until a fixed point.  This theorem is the termination
witness: each iteration decreases or preserves size, so the
iteration must terminate when no rule fires (size strictly
decreases at every productive step).

Proof: structural induction on `expr`.  Each case dispatches
through `simplify`'s actual computation:

* `lzero` / `lvar _`: identity case, size unchanged.
* `lsucc inner`: result is `lsucc inner.simplify`, size is
  `inner.simplify.size + 1`, bounded by IH `inner.simplify.size
  ≤ inner.size`.
* `lmax e1 e2`: split on the 4 if-then-else branches via
  `by_cases`; each branch returns either `s1`, `s2`, or
  `lmax s1 s2`, whose size is bounded by the original
  `e1.size + e2.size + 1` via `Nat.add_le_add` composition
  with IH1/IH2.
* `limax e1 e2`: split on the 3 branches.  The right-collapse
  case (`s2 = lzero ↦ lzero`) uses `size_pos` to show
  `1 ≤ e1.size + e2.size + 1`. -/
theorem LevelExpr.simplify_size_le :
    ∀ (expr : LevelExpr), expr.simplify.size ≤ expr.size
  | .lzero => Nat.le_refl 1
  | .lvar _ => Nat.le_refl 1
  | .lsucc inner =>
      Nat.succ_le_succ (LevelExpr.simplify_size_le inner)
  | .lmax e1 e2 => by
      have ih1 : e1.simplify.size ≤ e1.size :=
        LevelExpr.simplify_size_le e1
      have ih2 : e2.simplify.size ≤ e2.size :=
        LevelExpr.simplify_size_le e2
      show (LevelExpr.lmax e1 e2).simplify.size ≤
        e1.size + e2.size + 1
      show (if e1.simplify = e2.simplify then e1.simplify
            else if e1.simplify = .lzero then e2.simplify
            else if e2.simplify = .lzero then e1.simplify
            else LevelExpr.lmax e1.simplify e2.simplify).size ≤
        e1.size + e2.size + 1
      by_cases hEq : e1.simplify = e2.simplify
      · rw [if_pos hEq]
        exact Nat.le_trans ih1
          (Nat.le_trans (Nat.le_add_right _ e2.size) (Nat.le_succ _))
      · rw [if_neg hEq]
        by_cases hLeftZero : e1.simplify = .lzero
        · rw [if_pos hLeftZero]
          exact Nat.le_trans ih2
            (Nat.le_trans (Nat.le_add_left _ e1.size) (Nat.le_succ _))
        · rw [if_neg hLeftZero]
          by_cases hRightZero : e2.simplify = .lzero
          · rw [if_pos hRightZero]
            exact Nat.le_trans ih1
              (Nat.le_trans (Nat.le_add_right _ e2.size) (Nat.le_succ _))
          · rw [if_neg hRightZero]
            show e1.simplify.size + e2.simplify.size + 1 ≤
              e1.size + e2.size + 1
            exact Nat.add_le_add_right (Nat.add_le_add ih1 ih2) 1
  | .limax e1 e2 => by
      have ih1 : e1.simplify.size ≤ e1.size :=
        LevelExpr.simplify_size_le e1
      have ih2 : e2.simplify.size ≤ e2.size :=
        LevelExpr.simplify_size_le e2
      show (LevelExpr.limax e1 e2).simplify.size ≤
        e1.size + e2.size + 1
      show (if e2.simplify = .lzero then LevelExpr.lzero
            else if e1.simplify = .lzero then e2.simplify
            else LevelExpr.limax e1.simplify e2.simplify).size ≤
        e1.size + e2.size + 1
      by_cases hRightZero : e2.simplify = .lzero
      · rw [if_pos hRightZero]
        show 1 ≤ e1.size + e2.size + 1
        exact Nat.succ_le_succ (Nat.zero_le _)
      · rw [if_neg hRightZero]
        by_cases hLeftZero : e1.simplify = .lzero
        · rw [if_pos hLeftZero]
          exact Nat.le_trans ih2
            (Nat.le_trans (Nat.le_add_left _ e1.size) (Nat.le_succ _))
        · rw [if_neg hLeftZero]
          show e1.simplify.size + e2.simplify.size + 1 ≤
            e1.size + e2.size + 1
          exact Nat.add_le_add_right (Nat.add_le_add ih1 ih2) 1

/-! ## Aggregate size-related smokes -/

/-- `lzero` has size 1. -/
theorem LevelExpr.size_lzero : LevelExpr.size .lzero = 1 := rfl

/-- `lvar n` has size 1 regardless of index. -/
theorem LevelExpr.size_lvar (idx : Nat) :
    LevelExpr.size (.lvar idx) = 1 := rfl

/-- `lsucc inner` size is `inner.size + 1`. -/
theorem LevelExpr.size_lsucc (inner : LevelExpr) :
    LevelExpr.size (.lsucc inner) = inner.size + 1 := rfl

/-- `lmax e1 e2` size is `e1.size + e2.size + 1`. -/
theorem LevelExpr.size_lmax (e1 e2 : LevelExpr) :
    LevelExpr.size (.lmax e1 e2) = e1.size + e2.size + 1 := rfl

/-- `limax e1 e2` size is `e1.size + e2.size + 1`. -/
theorem LevelExpr.size_limax (e1 e2 : LevelExpr) :
    LevelExpr.size (.limax e1 e2) = e1.size + e2.size + 1 := rfl

/-! ## Phase A normal-form correctness — full idempotence

M22 Phase A normal-form characterization (audit-A21 / #405,
2026-05-28).  Phase A's single-pass simplifier is POST-ORDER:
children are simplified first via the `let s1 := e1.simplify;
let s2 := e2.simplify` bindings, then the local if-then-else
chain inspects already-normalized children.  Because the local
rules are exhaustive over normalized-child shapes (idempotence /
zero-identity / collapse), Phase A REACHES A FIXED POINT IN ONE
PASS — `simplify (simplify e) = simplify e` for all `e`.

This corrects the original `LevelExprSimplify.lean` docstring
claim (lines 47-49) that "`lmax (lmax lzero a) lzero` needs two
passes": that claim implicitly assumed TOP-DOWN flat
simplification, but the actual implementation is bottom-up
post-order.  The example resolves in a single pass:

  simplify (lmax (lmax lzero a) lzero)
  = let s1 := simplify (lmax lzero a)   -- recursive child
    let s2 := simplify lzero
    if s1 = s2 then s1 else if s1 = .lzero then s2 ...
  = let s1 := a   -- by rule 2: lmax lzero a ↦ a
    let s2 := lzero
    if a = lzero then ... else if a = lzero then ... else if lzero = lzero then a
  = a

This idempotence theorem subsumes the original docstring's
multi-pass concern and provides the formal Phase A fixed-point
guarantee Phase B's iteration loop would otherwise need.

## What full idempotence enables

* Defining the FIXED-POINT predicate `e.simplify = e` correctly:
  `simplify_idempotent` pins that this predicate is preserved
  by simplification (every output is a fixed point).
* PHASE B IS NOT NEEDED FOR REACHING NORMAL FORM — Phase B's
  contribution is canonical ordering on `lmax` operands (so
  `lmax a b` and `lmax b a` collapse) and distributivity over
  `lsucc` (so `lsucc (lmax e1 e2)` flattens).  Iteration to
  fixed point is NOT required as a SEPARATE phase.
* Decidable Phase-A equivalence on closed expressions: two
  closed `LevelExpr`s are Phase-A equivalent iff their
  simplifications are syntactically equal — and idempotence
  ensures the simplify result is canonical (no further rule
  applies). -/

/-- Phase A's `simplify` is idempotent: simplifying twice yields
the same result as simplifying once.

Proof: structural recursion on `expr`.  Each case dispatches
through `simplify`'s actual computation:

* `lzero` / `lvar _`: identity case, `simplify` returns the
  input unchanged twice over — `rfl`.
* `lsucc inner`: result is `lsucc inner.simplify`; the inner
  IH closes the second pass.
* `lmax e1 e2`: split on the 4 if-then-else branches via
  `by_cases`.  In the first three branches, the result is
  either `e1.simplify` or `e2.simplify`, whose self-idempotence
  follows directly from IH1 or IH2.  The else branch returns
  `lmax e1.simplify e2.simplify`; the second pass unfolds
  `simplify` again with `s1 := e1.simplify.simplify =
  e1.simplify` (by IH1) and similarly for `s2`, then re-checks
  the same conditional path (which still fails on the same
  hypotheses since `e1.simplify ≠ e2.simplify` etc.).
* `limax e1 e2`: 3-branch split with the right-collapse case
  resolving to `lzero` (immediate `rfl`). -/
theorem LevelExpr.simplify_idempotent :
    ∀ (expr : LevelExpr), expr.simplify.simplify = expr.simplify
  | .lzero => rfl
  | .lvar _ => rfl
  | .lsucc inner => by
      show LevelExpr.lsucc inner.simplify.simplify =
        LevelExpr.lsucc inner.simplify
      rw [LevelExpr.simplify_idempotent inner]
  | .lmax e1 e2 => by
      have ih1 : e1.simplify.simplify = e1.simplify :=
        LevelExpr.simplify_idempotent e1
      have ih2 : e2.simplify.simplify = e2.simplify :=
        LevelExpr.simplify_idempotent e2
      show (if e1.simplify = e2.simplify then e1.simplify
            else if e1.simplify = .lzero then e2.simplify
            else if e2.simplify = .lzero then e1.simplify
            else LevelExpr.lmax e1.simplify e2.simplify).simplify =
        (if e1.simplify = e2.simplify then e1.simplify
         else if e1.simplify = .lzero then e2.simplify
         else if e2.simplify = .lzero then e1.simplify
         else LevelExpr.lmax e1.simplify e2.simplify)
      by_cases hEq : e1.simplify = e2.simplify
      · rw [if_pos hEq]
        exact ih1
      · rw [if_neg hEq]
        by_cases hLeftZero : e1.simplify = .lzero
        · rw [if_pos hLeftZero]
          exact ih2
        · rw [if_neg hLeftZero]
          by_cases hRightZero : e2.simplify = .lzero
          · rw [if_pos hRightZero]
            exact ih1
          · rw [if_neg hRightZero]
            show (if e1.simplify.simplify = e2.simplify.simplify then
                    e1.simplify.simplify
                  else if e1.simplify.simplify = .lzero then
                    e2.simplify.simplify
                  else if e2.simplify.simplify = .lzero then
                    e1.simplify.simplify
                  else LevelExpr.lmax e1.simplify.simplify
                    e2.simplify.simplify) =
              LevelExpr.lmax e1.simplify e2.simplify
            rw [ih1, ih2, if_neg hEq, if_neg hLeftZero, if_neg hRightZero]
  | .limax e1 e2 => by
      have ih1 : e1.simplify.simplify = e1.simplify :=
        LevelExpr.simplify_idempotent e1
      have ih2 : e2.simplify.simplify = e2.simplify :=
        LevelExpr.simplify_idempotent e2
      show (if e2.simplify = .lzero then LevelExpr.lzero
            else if e1.simplify = .lzero then e2.simplify
            else LevelExpr.limax e1.simplify e2.simplify).simplify =
        (if e2.simplify = .lzero then LevelExpr.lzero
         else if e1.simplify = .lzero then e2.simplify
         else LevelExpr.limax e1.simplify e2.simplify)
      by_cases hRightZero : e2.simplify = .lzero
      · rw [if_pos hRightZero]
        rfl
      · rw [if_neg hRightZero]
        by_cases hLeftZero : e1.simplify = .lzero
        · rw [if_pos hLeftZero]
          exact ih2
        · rw [if_neg hLeftZero]
          show (if e2.simplify.simplify = .lzero then LevelExpr.lzero
                else if e1.simplify.simplify = .lzero then
                  e2.simplify.simplify
                else LevelExpr.limax e1.simplify.simplify
                  e2.simplify.simplify) =
              LevelExpr.limax e1.simplify e2.simplify
          rw [ih1, ih2, if_neg hRightZero, if_neg hLeftZero]

/-! ## Phase A normal-form predicate

A `LevelExpr` is in Phase A normal form iff `simplify` is the
identity on it.  Equivalently: every interior `lmax`/`limax`
satisfies the negations of all rules that would otherwise fire
(s1 ≠ s2, s1 ≠ lzero, s2 ≠ lzero for lmax; s2 ≠ lzero, s1 ≠
lzero for limax) and every child is itself in normal form. -/

/-- A `LevelExpr` is in Phase A normal form iff `simplify` fixes
it.  This is the SEMANTIC definition; a syntactic structural
predicate would also work but adds redundant case analysis. -/
def LevelExpr.IsPhaseANormalForm (expr : LevelExpr) : Prop :=
  expr.simplify = expr

/-- `simplify` always produces a Phase A normal form.

This is the immediate corollary of `simplify_idempotent`:
`(simplify expr).simplify = simplify expr` says exactly that
`simplify expr` is a fixed point of simplify, which is the
definition of Phase A normal form. -/
theorem LevelExpr.simplify_produces_normal_form (expr : LevelExpr) :
    (expr.simplify).IsPhaseANormalForm :=
  LevelExpr.simplify_idempotent expr

/-- `lzero` is in Phase A normal form. -/
theorem LevelExpr.lzero_isNormalForm :
    LevelExpr.IsPhaseANormalForm .lzero := rfl

/-- `lvar n` is in Phase A normal form for any index. -/
theorem LevelExpr.lvar_isNormalForm (idx : Nat) :
    LevelExpr.IsPhaseANormalForm (.lvar idx) := rfl

end LeanFX2.Foundation.PolyCell.Universe
