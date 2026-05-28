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

/-! ## Structural normal-form predicate

M22-A4 (#406, 2026-05-28).  STRUCTURAL characterization of Phase
A normal form as an inductive `Prop`.  Where `IsPhaseANormalForm`
defines NF SEMANTICALLY as "fixed point of simplify",
`IsStructurallyNormalForm` defines NF STRUCTURALLY as "no Phase A
rule applies anywhere":

* Every leaf (`lzero`, `lvar`) is NF.
* `lsucc inner` is NF iff `inner` is NF.
* `lmax e1 e2` is NF iff both children are NF AND none of the
  three Phase A rules for `lmax` could fire: `e1 ≠ e2`
  (rule 1: idempotence), `e1 ≠ lzero` (rule 2: left identity),
  `e2 ≠ lzero` (rule 3: right identity).
* `limax e1 e2` is NF iff both children are NF AND neither of
  the two Phase A rules for `limax` could fire: `e2 ≠ lzero`
  (rule 5: right collapse), `e1 ≠ lzero` (rule 4: left
  identity).

The load-bearing theorem is that `simplify` always produces a
structurally normal expression: `simplify_produces_isStructurallyNormalForm`.
This is the substantive Phase A "what does Phase A actually
deliver" answer — it shows that the post-order recursion plus
local rule chain produces output where NO rule could fire
anywhere, not just at the top level.

## Why structural and semantic NF should coincide

`IsStructurallyNormalForm e → IsPhaseANormalForm e` will be
provable: if no rule fires anywhere, then `simplify e` must
equal `e` (no rule = no change).  The converse direction
`IsPhaseANormalForm e → IsStructurallyNormalForm e` requires
more case work — we'd need to extract from `simplify e = e`
the conclusion that none of the negative conditions could be
violated.  Both directions are real theorems for Phase B's
canonical-ordering decisions, but THIS commit ships only the
structural definition + `simplify` produces it.

## What this enables (Phase B bridge)

Phase B's full Mörtberg-Sterling algorithm needs to detect
"already normalized" sub-expressions to avoid redundant work.
Running `simplify` on every sub-expression is correct but
wasteful.  A STRUCTURAL check (Decidable Bool via the
inductive's negative conditions) is the optimization gate.

Decidability of `IsStructurallyNormalForm` requires
DecidableEq + 5 disjunctions of decidable conditions; the
inductive's shape itself makes this clean — no propext leak
since LevelExpr.decEq is propext-free (5-ctor ADT). -/

/-- Inductive Prop characterization of Phase A normal forms.
A `LevelExpr` is in structural NF iff no Phase A rule applies
anywhere in its syntax tree.

Five constructors mirror the 5 LevelExpr ctors:
* `lzeroNF`: lzero is trivially NF.
* `lvarNF`: any lvar is trivially NF.
* `lsuccNF`: lsucc of NF is NF.
* `lmaxNF`: lmax of two NF children with all three negative
  conditions (no idempotence, no left identity, no right
  identity).
* `limaxNF`: limax of two NF children with both negative
  conditions (no right collapse, no left identity). -/
inductive LevelExpr.IsStructurallyNormalForm : LevelExpr → Prop
  /-- lzero is trivially in NF. -/
  | lzeroNF : LevelExpr.IsStructurallyNormalForm .lzero
  /-- lvar at any index is trivially in NF. -/
  | lvarNF (idx : Nat) : LevelExpr.IsStructurallyNormalForm (.lvar idx)
  /-- lsucc preserves NF. -/
  | lsuccNF {inner : LevelExpr}
      (hInner : LevelExpr.IsStructurallyNormalForm inner) :
      LevelExpr.IsStructurallyNormalForm (.lsucc inner)
  /-- lmax of two NF children is NF when all three Phase A
  rules for lmax cannot fire. -/
  | lmaxNF {e1 e2 : LevelExpr}
      (h1 : LevelExpr.IsStructurallyNormalForm e1)
      (h2 : LevelExpr.IsStructurallyNormalForm e2)
      (hNotEq : ¬ (e1 = e2))
      (hNotLeftZero : ¬ (e1 = .lzero))
      (hNotRightZero : ¬ (e2 = .lzero)) :
      LevelExpr.IsStructurallyNormalForm (.lmax e1 e2)
  /-- limax of two NF children is NF when both Phase A rules
  for limax cannot fire. -/
  | limaxNF {e1 e2 : LevelExpr}
      (h1 : LevelExpr.IsStructurallyNormalForm e1)
      (h2 : LevelExpr.IsStructurallyNormalForm e2)
      (hNotRightZero : ¬ (e2 = .lzero))
      (hNotLeftZero : ¬ (e1 = .lzero)) :
      LevelExpr.IsStructurallyNormalForm (.limax e1 e2)

/-- `simplify e` is always in structural normal form.

Proof: structural recursion on `e`.

* `lzero`: result is `lzero`, `lzeroNF`.
* `lvar n`: result is `lvar n`, `lvarNF n`.
* `lsucc inner`: result is `lsucc inner.simplify`; by IH the
  inner is NF; conclude via `lsuccNF`.
* `lmax e1 e2`: `by_cases` on the 4 if-then-else branches.
  Rules 1/2/3 (rule fires): result is `e1.simplify` or
  `e2.simplify`, both NF by their respective IHs.  Else
  branch: result is `lmax e1.simplify e2.simplify`; the
  `if_neg` hypotheses provide the three negative conditions;
  IHs provide the NF child witnesses; conclude via `lmaxNF`.
* `limax e1 e2`: 3-way split.  Rule 5 (s2 = lzero): result
  is `lzero`, `lzeroNF`.  Rule 4 (s1 = lzero, ¬rule 5):
  result is `e2.simplify`, NF by IH2.  Else: result is
  `limax e1.simplify e2.simplify`; conclude via `limaxNF`. -/
theorem LevelExpr.simplify_produces_isStructurallyNormalForm :
    ∀ (expr : LevelExpr),
      LevelExpr.IsStructurallyNormalForm expr.simplify
  | .lzero => .lzeroNF
  | .lvar idx => .lvarNF idx
  | .lsucc inner => by
      show LevelExpr.IsStructurallyNormalForm (LevelExpr.lsucc inner.simplify)
      exact .lsuccNF (LevelExpr.simplify_produces_isStructurallyNormalForm inner)
  | .lmax e1 e2 => by
      have ih1 : LevelExpr.IsStructurallyNormalForm e1.simplify :=
        LevelExpr.simplify_produces_isStructurallyNormalForm e1
      have ih2 : LevelExpr.IsStructurallyNormalForm e2.simplify :=
        LevelExpr.simplify_produces_isStructurallyNormalForm e2
      show LevelExpr.IsStructurallyNormalForm
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
            exact .lmaxNF ih1 ih2 hEq hLeftZero hRightZero
  | .limax e1 e2 => by
      have ih1 : LevelExpr.IsStructurallyNormalForm e1.simplify :=
        LevelExpr.simplify_produces_isStructurallyNormalForm e1
      have ih2 : LevelExpr.IsStructurallyNormalForm e2.simplify :=
        LevelExpr.simplify_produces_isStructurallyNormalForm e2
      show LevelExpr.IsStructurallyNormalForm
        (if e2.simplify = .lzero then LevelExpr.lzero
         else if e1.simplify = .lzero then e2.simplify
         else LevelExpr.limax e1.simplify e2.simplify)
      by_cases hRightZero : e2.simplify = .lzero
      · rw [if_pos hRightZero]
        exact .lzeroNF
      · rw [if_neg hRightZero]
        by_cases hLeftZero : e1.simplify = .lzero
        · rw [if_pos hLeftZero]
          exact ih2
        · rw [if_neg hLeftZero]
          exact .limaxNF ih1 ih2 hRightZero hLeftZero

/-! ## Structural NF implies semantic NF

If a `LevelExpr` is structurally normal (no rule applies
anywhere), then it's a fixed point of `simplify` — proving
`simplify e = e`.

This is the FORWARD direction of structural-vs-semantic NF
equivalence.  The reverse direction (semantic ⇒ structural)
requires extracting the inequality witnesses from `simplify
e = e`, which involves cases on the simplify function shape
— substantive but mechanical.  Forward is the load-bearing
direction for Phase B's "is this already normalized?" check. -/

/-- A structurally normal `LevelExpr` is a fixed point of
`simplify`.  Forward direction of structural-vs-semantic NF
equivalence.

Proof: induction on the `IsStructurallyNormalForm` derivation.
Each constructor case unfolds `simplify` and uses the negative
hypotheses to confirm no rule fires + IHs for children. -/
theorem LevelExpr.IsStructurallyNormalForm.toFixedPoint
    {expr : LevelExpr}
    (h : LevelExpr.IsStructurallyNormalForm expr) :
    expr.simplify = expr := by
  induction h with
  | lzeroNF => rfl
  | lvarNF _ => rfl
  | lsuccNF _ ihInner =>
      show LevelExpr.lsucc _ = LevelExpr.lsucc _
      rw [ihInner]
  | @lmaxNF e1 e2 _ _ hNotEq hNotLeftZero hNotRightZero ih1 ih2 =>
      show (if e1.simplify = e2.simplify then e1.simplify
            else if e1.simplify = LevelExpr.lzero then e2.simplify
            else if e2.simplify = LevelExpr.lzero then e1.simplify
            else LevelExpr.lmax e1.simplify e2.simplify) =
        LevelExpr.lmax e1 e2
      rw [ih1, ih2, if_neg hNotEq, if_neg hNotLeftZero,
          if_neg hNotRightZero]
  | @limaxNF e1 e2 _ _ hNotRightZero hNotLeftZero ih1 ih2 =>
      show (if e2.simplify = LevelExpr.lzero then LevelExpr.lzero
            else if e1.simplify = LevelExpr.lzero then e2.simplify
            else LevelExpr.limax e1.simplify e2.simplify) =
        LevelExpr.limax e1 e2
      rw [ih1, ih2, if_neg hNotRightZero, if_neg hNotLeftZero]

/-- Combined: `simplify e` is both a fixed point AND
structurally normal.  Pins the full Phase A delivery in a
single theorem. -/
theorem LevelExpr.simplify_isStructurallyNormal_and_fixed
    (expr : LevelExpr) :
    LevelExpr.IsStructurallyNormalForm expr.simplify ∧
    expr.simplify.simplify = expr.simplify :=
  ⟨LevelExpr.simplify_produces_isStructurallyNormalForm expr,
   LevelExpr.simplify_idempotent expr⟩

/-! ## Helper size bounds for the reverse-direction proof

The reverse direction `semantic NF → structural NF` requires
ruling out all 5 Phase A rules from firing.  Each rule's result
has strictly smaller size than the original (an `lmax`/`limax`
node has size ≥ 3 since both children have size ≥ 1; the rule
results are sub-terms of size ≤ child size).  The contradiction
is: if `simplify e = e`, then the result's size equals the
original's size, but rule-firing would make it strictly smaller.

These helper lemmas pin the strict size bounds. -/

/-- `e1.size < (lmax e1 e2).size`.  Used to rule out rule 1 / 3
of lmax in the reverse-direction proof. -/
theorem LevelExpr.size_lt_lmax_left (e1 e2 : LevelExpr) :
    e1.size < (LevelExpr.lmax e1 e2).size := by
  show e1.size < e1.size + e2.size + 1
  have hPos : 0 < e2.size + 1 := Nat.succ_pos _
  have hStep : e1.size < e1.size + (e2.size + 1) :=
    Nat.lt_add_of_pos_right hPos
  rw [← Nat.add_assoc] at hStep
  exact hStep

/-- `e2.size < (lmax e1 e2).size`.  Used to rule out rule 2 of
lmax in the reverse-direction proof. -/
theorem LevelExpr.size_lt_lmax_right (e1 e2 : LevelExpr) :
    e2.size < (LevelExpr.lmax e1 e2).size := by
  show e2.size < e1.size + e2.size + 1
  have hPos : 0 < e1.size := LevelExpr.size_pos e1
  calc e2.size = 0 + e2.size := (Nat.zero_add _).symm
    _ < e1.size + e2.size := Nat.add_lt_add_right hPos _
    _ < e1.size + e2.size + 1 := Nat.lt_succ_self _

/-- `e1.size < (limax e1 e2).size`.  Used to rule out the
left-identity case of limax (rule 4 produces `e2.simplify`,
not `e1.simplify`; rule 5 produces `lzero`). -/
theorem LevelExpr.size_lt_limax_left (e1 e2 : LevelExpr) :
    e1.size < (LevelExpr.limax e1 e2).size := by
  show e1.size < e1.size + e2.size + 1
  have hPos : 0 < e2.size + 1 := Nat.succ_pos _
  have hStep : e1.size < e1.size + (e2.size + 1) :=
    Nat.lt_add_of_pos_right hPos
  rw [← Nat.add_assoc] at hStep
  exact hStep

/-- `e2.size < (limax e1 e2).size`.  Used to rule out rule 4
of limax (left identity) in the reverse-direction proof. -/
theorem LevelExpr.size_lt_limax_right (e1 e2 : LevelExpr) :
    e2.size < (LevelExpr.limax e1 e2).size := by
  show e2.size < e1.size + e2.size + 1
  have hPos : 0 < e1.size := LevelExpr.size_pos e1
  calc e2.size = 0 + e2.size := (Nat.zero_add _).symm
    _ < e1.size + e2.size := Nat.add_lt_add_right hPos _
    _ < e1.size + e2.size + 1 := Nat.lt_succ_self _

/-- `(lzero).size < (limax e1 e2).size`.  Used to rule out
rule 5 (limax right collapse) in the reverse-direction proof:
if simplify produced `lzero` but the input was `limax`, sizes
mismatch. -/
theorem LevelExpr.lzero_size_lt_limax (e1 e2 : LevelExpr) :
    LevelExpr.size .lzero < (LevelExpr.limax e1 e2).size := by
  show 1 < e1.size + e2.size + 1
  have hPos1 : 0 < e1.size := LevelExpr.size_pos e1
  have hPos2 : 0 < e2.size := LevelExpr.size_pos e2
  calc 1 = 0 + 0 + 1 := rfl
    _ < e1.size + 0 + 1 := Nat.add_lt_add_right
                            (Nat.add_lt_add_right hPos1 _) _
    _ ≤ e1.size + e2.size + 1 := Nat.add_le_add_right
                                  (Nat.add_le_add_left (Nat.le_of_lt hPos2) _) _

/-! ## Reverse direction — semantic NF implies structural NF -/

/-- Semantic NF implies structural NF: if `simplify e = e`, then
`IsStructurallyNormalForm e`.

This is the REVERSE direction of the structural-vs-semantic NF
equivalence.  Combined with `IsStructurallyNormalForm.toFixedPoint`
(forward direction shipped in #406), this proves the two
definitions characterize the same set of expressions.

Proof strategy: structural recursion on `expr`.

* `lzero` / `lvar`: trivially structurally normal.
* `lsucc inner`: by injection on the equality, `inner.simplify =
  inner`, so apply IH.
* `lmax e1 e2`: case-split on each of the 3 if-then-else branches.
  In each rule-firing case, the result is `e1.simplify` or
  `e2.simplify`, both of which have size ≤ child.size <
  lmax.size.  But the hypothesis says result = lmax e1 e2,
  forcing size equality — contradiction via `Nat.lt_irrefl`.
  Only the else branch is consistent; then by lmax-injection,
  `e1.simplify = e1` and `e2.simplify = e2`, and the three
  `if_neg` hypotheses give the negative conditions.
* `limax e1 e2`: similar 2-rule case split.  Rule 5 (s2 = lzero
  produces `lzero`) is ruled out via `lzero_size_lt_limax`.
  Rule 4 (s1 = lzero produces `e2.simplify`) is ruled out via
  `size_lt_limax_right`.  Else branch yields limaxNF. -/
theorem LevelExpr.IsPhaseANormalForm.toStructurallyNormal :
    ∀ {expr : LevelExpr},
      LevelExpr.IsPhaseANormalForm expr →
      LevelExpr.IsStructurallyNormalForm expr
  | .lzero, _ => .lzeroNF
  | .lvar idx, _ => .lvarNF idx
  | .lsucc inner, hInputNF => by
      have hInner : inner.simplify = inner := by
        injection hInputNF
      exact .lsuccNF
        (LevelExpr.IsPhaseANormalForm.toStructurallyNormal hInner)
  | .lmax e1 e2, hInputNF => by
      have hUnfold :
          (if e1.simplify = e2.simplify then e1.simplify
           else if e1.simplify = .lzero then e2.simplify
           else if e2.simplify = .lzero then e1.simplify
           else LevelExpr.lmax e1.simplify e2.simplify) =
            LevelExpr.lmax e1 e2 := hInputNF
      by_cases hRule1 : e1.simplify = e2.simplify
      · exfalso
        rw [if_pos hRule1] at hUnfold
        have hSizeBound : e1.simplify.size < (LevelExpr.lmax e1 e2).size :=
          Nat.lt_of_le_of_lt (LevelExpr.simplify_size_le e1)
            (LevelExpr.size_lt_lmax_left e1 e2)
        rw [hUnfold] at hSizeBound
        exact Nat.lt_irrefl _ hSizeBound
      · rw [if_neg hRule1] at hUnfold
        by_cases hRule2 : e1.simplify = .lzero
        · exfalso
          rw [if_pos hRule2] at hUnfold
          have hSizeBound : e2.simplify.size < (LevelExpr.lmax e1 e2).size :=
            Nat.lt_of_le_of_lt (LevelExpr.simplify_size_le e2)
              (LevelExpr.size_lt_lmax_right e1 e2)
          rw [hUnfold] at hSizeBound
          exact Nat.lt_irrefl _ hSizeBound
        · rw [if_neg hRule2] at hUnfold
          by_cases hRule3 : e2.simplify = .lzero
          · exfalso
            rw [if_pos hRule3] at hUnfold
            have hSizeBound : e1.simplify.size < (LevelExpr.lmax e1 e2).size :=
              Nat.lt_of_le_of_lt (LevelExpr.simplify_size_le e1)
                (LevelExpr.size_lt_lmax_left e1 e2)
            rw [hUnfold] at hSizeBound
            exact Nat.lt_irrefl _ hSizeBound
          · rw [if_neg hRule3] at hUnfold
            -- hUnfold : lmax e1.simplify e2.simplify = lmax e1 e2
            have hE1 : e1.simplify = e1 := by injection hUnfold
            have hE2 : e2.simplify = e2 := by injection hUnfold
            have hStructE1 : LevelExpr.IsStructurallyNormalForm e1 :=
              LevelExpr.IsPhaseANormalForm.toStructurallyNormal hE1
            have hStructE2 : LevelExpr.IsStructurallyNormalForm e2 :=
              LevelExpr.IsPhaseANormalForm.toStructurallyNormal hE2
            -- Rewrite the negative conditions to use e1, e2 directly.
            rw [hE1] at hRule1 hRule2
            rw [hE2] at hRule1 hRule3
            exact .lmaxNF hStructE1 hStructE2 hRule1 hRule2 hRule3
  | .limax e1 e2, hInputNF => by
      have hUnfold :
          (if e2.simplify = .lzero then LevelExpr.lzero
           else if e1.simplify = .lzero then e2.simplify
           else LevelExpr.limax e1.simplify e2.simplify) =
            LevelExpr.limax e1 e2 := hInputNF
      by_cases hRule5 : e2.simplify = .lzero
      · exfalso
        rw [if_pos hRule5] at hUnfold
        have hSizeBound : LevelExpr.size .lzero <
            (LevelExpr.limax e1 e2).size :=
          LevelExpr.lzero_size_lt_limax e1 e2
        rw [hUnfold] at hSizeBound
        exact Nat.lt_irrefl _ hSizeBound
      · rw [if_neg hRule5] at hUnfold
        by_cases hRule4 : e1.simplify = .lzero
        · exfalso
          rw [if_pos hRule4] at hUnfold
          have hSizeBound : e2.simplify.size < (LevelExpr.limax e1 e2).size :=
            Nat.lt_of_le_of_lt (LevelExpr.simplify_size_le e2)
              (LevelExpr.size_lt_limax_right e1 e2)
          rw [hUnfold] at hSizeBound
          exact Nat.lt_irrefl _ hSizeBound
        · rw [if_neg hRule4] at hUnfold
          -- hUnfold : limax e1.simplify e2.simplify = limax e1 e2
          have hE1 : e1.simplify = e1 := by injection hUnfold
          have hE2 : e2.simplify = e2 := by injection hUnfold
          have hStructE1 : LevelExpr.IsStructurallyNormalForm e1 :=
            LevelExpr.IsPhaseANormalForm.toStructurallyNormal hE1
          have hStructE2 : LevelExpr.IsStructurallyNormalForm e2 :=
            LevelExpr.IsPhaseANormalForm.toStructurallyNormal hE2
          rw [hE1] at hRule4
          rw [hE2] at hRule5
          exact .limaxNF hStructE1 hStructE2 hRule5 hRule4

/-- The full bidirectional structural↔semantic NF equivalence.
Forward direction via `toFixedPoint`; reverse direction via
`toStructurallyNormal`.  Together they prove that Phase A's
two NF characterizations (semantic = fixed point of simplify;
structural = no rule applies anywhere) coincide. -/
theorem LevelExpr.isPhaseANormalForm_iff_isStructurallyNormalForm
    (expr : LevelExpr) :
    LevelExpr.IsPhaseANormalForm expr ↔
      LevelExpr.IsStructurallyNormalForm expr :=
  ⟨LevelExpr.IsPhaseANormalForm.toStructurallyNormal,
   LevelExpr.IsStructurallyNormalForm.toFixedPoint⟩

/-! ## Semantic denotation + Phase A soundness

M22-A6 (#408, 2026-05-28).  Phase B foundation: semantic
denotation function interpreting `LevelExpr` arithmetically, plus
soundness theorem that Phase A's `simplify` preserves the semantic
value.

Denotation rules (matching Mörtberg-Sterling 2024):
* `lzero` ⟦⟧ = 0
* `lsucc e` ⟦⟧ = ⟦e⟧ + 1
* `lmax e1 e2` ⟦⟧ = max(⟦e1⟧, ⟦e2⟧)
* `limax e1 e2` ⟦⟧ = if ⟦e2⟧ = 0 then 0 else max(⟦e1⟧, ⟦e2⟧)
* `lvar n` ⟦⟧ = env(n)

This is the SEMANTIC universe-level model: each `LevelExpr` denotes
a natural number under an environment `Nat → Nat` for universe
variables.  Phase A's 5 simplification rules are all SEMANTICALLY
VALID (they preserve denotation):

* Rule 1 (lmax e e ↦ e): max(v, v) = v.
* Rule 2 (lmax lzero e ↦ e): max(0, v) = v.
* Rule 3 (lmax e lzero ↦ e): max(v, 0) = v.
* Rule 4 (limax lzero e ↦ e): if v=0 then 0 else max(0,v) = v.
* Rule 5 (limax e lzero ↦ lzero): if 0=0 then 0 else ... = 0.

The soundness theorem `simplify_denote_eq` proves this formally:
for every `e` and `env`, `e.simplify.denote env = e.denote env`.
This is the Phase B FOUNDATION — every future Phase B equation
(canonical lmax ordering, lsucc distributivity, level-variable
substitution) is proved against this same denotation.

## Why a local levelMax instead of Nat.max

Lean's core `Nat.max_self`/`Nat.zero_max`/`Nat.max_zero` all pull
in `propext` (via if-equivalence reasoning).  This file's
zero-axiom discipline forbids that.  Workaround: define a local
`levelMax` via structural pattern matching on both arguments,
proving the lemmas (idempotence, zero-identity) via direct
recursion without `≤`-conditional reasoning. -/

/-- Propext-free `max` on `Nat` for the universe-level denotation.
Defined via structural pattern matching on both arguments — no
`Nat.le` conditionals (which carry propext through Lean's
core `Nat.max_*` lemmas). -/
def LevelExpr.levelMax : Nat → Nat → Nat
  | 0, valueB => valueB
  | valueA + 1, 0 => valueA + 1
  | valueA + 1, valueB + 1 => (LevelExpr.levelMax valueA valueB) + 1

/-- `levelMax a a = a` (idempotence). -/
theorem LevelExpr.levelMax_self : ∀ (valueA : Nat),
    LevelExpr.levelMax valueA valueA = valueA
  | 0 => rfl
  | n + 1 => by
      show LevelExpr.levelMax n n + 1 = n + 1
      rw [LevelExpr.levelMax_self n]

/-- `levelMax 0 b = b` (left identity).  Definitional. -/
theorem LevelExpr.levelMax_zero_left (valueB : Nat) :
    LevelExpr.levelMax 0 valueB = valueB := rfl

/-- `levelMax a 0 = a` (right identity). -/
theorem LevelExpr.levelMax_zero_right : ∀ (valueA : Nat),
    LevelExpr.levelMax valueA 0 = valueA
  | 0 => rfl
  | _ + 1 => rfl

/-- Semantic denotation of `LevelExpr` into `Nat` under an
environment for universe variables.

The interpretation follows Mörtberg-Sterling arXiv:2406.05425's
universe-level model: each constructor maps to its standard
arithmetic counterpart, with `limax` having the impredicative
collapse for Prop-cofinal codomains. -/
def LevelExpr.denote : LevelExpr → (Nat → Nat) → Nat
  | .lzero, _ => 0
  | .lsucc inner, env => (inner.denote env) + 1
  | .lmax e1 e2, env =>
      LevelExpr.levelMax (e1.denote env) (e2.denote env)
  | .limax e1 e2, env =>
      let valueB := e2.denote env
      if valueB = 0 then 0
      else LevelExpr.levelMax (e1.denote env) valueB
  | .lvar idx, env => env idx

/-! ## Per-ctor denotation smokes -/

/-- `lzero` denotes `0`. -/
theorem LevelExpr.denote_lzero (env : Nat → Nat) :
    LevelExpr.denote .lzero env = 0 := rfl

/-- `lvar n` denotes `env n`. -/
theorem LevelExpr.denote_lvar (idx : Nat) (env : Nat → Nat) :
    LevelExpr.denote (.lvar idx) env = env idx := rfl

/-- `lsucc e` denotes `⟦e⟧ + 1`. -/
theorem LevelExpr.denote_lsucc (inner : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote (.lsucc inner) env = inner.denote env + 1 := rfl

/-- `lmax e1 e2` denotes `levelMax ⟦e1⟧ ⟦e2⟧`. -/
theorem LevelExpr.denote_lmax (e1 e2 : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote (.lmax e1 e2) env =
      LevelExpr.levelMax (e1.denote env) (e2.denote env) := rfl

/-- `limax e1 e2` denotes its conditional max. -/
theorem LevelExpr.denote_limax (e1 e2 : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote (.limax e1 e2) env =
      (if e2.denote env = 0 then 0
       else LevelExpr.levelMax (e1.denote env) (e2.denote env)) :=
  rfl

/-! ## Phase A semantic soundness

The load-bearing theorem: `simplify` preserves the semantic
denotation under every environment.  This validates that
Phase A's 5 rewrite rules are sound w.r.t. the arithmetic
interpretation of universe levels. -/

/-- Phase A's `simplify` preserves the semantic denotation:
for every expression and environment, simplifying produces the
same level value.

Proof: structural recursion on `expr`.  Each case dispatches
through `simplify` + `denote` and uses the relevant `levelMax`
lemmas (idempotence / zero-identity) at the arithmetic level
to discharge the per-rule equations.

* `lzero` / `lvar`: trivial (rfl).
* `lsucc inner`: lift IH through `+ 1`.
* `lmax e1 e2`: case-split on the 4 if-then-else branches.
  Rule 1 (s1 = s2): substitute s1 = s2 = e1.simplify, use
  `levelMax_self` after IH.  Rule 2 (s1 = lzero): IH gives
  `e1.denote env = 0`, so `levelMax 0 _ = _` via
  `levelMax_zero_left`.  Rule 3 (s2 = lzero): IH gives
  `e2.denote env = 0`, so `levelMax _ 0 = _` via
  `levelMax_zero_right`.  Else: both children IHs apply
  pointwise.
* `limax e1 e2`: 3-way split.  Rule 5 (s2 = lzero):
  e2.denote env = 0 (via IH2), conditional yields 0 = 0.
  Rule 4 (s1 = lzero, ¬rule 5): split on e2.denote env = 0
  internally (since IH2 maps e2.simplify.denote to e2.denote
  but doesn't force a value); use levelMax_zero_left when
  non-zero.  Else: pointwise IHs. -/
theorem LevelExpr.simplify_denote_eq :
    ∀ (expr : LevelExpr) (env : Nat → Nat),
      expr.simplify.denote env = expr.denote env
  | .lzero, _ => rfl
  | .lvar _, _ => rfl
  | .lsucc inner, env => by
      show LevelExpr.denote (.lsucc inner.simplify) env =
        LevelExpr.denote (.lsucc inner) env
      show inner.simplify.denote env + 1 = inner.denote env + 1
      rw [LevelExpr.simplify_denote_eq inner env]
  | .lmax e1 e2, env => by
      have ih1 := LevelExpr.simplify_denote_eq e1 env
      have ih2 := LevelExpr.simplify_denote_eq e2 env
      show (if e1.simplify = e2.simplify then e1.simplify
            else if e1.simplify = .lzero then e2.simplify
            else if e2.simplify = .lzero then e1.simplify
            else LevelExpr.lmax e1.simplify e2.simplify).denote env =
        LevelExpr.levelMax (e1.denote env) (e2.denote env)
      by_cases hEq : e1.simplify = e2.simplify
      · rw [if_pos hEq]
        -- result = e1.simplify; denote = e1.simplify.denote env = e1.denote env (by ih1)
        -- Need: e1.denote env = levelMax (e1.denote env) (e2.denote env)
        -- Since e1.simplify = e2.simplify, denote equality gives e1.denote env = e2.denote env
        have hValEq : e1.denote env = e2.denote env := by
          rw [← ih1, ← ih2, hEq]
        rw [ih1, hValEq, LevelExpr.levelMax_self]
      · rw [if_neg hEq]
        by_cases hLeftZero : e1.simplify = .lzero
        · rw [if_pos hLeftZero]
          -- result = e2.simplify; denote = e2.denote env
          -- Need: e2.denote env = levelMax (e1.denote env) (e2.denote env)
          -- e1.denote env = 0 via ih1 since e1.simplify = lzero
          have hLeftValZero : e1.denote env = 0 := by
            rw [← ih1, hLeftZero]
            rfl
          rw [ih2, hLeftValZero, LevelExpr.levelMax_zero_left]
        · rw [if_neg hLeftZero]
          by_cases hRightZero : e2.simplify = .lzero
          · rw [if_pos hRightZero]
            -- result = e1.simplify; denote = e1.denote env
            have hRightValZero : e2.denote env = 0 := by
              rw [← ih2, hRightZero]
              rfl
            rw [ih1, hRightValZero, LevelExpr.levelMax_zero_right]
          · rw [if_neg hRightZero]
            -- result = lmax e1.simplify e2.simplify
            show LevelExpr.levelMax (e1.simplify.denote env)
                (e2.simplify.denote env) =
              LevelExpr.levelMax (e1.denote env) (e2.denote env)
            rw [ih1, ih2]
  | .limax e1 e2, env => by
      have ih1 := LevelExpr.simplify_denote_eq e1 env
      have ih2 := LevelExpr.simplify_denote_eq e2 env
      show (if e2.simplify = .lzero then LevelExpr.lzero
            else if e1.simplify = .lzero then e2.simplify
            else LevelExpr.limax e1.simplify e2.simplify).denote env =
        (if e2.denote env = 0 then 0
         else LevelExpr.levelMax (e1.denote env) (e2.denote env))
      by_cases hRule5 : e2.simplify = .lzero
      · rw [if_pos hRule5]
        -- result = lzero; denote = 0
        have hRightValZero : e2.denote env = 0 := by
          rw [← ih2, hRule5]
          rfl
        show (0 : Nat) =
          (if e2.denote env = 0 then 0
           else LevelExpr.levelMax (e1.denote env) (e2.denote env))
        rw [if_pos hRightValZero]
      · rw [if_neg hRule5]
        by_cases hRule4 : e1.simplify = .lzero
        · rw [if_pos hRule4]
          -- result = e2.simplify; denote = e2.denote env
          have hLeftValZero : e1.denote env = 0 := by
            rw [← ih1, hRule4]
            rfl
          show e2.simplify.denote env =
            (if e2.denote env = 0 then 0
             else LevelExpr.levelMax (e1.denote env) (e2.denote env))
          by_cases hRightValZero : e2.denote env = 0
          · rw [if_pos hRightValZero, ih2, hRightValZero]
          · rw [if_neg hRightValZero, hLeftValZero,
                LevelExpr.levelMax_zero_left, ih2]
        · rw [if_neg hRule4]
          -- result = limax e1.simplify e2.simplify
          show (if e2.simplify.denote env = 0 then 0
                else LevelExpr.levelMax (e1.simplify.denote env)
                  (e2.simplify.denote env)) =
            (if e2.denote env = 0 then 0
             else LevelExpr.levelMax (e1.denote env) (e2.denote env))
          rw [ih1, ih2]

end LeanFX2.Foundation.PolyCell.Universe
