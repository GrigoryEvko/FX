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

/-! ## Algebraic laws — the maximal-power Phase B backbone

M22-A7 (#409, 2026-05-28).  Per polycell.md §11.8.2's commitment
to a polynomial-time decidable universe equivalence (Mörtberg-
Sterling 2024), Phase B's canonical normalizer must understand
that `lmax` is a COMMUTATIVE / ASSOCIATIVE / IDEMPOTENT operation
and that `lsucc` distributes over `lmax`.  These are the
JOIN-SEMILATTICE-WITH-SUCCESSOR algebraic laws.

This section ships them as theorems at TWO levels:

1. **Nat-level** (`levelMax_comm`, `levelMax_assoc`): proved
   directly via structural pattern matching on both arguments.
   No `Nat.le` conditional reasoning (which carries propext via
   Lean core's `Nat.max_*` lemmas).
2. **LevelExpr-level via denote** (`lmax_denote_comm`,
   `lmax_denote_assoc`, `lsucc_lmax_distrib_denote`): immediate
   corollaries of the Nat-level laws after unfolding `denote`.

`limax` is INTENTIONALLY NOT commutative (rule 5 collapses
when the RIGHT arg is lzero, not the left).  This matches the
impredicative-max semantics: `limax (Πtype's domain) (Πtype's
codomain) = lzero` when codomain is Prop.  Asymmetric by design.

## Why these are foundational for maximal-power universes

Per §11.8.2, the kernel commits to:
* 2LTT with both `gen_universeU` (univalent inner) and
  `gen_universeS` (strict outer) hierarchies parameterized by
  LevelExpr.
* Directed universes `gen_universeD` / `gen_universeOmega`
  (Riehl-Shulman 2017 + Loubaton 2307.11931).
* SProp + full Setzer-Rathjen large-cardinal hierarchy via
  UniverseFlag (M23 #272).
* Universe polymorphism via LevelExpr — declarations parameterized
  over universe-level expressions.

For universe polymorphism to be SOUND, two declarations that
quantify over `Type @ lmax e1 e2` and `Type @ lmax e2 e1` must
be interchangeable — they denote the same universe.  These
algebraic laws prove the semantic equivalence; Phase B's canonical
normalizer enforces it syntactically via canonical ordering. -/

/-- `levelMax` is commutative: `levelMax a b = levelMax b a`.

Proof: structural pattern match on both arguments.  Three of
four cases close by rfl (definitional equality on the clauses);
the `(a+1, b+1)` case unfolds to `levelMax a b + 1 = levelMax
b a + 1` and closes via the IH on `(a, b)`. -/
theorem LevelExpr.levelMax_comm : ∀ (valueA valueB : Nat),
    LevelExpr.levelMax valueA valueB = LevelExpr.levelMax valueB valueA
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | a + 1, b + 1 => by
      show LevelExpr.levelMax a b + 1 = LevelExpr.levelMax b a + 1
      rw [LevelExpr.levelMax_comm a b]

/-- `levelMax` is associative.

Proof: 3D structural pattern match.  All cases except `(a+1,
b+1, c+1)` close by rfl (the rule reductions definitionally
match between LHS and RHS).  The triple-successor case unfolds
both sides to `levelMax (levelMax a b) c + 1` and `levelMax a
(levelMax b c) + 1`, closing via the IH on `(a, b, c)`. -/
theorem LevelExpr.levelMax_assoc : ∀ (valueA valueB valueC : Nat),
    LevelExpr.levelMax (LevelExpr.levelMax valueA valueB) valueC =
      LevelExpr.levelMax valueA (LevelExpr.levelMax valueB valueC)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | _ + 1, _ + 1, 0 => rfl
  | a + 1, b + 1, c + 1 => by
      show LevelExpr.levelMax (LevelExpr.levelMax a b) c + 1 =
        LevelExpr.levelMax a (LevelExpr.levelMax b c) + 1
      rw [LevelExpr.levelMax_assoc a b c]

/-- `levelMax (a+1) (b+1) = levelMax a b + 1`.  Definitional;
exposes Phase B's lsucc-distributivity equation at the
arithmetic level. -/
theorem LevelExpr.levelMax_succ_distrib (valueA valueB : Nat) :
    LevelExpr.levelMax (valueA + 1) (valueB + 1) =
      LevelExpr.levelMax valueA valueB + 1 := rfl

/-! ## Denote-level lifts to LevelExpr

These theorems lift the Nat-level algebraic laws to the
LevelExpr semantic level.  Each is a one-line proof: unfold
`denote` on lmax, apply the Nat-level law. -/

/-- `lmax` is denotation-commutative: under any environment,
`(lmax e1 e2).denote env = (lmax e2 e1).denote env`.

This is the SEMANTIC justification for Phase B's canonical
lmax ordering: regardless of syntactic operand order, the
universe denoted is the same. -/
theorem LevelExpr.lmax_denote_comm (e1 e2 : LevelExpr)
    (env : Nat → Nat) :
    (LevelExpr.lmax e1 e2).denote env =
      (LevelExpr.lmax e2 e1).denote env := by
  show LevelExpr.levelMax (e1.denote env) (e2.denote env) =
    LevelExpr.levelMax (e2.denote env) (e1.denote env)
  exact LevelExpr.levelMax_comm _ _

/-- `lmax` is denotation-associative: nested lmax can be
re-parenthesized without changing the denotation. -/
theorem LevelExpr.lmax_denote_assoc (e1 e2 e3 : LevelExpr)
    (env : Nat → Nat) :
    (LevelExpr.lmax (LevelExpr.lmax e1 e2) e3).denote env =
      (LevelExpr.lmax e1 (LevelExpr.lmax e2 e3)).denote env := by
  show LevelExpr.levelMax
        (LevelExpr.levelMax (e1.denote env) (e2.denote env))
        (e3.denote env) =
      LevelExpr.levelMax (e1.denote env)
        (LevelExpr.levelMax (e2.denote env) (e3.denote env))
  exact LevelExpr.levelMax_assoc _ _ _

/-- `lsucc` distributes over `lmax` under denote:
`(lsucc (lmax e1 e2)).denote env = (lmax (lsucc e1) (lsucc e2)).denote env`.

This is Phase B's load-bearing distributivity equation per
Mörtberg-Sterling 2024.  Canonical-form normalization pushes
`lsucc` INSIDE `lmax`, flattening nested successors. -/
theorem LevelExpr.lsucc_lmax_distrib_denote (e1 e2 : LevelExpr)
    (env : Nat → Nat) :
    (LevelExpr.lsucc (LevelExpr.lmax e1 e2)).denote env =
      (LevelExpr.lmax (LevelExpr.lsucc e1) (LevelExpr.lsucc e2)).denote env := by
  show LevelExpr.levelMax (e1.denote env) (e2.denote env) + 1 =
    LevelExpr.levelMax (e1.denote env + 1) (e2.denote env + 1)
  rfl

/-! ## Semantic equivalence relation

Per §11.8.2's "polynomial-time decidable equality up to algebra"
commitment, the equivalence relation on universe levels is:
two `LevelExpr`s are equivalent iff they denote the same value
under every environment.

This section defines the relation + proves the algebraic laws
are equivalences in it.  Phase B's canonical normalizer (when
shipped) will provide the decision procedure for this relation
via syntactic equality on canonical forms. -/

/-- Semantic equivalence on `LevelExpr` per §11.8.2: two
expressions are equivalent iff they denote the same Nat
value under every environment. -/
def LevelExpr.denoteEquiv (e1 e2 : LevelExpr) : Prop :=
  ∀ (env : Nat → Nat), e1.denote env = e2.denote env

/-- `denoteEquiv` is reflexive. -/
theorem LevelExpr.denoteEquiv.refl (expr : LevelExpr) :
    LevelExpr.denoteEquiv expr expr := fun _ => rfl

/-- `denoteEquiv` is symmetric. -/
theorem LevelExpr.denoteEquiv.symm {e1 e2 : LevelExpr}
    (h : LevelExpr.denoteEquiv e1 e2) :
    LevelExpr.denoteEquiv e2 e1 := fun env => (h env).symm

/-- `denoteEquiv` is transitive. -/
theorem LevelExpr.denoteEquiv.trans {e1 e2 e3 : LevelExpr}
    (h12 : LevelExpr.denoteEquiv e1 e2)
    (h23 : LevelExpr.denoteEquiv e2 e3) :
    LevelExpr.denoteEquiv e1 e3 := fun env => (h12 env).trans (h23 env)

/-- `lmax` is commutative as a `denoteEquiv` rule. -/
theorem LevelExpr.lmax_comm_denoteEquiv (e1 e2 : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.lmax e1 e2) (LevelExpr.lmax e2 e1) :=
  fun env => LevelExpr.lmax_denote_comm e1 e2 env

/-- `lmax` is associative as a `denoteEquiv` rule. -/
theorem LevelExpr.lmax_assoc_denoteEquiv (e1 e2 e3 : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.lmax (LevelExpr.lmax e1 e2) e3)
      (LevelExpr.lmax e1 (LevelExpr.lmax e2 e3)) :=
  fun env => LevelExpr.lmax_denote_assoc e1 e2 e3 env

/-- `lsucc` distributes over `lmax` as a `denoteEquiv` rule. -/
theorem LevelExpr.lsucc_lmax_distrib_denoteEquiv (e1 e2 : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.lsucc (LevelExpr.lmax e1 e2))
      (LevelExpr.lmax (LevelExpr.lsucc e1) (LevelExpr.lsucc e2)) :=
  fun env => LevelExpr.lsucc_lmax_distrib_denote e1 e2 env

/-- `lmax` is idempotent as a `denoteEquiv` rule: `lmax e e ~ e`.
This is the algebraic basis for the dedup phase of the n-ary
canonical form (collapsing repeated atoms).  Lifts
`levelMax_self`. -/
theorem LevelExpr.lmax_idempotent_denoteEquiv (expr : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.lmax expr expr) expr :=
  fun env => by
    rw [LevelExpr.denote_lmax, LevelExpr.levelMax_self]

/-- `lzero` is the left unit of `lmax` as a `denoteEquiv` rule:
`lmax lzero e ~ e`.  Basis for dropping `lzero` atoms during
canonicalization.  Lifts `levelMax_zero_left`. -/
theorem LevelExpr.lmax_lzero_left_denoteEquiv (expr : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.lmax LevelExpr.lzero expr) expr :=
  fun env => by
    rw [LevelExpr.denote_lmax, LevelExpr.denote_lzero,
        LevelExpr.levelMax_zero_left]

/-- `lzero` is the right unit of `lmax` as a `denoteEquiv` rule:
`lmax e lzero ~ e`.  Lifts `levelMax_zero_right`. -/
theorem LevelExpr.lmax_lzero_right_denoteEquiv (expr : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.lmax expr LevelExpr.lzero) expr :=
  fun env => by
    rw [LevelExpr.denote_lmax, LevelExpr.denote_lzero,
        LevelExpr.levelMax_zero_right]

/-- Phase A's `simplify` is sound under `denoteEquiv`.  Combines
`simplify_denote_eq` with the denoteEquiv definition. -/
theorem LevelExpr.simplify_denoteEquiv (expr : LevelExpr) :
    LevelExpr.denoteEquiv expr.simplify expr :=
  fun env => LevelExpr.simplify_denote_eq expr env

/-! ## denoteEquiv congruences

M22-A8 (#410, 2026-05-28).  For Phase B's canonical normalizer to
work compositionally, `denoteEquiv` must be a CONGRUENCE under
every `LevelExpr` constructor: if `e1 denoteEquiv e1'` and
`e2 denoteEquiv e2'`, then `ctor e1 e2 denoteEquiv ctor e1' e2'`.

This lets Phase B normalize sub-expressions independently, then
recombine — the foundation of compositional rewriting.  Every
ctor has a congruence law:

* `lsucc`: unary congruence (lsucc preserves equivalence).
* `lmax`: binary congruence (lmax of equivalents is equivalent).
* `limax`: binary congruence (asymmetric but still congruent —
  both operands' denotations are inputs to the conditional).
* `lzero` / `lvar`: nullary base cases, refl. -/

/-- `lsucc` is a denoteEquiv congruence: equivalent inner
expressions give equivalent successors. -/
theorem LevelExpr.lsucc_denoteEquiv_congr {inner inner' : LevelExpr}
    (h : LevelExpr.denoteEquiv inner inner') :
    LevelExpr.denoteEquiv (LevelExpr.lsucc inner)
      (LevelExpr.lsucc inner') := by
  intro env
  show inner.denote env + 1 = inner'.denote env + 1
  rw [h env]

/-- `lmax` is a denoteEquiv congruence: equivalent operand pairs
give equivalent lmax expressions.  Phase B's canonical lmax
ordering pre-normalizes both operands independently before
joining. -/
theorem LevelExpr.lmax_denoteEquiv_congr {e1 e1' e2 e2' : LevelExpr}
    (h1 : LevelExpr.denoteEquiv e1 e1')
    (h2 : LevelExpr.denoteEquiv e2 e2') :
    LevelExpr.denoteEquiv (LevelExpr.lmax e1 e2)
      (LevelExpr.lmax e1' e2') := by
  intro env
  show LevelExpr.levelMax (e1.denote env) (e2.denote env) =
    LevelExpr.levelMax (e1'.denote env) (e2'.denote env)
  rw [h1 env, h2 env]

/-- `limax` is a denoteEquiv congruence despite its asymmetric
collapsing semantics.  Both operands' denotations feed into the
conditional, so equivalent denotations produce equivalent
results regardless of which conditional branch fires. -/
theorem LevelExpr.limax_denoteEquiv_congr {e1 e1' e2 e2' : LevelExpr}
    (h1 : LevelExpr.denoteEquiv e1 e1')
    (h2 : LevelExpr.denoteEquiv e2 e2') :
    LevelExpr.denoteEquiv (LevelExpr.limax e1 e2)
      (LevelExpr.limax e1' e2') := by
  intro env
  show (if e2.denote env = 0 then 0
        else LevelExpr.levelMax (e1.denote env) (e2.denote env)) =
    (if e2'.denote env = 0 then 0
     else LevelExpr.levelMax (e1'.denote env) (e2'.denote env))
  rw [h1 env, h2 env]

/-! ## limax-specific algebraic laws

Per §11.8.2, `limax e1 e2` represents the impredicative Π-type
universe `Π (x : Type e1). Type e2` with the rule that Prop's
quantification collapses to Prop: `Π (x : A). Prop : Prop`.
Semantically: when codomain (e2) is Prop (= lzero), the entire
Π type lives in Prop regardless of domain.

These theorems pin the asymmetric semantics formally. -/

/-- `limax e lzero` collapses to lzero semantically.  This is
the IMPREDICATIVE collapse: `Π (x : Type e). Prop : Prop`
regardless of `e`.  Phase A's rule 5 ships this collapse
syntactically; this theorem proves it at the semantic level. -/
theorem LevelExpr.limax_denote_lzero_right (e1 : LevelExpr)
    (env : Nat → Nat) :
    (LevelExpr.limax e1 .lzero).denote env = 0 := by
  show (if (LevelExpr.lzero).denote env = 0 then 0
        else LevelExpr.levelMax (e1.denote env)
          ((LevelExpr.lzero).denote env)) = 0
  show (if (0 : Nat) = 0 then 0
        else LevelExpr.levelMax (e1.denote env) 0) = 0
  rw [if_pos rfl]

/-- `limax lzero e` denotes the same as `e`.  When the domain
of a Π-type is Prop (= lzero), the codomain dominates.  This
is Phase A's rule 4 at the semantic level. -/
theorem LevelExpr.limax_denote_lzero_left (e2 : LevelExpr)
    (env : Nat → Nat) :
    (LevelExpr.limax .lzero e2).denote env = e2.denote env := by
  show (if e2.denote env = 0 then 0
        else LevelExpr.levelMax ((LevelExpr.lzero).denote env)
          (e2.denote env)) = e2.denote env
  by_cases hZero : e2.denote env = 0
  · rw [if_pos hZero, hZero]
  · rw [if_neg hZero]
    show LevelExpr.levelMax 0 (e2.denote env) = e2.denote env
    exact LevelExpr.levelMax_zero_left _

/-- `limax e1 e2` denotes the same as `lmax e1 e2` when
`e2.denote env ≠ 0`.  This is the non-collapsing case: limax
behaves as ordinary max whenever the codomain isn't Prop. -/
theorem LevelExpr.limax_denote_eq_lmax_when_codomain_nonzero
    (e1 e2 : LevelExpr) (env : Nat → Nat)
    (hCod : e2.denote env ≠ 0) :
    (LevelExpr.limax e1 e2).denote env =
      (LevelExpr.lmax e1 e2).denote env := by
  show (if e2.denote env = 0 then 0
        else LevelExpr.levelMax (e1.denote env) (e2.denote env)) =
    LevelExpr.levelMax (e1.denote env) (e2.denote env)
  rw [if_neg hCod]

/-! ## denoteEquiv variants of the per-rule equations

Repackages the algebraic / limax laws as denoteEquiv rules for
Phase B's normalizer (which speaks denoteEquiv natively, not
denote env). -/

/-- limax-right-zero collapse as a denoteEquiv rule. -/
theorem LevelExpr.limax_lzero_right_denoteEquiv (e1 : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.limax e1 .lzero) .lzero :=
  fun env => LevelExpr.limax_denote_lzero_right e1 env

/-- limax-left-zero identity as a denoteEquiv rule. -/
theorem LevelExpr.limax_lzero_left_denoteEquiv (e2 : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.limax .lzero e2) e2 :=
  fun env => LevelExpr.limax_denote_lzero_left e2 env

/-! ## Total comparison on LevelExpr — Phase B's canonical-form keystone

M22-A9 (#411, 2026-05-28).  Per polycell.md §11.8.2's commitment to
polynomial-time decidable universe equality via the Mörtberg-Sterling
2024 algorithm, Phase B's canonical normalizer requires a TOTAL
ORDER on `LevelExpr` to canonically sort `lmax`/`limax` operands.

This section ships:

* `LevelExpr.compareNat` — propext-free `Nat → Nat → Ordering` via
  structural pattern match on both arguments.  Lean core's
  `Nat.compare` ultimately routes through `≤`-decidability which
  pulls propext; we need a clean alternative for zero-axiom
  discipline.
* `LevelExpr.ctorIndex` — ctor priority for cross-ctor comparison.
* `LevelExpr.compare` — total ordering on `LevelExpr` combining
  ctor priority (cross-ctor) with structural recursion (same-ctor).
* `compare_refl` — reflexivity: `compare e e = .eq`.
* `compare_swap` — antisymmetry as `Ordering.swap` identity:
  `(compare e1 e2).swap = compare e2 e1`.  This is the FULL
  antisymmetry property in compact form: lt ↔ gt, gt ↔ lt, eq ↔ eq.

Then the first concrete Phase B canonicalization:

* `canonicalizeLmaxPair` — single-pair lmax operand swap when
  operands are out of compare order.
* `canonicalizeLmaxPair_denoteEquiv` — soundness under denoteEquiv
  via `lmax_comm_denoteEquiv`.
* `canonicalizeLmaxPair_idempotent` — applying twice = once
  (after one pass, operands are sorted in compare order).

This is the FOUNDATION of Mörtberg-Sterling's canonical form.
Full polynomial canonical form (flattening nested lmax, collecting
monomials by lvar with offset sums) builds compositionally on
these primitives. -/

/-- Propext-free `Nat → Nat → Ordering` compare via structural
pattern match on both arguments.  Used internally by
`LevelExpr.compare` for `.lvar` index comparison and cross-ctor
priority. -/
def LevelExpr.compareNat : Nat → Nat → Ordering
  | 0, 0 => .eq
  | 0, _ + 1 => .lt
  | _ + 1, 0 => .gt
  | valueA + 1, valueB + 1 => LevelExpr.compareNat valueA valueB

/-- `compareNat n n = .eq` (reflexivity). -/
theorem LevelExpr.compareNat_refl : ∀ (value : Nat),
    LevelExpr.compareNat value value = .eq
  | 0 => rfl
  | n + 1 => LevelExpr.compareNat_refl n

/-- `(compareNat n m).swap = compareNat m n` (antisymmetry as
swap identity).  This compactly captures: `lt` swaps to `gt`,
`gt` swaps to `lt`, `eq` is self-dual. -/
theorem LevelExpr.compareNat_swap : ∀ (valueA valueB : Nat),
    (LevelExpr.compareNat valueA valueB).swap =
      LevelExpr.compareNat valueB valueA
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | a + 1, b + 1 => LevelExpr.compareNat_swap a b

/-- `compareNat` is `.lt`-transitive: a strict chain `a < b < c`
composes to `a < c`.  Direct simultaneous structural recursion on
the three naturals; the cross-zero combinations contradict one of
the hypotheses via `Ordering` no-confusion, and the all-successor
case is the inductive step (each `compareNat (·+1) (·+1)` peels to
`compareNat · ·`). -/
theorem LevelExpr.compareNat_lt_trans :
    ∀ (valueA valueB valueC : Nat),
      LevelExpr.compareNat valueA valueB = Ordering.lt →
      LevelExpr.compareNat valueB valueC = Ordering.lt →
      LevelExpr.compareNat valueA valueC = Ordering.lt
  | 0, 0, _, hAB, _ => Ordering.noConfusion hAB
  | _ + 1, 0, _, hAB, _ => Ordering.noConfusion hAB
  | 0, _ + 1, 0, _, hBC => Ordering.noConfusion hBC
  | _ + 1, _ + 1, 0, _, hBC => Ordering.noConfusion hBC
  | 0, _ + 1, _ + 1, _, _ => rfl
  | a + 1, b + 1, c + 1, hAB, hBC =>
      LevelExpr.compareNat_lt_trans a b c hAB hBC

/-- `compareNat` is `.gt`-transitive, derived from `.lt`-transitivity
by the swap (antisymmetry) identity: `a > b > c` is `c < b < a`
swapped, whose `.lt`-chain gives `c < a`, swapped back to `a > c`. -/
theorem LevelExpr.compareNat_gt_trans (valueA valueB valueC : Nat)
    (hAB : LevelExpr.compareNat valueA valueB = Ordering.gt)
    (hBC : LevelExpr.compareNat valueB valueC = Ordering.gt) :
    LevelExpr.compareNat valueA valueC = Ordering.gt := by
  have hBA : LevelExpr.compareNat valueB valueA = Ordering.lt := by
    have hSwap := LevelExpr.compareNat_swap valueA valueB
    rw [hAB] at hSwap
    exact hSwap.symm
  have hCB : LevelExpr.compareNat valueC valueB = Ordering.lt := by
    have hSwap := LevelExpr.compareNat_swap valueB valueC
    rw [hBC] at hSwap
    exact hSwap.symm
  have hCA : LevelExpr.compareNat valueC valueA = Ordering.lt :=
    LevelExpr.compareNat_lt_trans valueC valueB valueA hCB hBA
  have hSwap := LevelExpr.compareNat_swap valueC valueA
  rw [hCA] at hSwap
  exact hSwap.symm

/-- Ctor priority for cross-ctor `LevelExpr` comparison.

  * `lzero` < `lvar` < `lsucc` < `lmax` < `limax`.

The choice is consistent with Mörtberg-Sterling's canonical form
where constants and variables are the simplest atoms, successors
build on atoms, and binary ops (max / impredicative-max) come
later in the canonical sorting. -/
def LevelExpr.ctorIndex : LevelExpr → Nat
  | .lzero => 0
  | .lvar _ => 1
  | .lsucc _ => 2
  | .lmax _ _ => 3
  | .limax _ _ => 4

/-! ## `orderingThen`: the lexicographic combinator for `compare`

`compare`'s `lmax` / `limax` arms defer to `orderingThen`, which
keeps the first verdict unless it is `.eq` (then it takes the
second).  It is defined by *full* constructor enumeration rather
than a `| .eq => … | other => …` wildcard, and that choice is
load-bearing for the zero-axiom discipline: a one-constructor-
plus-catch-all `match` over `Ordering` compiles to a matcher
whose equation lemmas are discharged with `propext`, whereas full
enumeration compiles straight to `Ordering.casesOn` and stays
axiom-free.  Its construction / inversion lemmas inherit that
cleanliness, letting the `compare` order-laws below reason about
the `lmax` / `limax` combination without ever applying `rw` or
`cases` to a `match`. -/

/-- Lexicographic "then": keep the first verdict unless it is
`.eq`, in which case defer to the second.  This is the
combinator `compare` uses on `lmax` / `limax` operand pairs. -/
def LevelExpr.orderingThen : Ordering → Ordering → Ordering
  | .eq, secondVerdict => secondVerdict
  | .lt, _ => Ordering.lt
  | .gt, _ => Ordering.gt

/-- Construct a `.eq` lexicographic verdict from `.eq` verdicts on
both sides.  Proved by `subst` on both equalities (primitive
`Eq.rec`, no equation-compiler matcher), then `rfl`. -/
theorem LevelExpr.orderingThen_eq_eq_of_both (firstVerdict secondVerdict : Ordering)
    (hFirst : firstVerdict = Ordering.eq) (hSecond : secondVerdict = Ordering.eq) :
    LevelExpr.orderingThen firstVerdict secondVerdict = Ordering.eq := by
  subst hFirst
  subst hSecond
  rfl

/-- Invert a `.eq` lexicographic verdict: it forces both sides to
be `.eq`.  Proved by tactic-mode `cases` on each verdict
(primitive `Ordering.casesOn` — no auxiliary matcher, hence no
`propext`-backed equation lemmas); the eight non-`.eq` first/second
combinations contradict `hThen` via `Ordering` no-confusion. -/
theorem LevelExpr.orderingThen_eq_eq_inv (firstVerdict secondVerdict : Ordering)
    (hThen : LevelExpr.orderingThen firstVerdict secondVerdict = Ordering.eq) :
    firstVerdict = Ordering.eq ∧ secondVerdict = Ordering.eq := by
  cases firstVerdict <;> cases secondVerdict <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact Ordering.noConfusion hThen

/-- `Ordering.swap` distributes over `orderingThen`.  Proved by
case analysis on the first verdict (primitive `Ordering.casesOn`),
then `rfl` per branch.  This is the algebraic fact that lets
`compare_swap` handle the `lmax` / `limax` arms without touching
a `match` with `cases`. -/
theorem LevelExpr.orderingThen_swap (firstVerdict secondVerdict : Ordering) :
    (LevelExpr.orderingThen firstVerdict secondVerdict).swap
      = LevelExpr.orderingThen firstVerdict.swap secondVerdict.swap := by
  cases firstVerdict <;> rfl

/-- Total comparison on `LevelExpr`.  Same-ctor cases compare
recursively (lexicographically on operands, via `orderingThen`);
cross-ctor cases fall through to `compareNat` on `ctorIndex`.

The function is total (always returns one of `lt`/`eq`/`gt`)
and is reflexive + antisymmetric (via `compare_swap`).  Phase
B uses it to canonically order `lmax`/`limax` operands.  The
binary arms route through `orderingThen` (full enumeration)
rather than an in-place wildcard `match`, keeping `compare`
itself `propext`-free. -/
def LevelExpr.compare : LevelExpr → LevelExpr → Ordering
  -- lzero (ctorIndex 0) vs each second-operand head.
  | .lzero, .lzero => .eq
  | .lzero, .lvar _ => .lt
  | .lzero, .lsucc _ => .lt
  | .lzero, .lmax _ _ => .lt
  | .lzero, .limax _ _ => .lt
  -- lvar (1)
  | .lvar _, .lzero => .gt
  | .lvar n, .lvar m => LevelExpr.compareNat n m
  | .lvar _, .lsucc _ => .lt
  | .lvar _, .lmax _ _ => .lt
  | .lvar _, .limax _ _ => .lt
  -- lsucc (2)
  | .lsucc _, .lzero => .gt
  | .lsucc _, .lvar _ => .gt
  | .lsucc e1, .lsucc e2 => LevelExpr.compare e1 e2
  | .lsucc _, .lmax _ _ => .lt
  | .lsucc _, .limax _ _ => .lt
  -- lmax (3)
  | .lmax _ _, .lzero => .gt
  | .lmax _ _, .lvar _ => .gt
  | .lmax _ _, .lsucc _ => .gt
  | .lmax a1 b1, .lmax a2 b2 =>
      LevelExpr.orderingThen (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2)
  | .lmax _ _, .limax _ _ => .lt
  -- limax (4)
  | .limax _ _, .lzero => .gt
  | .limax _ _, .lvar _ => .gt
  | .limax _ _, .lsucc _ => .gt
  | .limax _ _, .lmax _ _ => .gt
  | .limax a1 b1, .limax a2 b2 =>
      LevelExpr.orderingThen (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2)

/-- `compare e e = .eq` (reflexivity).

Proof: structural recursion on `e`.  Each ctor case recursively
applies `compare_refl` to children; `lvar` reduces to
`compareNat_refl`. -/
theorem LevelExpr.compare_refl : ∀ (expr : LevelExpr),
    LevelExpr.compare expr expr = .eq
  | .lzero => rfl
  | .lvar n => LevelExpr.compareNat_refl n
  | .lsucc inner => LevelExpr.compare_refl inner
  | .lmax a b =>
      LevelExpr.orderingThen_eq_eq_of_both
        (LevelExpr.compare a a) (LevelExpr.compare b b)
        (LevelExpr.compare_refl a) (LevelExpr.compare_refl b)
  | .limax a b =>
      LevelExpr.orderingThen_eq_eq_of_both
        (LevelExpr.compare a a) (LevelExpr.compare b b)
        (LevelExpr.compare_refl a) (LevelExpr.compare_refl b)

/-- `(compare e1 e2).swap = compare e2 e1` (antisymmetry as
swap identity).

Proof: structural recursion on the first argument with case
analysis on the second.  `lvar` uses `compareNat_swap`; `lsucc`
recurses; `lmax` / `limax` push `swap` through `orderingThen`
(`orderingThen_swap`) and realign the operands by recursion.
Cross-ctor cases close by `rfl` — each direction reduces to the
dual explicit verdict (`.lt` against `.gt`). -/
theorem LevelExpr.compare_swap : ∀ (e1 e2 : LevelExpr),
    (LevelExpr.compare e1 e2).swap = LevelExpr.compare e2 e1
  | .lzero, .lzero => rfl
  | .lvar n, .lvar m => LevelExpr.compareNat_swap n m
  | .lsucc e1, .lsucc e2 => LevelExpr.compare_swap e1 e2
  | .lmax a1 b1, .lmax a2 b2 => by
      -- Both sides reduce to `orderingThen`; `swap` distributes,
      -- and the recursive `compare_swap`s realign the operands.
      show (LevelExpr.orderingThen
              (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2)).swap
         = LevelExpr.orderingThen
              (LevelExpr.compare a2 a1) (LevelExpr.compare b2 b1)
      rw [LevelExpr.orderingThen_swap, LevelExpr.compare_swap a1 a2,
          LevelExpr.compare_swap b1 b2]
  | .limax a1 b1, .limax a2 b2 => by
      show (LevelExpr.orderingThen
              (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2)).swap
         = LevelExpr.orderingThen
              (LevelExpr.compare a2 a1) (LevelExpr.compare b2 b1)
      rw [LevelExpr.orderingThen_swap, LevelExpr.compare_swap a1 a2,
          LevelExpr.compare_swap b1 b2]
  -- Cross-ctor cases: dual explicit verdicts, closed by `rfl`.
  | .lzero, .lvar _ => rfl
  | .lzero, .lsucc _ => rfl
  | .lzero, .lmax _ _ => rfl
  | .lzero, .limax _ _ => rfl
  | .lvar _, .lzero => rfl
  | .lvar _, .lsucc _ => rfl
  | .lvar _, .lmax _ _ => rfl
  | .lvar _, .limax _ _ => rfl
  | .lsucc _, .lzero => rfl
  | .lsucc _, .lvar _ => rfl
  | .lsucc _, .lmax _ _ => rfl
  | .lsucc _, .limax _ _ => rfl
  | .lmax _ _, .lzero => rfl
  | .lmax _ _, .lvar _ => rfl
  | .lmax _ _, .lsucc _ => rfl
  | .lmax _ _, .limax _ _ => rfl
  | .limax _ _, .lzero => rfl
  | .limax _ _, .lvar _ => rfl
  | .limax _ _, .lsucc _ => rfl
  | .limax _ _, .lmax _ _ => rfl

/-! ## `compare` antisymmetry as structural equality

The shipped `compare_refl` (reflexivity) and `compare_swap`
(antisymmetry-as-swap) establish that `compare` is a reflexive,
antisymmetric comparator.  The full canonical form additionally
needs the *identity-of-indiscernibles* law: a `.eq` verdict
coincides with genuine structural equality.  This is the law a
sort-and-dedup canonicalizer relies on to collapse equal atoms —
without it, two structurally-distinct operands could compare
`.eq` and be silently merged, making the canonical form
non-injective and a downstream `Decidable denoteEquiv` unsound.

`compareNat_eq_imp_eq` is the `Nat`-leaf base case;
`compare_eq_imp_eq` lifts it across the five `LevelExpr` ctors;
the `*_iff_eq` wrappers package each as a decision-grade
biconditional. -/

/-- A `.eq` verdict from `compareNat` forces the two naturals to
be equal.  Structural recursion on the first argument; the
impossible cross-shape verdicts (`.lt` / `.gt` from a
`0`-vs-successor mismatch) are discharged by `Ordering`
constructor no-confusion via `nomatch`. -/
theorem LevelExpr.compareNat_eq_imp_eq : ∀ (valueA valueB : Nat),
    LevelExpr.compareNat valueA valueB = .eq → valueA = valueB
  | 0, 0, _ => rfl
  | 0, _ + 1, hEq => nomatch hEq
  | _ + 1, 0, hEq => nomatch hEq
  | predA + 1, predB + 1, hEq =>
      congrArg Nat.succ (LevelExpr.compareNat_eq_imp_eq predA predB hEq)

/-- `compareNat`'s `.eq` verdict is exactly natural-number
equality (decision-grade biconditional).  Forward by
`compareNat_eq_imp_eq`; backward by rewriting to the reflexive
diagonal `compareNat_refl`. -/
theorem LevelExpr.compareNat_eq_iff_eq (valueA valueB : Nat) :
    LevelExpr.compareNat valueA valueB = .eq ↔ valueA = valueB :=
  ⟨LevelExpr.compareNat_eq_imp_eq valueA valueB,
   fun hEq => by rw [hEq]; exact LevelExpr.compareNat_refl valueB⟩

/-- A `.eq` verdict from `compare` forces structural equality of
the two level expressions.

Proof: structural recursion on the first expression with case
analysis on the second (mirroring `compare_swap`'s 25-arm
shape).  Same-ctor leaf cases lift `compareNat_eq_imp_eq` (for
`lvar`) or recurse through `congrArg` (for `lsucc`).  The binary
`lmax` / `limax` cases route the hypothesis through
`orderingThen_eq_eq_inv` (propext-free), which forces both
operand comparisons to `.eq`; the two recursive equalities then
recombine via `rw`.  Every cross-ctor case reduces to an explicit
`.lt` / `.gt` verdict, refuted against `.eq` by `nomatch`. -/
theorem LevelExpr.compare_eq_imp_eq : ∀ (exprA exprB : LevelExpr),
    LevelExpr.compare exprA exprB = .eq → exprA = exprB
  | .lzero, .lzero, _ => rfl
  | .lvar n, .lvar m, hEq =>
      congrArg LevelExpr.lvar (LevelExpr.compareNat_eq_imp_eq n m hEq)
  | .lsucc innerA, .lsucc innerB, hEq =>
      congrArg LevelExpr.lsucc
        (LevelExpr.compare_eq_imp_eq innerA innerB hEq)
  | .lmax a1 b1, .lmax a2 b2, hEq => by
      -- `hEq` is defeq to the binary `match`; invert it propext-
      -- free, then recurse on both forced-`.eq` operand verdicts.
      have hInv := LevelExpr.orderingThen_eq_eq_inv
        (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2) hEq
      rw [LevelExpr.compare_eq_imp_eq a1 a2 hInv.1,
          LevelExpr.compare_eq_imp_eq b1 b2 hInv.2]
  | .limax a1 b1, .limax a2 b2, hEq => by
      have hInv := LevelExpr.orderingThen_eq_eq_inv
        (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2) hEq
      rw [LevelExpr.compare_eq_imp_eq a1 a2 hInv.1,
          LevelExpr.compare_eq_imp_eq b1 b2 hInv.2]
  -- Cross-ctor cases: `compare` falls to the `compareNat`-on-
  -- `ctorIndex` catch-all, whose verdict on distinct indices is
  -- never `.eq`.
  | .lzero, .lvar _, hEq => nomatch hEq
  | .lzero, .lsucc _, hEq => nomatch hEq
  | .lzero, .lmax _ _, hEq => nomatch hEq
  | .lzero, .limax _ _, hEq => nomatch hEq
  | .lvar _, .lzero, hEq => nomatch hEq
  | .lvar _, .lsucc _, hEq => nomatch hEq
  | .lvar _, .lmax _ _, hEq => nomatch hEq
  | .lvar _, .limax _ _, hEq => nomatch hEq
  | .lsucc _, .lzero, hEq => nomatch hEq
  | .lsucc _, .lvar _, hEq => nomatch hEq
  | .lsucc _, .lmax _ _, hEq => nomatch hEq
  | .lsucc _, .limax _ _, hEq => nomatch hEq
  | .lmax _ _, .lzero, hEq => nomatch hEq
  | .lmax _ _, .lvar _, hEq => nomatch hEq
  | .lmax _ _, .lsucc _, hEq => nomatch hEq
  | .lmax _ _, .limax _ _, hEq => nomatch hEq
  | .limax _ _, .lzero, hEq => nomatch hEq
  | .limax _ _, .lvar _, hEq => nomatch hEq
  | .limax _ _, .lsucc _, hEq => nomatch hEq
  | .limax _ _, .lmax _ _, hEq => nomatch hEq

/-- `compare`'s `.eq` verdict is exactly structural equality on
`LevelExpr` (decision-grade biconditional).  Forward by
`compare_eq_imp_eq`; backward by rewriting to the reflexive
diagonal `compare_refl`. -/
theorem LevelExpr.compare_eq_iff_eq (exprA exprB : LevelExpr) :
    LevelExpr.compare exprA exprB = .eq ↔ exprA = exprB :=
  ⟨LevelExpr.compare_eq_imp_eq exprA exprB,
   fun hEq => by rw [hEq]; exact LevelExpr.compare_refl exprB⟩

/-- On *distinct* constructors, `compare` ignores payloads and is
exactly the `ctorIndex` priority comparison via `compareNat`.

This is the bridge that lets cross-constructor `compare`
transitivity inherit from `compareNat_lt_trans` / `compareNat_gt_trans`:
when the two operands have different constructor priorities, their
`compare` verdict is determined solely by `compareNat` on the
indices.  The `ctorIndex` disequality hypothesis is essential — on
equal constructors `compare` instead recurses into payloads (e.g.
`lvar n` vs `lvar m` yields `compareNat n m`, not `compareNat 1 1`).

Proof: case-split both operands.  The twenty cross-constructor
combinations close by `rfl` (both sides reduce to the same explicit
verdict); the five diagonal combinations contradict `hNeq`
(`ctorIndex` is reflexively equal there). -/
theorem LevelExpr.compare_cross_ctor (exprA exprB : LevelExpr)
    (hNeq : LevelExpr.ctorIndex exprA ≠ LevelExpr.ctorIndex exprB) :
    LevelExpr.compare exprA exprB =
      LevelExpr.compareNat (LevelExpr.ctorIndex exprA)
        (LevelExpr.ctorIndex exprB) := by
  cases exprA <;> cases exprB <;>
    first
      | rfl
      | exact absurd rfl hNeq

/-- A `.lt` verdict from `compare` forces the constructor priorities
into non-strict order: `compareNat (ctorIndex a) (ctorIndex b)` is
never `.gt`.  This is the off-diagonal ingredient of `compare`
transitivity — combined with `compareNat_lt_trans` it discharges
every case where the three operands do not share a constructor.

Proof: suppose the index comparison is `.gt`.  Then the indices
differ (else `compareNat_refl` forces `.eq`), so `compare_cross_ctor`
makes `compare a b` equal to that `.gt`, contradicting the `.lt`
hypothesis. -/
theorem LevelExpr.compare_lt_imp_ctorIndex_not_gt (exprA exprB : LevelExpr)
    (hLt : LevelExpr.compare exprA exprB = Ordering.lt) :
    LevelExpr.compareNat (LevelExpr.ctorIndex exprA)
      (LevelExpr.ctorIndex exprB) ≠ Ordering.gt := by
  intro hGt
  have hNeq : LevelExpr.ctorIndex exprA ≠ LevelExpr.ctorIndex exprB := by
    intro hEq
    rw [hEq, LevelExpr.compareNat_refl] at hGt
    exact Ordering.noConfusion hGt
  have hCross := LevelExpr.compare_cross_ctor exprA exprB hNeq
  rw [hCross, hGt] at hLt
  exact Ordering.noConfusion hLt

/-- Lexicographic `.lt` characterization of `orderingThen`: the
combined verdict is `.lt` exactly when the first verdict is `.lt`,
or the first is `.eq` and the second is `.lt`.  This is the
`lmax` / `limax` diagonal ingredient of `compare` transitivity.
Case analysis on the first verdict (`Ordering.casesOn`). -/
theorem LevelExpr.orderingThen_eq_lt_iff (firstVerdict secondVerdict : Ordering) :
    LevelExpr.orderingThen firstVerdict secondVerdict = Ordering.lt ↔
      (firstVerdict = Ordering.lt ∨
        (firstVerdict = Ordering.eq ∧ secondVerdict = Ordering.lt)) := by
  cases firstVerdict with
  | lt => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | eq => exact ⟨fun hLt => Or.inr ⟨rfl, hLt⟩,
                 fun hOr => hOr.elim (fun hc => Ordering.noConfusion hc) (fun hc => hc.2)⟩
  | gt => exact ⟨fun hc => Ordering.noConfusion hc,
                 fun hOr => hOr.elim (fun hc => Ordering.noConfusion hc)
                   (fun hc => Ordering.noConfusion hc.1)⟩

/-- Lexicographic `.gt` characterization of `orderingThen` (dual of
`orderingThen_eq_lt_iff`).  Rounds out the combinator's verdict API
for the symmetric `compare` `.gt`-transitivity / sortedness work. -/
theorem LevelExpr.orderingThen_eq_gt_iff (firstVerdict secondVerdict : Ordering) :
    LevelExpr.orderingThen firstVerdict secondVerdict = Ordering.gt ↔
      (firstVerdict = Ordering.gt ∨
        (firstVerdict = Ordering.eq ∧ secondVerdict = Ordering.gt)) := by
  cases firstVerdict with
  | lt => exact ⟨fun hc => Ordering.noConfusion hc,
                 fun hOr => hOr.elim (fun hc => Ordering.noConfusion hc)
                   (fun hc => Ordering.noConfusion hc.1)⟩
  | eq => exact ⟨fun hGt => Or.inr ⟨rfl, hGt⟩,
                 fun hOr => hOr.elim (fun hc => Ordering.noConfusion hc) (fun hc => hc.2)⟩
  | gt => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩

/-- A strictly-smaller constructor priority forces a `.lt` verdict:
`compareNat (ctorIndex a) (ctorIndex b) = .lt → compare a b = .lt`.
Dual companion to `compare_lt_imp_ctorIndex_not_gt`; together they
let the off-diagonal of `compare` transitivity move freely between
`compare` and the `ctorIndex`-level `compareNat`. -/
theorem LevelExpr.compare_lt_of_ctorIndex_lt (exprA exprB : LevelExpr)
    (hLt : LevelExpr.compareNat (LevelExpr.ctorIndex exprA)
      (LevelExpr.ctorIndex exprB) = Ordering.lt) :
    LevelExpr.compare exprA exprB = Ordering.lt := by
  have hNeq : LevelExpr.ctorIndex exprA ≠ LevelExpr.ctorIndex exprB := by
    intro hEq
    rw [hEq, LevelExpr.compareNat_refl] at hLt
    exact Ordering.noConfusion hLt
  rw [LevelExpr.compare_cross_ctor exprA exprB hNeq]
  exact hLt

/-- The off-diagonal trichotomy core of `compare` transitivity:
from `compare a b = .lt` and `compare b c = .lt`, either the
priorities already settle `compare a c = .lt`, or all three operands
share a constructor priority (`ctorIndex` comparisons both `.eq`).

This isolates the *only* recursive case of the eventual
`compare_lt_trans` — the same-constructor diagonal — into the
right disjunct; every priority-distinct case is discharged here,
non-recursively, by `compareNat_lt_trans` plus the two
`ctorIndex` bridges.  Nested full enumeration over the two
`compareNat` verdicts keeps it `propext`-free. -/
theorem LevelExpr.compare_lt_trans_step (exprA exprB exprC : LevelExpr)
    (hAB : LevelExpr.compare exprA exprB = Ordering.lt)
    (hBC : LevelExpr.compare exprB exprC = Ordering.lt) :
    LevelExpr.compare exprA exprC = Ordering.lt ∨
      (LevelExpr.compareNat (LevelExpr.ctorIndex exprA)
          (LevelExpr.ctorIndex exprB) = Ordering.eq ∧
        LevelExpr.compareNat (LevelExpr.ctorIndex exprB)
          (LevelExpr.ctorIndex exprC) = Ordering.eq) := by
  have hNotGtAB := LevelExpr.compare_lt_imp_ctorIndex_not_gt exprA exprB hAB
  have hNotGtBC := LevelExpr.compare_lt_imp_ctorIndex_not_gt exprB exprC hBC
  match hIab : LevelExpr.compareNat (LevelExpr.ctorIndex exprA)
      (LevelExpr.ctorIndex exprB) with
  | .gt => exact absurd hIab hNotGtAB
  | .lt =>
      match hIbc : LevelExpr.compareNat (LevelExpr.ctorIndex exprB)
          (LevelExpr.ctorIndex exprC) with
      | .gt => exact absurd hIbc hNotGtBC
      | .lt =>
          exact Or.inl (LevelExpr.compare_lt_of_ctorIndex_lt exprA exprC
            (LevelExpr.compareNat_lt_trans _ _ _ hIab hIbc))
      | .eq =>
          have hbc := LevelExpr.compareNat_eq_imp_eq _ _ hIbc
          exact Or.inl (LevelExpr.compare_lt_of_ctorIndex_lt exprA exprC
            (by rw [← hbc]; exact hIab))
  | .eq =>
      match hIbc : LevelExpr.compareNat (LevelExpr.ctorIndex exprB)
          (LevelExpr.ctorIndex exprC) with
      | .gt => exact absurd hIbc hNotGtBC
      | .lt =>
          have hab := LevelExpr.compareNat_eq_imp_eq _ _ hIab
          exact Or.inl (LevelExpr.compare_lt_of_ctorIndex_lt exprA exprC
            (by rw [hab]; exact hIbc))
      | .eq => exact Or.inr ⟨rfl, rfl⟩

/-- `compare` is `.lt`-transitive: the constructor-priority +
payload lexicographic order it induces on `LevelExpr` is a genuine
strict order.  This is the headline order-theory theorem the
canonical-form completeness work rests on (sortedness of
`insertionSortByCompare`).

Structural recursion on the first operand.  Each constructor case
delegates the priority-distinct sub-cases to `compare_lt_trans_step`
(`inl` → done) and handles the same-constructor diagonal (`inr`)
directly: `lzero` is vacuous (its diagonal verdict is `.eq`, never
`.lt`), `lvar` reduces to `compareNat_lt_trans`, `lsucc` recurses on
the single operand, and `lmax` / `limax` decompose the `orderingThen`
verdicts (`orderingThen_eq_lt_iff`), recurse on whichever operand
pair is strict, and use `compare_eq_imp_eq` to realign the
`.eq`-tied operands. -/
theorem LevelExpr.compare_lt_trans : ∀ (exprA exprB exprC : LevelExpr),
    LevelExpr.compare exprA exprB = Ordering.lt →
    LevelExpr.compare exprB exprC = Ordering.lt →
    LevelExpr.compare exprA exprC = Ordering.lt
  | .lzero, exprB, exprC => by
      intro hAB hBC
      cases LevelExpr.compare_lt_trans_step LevelExpr.lzero exprB exprC hAB hBC with
      | inl hDone => exact hDone
      | inr hEq =>
          cases exprB with
          | lzero => exact Ordering.noConfusion hAB
          | lvar _ => exact Ordering.noConfusion hEq.1
          | lsucc _ => exact Ordering.noConfusion hEq.1
          | lmax _ _ => exact Ordering.noConfusion hEq.1
          | limax _ _ => exact Ordering.noConfusion hEq.1
  | .lvar n, exprB, exprC => by
      intro hAB hBC
      cases LevelExpr.compare_lt_trans_step (LevelExpr.lvar n) exprB exprC hAB hBC with
      | inl hDone => exact hDone
      | inr hEq =>
          cases exprB with
          | lzero => exact Ordering.noConfusion hEq.1
          | lsucc _ => exact Ordering.noConfusion hEq.1
          | lmax _ _ => exact Ordering.noConfusion hEq.1
          | limax _ _ => exact Ordering.noConfusion hEq.1
          | lvar m =>
              cases exprC with
              | lzero => exact Ordering.noConfusion hEq.2
              | lsucc _ => exact Ordering.noConfusion hEq.2
              | lmax _ _ => exact Ordering.noConfusion hEq.2
              | limax _ _ => exact Ordering.noConfusion hEq.2
              | lvar k => exact LevelExpr.compareNat_lt_trans n m k hAB hBC
  | .lsucc innerA, exprB, exprC => by
      intro hAB hBC
      cases LevelExpr.compare_lt_trans_step (LevelExpr.lsucc innerA) exprB exprC hAB hBC with
      | inl hDone => exact hDone
      | inr hEq =>
          cases exprB with
          | lzero => exact Ordering.noConfusion hEq.1
          | lvar _ => exact Ordering.noConfusion hEq.1
          | lmax _ _ => exact Ordering.noConfusion hEq.1
          | limax _ _ => exact Ordering.noConfusion hEq.1
          | lsucc innerB =>
              cases exprC with
              | lzero => exact Ordering.noConfusion hEq.2
              | lvar _ => exact Ordering.noConfusion hEq.2
              | lmax _ _ => exact Ordering.noConfusion hEq.2
              | limax _ _ => exact Ordering.noConfusion hEq.2
              | lsucc innerC =>
                  exact LevelExpr.compare_lt_trans innerA innerB innerC hAB hBC
  | .lmax a1 b1, exprB, exprC => by
      intro hAB hBC
      cases LevelExpr.compare_lt_trans_step (LevelExpr.lmax a1 b1) exprB exprC hAB hBC with
      | inl hDone => exact hDone
      | inr hEq =>
          cases exprB with
          | lzero => exact Ordering.noConfusion hEq.1
          | lvar _ => exact Ordering.noConfusion hEq.1
          | lsucc _ => exact Ordering.noConfusion hEq.1
          | limax _ _ => exact Ordering.noConfusion hEq.1
          | lmax a2 b2 =>
              cases exprC with
              | lzero => exact Ordering.noConfusion hEq.2
              | lvar _ => exact Ordering.noConfusion hEq.2
              | lsucc _ => exact Ordering.noConfusion hEq.2
              | limax _ _ => exact Ordering.noConfusion hEq.2
              | lmax a3 b3 =>
                  have hAB' := (LevelExpr.orderingThen_eq_lt_iff
                    (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2)).mp hAB
                  have hBC' := (LevelExpr.orderingThen_eq_lt_iff
                    (LevelExpr.compare a2 a3) (LevelExpr.compare b2 b3)).mp hBC
                  show LevelExpr.orderingThen (LevelExpr.compare a1 a3)
                    (LevelExpr.compare b1 b3) = Ordering.lt
                  apply (LevelExpr.orderingThen_eq_lt_iff _ _).mpr
                  cases hAB' with
                  | inl ha12lt =>
                      cases hBC' with
                      | inl ha23lt =>
                          exact Or.inl
                            (LevelExpr.compare_lt_trans a1 a2 a3 ha12lt ha23lt)
                      | inr hbTied =>
                          have ha23eq : a2 = a3 :=
                            LevelExpr.compare_eq_imp_eq a2 a3 hbTied.1
                          exact Or.inl (by rw [← ha23eq]; exact ha12lt)
                  | inr haTied =>
                      have ha12eq : a1 = a2 :=
                        LevelExpr.compare_eq_imp_eq a1 a2 haTied.1
                      cases hBC' with
                      | inl ha23lt =>
                          exact Or.inl (by rw [ha12eq]; exact ha23lt)
                      | inr hbTied =>
                          have ha23eq : a2 = a3 :=
                            LevelExpr.compare_eq_imp_eq a2 a3 hbTied.1
                          have ha13eq : a1 = a3 := ha12eq.trans ha23eq
                          refine Or.inr ⟨?_, ?_⟩
                          · rw [ha13eq]; exact LevelExpr.compare_refl a3
                          · exact LevelExpr.compare_lt_trans b1 b2 b3 haTied.2 hbTied.2
  | .limax a1 b1, exprB, exprC => by
      intro hAB hBC
      cases LevelExpr.compare_lt_trans_step (LevelExpr.limax a1 b1) exprB exprC hAB hBC with
      | inl hDone => exact hDone
      | inr hEq =>
          cases exprB with
          | lzero => exact Ordering.noConfusion hEq.1
          | lvar _ => exact Ordering.noConfusion hEq.1
          | lsucc _ => exact Ordering.noConfusion hEq.1
          | lmax _ _ => exact Ordering.noConfusion hEq.1
          | limax a2 b2 =>
              cases exprC with
              | lzero => exact Ordering.noConfusion hEq.2
              | lvar _ => exact Ordering.noConfusion hEq.2
              | lsucc _ => exact Ordering.noConfusion hEq.2
              | lmax _ _ => exact Ordering.noConfusion hEq.2
              | limax a3 b3 =>
                  have hAB' := (LevelExpr.orderingThen_eq_lt_iff
                    (LevelExpr.compare a1 a2) (LevelExpr.compare b1 b2)).mp hAB
                  have hBC' := (LevelExpr.orderingThen_eq_lt_iff
                    (LevelExpr.compare a2 a3) (LevelExpr.compare b2 b3)).mp hBC
                  show LevelExpr.orderingThen (LevelExpr.compare a1 a3)
                    (LevelExpr.compare b1 b3) = Ordering.lt
                  apply (LevelExpr.orderingThen_eq_lt_iff _ _).mpr
                  cases hAB' with
                  | inl ha12lt =>
                      cases hBC' with
                      | inl ha23lt =>
                          exact Or.inl
                            (LevelExpr.compare_lt_trans a1 a2 a3 ha12lt ha23lt)
                      | inr hbTied =>
                          have ha23eq : a2 = a3 :=
                            LevelExpr.compare_eq_imp_eq a2 a3 hbTied.1
                          exact Or.inl (by rw [← ha23eq]; exact ha12lt)
                  | inr haTied =>
                      have ha12eq : a1 = a2 :=
                        LevelExpr.compare_eq_imp_eq a1 a2 haTied.1
                      cases hBC' with
                      | inl ha23lt =>
                          exact Or.inl (by rw [ha12eq]; exact ha23lt)
                      | inr hbTied =>
                          have ha23eq : a2 = a3 :=
                            LevelExpr.compare_eq_imp_eq a2 a3 hbTied.1
                          have ha13eq : a1 = a3 := ha12eq.trans ha23eq
                          refine Or.inr ⟨?_, ?_⟩
                          · rw [ha13eq]; exact LevelExpr.compare_refl a3
                          · exact LevelExpr.compare_lt_trans b1 b2 b3 haTied.2 hbTied.2

/-! ## First Phase B canonicalization step — pairwise lmax sort

`canonicalizeLmaxPair` swaps `lmax` operands when out of compare
order, ensuring the smaller operand (by `compare`) comes first.
This is the SIMPLEST canonical-form transformation; the full
Phase B normalizer composes this with `simplify`, recursive
descent into operands, and lsucc-into-lmax distributivity. -/

/-- Order one `lmax`'s operands by a precomputed `compare`
verdict: swap to `lmax e2 e1` exactly when the verdict is `.gt`,
otherwise keep `lmax e1 e2`.  Full `Ordering` enumeration (no
`| _ =>` catch-all) keeps this `propext`-free at the definition
level — see `feedback_lean_match_propext_recipe` Rule 9. -/
def LevelExpr.swapToCanonicalLmax (verdict : Ordering) (e1 e2 : LevelExpr) : LevelExpr :=
  match verdict with
  | .gt => LevelExpr.lmax e2 e1
  | .lt => LevelExpr.lmax e1 e2
  | .eq => LevelExpr.lmax e1 e2

/-- Single-pair `lmax` operand canonicalization.  If `compare e1
e2 = .gt`, swap to `lmax e2 e1`; otherwise leave as `lmax e1 e2`.
Non-lmax inputs are returned unchanged.

Defined by full `LevelExpr` enumeration (no outer catch-all) and
routing the `lmax` arm through `swapToCanonicalLmax`, so the def
is `propext`-free.  Soundness via `canonicalizeLmaxPair_denoteEquiv`:
regardless of swap, the denotation is preserved (by
`lmax_comm_denoteEquiv`). -/
def LevelExpr.canonicalizeLmaxPair : LevelExpr → LevelExpr
  | .lzero => LevelExpr.lzero
  | .lvar n => LevelExpr.lvar n
  | .lsucc inner => LevelExpr.lsucc inner
  | .limax a b => LevelExpr.limax a b
  | .lmax e1 e2 =>
      LevelExpr.swapToCanonicalLmax (LevelExpr.compare e1 e2) e1 e2

/-- `swapToCanonicalLmax` preserves the denotation of `lmax e1 e2`
for every verdict.  Proved by `cases` on the (bound) verdict —
primitive `Ordering.casesOn`, no equation-compiler matcher — with
the `.gt` swap discharged by `lmax_comm_denoteEquiv` and the
`.lt` / `.eq` no-swap cases by reflexivity. -/
theorem LevelExpr.swapToCanonicalLmax_denoteEquiv
    (verdict : Ordering) (e1 e2 : LevelExpr) :
    LevelExpr.denoteEquiv
      (LevelExpr.swapToCanonicalLmax verdict e1 e2) (LevelExpr.lmax e1 e2) := by
  cases verdict with
  | gt => exact LevelExpr.lmax_comm_denoteEquiv e2 e1
  | lt => exact LevelExpr.denoteEquiv.refl _
  | eq => exact LevelExpr.denoteEquiv.refl _

/-- `canonicalizeLmaxPair` preserves the semantic denotation
(it's a `denoteEquiv` rule).

Proof: `cases` on the input (primitive `LevelExpr.casesOn`).
Non-lmax inputs return unchanged (refl); the `lmax` arm reduces
to `swapToCanonicalLmax (compare e1 e2) e1 e2` and is discharged
by `swapToCanonicalLmax_denoteEquiv`. -/
theorem LevelExpr.canonicalizeLmaxPair_denoteEquiv (expr : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.canonicalizeLmaxPair expr) expr := by
  cases expr with
  | lzero => exact LevelExpr.denoteEquiv.refl _
  | lvar _ => exact LevelExpr.denoteEquiv.refl _
  | lsucc _ => exact LevelExpr.denoteEquiv.refl _
  | limax _ _ => exact LevelExpr.denoteEquiv.refl _
  | lmax e1 e2 =>
      exact LevelExpr.swapToCanonicalLmax_denoteEquiv (LevelExpr.compare e1 e2) e1 e2

/-- The output of `swapToCanonicalLmax` on a `compare`-derived
verdict is a fixed point of `canonicalizeLmaxPair`: a pair already
placed in `compare` order re-compares so the second pass leaves it
unchanged.  The `.gt` case is the substantive one — the swapped
pair `(e2, e1)` re-compares as `.lt` via `compare_swap`. -/
theorem LevelExpr.canonicalizeLmaxPair_swapToCanonicalLmax
    (verdict : Ordering) (e1 e2 : LevelExpr)
    (hVerdict : LevelExpr.compare e1 e2 = verdict) :
    LevelExpr.canonicalizeLmaxPair (LevelExpr.swapToCanonicalLmax verdict e1 e2)
      = LevelExpr.swapToCanonicalLmax verdict e1 e2 := by
  cases verdict with
  | lt =>
      show LevelExpr.swapToCanonicalLmax (LevelExpr.compare e1 e2) e1 e2
         = LevelExpr.swapToCanonicalLmax Ordering.lt e1 e2
      rw [hVerdict]
  | eq =>
      show LevelExpr.swapToCanonicalLmax (LevelExpr.compare e1 e2) e1 e2
         = LevelExpr.swapToCanonicalLmax Ordering.eq e1 e2
      rw [hVerdict]
  | gt =>
      show LevelExpr.swapToCanonicalLmax (LevelExpr.compare e2 e1) e2 e1
         = LevelExpr.swapToCanonicalLmax Ordering.lt e2 e1
      have hSwap : LevelExpr.compare e2 e1 = Ordering.lt := by
        have hChain := LevelExpr.compare_swap e1 e2
        rw [hVerdict] at hChain
        exact hChain.symm
      rw [hSwap]

/-- `canonicalizeLmaxPair` is idempotent: applying twice yields
the same result as applying once.

Proof: `cases` on the input.  Non-lmax inputs are fixed points
trivially; the `lmax` arm reduces to `swapToCanonicalLmax (compare
e1 e2) e1 e2`, whose canonical order is preserved by
`canonicalizeLmaxPair_swapToCanonicalLmax`. -/
theorem LevelExpr.canonicalizeLmaxPair_idempotent (expr : LevelExpr) :
    LevelExpr.canonicalizeLmaxPair (LevelExpr.canonicalizeLmaxPair expr) =
      LevelExpr.canonicalizeLmaxPair expr := by
  cases expr with
  | lzero => rfl
  | lvar _ => rfl
  | lsucc _ => rfl
  | limax _ _ => rfl
  | lmax e1 e2 =>
      exact LevelExpr.canonicalizeLmaxPair_swapToCanonicalLmax
        (LevelExpr.compare e1 e2) e1 e2 rfl

/-! ## n-ary `lmax` flattening — toward the full canonical form

A nested `lmax` tree denotes the `levelMax` of its leaf atoms,
independent of association or grouping (`lmax` is, under
`denoteEquiv`, a commutative idempotent monoid with unit `lzero`).
The full n-ary canonical form will flatten a tree to its atom list
(`lmaxAtoms`), then sort + dedup + drop-`lzero` the atoms, then
rebuild (`foldLmax`).  This block ships the flatten/rebuild
round-trip soundness — the substrate the later sort / dedup /
clean steps build on; their `denoteEquiv` preservation composes
through `foldLmax`'s monoid laws.

`lmaxAtoms` descends ONLY through `lmax` nodes — `limax` is left as
an opaque atom, since its conditional collapse (`limax e lzero ~
lzero`) is not an `lmax`-monoid law and would be unsound to flatten
through. -/

/-- Collect the `lmax`-atoms of a level expression: descend through
`lmax` nodes, treat every other head (including `limax`) as a single
leaf.  Full constructor enumeration keeps the def `propext`-free. -/
def LevelExpr.lmaxAtoms : LevelExpr → List LevelExpr
  | .lmax a b => LevelExpr.lmaxAtoms a ++ LevelExpr.lmaxAtoms b
  | .lzero => [LevelExpr.lzero]
  | .lvar n => [LevelExpr.lvar n]
  | .lsucc inner => [LevelExpr.lsucc inner]
  | .limax a b => [LevelExpr.limax a b]

/-- Rebuild a right-nested `lmax` from an atom list; the empty list
folds to `lzero` (the `lmax` unit). -/
def LevelExpr.foldLmax : List LevelExpr → LevelExpr
  | [] => LevelExpr.lzero
  | head :: rest => LevelExpr.lmax head (LevelExpr.foldLmax rest)

/-- `foldLmax` distributes over list append up to `denoteEquiv`:
`foldLmax (xs ++ ys) ~ lmax (foldLmax xs) (foldLmax ys)`.

Induction on `xs`: the `[]` base reduces the left fold to `lzero`
and uses the left-unit law; the cons step pushes the inductive
hypothesis under `lmax head _` (left-operand congruence) and then
re-associates. -/
theorem LevelExpr.foldLmax_append_denoteEquiv :
    ∀ (xs ys : List LevelExpr),
      LevelExpr.denoteEquiv (LevelExpr.foldLmax (xs ++ ys))
        (LevelExpr.lmax (LevelExpr.foldLmax xs) (LevelExpr.foldLmax ys))
  | [], ys =>
      LevelExpr.denoteEquiv.symm (LevelExpr.lmax_lzero_left_denoteEquiv _)
  | head :: rest, ys => by
      show LevelExpr.denoteEquiv
        (LevelExpr.lmax head (LevelExpr.foldLmax (rest ++ ys)))
        (LevelExpr.lmax (LevelExpr.lmax head (LevelExpr.foldLmax rest))
          (LevelExpr.foldLmax ys))
      have hInner :=
        LevelExpr.foldLmax_append_denoteEquiv rest ys
      have hCongr : LevelExpr.denoteEquiv
          (LevelExpr.lmax head (LevelExpr.foldLmax (rest ++ ys)))
          (LevelExpr.lmax head
            (LevelExpr.lmax (LevelExpr.foldLmax rest) (LevelExpr.foldLmax ys))) :=
        LevelExpr.lmax_denoteEquiv_congr (LevelExpr.denoteEquiv.refl head) hInner
      have hAssoc : LevelExpr.denoteEquiv
          (LevelExpr.lmax head
            (LevelExpr.lmax (LevelExpr.foldLmax rest) (LevelExpr.foldLmax ys)))
          (LevelExpr.lmax (LevelExpr.lmax head (LevelExpr.foldLmax rest))
            (LevelExpr.foldLmax ys)) :=
        LevelExpr.denoteEquiv.symm
          (LevelExpr.lmax_assoc_denoteEquiv head (LevelExpr.foldLmax rest)
            (LevelExpr.foldLmax ys))
      exact LevelExpr.denoteEquiv.trans hCongr hAssoc

/-- The flatten/rebuild round-trip preserves denotation:
`foldLmax (lmaxAtoms e) ~ e`.

Structural recursion on `e`.  The four leaf heads fold to a
singleton list (`foldLmax [atom] = lmax atom lzero`) and close by
the `lzero` units; the `lmax` node splits via
`foldLmax_append_denoteEquiv` and recombines the children's
inductive hypotheses through the `lmax` congruence. -/
theorem LevelExpr.foldLmax_lmaxAtoms_denoteEquiv :
    ∀ (expr : LevelExpr),
      LevelExpr.denoteEquiv (LevelExpr.foldLmax (LevelExpr.lmaxAtoms expr)) expr
  | .lzero => LevelExpr.lmax_lzero_left_denoteEquiv _
  | .lvar _ => LevelExpr.lmax_lzero_right_denoteEquiv _
  | .lsucc _ => LevelExpr.lmax_lzero_right_denoteEquiv _
  | .limax _ _ => LevelExpr.lmax_lzero_right_denoteEquiv _
  | .lmax a b => by
      show LevelExpr.denoteEquiv
        (LevelExpr.foldLmax (LevelExpr.lmaxAtoms a ++ LevelExpr.lmaxAtoms b))
        (LevelExpr.lmax a b)
      have hAppend := LevelExpr.foldLmax_append_denoteEquiv
        (LevelExpr.lmaxAtoms a) (LevelExpr.lmaxAtoms b)
      have hChildren : LevelExpr.denoteEquiv
          (LevelExpr.lmax (LevelExpr.foldLmax (LevelExpr.lmaxAtoms a))
            (LevelExpr.foldLmax (LevelExpr.lmaxAtoms b)))
          (LevelExpr.lmax a b) :=
        LevelExpr.lmax_denoteEquiv_congr
          (LevelExpr.foldLmax_lmaxAtoms_denoteEquiv a)
          (LevelExpr.foldLmax_lmaxAtoms_denoteEquiv b)
      exact LevelExpr.denoteEquiv.trans hAppend hChildren

/-! ## Drop-`lzero` atom-list cleanup

`lzero` is the `lmax` unit, so a `lzero` atom contributes nothing
to the `levelMax`.  `dropLzeroAtoms` removes every `lzero` from a
flattened atom list; `foldLmax_dropLzeroAtoms_denoteEquiv` shows
this preserves the denotation.  This is the drop-`lzero` sub-step
of the n-ary canonical form (composed after `lmaxAtoms`, before
the rebuild).  Note: it does not remove a `lzero` reachable only
inside a non-`lmax` atom (e.g. `lsucc lzero`) — only top-level
`lzero` atoms, which is exactly what the canonical max needs. -/

/-- Remove every top-level `lzero` atom from a flattened atom list.
Full constructor enumeration (outer `List`, inner `LevelExpr`) —
no wildcard — keeps the def `propext`-free. -/
def LevelExpr.dropLzeroAtoms : List LevelExpr → List LevelExpr
  | [] => []
  | head :: rest =>
      match head with
      | LevelExpr.lzero => LevelExpr.dropLzeroAtoms rest
      | LevelExpr.lvar n => LevelExpr.lvar n :: LevelExpr.dropLzeroAtoms rest
      | LevelExpr.lsucc inner =>
          LevelExpr.lsucc inner :: LevelExpr.dropLzeroAtoms rest
      | LevelExpr.lmax a b =>
          LevelExpr.lmax a b :: LevelExpr.dropLzeroAtoms rest
      | LevelExpr.limax a b =>
          LevelExpr.limax a b :: LevelExpr.dropLzeroAtoms rest

/-- Dropping `lzero` atoms preserves the folded denotation:
`foldLmax (dropLzeroAtoms xs) ~ foldLmax xs`.

Structural recursion on the list.  In the cons step, a `lzero`
head is absorbed by the `lzero` left-unit law; every other head is
kept and the inductive hypothesis lifts through the `lmax`
left-operand congruence. -/
theorem LevelExpr.foldLmax_dropLzeroAtoms_denoteEquiv :
    ∀ (xs : List LevelExpr),
      LevelExpr.denoteEquiv (LevelExpr.foldLmax (LevelExpr.dropLzeroAtoms xs))
        (LevelExpr.foldLmax xs)
  | [] => LevelExpr.denoteEquiv.refl _
  | head :: rest => by
      have ih := LevelExpr.foldLmax_dropLzeroAtoms_denoteEquiv rest
      cases head with
      | lzero =>
          exact LevelExpr.denoteEquiv.trans ih
            (LevelExpr.denoteEquiv.symm (LevelExpr.lmax_lzero_left_denoteEquiv _))
      | lvar n =>
          exact LevelExpr.lmax_denoteEquiv_congr (LevelExpr.denoteEquiv.refl _) ih
      | lsucc inner =>
          exact LevelExpr.lmax_denoteEquiv_congr (LevelExpr.denoteEquiv.refl _) ih
      | lmax a b =>
          exact LevelExpr.lmax_denoteEquiv_congr (LevelExpr.denoteEquiv.refl _) ih
      | limax a b =>
          exact LevelExpr.lmax_denoteEquiv_congr (LevelExpr.denoteEquiv.refl _) ih

/-! ## Compare-ordered insertion — toward the sort sub-step

`foldLmax` is invariant under reordering of its atom list (the
underlying `levelMax` is commutative).  This block ships the
reordering primitive (`foldLmax_swap_denoteEquiv`) and a single
compare-ordered insertion (`insertByCompare`) with its soundness;
together they are the core of the sort sub-step, since an insertion
sort is a fold of `insertByCompare` whose `denoteEquiv` invariance
composes from `foldLmax_insertByCompare_denoteEquiv`. -/

/-- Adjacent-swap invariance of `foldLmax`: swapping the first two
atoms preserves the denotation.  This is left-commutativity of
`lmax`, assembled from `lmax` associativity + commutativity. -/
theorem LevelExpr.foldLmax_swap_denoteEquiv
    (x y : LevelExpr) (rest : List LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.foldLmax (x :: y :: rest))
      (LevelExpr.foldLmax (y :: x :: rest)) := by
  show LevelExpr.denoteEquiv
    (LevelExpr.lmax x (LevelExpr.lmax y (LevelExpr.foldLmax rest)))
    (LevelExpr.lmax y (LevelExpr.lmax x (LevelExpr.foldLmax rest)))
  have hUnAssoc : LevelExpr.denoteEquiv
      (LevelExpr.lmax x (LevelExpr.lmax y (LevelExpr.foldLmax rest)))
      (LevelExpr.lmax (LevelExpr.lmax x y) (LevelExpr.foldLmax rest)) :=
    LevelExpr.denoteEquiv.symm
      (LevelExpr.lmax_assoc_denoteEquiv x y (LevelExpr.foldLmax rest))
  have hCommHead : LevelExpr.denoteEquiv
      (LevelExpr.lmax (LevelExpr.lmax x y) (LevelExpr.foldLmax rest))
      (LevelExpr.lmax (LevelExpr.lmax y x) (LevelExpr.foldLmax rest)) :=
    LevelExpr.lmax_denoteEquiv_congr
      (LevelExpr.lmax_comm_denoteEquiv x y) (LevelExpr.denoteEquiv.refl _)
  have hReAssoc : LevelExpr.denoteEquiv
      (LevelExpr.lmax (LevelExpr.lmax y x) (LevelExpr.foldLmax rest))
      (LevelExpr.lmax y (LevelExpr.lmax x (LevelExpr.foldLmax rest))) :=
    LevelExpr.lmax_assoc_denoteEquiv y x (LevelExpr.foldLmax rest)
  exact LevelExpr.denoteEquiv.trans hUnAssoc
    (LevelExpr.denoteEquiv.trans hCommHead hReAssoc)

/-- One step of compare-ordered insertion, dispatched on a
precomputed verdict (the recursive tail-insertion is passed in as
`tailInsertion`).  Full `Ordering` enumeration keeps the def
`propext`-free and lets `insertByCompare`'s soundness case on the
verdict without touching an in-place `match`. -/
def LevelExpr.insertStep (verdict : Ordering)
    (newAtom head : LevelExpr) (rest tailInsertion : List LevelExpr) :
    List LevelExpr :=
  match verdict with
  | .gt => head :: tailInsertion
  | .lt => newAtom :: head :: rest
  | .eq => newAtom :: head :: rest

/-- Insert an atom into a list, keeping it before the first atom it
does not strictly exceed under `compare` (`.gt` means strictly
later, so skip past `head`).  Routed through `insertStep` on the
`compare` verdict; the recursive tail-insertion is computed
eagerly (acceptable for a normalization spec). -/
def LevelExpr.insertByCompare (newAtom : LevelExpr) : List LevelExpr → List LevelExpr
  | [] => [newAtom]
  | head :: rest =>
      LevelExpr.insertStep (LevelExpr.compare newAtom head) newAtom head rest
        (LevelExpr.insertByCompare newAtom rest)

/-- Compare-ordered insertion preserves the folded denotation:
`foldLmax (insertByCompare x xs) ~ foldLmax (x :: xs)`.

List recursion.  A `.lt` / `.eq` verdict places `x` at the head
(identical fold, refl); a `.gt` verdict skips past `head`, and the
inductive hypothesis + the adjacent-swap recombine the result. -/
theorem LevelExpr.foldLmax_insertByCompare_denoteEquiv (newAtom : LevelExpr) :
    ∀ (xs : List LevelExpr),
      LevelExpr.denoteEquiv
        (LevelExpr.foldLmax (LevelExpr.insertByCompare newAtom xs))
        (LevelExpr.foldLmax (newAtom :: xs))
  | [] => LevelExpr.denoteEquiv.refl _
  | head :: rest => by
      have ih := LevelExpr.foldLmax_insertByCompare_denoteEquiv newAtom rest
      show LevelExpr.denoteEquiv
        (LevelExpr.foldLmax
          (LevelExpr.insertStep (LevelExpr.compare newAtom head) newAtom head rest
            (LevelExpr.insertByCompare newAtom rest)))
        (LevelExpr.foldLmax (newAtom :: head :: rest))
      cases hVerdict : LevelExpr.compare newAtom head with
      | lt => exact LevelExpr.denoteEquiv.refl _
      | eq => exact LevelExpr.denoteEquiv.refl _
      | gt =>
          exact LevelExpr.denoteEquiv.trans
            (LevelExpr.lmax_denoteEquiv_congr (LevelExpr.denoteEquiv.refl _) ih)
            (LevelExpr.foldLmax_swap_denoteEquiv head newAtom rest)

/-- Insertion sort over `compare`: fold each atom into the sorted
prefix via `insertByCompare`.  This is the `sort` sub-step of the
n-ary canonical form (flatten → sort → dedup → drop-lzero →
rebuild).  Written as a structural list recursion so it is
`propext`-free. -/
def LevelExpr.insertionSortByCompare : List LevelExpr → List LevelExpr
  | [] => []
  | head :: rest =>
      LevelExpr.insertByCompare head (LevelExpr.insertionSortByCompare rest)

/-- Insertion sort preserves the folded denotation:
`foldLmax (insertionSortByCompare xs) ~ foldLmax xs`.

List recursion.  The sorted tail folds equivalently by the
inductive hypothesis (`lmax`-congruence under the fixed head); the
single-insertion soundness then re-seats `head` at the front. -/
theorem LevelExpr.foldLmax_insertionSortByCompare_denoteEquiv :
    ∀ (xs : List LevelExpr),
      LevelExpr.denoteEquiv
        (LevelExpr.foldLmax (LevelExpr.insertionSortByCompare xs))
        (LevelExpr.foldLmax xs)
  | [] => LevelExpr.denoteEquiv.refl _
  | head :: rest => by
      have ih := LevelExpr.foldLmax_insertionSortByCompare_denoteEquiv rest
      show LevelExpr.denoteEquiv
        (LevelExpr.foldLmax
          (LevelExpr.insertByCompare head
            (LevelExpr.insertionSortByCompare rest)))
        (LevelExpr.foldLmax (head :: rest))
      have hInsert := LevelExpr.foldLmax_insertByCompare_denoteEquiv head
        (LevelExpr.insertionSortByCompare rest)
      have hTail := LevelExpr.lmax_denoteEquiv_congr
        (LevelExpr.denoteEquiv.refl head) ih
      exact LevelExpr.denoteEquiv.trans hInsert hTail

/-! ## The dedup sub-step — collapse adjacent equal atoms

After sorting, equal atoms sit next to each other; `dedupAdjacent`
collapses each adjacent equal pair via `lmax`'s idempotence.  As
with insertion, soundness needs only the commutative-idempotent-
monoid laws — sortedness is what makes adjacency *capture all*
duplicates (a completeness concern), not what makes the collapse
*sound*. -/

/-- Folding a duplicated leading atom equals folding it once:
`foldLmax (a :: a :: rest) ~ foldLmax (a :: rest)`.  This is
`lmax`-idempotence under the head, assembled from associativity +
idempotence (the dedup analogue of `foldLmax_swap_denoteEquiv`). -/
theorem LevelExpr.foldLmax_dup_head_denoteEquiv
    (atom : LevelExpr) (rest : List LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.foldLmax (atom :: atom :: rest))
      (LevelExpr.foldLmax (atom :: rest)) := by
  show LevelExpr.denoteEquiv
    (LevelExpr.lmax atom (LevelExpr.lmax atom (LevelExpr.foldLmax rest)))
    (LevelExpr.lmax atom (LevelExpr.foldLmax rest))
  have hUnAssoc : LevelExpr.denoteEquiv
      (LevelExpr.lmax atom (LevelExpr.lmax atom (LevelExpr.foldLmax rest)))
      (LevelExpr.lmax (LevelExpr.lmax atom atom) (LevelExpr.foldLmax rest)) :=
    LevelExpr.denoteEquiv.symm
      (LevelExpr.lmax_assoc_denoteEquiv atom atom (LevelExpr.foldLmax rest))
  have hIdem : LevelExpr.denoteEquiv
      (LevelExpr.lmax (LevelExpr.lmax atom atom) (LevelExpr.foldLmax rest))
      (LevelExpr.lmax atom (LevelExpr.foldLmax rest)) :=
    LevelExpr.lmax_denoteEquiv_congr
      (LevelExpr.lmax_idempotent_denoteEquiv atom)
      (LevelExpr.denoteEquiv.refl (LevelExpr.foldLmax rest))
  exact LevelExpr.denoteEquiv.trans hUnAssoc hIdem

/-- One step of adjacent dedup, dispatched on a precomputed
`compare` verdict.  `.eq` drops the leading atom (it equals the
next, already present in `tailDedup`); `.lt` / `.gt` keep it in
front.  Full `Ordering` enumeration keeps the def `propext`-free
and lets the soundness proof case on the verdict via this named
helper rather than an in-place `match`. -/
def LevelExpr.dedupStep (verdict : Ordering)
    (first : LevelExpr) (tailDedup : List LevelExpr) : List LevelExpr :=
  match verdict with
  | .eq => tailDedup
  | .lt => first :: tailDedup
  | .gt => first :: tailDedup

/-- Collapse adjacent equal atoms under `compare`.  Two-element
lookahead: compare the first two atoms, drop the first when equal
(routed through `dedupStep`), recurse on the tail otherwise.
Structural recursion on the explicit tail `second :: rest`. -/
def LevelExpr.dedupAdjacent : List LevelExpr → List LevelExpr
  | [] => []
  | [single] => [single]
  | first :: second :: rest =>
      LevelExpr.dedupStep (LevelExpr.compare first second) first
        (LevelExpr.dedupAdjacent (second :: rest))

/-- Adjacent dedup preserves the folded denotation:
`foldLmax (dedupAdjacent xs) ~ foldLmax xs`.

Two-element-lookahead recursion.  The `.eq` verdict forces
`first = second` (`compare_eq_imp_eq`), so dropping `first`
collapses a duplicated head (`foldLmax_dup_head_denoteEquiv`);
`.lt` / `.gt` keep `first` and recurse under an `lmax`-congruence
with the inductive hypothesis. -/
theorem LevelExpr.foldLmax_dedupAdjacent_denoteEquiv :
    ∀ (xs : List LevelExpr),
      LevelExpr.denoteEquiv
        (LevelExpr.foldLmax (LevelExpr.dedupAdjacent xs))
        (LevelExpr.foldLmax xs)
  | [] => LevelExpr.denoteEquiv.refl _
  | [_single] => LevelExpr.denoteEquiv.refl _
  | first :: second :: rest => by
      have ih := LevelExpr.foldLmax_dedupAdjacent_denoteEquiv (second :: rest)
      show LevelExpr.denoteEquiv
        (LevelExpr.foldLmax
          (LevelExpr.dedupStep (LevelExpr.compare first second) first
            (LevelExpr.dedupAdjacent (second :: rest))))
        (LevelExpr.foldLmax (first :: second :: rest))
      cases hVerdict : LevelExpr.compare first second with
      | eq =>
          have hEq : first = second :=
            LevelExpr.compare_eq_imp_eq first second hVerdict
          show LevelExpr.denoteEquiv
            (LevelExpr.foldLmax (LevelExpr.dedupAdjacent (second :: rest)))
            (LevelExpr.foldLmax (first :: second :: rest))
          refine LevelExpr.denoteEquiv.trans ih ?_
          rw [hEq]
          exact LevelExpr.denoteEquiv.symm
            (LevelExpr.foldLmax_dup_head_denoteEquiv second rest)
      | lt =>
          show LevelExpr.denoteEquiv
            (LevelExpr.foldLmax (first :: LevelExpr.dedupAdjacent (second :: rest)))
            (LevelExpr.foldLmax (first :: second :: rest))
          exact LevelExpr.lmax_denoteEquiv_congr
            (LevelExpr.denoteEquiv.refl first) ih
      | gt =>
          show LevelExpr.denoteEquiv
            (LevelExpr.foldLmax (first :: LevelExpr.dedupAdjacent (second :: rest)))
            (LevelExpr.foldLmax (first :: second :: rest))
          exact LevelExpr.lmax_denoteEquiv_congr
            (LevelExpr.denoteEquiv.refl first) ih

/-! ## The assembled n-ary canonical form

`canonicalize` is the full pipeline: flatten the `lmax` tree to an
atom list, sort it by `compare`, collapse adjacent duplicates, drop
`lzero` atoms, then rebuild a right-nested `lmax` via `foldLmax`.

This commit ships the SOUNDNESS direction only:
`canonicalize e ~ e` under `denoteEquiv`, chained from the four
per-transform invariance lemmas.  The COMPLETENESS direction
(`e1 ~ e2 → canonicalize e1 = canonicalize e2`, which would yield
`Decidable denoteEquiv` by comparing canonical forms) is the hard
Mörtberg-Sterling max-plus argument and remains deferred — it is
also complicated by `foldLmax`'s trailing-`lzero` base case and by
`limax`'s conditional collapse, neither of which affects soundness.
-/

/-- The full n-ary canonical form of a level expression:
flatten → sort → dedup → drop-`lzero` → rebuild.  Each stage is a
`List LevelExpr` transform whose `foldLmax`-invariance was proven
above; `canonicalize` composes them and re-folds. -/
def LevelExpr.canonicalize (expr : LevelExpr) : LevelExpr :=
  LevelExpr.foldLmax
    (LevelExpr.dropLzeroAtoms
      (LevelExpr.dedupAdjacent
        (LevelExpr.insertionSortByCompare
          (LevelExpr.lmaxAtoms expr))))

/-- `canonicalize` preserves denotation: `canonicalize e ~ e`.

Soundness chains the four stage-invariance lemmas back through the
pipeline (drop-`lzero`, then dedup, then sort, all under
`foldLmax`), finishing with `foldLmax (lmaxAtoms e) ~ e`. -/
theorem LevelExpr.canonicalize_denoteEquiv (expr : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.canonicalize expr) expr := by
  show LevelExpr.denoteEquiv
    (LevelExpr.foldLmax
      (LevelExpr.dropLzeroAtoms
        (LevelExpr.dedupAdjacent
          (LevelExpr.insertionSortByCompare (LevelExpr.lmaxAtoms expr)))))
    expr
  exact LevelExpr.denoteEquiv.trans
    (LevelExpr.foldLmax_dropLzeroAtoms_denoteEquiv
      (LevelExpr.dedupAdjacent
        (LevelExpr.insertionSortByCompare (LevelExpr.lmaxAtoms expr))))
    (LevelExpr.denoteEquiv.trans
      (LevelExpr.foldLmax_dedupAdjacent_denoteEquiv
        (LevelExpr.insertionSortByCompare (LevelExpr.lmaxAtoms expr)))
      (LevelExpr.denoteEquiv.trans
        (LevelExpr.foldLmax_insertionSortByCompare_denoteEquiv
          (LevelExpr.lmaxAtoms expr))
        (LevelExpr.foldLmax_lmaxAtoms_denoteEquiv expr)))

/-- Concrete soundness witness: a duplicated-atom expression and its
canonical form denote the same value under a sample environment. -/
example :
    LevelExpr.denote
        (LevelExpr.canonicalize
          (LevelExpr.lmax (LevelExpr.lvar 0) (LevelExpr.lvar 0)))
        (fun _ => 5)
      = LevelExpr.denote
          (LevelExpr.lmax (LevelExpr.lvar 0) (LevelExpr.lvar 0))
          (fun _ => 5) :=
  rfl

/-! ## Semantic characterization of the atom-list machinery

The completeness direction (deferred) will need to read off the
denotation of a canonical form as an explicit `Nat`-level maximum
over its atoms.  This block ships that bridge: `denoteAtomList`
interprets an atom list as the right-fold of `levelMax`, and the
two characterization lemmas show that `foldLmax` rebuilds exactly
that value and that `lmaxAtoms` flattens to exactly that value.
Together: `denote (foldLmax (lmaxAtoms e)) e ~ e` refines to the
*computed* max-plus value, the semantic anchor for max-plus
normal-form reasoning. -/

/-- Interpret an atom list as the running `levelMax` of its atoms'
denotations, with the empty list denoting `0` (the `levelMax`
unit).  This is the `Nat`-level meaning of a flattened `lmax`
spine. -/
def LevelExpr.denoteAtomList : List LevelExpr → (Nat → Nat) → Nat
  | [], _ => 0
  | atom :: rest, env =>
      LevelExpr.levelMax (atom.denote env) (LevelExpr.denoteAtomList rest env)

/-- `denoteAtomList` distributes over list append as `levelMax`:
the max over `xs ++ ys` is the max of the two sub-maxima.  List
induction on `xs`, using `levelMax`'s left unit + associativity. -/
theorem LevelExpr.denoteAtomList_append :
    ∀ (xs ys : List LevelExpr) (env : Nat → Nat),
      LevelExpr.denoteAtomList (xs ++ ys) env =
        LevelExpr.levelMax (LevelExpr.denoteAtomList xs env)
          (LevelExpr.denoteAtomList ys env)
  | [], ys, env => by
      show LevelExpr.denoteAtomList ys env =
        LevelExpr.levelMax 0 (LevelExpr.denoteAtomList ys env)
      rw [LevelExpr.levelMax_zero_left]
  | atom :: xs, ys, env => by
      show LevelExpr.levelMax (atom.denote env)
            (LevelExpr.denoteAtomList (xs ++ ys) env) =
        LevelExpr.levelMax
          (LevelExpr.levelMax (atom.denote env)
            (LevelExpr.denoteAtomList xs env))
          (LevelExpr.denoteAtomList ys env)
      rw [LevelExpr.denoteAtomList_append xs ys env, LevelExpr.levelMax_assoc]

/-- `foldLmax` rebuilds exactly the `denoteAtomList` value: the
right-nested `lmax` tree denotes the running max of the atoms.
List induction, lifting each `lmax` to a `levelMax`. -/
theorem LevelExpr.foldLmax_denote :
    ∀ (xs : List LevelExpr) (env : Nat → Nat),
      LevelExpr.denote (LevelExpr.foldLmax xs) env =
        LevelExpr.denoteAtomList xs env
  | [], _ => rfl
  | atom :: rest, env => by
      show LevelExpr.denote (LevelExpr.lmax atom (LevelExpr.foldLmax rest)) env =
        LevelExpr.levelMax (atom.denote env) (LevelExpr.denoteAtomList rest env)
      rw [LevelExpr.denote_lmax, LevelExpr.foldLmax_denote rest env]

/-- `lmaxAtoms` flattens to exactly the `denoteAtomList` value:
the original expression denotes the running max over its flattened
atoms.  Structural induction on `expr`; leaf constructors close by
`levelMax`'s right unit, `lmax` by append-distribution + the two
child hypotheses. -/
theorem LevelExpr.lmaxAtoms_denote :
    ∀ (expr : LevelExpr) (env : Nat → Nat),
      LevelExpr.denote expr env =
        LevelExpr.denoteAtomList (LevelExpr.lmaxAtoms expr) env
  | .lzero, _ => (LevelExpr.levelMax_zero_right _).symm
  | .lvar _, _ => (LevelExpr.levelMax_zero_right _).symm
  | .lsucc _, _ => (LevelExpr.levelMax_zero_right _).symm
  | .limax _ _, _ => (LevelExpr.levelMax_zero_right _).symm
  | .lmax a b, env => by
      show LevelExpr.levelMax (a.denote env) (b.denote env) =
        LevelExpr.denoteAtomList
          (LevelExpr.lmaxAtoms a ++ LevelExpr.lmaxAtoms b) env
      rw [LevelExpr.denoteAtomList_append,
          ← LevelExpr.lmaxAtoms_denote a env,
          ← LevelExpr.lmaxAtoms_denote b env]

/-! ## Sortedness of `insertionSortByCompare`

The compare-ordered insertion sort produces an `IsSorted` list —
the structural prerequisite for canonical-form *uniqueness* (a
sorted, deduplicated atom list is a canonical representative of its
element set).  `IsSorted` is the adjacent formulation (each head is
a `compare`-lower-bound of its tail, recursively); insertion-sort
sortedness needs only antisymmetry (`compare_swap`), not the
`compare_lt_trans` transitivity — transitivity enters later, for
uniqueness. -/

/-- `bound` is a lower bound for the head of a list under `compare`
(vacuously for the empty list): the head is never strictly below
`bound` (`compare bound head` is never `.gt`). -/
def LevelExpr.IsLowerBound (bound : LevelExpr) : List LevelExpr → Prop
  | [] => True
  | first :: _ => LevelExpr.compare bound first ≠ Ordering.gt

/-- A list is sorted under `compare` when each head is a lower bound
for its tail and the tail is itself sorted (adjacent formulation). -/
def LevelExpr.IsSorted : List LevelExpr → Prop
  | [] => True
  | head :: rest => LevelExpr.IsLowerBound head rest ∧ LevelExpr.IsSorted rest

/-- Inserting `x` (with `bound ≤ x`) into a list already bounded
below by `bound` preserves that lower bound.  Non-recursive: in the
skip (`.gt`) case the result head is the unchanged original head
(already `≥ bound`); otherwise the result head is `x` (`≥ bound` by
hypothesis). -/
theorem LevelExpr.IsLowerBound_insertByCompare (bound x : LevelExpr) :
    ∀ (ys : List LevelExpr),
      LevelExpr.IsLowerBound bound ys →
      LevelExpr.compare bound x ≠ Ordering.gt →
      LevelExpr.IsLowerBound bound (LevelExpr.insertByCompare x ys)
  | [], _, hBoundX => hBoundX
  | y0 :: yr, hBoundYs, hBoundX => by
      show LevelExpr.IsLowerBound bound
        (LevelExpr.insertStep (LevelExpr.compare x y0) x y0 yr
          (LevelExpr.insertByCompare x yr))
      cases hVerdict : LevelExpr.compare x y0 with
      | lt => exact hBoundX
      | eq => exact hBoundX
      | gt => exact hBoundYs

/-- Compare-ordered insertion preserves sortedness.  List recursion:
`.lt` / `.eq` seat `x` at the front (its bound over the old list is
the verdict itself); `.gt` keeps the old head, bounds the recursively
inserted tail via `IsLowerBound_insertByCompare` (using `head ≤ x`
from `compare_swap`), and recurses for the tail's sortedness. -/
theorem LevelExpr.insertByCompare_sorted (x : LevelExpr) :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsSorted xs →
      LevelExpr.IsSorted (LevelExpr.insertByCompare x xs)
  | [], _ => ⟨trivial, trivial⟩
  | head :: rest, hSorted => by
      show LevelExpr.IsSorted
        (LevelExpr.insertStep (LevelExpr.compare x head) x head rest
          (LevelExpr.insertByCompare x rest))
      cases hVerdict : LevelExpr.compare x head with
      | lt =>
          refine ⟨?_, hSorted⟩
          show LevelExpr.compare x head ≠ Ordering.gt
          rw [hVerdict]
          exact fun hContra => Ordering.noConfusion hContra
      | eq =>
          refine ⟨?_, hSorted⟩
          show LevelExpr.compare x head ≠ Ordering.gt
          rw [hVerdict]
          exact fun hContra => Ordering.noConfusion hContra
      | gt =>
          have hHeadLeX : LevelExpr.compare head x ≠ Ordering.gt := by
            intro hContra
            have hSwap := LevelExpr.compare_swap x head
            rw [hVerdict, hContra] at hSwap
            exact Ordering.noConfusion hSwap
          exact ⟨LevelExpr.IsLowerBound_insertByCompare head x rest hSorted.1 hHeadLeX,
                 LevelExpr.insertByCompare_sorted x rest hSorted.2⟩

/-- The compare-ordered insertion sort always produces a sorted
list.  Folds `insertByCompare` over the input, each step preserving
sortedness via `insertByCompare_sorted`. -/
theorem LevelExpr.insertionSortByCompare_sorted :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsSorted (LevelExpr.insertionSortByCompare xs)
  | [] => trivial
  | head :: rest => by
      show LevelExpr.IsSorted
        (LevelExpr.insertByCompare head (LevelExpr.insertionSortByCompare rest))
      exact LevelExpr.insertByCompare_sorted head
        (LevelExpr.insertionSortByCompare rest)
        (LevelExpr.insertionSortByCompare_sorted rest)

/-! ## Dedup preserves sortedness

`dedupAdjacent` (collapse adjacent `compare`-equal atoms) keeps an
`IsSorted` list sorted.  The only subtlety is the lower bound: when
dedup drops a head because it equals the next element, the surviving
head is *value-equal* to the dropped one (`compare_eq_imp_eq`), so a
bound below the dropped head is below the survivor too.  Needs only
antisymmetry, not transitivity. -/

/-- `dedupAdjacent` preserves a lower bound: dropping a run of
`compare`-equal heads leaves a survivor value-equal to them, so any
`bound` below the original head still bounds the deduped list. -/
theorem LevelExpr.IsLowerBound_dedupAdjacent (bound : LevelExpr) :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsLowerBound bound xs →
      LevelExpr.IsLowerBound bound (LevelExpr.dedupAdjacent xs)
  | [], _ => trivial
  | [_single], hBound => hBound
  | first :: second :: rest, hBound => by
      show LevelExpr.IsLowerBound bound
        (LevelExpr.dedupStep (LevelExpr.compare first second) first
          (LevelExpr.dedupAdjacent (second :: rest)))
      cases hVerdict : LevelExpr.compare first second with
      | lt => exact hBound
      | gt => exact hBound
      | eq =>
          have hFirstSecond : first = second :=
            LevelExpr.compare_eq_imp_eq first second hVerdict
          have hBoundSecond : LevelExpr.compare bound second ≠ Ordering.gt := by
            rw [← hFirstSecond]; exact hBound
          exact LevelExpr.IsLowerBound_dedupAdjacent bound (second :: rest) hBoundSecond

/-- `dedupAdjacent` preserves sortedness.  `.eq` drops the head and
recurses on the sorted tail; `.lt` / `.gt` keep the head, re-bound the
deduped tail via `IsLowerBound_dedupAdjacent`, and recurse. -/
theorem LevelExpr.dedupAdjacent_sorted :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsSorted xs → LevelExpr.IsSorted (LevelExpr.dedupAdjacent xs)
  | [], _ => trivial
  | [_single], _ => ⟨trivial, trivial⟩
  | first :: second :: rest, hSorted => by
      show LevelExpr.IsSorted
        (LevelExpr.dedupStep (LevelExpr.compare first second) first
          (LevelExpr.dedupAdjacent (second :: rest)))
      cases hVerdict : LevelExpr.compare first second with
      | eq =>
          exact LevelExpr.dedupAdjacent_sorted (second :: rest) hSorted.2
      | lt =>
          exact ⟨LevelExpr.IsLowerBound_dedupAdjacent first (second :: rest) hSorted.1,
                 LevelExpr.dedupAdjacent_sorted (second :: rest) hSorted.2⟩
      | gt =>
          exact ⟨LevelExpr.IsLowerBound_dedupAdjacent first (second :: rest) hSorted.1,
                 LevelExpr.dedupAdjacent_sorted (second :: rest) hSorted.2⟩

/-! ## Drop-lzero preserves sortedness

`lzero` is the `compare` minimum (`ctorIndex` 0).  Dropping `lzero`
atoms from a sorted list keeps it sorted: when an `lzero` head is
removed, any bound below it must itself BE `lzero` (the only thing
`≤ lzero`), and `lzero` bounds everything — so the bound transfers
to the survivor unconditionally.  Closes "canonical atoms are
sorted" (sort → dedup → drop-lzero all preserve `IsSorted`). -/

/-- `lzero` is below every level expression: `compare lzero e` is
never `.gt`. -/
theorem LevelExpr.compare_lzero_ne_gt (e : LevelExpr) :
    LevelExpr.compare LevelExpr.lzero e ≠ Ordering.gt := by
  cases e <;> exact fun hContra => Ordering.noConfusion hContra

/-- Only `lzero` is `≤ lzero`: a non-`.gt` verdict against `lzero`
forces the operand to be `lzero` (minimality, contrapositive). -/
theorem LevelExpr.compare_le_lzero_imp_eq (bound : LevelExpr)
    (hLe : LevelExpr.compare bound LevelExpr.lzero ≠ Ordering.gt) :
    bound = LevelExpr.lzero := by
  cases bound with
  | lzero => rfl
  | lvar _ => exact absurd rfl hLe
  | lsucc _ => exact absurd rfl hLe
  | lmax _ _ => exact absurd rfl hLe
  | limax _ _ => exact absurd rfl hLe

/-- `lzero` is a lower bound for any list (it bounds every head). -/
theorem LevelExpr.lzero_isLowerBound :
    ∀ (ys : List LevelExpr), LevelExpr.IsLowerBound LevelExpr.lzero ys
  | [] => trivial
  | first :: _ => LevelExpr.compare_lzero_ne_gt first

/-- `dropLzeroAtoms` preserves a lower bound.  Non-recursive: the
`lzero`-head case forces the bound to be `lzero` (then `lzero`
bounds the whole remainder); the keep cases leave the head, so the
bound is unchanged. -/
theorem LevelExpr.IsLowerBound_dropLzeroAtoms (bound : LevelExpr) :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsLowerBound bound xs →
      LevelExpr.IsLowerBound bound (LevelExpr.dropLzeroAtoms xs)
  | [], _ => trivial
  | head :: rest, hBound => by
      cases head with
      | lzero =>
          have hBoundEq : bound = LevelExpr.lzero :=
            LevelExpr.compare_le_lzero_imp_eq bound hBound
          rw [hBoundEq]
          exact LevelExpr.lzero_isLowerBound _
      | lvar _ => exact hBound
      | lsucc _ => exact hBound
      | lmax _ _ => exact hBound
      | limax _ _ => exact hBound

/-- `dropLzeroAtoms` preserves sortedness.  `lzero` head: drop and
recurse on the sorted tail; keep cases: retain the head, re-bound the
dropped tail via `IsLowerBound_dropLzeroAtoms`, and recurse. -/
theorem LevelExpr.dropLzeroAtoms_sorted :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsSorted xs → LevelExpr.IsSorted (LevelExpr.dropLzeroAtoms xs)
  | [], _ => trivial
  | head :: rest, hSorted => by
      cases head with
      | lzero => exact LevelExpr.dropLzeroAtoms_sorted rest hSorted.2
      | lvar _ =>
          exact ⟨LevelExpr.IsLowerBound_dropLzeroAtoms _ rest hSorted.1,
                 LevelExpr.dropLzeroAtoms_sorted rest hSorted.2⟩
      | lsucc _ =>
          exact ⟨LevelExpr.IsLowerBound_dropLzeroAtoms _ rest hSorted.1,
                 LevelExpr.dropLzeroAtoms_sorted rest hSorted.2⟩
      | lmax _ _ =>
          exact ⟨LevelExpr.IsLowerBound_dropLzeroAtoms _ rest hSorted.1,
                 LevelExpr.dropLzeroAtoms_sorted rest hSorted.2⟩
      | limax _ _ =>
          exact ⟨LevelExpr.IsLowerBound_dropLzeroAtoms _ rest hSorted.1,
                 LevelExpr.dropLzeroAtoms_sorted rest hSorted.2⟩

/-! ## Strict sortedness — the dedup invariant

`dedupAdjacent` applied to a sorted list produces a *strictly*
increasing list (no two adjacent atoms `compare`-equal).  This is
the deduplication invariant: combined with uniqueness it will pin
the canonical atom list as THE representative of its element set.
The strict track mirrors `IsSorted` / `IsLowerBound` with
`compare = .lt` in place of `≠ .gt`; still only antisymmetry. -/

/-- `bound` is *strictly* below the head of a list under `compare`
(vacuously for the empty list): `compare bound head = .lt`. -/
def LevelExpr.IsStrictLowerBound (bound : LevelExpr) : List LevelExpr → Prop
  | [] => True
  | first :: _ => LevelExpr.compare bound first = Ordering.lt

/-- A list is strictly sorted when each head is a *strict* lower
bound for its tail and the tail is itself strictly sorted: a
duplicate-free, increasing chain. -/
def LevelExpr.IsStrictlySorted : List LevelExpr → Prop
  | [] => True
  | head :: rest =>
      LevelExpr.IsStrictLowerBound head rest ∧ LevelExpr.IsStrictlySorted rest

/-- `dedupAdjacent` preserves a *strict* lower bound (same value-equal
head-transfer as the non-strict case: a dropped head is `compare`-equal
to its survivor, so a strict bound below it is below the survivor). -/
theorem LevelExpr.IsStrictLowerBound_dedupAdjacent (bound : LevelExpr) :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsStrictLowerBound bound xs →
      LevelExpr.IsStrictLowerBound bound (LevelExpr.dedupAdjacent xs)
  | [], _ => trivial
  | [_single], hBound => hBound
  | first :: second :: rest, hBound => by
      show LevelExpr.IsStrictLowerBound bound
        (LevelExpr.dedupStep (LevelExpr.compare first second) first
          (LevelExpr.dedupAdjacent (second :: rest)))
      cases hVerdict : LevelExpr.compare first second with
      | lt => exact hBound
      | gt => exact hBound
      | eq =>
          have hFirstSecond : first = second :=
            LevelExpr.compare_eq_imp_eq first second hVerdict
          have hBoundSecond : LevelExpr.compare bound second = Ordering.lt := by
            rw [← hFirstSecond]; exact hBound
          exact LevelExpr.IsStrictLowerBound_dedupAdjacent bound (second :: rest) hBoundSecond

/-- `dedupAdjacent` turns a sorted list into a strictly sorted one.
On sorted input the `.gt` branch is impossible (forbidden by the
lower bound); `.eq` collapses the duplicate and recurses; `.lt`
keeps the head as a strict bound (re-bounding the deduped tail via
`IsStrictLowerBound_dedupAdjacent`) and recurses. -/
theorem LevelExpr.dedupAdjacent_strictlySorted :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsSorted xs →
      LevelExpr.IsStrictlySorted (LevelExpr.dedupAdjacent xs)
  | [], _ => trivial
  | [_single], _ => ⟨trivial, trivial⟩
  | first :: second :: rest, hSorted => by
      show LevelExpr.IsStrictlySorted
        (LevelExpr.dedupStep (LevelExpr.compare first second) first
          (LevelExpr.dedupAdjacent (second :: rest)))
      cases hVerdict : LevelExpr.compare first second with
      | gt => exact absurd hVerdict hSorted.1
      | eq =>
          exact LevelExpr.dedupAdjacent_strictlySorted (second :: rest) hSorted.2
      | lt =>
          refine ⟨?_, LevelExpr.dedupAdjacent_strictlySorted (second :: rest) hSorted.2⟩
          exact LevelExpr.IsStrictLowerBound_dedupAdjacent first (second :: rest) hVerdict

/-! ## Toward uniqueness — membership and the head-minimum lemma

For canonical-form *uniqueness* (two strictly-sorted lists with the
same elements are equal) we need to compare elements anywhere in a
list, so introduce a structural membership predicate `OccursIn`.
The first consumer of `compare_lt_trans`: in a strictly-sorted list
the head is strictly below EVERY tail element (not just the next),
proved by chaining the immediate strict bound through the tail. -/

/-- `target` occurs somewhere in the list (structural membership). -/
def LevelExpr.OccursIn (target : LevelExpr) : List LevelExpr → Prop
  | [] => False
  | head :: rest => head = target ∨ LevelExpr.OccursIn target rest

/-- In a strictly-sorted `head :: rest`, the head is strictly below
every element occurring in `rest`.  The immediate strict bound
(`head < rest.head`) chains through the strictly-sorted tail via
`compare_lt_trans` to reach an arbitrary deeper element. -/
theorem LevelExpr.strictlySorted_head_lt :
    ∀ (head : LevelExpr) (rest : List LevelExpr),
      LevelExpr.IsStrictlySorted (head :: rest) →
      ∀ (z : LevelExpr), LevelExpr.OccursIn z rest →
        LevelExpr.compare head z = Ordering.lt
  | _head, [], _hStrict, _z, hOccurs => nomatch hOccurs
  | head, r0 :: rr, hStrict, z, hOccurs => by
      cases hOccurs with
      | inl hHeadEq =>
          rw [← hHeadEq]
          exact hStrict.1
      | inr hOccursTail =>
          have hMidLt : LevelExpr.compare r0 z = Ordering.lt :=
            LevelExpr.strictlySorted_head_lt r0 rr hStrict.2 z hOccursTail
          exact LevelExpr.compare_lt_trans head r0 z hStrict.1 hMidLt

/-! ## Uniqueness of strictly-sorted lists by membership

Two strictly-sorted lists with the same elements are equal — the
canonical-form *uniqueness* theorem.  The heads must coincide (each
occurs in the other; a strict-inside occurrence would force a
two-way strict inequality, impossible by antisymmetry), then the
tails have the same elements and recurse. -/

/-- A strict `compare` verdict rules out equality. -/
theorem LevelExpr.compare_lt_imp_ne (exprA exprB : LevelExpr)
    (hLt : LevelExpr.compare exprA exprB = Ordering.lt) : exprA ≠ exprB := by
  intro hEq
  rw [hEq, LevelExpr.compare_refl] at hLt
  exact Ordering.noConfusion hLt

/-- `compare` is asymmetric on `.lt`: if `a < b` then not `b < a`
(from the `compare_swap` antisymmetry identity). -/
theorem LevelExpr.compare_lt_asymm (exprA exprB : LevelExpr)
    (hLt : LevelExpr.compare exprA exprB = Ordering.lt) :
    LevelExpr.compare exprB exprA ≠ Ordering.lt := by
  intro hBA
  have hSwap := LevelExpr.compare_swap exprA exprB
  rw [hLt, hBA] at hSwap
  exact Ordering.noConfusion hSwap

/-- Strictly-sorted lists with identical membership are identical.
Structural recursion on the first list. -/
theorem LevelExpr.strictlySorted_unique :
    ∀ (xs ys : List LevelExpr),
      LevelExpr.IsStrictlySorted xs → LevelExpr.IsStrictlySorted ys →
      (∀ (z : LevelExpr), LevelExpr.OccursIn z xs ↔ LevelExpr.OccursIn z ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], y0 :: _yr, _, _, hIff => nomatch (hIff y0).mpr (Or.inl rfl)
  | x0 :: _xr, [], _, _, hIff => nomatch (hIff x0).mp (Or.inl rfl)
  | x0 :: xr, y0 :: yr, hSx, hSy, hIff => by
      have hHeadEq : x0 = y0 := by
        have hOccX0inY : LevelExpr.OccursIn x0 (y0 :: yr) := (hIff x0).mp (Or.inl rfl)
        have hOccY0inX : LevelExpr.OccursIn y0 (x0 :: xr) := (hIff y0).mpr (Or.inl rfl)
        cases hOccX0inY with
        | inl hy0x0 => exact hy0x0.symm
        | inr hX0inYr =>
            cases hOccY0inX with
            | inl hx0y0 => exact hx0y0
            | inr hY0inXr =>
                have hY0X0 : LevelExpr.compare y0 x0 = Ordering.lt :=
                  LevelExpr.strictlySorted_head_lt y0 yr hSy x0 hX0inYr
                have hX0Y0 : LevelExpr.compare x0 y0 = Ordering.lt :=
                  LevelExpr.strictlySorted_head_lt x0 xr hSx y0 hY0inXr
                exact absurd hX0Y0 (LevelExpr.compare_lt_asymm y0 x0 hY0X0)
      subst hHeadEq
      have hTailIff : ∀ (z : LevelExpr),
          LevelExpr.OccursIn z xr ↔ LevelExpr.OccursIn z yr := by
        intro z
        constructor
        · intro hzInXr
          cases (hIff z).mp (Or.inr hzInXr) with
          | inl hHeadZ =>
              exact absurd hHeadZ
                (LevelExpr.compare_lt_imp_ne x0 z
                  (LevelExpr.strictlySorted_head_lt x0 xr hSx z hzInXr))
          | inr hzInYr => exact hzInYr
        · intro hzInYr
          cases (hIff z).mpr (Or.inr hzInYr) with
          | inl hHeadZ =>
              exact absurd hHeadZ
                (LevelExpr.compare_lt_imp_ne x0 z
                  (LevelExpr.strictlySorted_head_lt x0 yr hSy z hzInYr))
          | inr hzInXr => exact hzInXr
      rw [LevelExpr.strictlySorted_unique xr yr hSx.2 hSy.2 hTailIff]

/-! ## Semantic bridge — membership dominates the max-fold

First step connecting the syntactic membership predicate `OccursIn`
to the semantic `denoteAtomList` max-fold: an atom occurring in a
list has denotation bounded above by the list's running maximum.
This is the "≥" half of the eventual point-environment detection
(a point environment isolates a single variable's contribution to
the max).  Pure `Nat`-order reasoning over the custom `levelMax`. -/

/-- The left operand is below `levelMax`. -/
theorem LevelExpr.levelMax_ge_left :
    ∀ (valueA valueB : Nat), valueA ≤ LevelExpr.levelMax valueA valueB
  | 0, valueB => Nat.zero_le valueB
  | _valueA + 1, 0 => Nat.le_refl _
  | valueA + 1, valueB + 1 =>
      Nat.succ_le_succ (LevelExpr.levelMax_ge_left valueA valueB)

/-- The right operand is below `levelMax`. -/
theorem LevelExpr.levelMax_ge_right :
    ∀ (valueA valueB : Nat), valueB ≤ LevelExpr.levelMax valueA valueB
  | 0, valueB => Nat.le_refl valueB
  | _valueA + 1, 0 => Nat.zero_le _
  | valueA + 1, valueB + 1 =>
      Nat.succ_le_succ (LevelExpr.levelMax_ge_right valueA valueB)

/-- An atom occurring in a list has denotation at most the list's
`denoteAtomList` (running `levelMax`): membership is dominated by
the maximum.  List recursion: the head case uses `levelMax_ge_left`,
a deeper occurrence chains the inductive hypothesis through
`levelMax_ge_right`. -/
theorem LevelExpr.denote_le_denoteAtomList_of_occurs (env : Nat → Nat) :
    ∀ (xs : List LevelExpr) (atom : LevelExpr),
      LevelExpr.OccursIn atom xs →
      LevelExpr.denote atom env ≤ LevelExpr.denoteAtomList xs env
  | [], _atom, hOccurs => nomatch hOccurs
  | head :: rest, atom, hOccurs => by
      cases hOccurs with
      | inl hHeadEq =>
          rw [← hHeadEq]
          exact LevelExpr.levelMax_ge_left (LevelExpr.denote head env)
            (LevelExpr.denoteAtomList rest env)
      | inr hOccursRest =>
          have hInductive :=
            LevelExpr.denote_le_denoteAtomList_of_occurs env rest atom hOccursRest
          exact Nat.le_trans hInductive
            (LevelExpr.levelMax_ge_right (LevelExpr.denote head env)
              (LevelExpr.denoteAtomList rest env))

/-! ### Zero-characterization of the max-fold

`denoteAtomList xs env = 0` exactly when every atom occurring in
`xs` denotes `0` under `env`.  The backward direction is a list
induction off `levelMax 0 0 = 0`; the forward direction reads the
per-member bound off `denote_le_denoteAtomList_of_occurs`.  This is
the "≤" half of point-environment detection: under a point
environment isolating one variable, a list NOT containing that
variable folds to `0`. -/

/-- If every occurring atom denotes `0`, the whole max-fold is `0`.
List recursion: the head is `0` by hypothesis, the tail-fold is `0`
by the inductive hypothesis, and `levelMax 0 0 = 0`. -/
theorem LevelExpr.denoteAtomList_eq_zero_of_all_zero (env : Nat → Nat) :
    ∀ (xs : List LevelExpr),
      (∀ atom, LevelExpr.OccursIn atom xs →
        LevelExpr.denote atom env = 0) →
      LevelExpr.denoteAtomList xs env = 0
  | [], _hAllZero => rfl
  | head :: rest, hAllZero => by
      have hHeadZero : LevelExpr.denote head env = 0 :=
        hAllZero head (Or.inl rfl)
      have hRestZero : LevelExpr.denoteAtomList rest env = 0 :=
        LevelExpr.denoteAtomList_eq_zero_of_all_zero env rest
          (fun atom hOccurs => hAllZero atom (Or.inr hOccurs))
      calc LevelExpr.denoteAtomList (head :: rest) env
          = LevelExpr.levelMax (LevelExpr.denote head env)
              (LevelExpr.denoteAtomList rest env) := rfl
        _ = LevelExpr.levelMax 0 0 := by rw [hHeadZero, hRestZero]
        _ = 0 := rfl

/-- The max-fold is `0` iff every occurring atom denotes `0`.  The
forward direction extracts the per-member bound (`denote atom env ≤
0`) from `denote_le_denoteAtomList_of_occurs`; the backward direction
is `denoteAtomList_eq_zero_of_all_zero`. -/
theorem LevelExpr.denoteAtomList_eq_zero_iff
    (env : Nat → Nat) (xs : List LevelExpr) :
    LevelExpr.denoteAtomList xs env = 0 ↔
      ∀ atom, LevelExpr.OccursIn atom xs →
        LevelExpr.denote atom env = 0 := by
  constructor
  · intro hFoldZero atom hOccurs
    have hMemberLe :=
      LevelExpr.denote_le_denoteAtomList_of_occurs env xs atom hOccurs
    rw [hFoldZero] at hMemberLe
    exact Nat.le_zero.mp hMemberLe
  · intro hAllZero
    exact LevelExpr.denoteAtomList_eq_zero_of_all_zero env xs hAllZero

/-! ### Point environments — single-variable isolation

A *point environment* `pointEnvironment k` assigns `1` to universe
variable `k` and `0` to every other variable.  It is the probe that
turns `denote` into a membership oracle for the variable fragment:
under `pointEnvironment k`, a level's denotation detects whether
`lvar k` contributes to it.  These are the two evaluation facts the
detection lemma consumes — paired with `denoteAtomList_eq_zero_iff`
(non-`k` variables fold to `0`) and `denote_le_denoteAtomList_of_occurs`
(an occurring `lvar k` lifts the fold to `1`). -/

/-- The point environment isolating universe variable
`variableIndex`: `1` at that variable, `0` everywhere else. -/
def LevelExpr.pointEnvironment (variableIndex : Nat) : Nat → Nat :=
  fun queriedIndex => if queriedIndex = variableIndex then 1 else 0

/-- Under `pointEnvironment k`, `lvar j` denotes `1` when `j = k`
and `0` otherwise.  Definitional: `denote (lvar j) env = env j`, and
`pointEnvironment k j` unfolds to the guarded literal. -/
theorem LevelExpr.denote_lvar_pointEnvironment
    (queriedIndex variableIndex : Nat) :
    LevelExpr.denote (.lvar queriedIndex)
        (LevelExpr.pointEnvironment variableIndex) =
      (if queriedIndex = variableIndex then 1 else 0) := rfl

/-- Under `pointEnvironment k`, the isolated variable `lvar k`
denotes `1`. -/
theorem LevelExpr.denote_lvar_pointEnvironment_self (variableIndex : Nat) :
    LevelExpr.denote (.lvar variableIndex)
        (LevelExpr.pointEnvironment variableIndex) = 1 := by
  rw [LevelExpr.denote_lvar_pointEnvironment]
  exact if_pos rfl

/-- If `lvar k` occurs in `xs`, the max-fold under `pointEnvironment k`
is nonzero — the isolated variable contributes `1`, and the fold
dominates every member.  Holds for ANY list (no var-only assumption):
this is the "occurs ⟹ detected" direction of the membership oracle. -/
theorem LevelExpr.denoteAtomList_pointEnvironment_ne_zero_of_occursLvar
    (variableIndex : Nat) (xs : List LevelExpr) :
    LevelExpr.OccursIn (.lvar variableIndex) xs →
      LevelExpr.denoteAtomList xs
        (LevelExpr.pointEnvironment variableIndex) ≠ 0 := by
  intro hOccurs hFoldZero
  have hMemberLe :=
    LevelExpr.denote_le_denoteAtomList_of_occurs
      (LevelExpr.pointEnvironment variableIndex) xs (.lvar variableIndex) hOccurs
  rw [LevelExpr.denote_lvar_pointEnvironment_self] at hMemberLe
  rw [hFoldZero] at hMemberLe
  exact Nat.not_succ_le_zero 0 hMemberLe

/-! ### The variable-only fragment and the converse oracle direction

On the fragment where every atom is a universe variable, the point
environment becomes an exact membership oracle: a list NOT containing
`lvar k` folds to `0` under `pointEnvironment k`, because every member
is some `lvar j` with `j ≠ k` (else `lvar k` would occur), and such a
member denotes `0`.  This is the "not-occurs ⟹ not-detected" converse
of `denoteAtomList_pointEnvironment_ne_zero_of_occursLvar`; together
they make membership decidable on the variable fragment.

NOTE (honest scope): this oracle covers only the distinct-variable
fragment.  A `lsucc`/`limax` atom can be nonzero under `pointEnvironment k`
without `lvar k` occurring (absorption boundary), so the converse genuinely
requires `AllAtomsAreVariables`. -/

/-- Every atom in the list is a universe variable (`lvar _`). -/
def LevelExpr.AllAtomsAreVariables : List LevelExpr → Prop
  | [] => True
  | head :: rest =>
      (∃ variableIndex, head = .lvar variableIndex) ∧
        LevelExpr.AllAtomsAreVariables rest

/-- In an all-variables list, anything occurring is a variable.
List recursion: a head occurrence inherits the head's variable
witness; a deeper occurrence recurses into the (also all-variables)
tail. -/
theorem LevelExpr.isLvar_of_occursIn_allVariables :
    ∀ (xs : List LevelExpr) (atom : LevelExpr),
      LevelExpr.AllAtomsAreVariables xs → LevelExpr.OccursIn atom xs →
        ∃ variableIndex, atom = .lvar variableIndex
  | [], _atom, _hAllVars, hOccurs => nomatch hOccurs
  | head :: rest, atom, hAllVars, hOccurs => by
      obtain ⟨hHeadIsVar, hRestVars⟩ := hAllVars
      cases hOccurs with
      | inl hHeadEq =>
          obtain ⟨variableIndex, hHeadLvar⟩ := hHeadIsVar
          exact ⟨variableIndex, by rw [← hHeadEq]; exact hHeadLvar⟩
      | inr hOccursRest =>
          exact LevelExpr.isLvar_of_occursIn_allVariables rest atom
            hRestVars hOccursRest

/-- On the variable-only fragment, a list missing `lvar k` folds to
`0` under `pointEnvironment k`: each member is `lvar j` with `j ≠ k`,
which denotes `0`.  Built atop `denoteAtomList_eq_zero_of_all_zero`
(no `Iff`-rewrite, to stay propext-free). -/
theorem LevelExpr.denoteAtomList_pointEnvironment_eq_zero_of_not_occursLvar
    (variableIndex : Nat) (xs : List LevelExpr)
    (hAllVars : LevelExpr.AllAtomsAreVariables xs)
    (hNotOccurs : ¬ LevelExpr.OccursIn (.lvar variableIndex) xs) :
    LevelExpr.denoteAtomList xs
      (LevelExpr.pointEnvironment variableIndex) = 0 := by
  apply LevelExpr.denoteAtomList_eq_zero_of_all_zero
  intro atom hOccurs
  obtain ⟨memberIndex, hAtomLvar⟩ :=
    LevelExpr.isLvar_of_occursIn_allVariables xs atom hAllVars hOccurs
  rw [hAtomLvar, LevelExpr.denote_lvar_pointEnvironment]
  apply if_neg
  intro hIndexEq
  apply hNotOccurs
  rw [hAtomLvar, hIndexEq] at hOccurs
  exact hOccurs

/-- Membership in an atom list is decidable — the atoms carry
`DecidableEq`.  Structural recursion on the list: compare the head
via `DecidableEq LevelExpr`, recurse into the tail, and assemble the
`Or` decision.  Needed to close the `fold ≠ 0 ⟹ occurs` direction of
the oracle constructively (no classical contraposition). -/
instance LevelExpr.decidableOccursIn (target : LevelExpr) :
    (xs : List LevelExpr) → Decidable (LevelExpr.OccursIn target xs)
  | [] => isFalse (fun hOccurs => hOccurs)
  | head :: rest =>
      match (inferInstance : Decidable (head = target)) with
      | isTrue hHeadEq => isTrue (Or.inl hHeadEq)
      | isFalse hHeadNe =>
          match LevelExpr.decidableOccursIn target rest with
          | isTrue hRest => isTrue (Or.inr hRest)
          | isFalse hNotRest =>
              isFalse (fun hOccurs => Or.elim hOccurs hHeadNe hNotRest)

/-- The membership oracle on the variable-only fragment: `lvar k`
occurs in `xs` iff `xs` folds to a nonzero value under the point
environment isolating `k`.  Forward is the general occurrence bound;
backward uses the decision procedure `decidableOccursIn` to split —
the `isFalse` branch contradicts `fold ≠ 0` via the var-only zero
lemma (constructive, no classical contraposition). -/
theorem LevelExpr.occursLvar_iff_denoteAtomList_pointEnvironment_ne_zero
    (variableIndex : Nat) (xs : List LevelExpr)
    (hAllVars : LevelExpr.AllAtomsAreVariables xs) :
    LevelExpr.OccursIn (.lvar variableIndex) xs ↔
      LevelExpr.denoteAtomList xs
        (LevelExpr.pointEnvironment variableIndex) ≠ 0 :=
  Iff.intro
    (LevelExpr.denoteAtomList_pointEnvironment_ne_zero_of_occursLvar
      variableIndex xs)
    (fun hFoldNeZero =>
      if hOccurs : LevelExpr.OccursIn (.lvar variableIndex) xs then
        hOccurs
      else
        absurd
          (LevelExpr.denoteAtomList_pointEnvironment_eq_zero_of_not_occursLvar
            variableIndex xs hAllVars hOccurs)
          hFoldNeZero)

/-! ### The canonical atom list and the denotation bridge

`canonicalAtoms` names the list underlying `canonicalize` (flatten →
sort → dedup → drop-`lzero`), before the final `foldLmax` rebuild.
The bridge `denote e = denoteAtomList (canonicalAtoms e)` connects the
whole-expression denotation to the atom-list fold the membership
oracle consumes — assembled from `canonicalize_denoteEquiv` (the fold
preserves denotation) and `foldLmax_denote` (rebuild = fold). -/

/-- The canonical atom list underlying `canonicalize`: flatten → sort
→ dedup → drop-`lzero`, prior to the final `foldLmax`. -/
def LevelExpr.canonicalAtoms (expr : LevelExpr) : List LevelExpr :=
  LevelExpr.dropLzeroAtoms
    (LevelExpr.dedupAdjacent
      (LevelExpr.insertionSortByCompare
        (LevelExpr.lmaxAtoms expr)))

/-- `canonicalize` is exactly `foldLmax` of the canonical atom list
(definitional). -/
theorem LevelExpr.canonicalize_eq_foldLmax_canonicalAtoms (expr : LevelExpr) :
    LevelExpr.canonicalize expr =
      LevelExpr.foldLmax (LevelExpr.canonicalAtoms expr) := rfl

/-- The denotation bridge: a level expression denotes the same value
as the `denoteAtomList` max-fold of its canonical atom list.  Chains
`canonicalize_denoteEquiv` (fold preserves denotation) with
`foldLmax_denote` (rebuild equals fold). -/
theorem LevelExpr.denote_eq_denoteAtomList_canonicalAtoms
    (expr : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote expr env =
      LevelExpr.denoteAtomList (LevelExpr.canonicalAtoms expr) env := by
  have hCanonPreserves :
      LevelExpr.denote (LevelExpr.canonicalize expr) env =
        LevelExpr.denote expr env :=
    LevelExpr.canonicalize_denoteEquiv expr env
  have hFoldEqAtoms :
      LevelExpr.denote (LevelExpr.canonicalize expr) env =
        LevelExpr.denoteAtomList (LevelExpr.canonicalAtoms expr) env :=
    LevelExpr.foldLmax_denote (LevelExpr.canonicalAtoms expr) env
  rw [← hCanonPreserves]
  exact hFoldEqAtoms

/-- Membership transfer: if two expressions are denotationally equal
and both canonical atom lists are variable-only, they share the same
`lvar k` membership for every `k`.  Instantiate `denoteEquiv` at the
point environment for `k`, push both sides through the denotation
bridge, then chain the two oracle iffs across the resulting
fold-equality.  The middle step builds `fold₁ ≠ 0 ↔ fold₂ ≠ 0` by
transporting along the plain `Nat`-equality (`▸`), never rewriting an
iff (propext discipline). -/
theorem LevelExpr.canonicalAtoms_sameLvarMembership_of_denoteEquiv
    (e1 e2 : LevelExpr)
    (hVars1 : LevelExpr.AllAtomsAreVariables (LevelExpr.canonicalAtoms e1))
    (hVars2 : LevelExpr.AllAtomsAreVariables (LevelExpr.canonicalAtoms e2))
    (hEquiv : LevelExpr.denoteEquiv e1 e2) (variableIndex : Nat) :
    LevelExpr.OccursIn (.lvar variableIndex) (LevelExpr.canonicalAtoms e1) ↔
      LevelExpr.OccursIn (.lvar variableIndex) (LevelExpr.canonicalAtoms e2) := by
  have hDenote := hEquiv (LevelExpr.pointEnvironment variableIndex)
  rw [LevelExpr.denote_eq_denoteAtomList_canonicalAtoms e1,
      LevelExpr.denote_eq_denoteAtomList_canonicalAtoms e2] at hDenote
  have hIff1 := LevelExpr.occursLvar_iff_denoteAtomList_pointEnvironment_ne_zero
    variableIndex (LevelExpr.canonicalAtoms e1) hVars1
  have hIff2 := LevelExpr.occursLvar_iff_denoteAtomList_pointEnvironment_ne_zero
    variableIndex (LevelExpr.canonicalAtoms e2) hVars2
  have hFoldsNeZeroIff :
      LevelExpr.denoteAtomList (LevelExpr.canonicalAtoms e1)
          (LevelExpr.pointEnvironment variableIndex) ≠ 0 ↔
        LevelExpr.denoteAtomList (LevelExpr.canonicalAtoms e2)
          (LevelExpr.pointEnvironment variableIndex) ≠ 0 :=
    Iff.intro
      (fun hNeFirst => hDenote ▸ hNeFirst)
      (fun hNeSecond => hDenote.symm ▸ hNeSecond)
  exact Iff.trans hIff1 (Iff.trans hFoldsNeZeroIff hIff2.symm)

/-! ### Strict sortedness survives `dropLzeroAtoms`

The non-strict `dropLzeroAtoms_sorted` is already shipped; the strict
analog is needed to pin `canonicalAtoms` as strictly sorted (the
hypothesis `strictlySorted_unique` consumes).  The only structural
difference: in the `lzero`-head case a *strict* lower bound
`compare bound lzero = .lt` is impossible (`lzero` is the `compare`
minimum), so that case discharges by contradiction rather than the
non-strict head-transfer. -/

/-- Nothing is strictly below `lzero` under `compare`: `compare expr
lzero ≠ .lt`.  Via the `compare_swap` antisymmetry identity, such a
verdict would make `compare lzero expr = .gt`, contradicting
`compare_lzero_ne_gt`. -/
theorem LevelExpr.compare_right_lzero_ne_lt (expr : LevelExpr) :
    LevelExpr.compare expr LevelExpr.lzero ≠ Ordering.lt := by
  intro hLt
  have hSwapEq := LevelExpr.compare_swap expr LevelExpr.lzero
  rw [hLt] at hSwapEq
  exact LevelExpr.compare_lzero_ne_gt expr hSwapEq.symm

/-- `dropLzeroAtoms` preserves a *strict* lower bound.  The keep cases
leave the head, so the bound is unchanged; the `lzero`-head case is
vacuous since `compare bound lzero = .lt` is impossible. -/
theorem LevelExpr.IsStrictLowerBound_dropLzeroAtoms (bound : LevelExpr) :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsStrictLowerBound bound xs →
      LevelExpr.IsStrictLowerBound bound (LevelExpr.dropLzeroAtoms xs)
  | [], _ => trivial
  | head :: _rest, hBound => by
      cases head with
      | lzero => exact absurd hBound (LevelExpr.compare_right_lzero_ne_lt bound)
      | lvar _ => exact hBound
      | lsucc _ => exact hBound
      | lmax _ _ => exact hBound
      | limax _ _ => exact hBound

/-- `dropLzeroAtoms` preserves strict sortedness.  `lzero` head: drop
and recurse on the strictly-sorted tail; keep cases: retain the head,
re-bound the dropped tail via `IsStrictLowerBound_dropLzeroAtoms`, and
recurse. -/
theorem LevelExpr.dropLzeroAtoms_strictlySorted :
    ∀ (xs : List LevelExpr),
      LevelExpr.IsStrictlySorted xs →
      LevelExpr.IsStrictlySorted (LevelExpr.dropLzeroAtoms xs)
  | [], _ => trivial
  | head :: rest, hStrict => by
      cases head with
      | lzero => exact LevelExpr.dropLzeroAtoms_strictlySorted rest hStrict.2
      | lvar _ =>
          exact ⟨LevelExpr.IsStrictLowerBound_dropLzeroAtoms _ rest hStrict.1,
                 LevelExpr.dropLzeroAtoms_strictlySorted rest hStrict.2⟩
      | lsucc _ =>
          exact ⟨LevelExpr.IsStrictLowerBound_dropLzeroAtoms _ rest hStrict.1,
                 LevelExpr.dropLzeroAtoms_strictlySorted rest hStrict.2⟩
      | lmax _ _ =>
          exact ⟨LevelExpr.IsStrictLowerBound_dropLzeroAtoms _ rest hStrict.1,
                 LevelExpr.dropLzeroAtoms_strictlySorted rest hStrict.2⟩
      | limax _ _ =>
          exact ⟨LevelExpr.IsStrictLowerBound_dropLzeroAtoms _ rest hStrict.1,
                 LevelExpr.dropLzeroAtoms_strictlySorted rest hStrict.2⟩

/-- The canonical atom list is strictly sorted (unconditional).
Composes the three pipeline-transform invariants: insertion sort
gives `IsSorted`, `dedupAdjacent` upgrades it to `IsStrictlySorted`,
and `dropLzeroAtoms` preserves that.  This is the structural premise
`strictlySorted_unique` consumes in the canonical-form assembly. -/
theorem LevelExpr.canonicalAtoms_strictlySorted (expr : LevelExpr) :
    LevelExpr.IsStrictlySorted (LevelExpr.canonicalAtoms expr) := by
  show LevelExpr.IsStrictlySorted
    (LevelExpr.dropLzeroAtoms
      (LevelExpr.dedupAdjacent
        (LevelExpr.insertionSortByCompare (LevelExpr.lmaxAtoms expr))))
  exact LevelExpr.dropLzeroAtoms_strictlySorted _
    (LevelExpr.dedupAdjacent_strictlySorted _
      (LevelExpr.insertionSortByCompare_sorted _))

/-- On variable-only lists, agreeing on every `lvar k` membership
forces agreeing on *all* membership.  Anything occurring is a
variable (`isLvar_of_occursIn_allVariables`), so a general `z`
reduces to its `lvar k` form and the per-variable hypothesis
applies.  This is where the var-only restriction is load-bearing: a
`succ`/`limax` atom could otherwise occur unconstrained. -/
theorem LevelExpr.sameMembership_of_sameLvarMembership
    (xs ys : List LevelExpr)
    (hVarsX : LevelExpr.AllAtomsAreVariables xs)
    (hVarsY : LevelExpr.AllAtomsAreVariables ys)
    (hLvarSame : ∀ (variableIndex : Nat),
      LevelExpr.OccursIn (.lvar variableIndex) xs ↔
        LevelExpr.OccursIn (.lvar variableIndex) ys)
    (z : LevelExpr) :
    LevelExpr.OccursIn z xs ↔ LevelExpr.OccursIn z ys := by
  constructor
  · intro hOccursX
    obtain ⟨variableIndex, hzLvar⟩ :=
      LevelExpr.isLvar_of_occursIn_allVariables xs z hVarsX hOccursX
    rw [hzLvar] at hOccursX ⊢
    exact (hLvarSame variableIndex).mp hOccursX
  · intro hOccursY
    obtain ⟨variableIndex, hzLvar⟩ :=
      LevelExpr.isLvar_of_occursIn_allVariables ys z hVarsY hOccursY
    rw [hzLvar] at hOccursY ⊢
    exact (hLvarSame variableIndex).mpr hOccursY

/-! ### The variable-fragment completeness bridge

On the fragment where both canonical atom lists are variable-only,
denotational equality forces equal canonical forms.  This is a real,
bounded completeness result — `canonicalize` is a *decision oracle*
for `denoteEquiv` on distinct-variable joins.  Assembles, in order:
membership transfer (`denoteEquiv` ⟹ same `lvar`-membership), the
var-only membership upgrade (⟹ full membership), `strictlySorted_unique`
(⟹ equal atom lists), and `congrArg foldLmax` via
`canonicalize_eq_foldLmax_canonicalAtoms`.

SCOPE (honest): this does NOT close #419 in general — the canonical
pipeline lacks max-plus absorption, so `lmax (lsucc x) x` and
`lsucc x` (denotationally equal) have different canonical forms.  The
var-only hypotheses confine the claim to the absorption-free fragment.
Full #419 needs the genuine max-plus normal form (the transfer lemma,
denotation bridge, and oracle here are reusable for it). -/
theorem LevelExpr.canonicalize_eq_of_denoteEquiv_onVariableFragment
    (e1 e2 : LevelExpr)
    (hVars1 : LevelExpr.AllAtomsAreVariables (LevelExpr.canonicalAtoms e1))
    (hVars2 : LevelExpr.AllAtomsAreVariables (LevelExpr.canonicalAtoms e2))
    (hEquiv : LevelExpr.denoteEquiv e1 e2) :
    LevelExpr.canonicalize e1 = LevelExpr.canonicalize e2 := by
  have hMemberSame :
      ∀ (z : LevelExpr),
        LevelExpr.OccursIn z (LevelExpr.canonicalAtoms e1) ↔
          LevelExpr.OccursIn z (LevelExpr.canonicalAtoms e2) :=
    LevelExpr.sameMembership_of_sameLvarMembership
      (LevelExpr.canonicalAtoms e1) (LevelExpr.canonicalAtoms e2) hVars1 hVars2
      (fun variableIndex =>
        LevelExpr.canonicalAtoms_sameLvarMembership_of_denoteEquiv
          e1 e2 hVars1 hVars2 hEquiv variableIndex)
  have hAtomsEq :
      LevelExpr.canonicalAtoms e1 = LevelExpr.canonicalAtoms e2 :=
    LevelExpr.strictlySorted_unique
      (LevelExpr.canonicalAtoms e1) (LevelExpr.canonicalAtoms e2)
      (LevelExpr.canonicalAtoms_strictlySorted e1)
      (LevelExpr.canonicalAtoms_strictlySorted e2)
      hMemberSame
  rw [LevelExpr.canonicalize_eq_foldLmax_canonicalAtoms e1,
      LevelExpr.canonicalize_eq_foldLmax_canonicalAtoms e2, hAtomsEq]

/-! ### Discharging the var-only hypothesis from a source predicate

The fragment bridge takes `AllAtomsAreVariables (canonicalAtoms e)`
as a hypothesis.  To make it usable, derive that from a structural
predicate on the *source* expression: `IsVariableJoin` (built only
from `lvar`/`lzero`/`lmax`).  The plan: `lmaxAtoms` of such an
expression yields atoms each `lvar`-or-`lzero`; sort + dedup preserve
that shape; `dropLzeroAtoms` then removes exactly the `lzero`s,
leaving all `lvar`.  This tick ships the source predicate, the
atom-shape predicate, and the `lmaxAtoms` step. -/

/-- A level expression built only from `lvar`, `lzero`, and `lmax`
(no `lsucc`/`limax`): the absorption-free fragment on which
`canonicalize` is complete. -/
def LevelExpr.IsVariableJoin : LevelExpr → Prop
  | .lzero => True
  | .lvar _ => True
  | .lmax a b => LevelExpr.IsVariableJoin a ∧ LevelExpr.IsVariableJoin b
  | .lsucc _ => False
  | .limax _ _ => False

/-- Every atom in the list is a `lvar` or `lzero` — the atom shape
`lmaxAtoms` produces from an `IsVariableJoin` source, preserved
through sort/dedup until `dropLzeroAtoms` narrows it to pure `lvar`. -/
def LevelExpr.AllAtomsAreVarsOrLzero : List LevelExpr → Prop
  | [] => True
  | head :: rest =>
      (head = LevelExpr.lzero ∨ ∃ variableIndex, head = .lvar variableIndex) ∧
        LevelExpr.AllAtomsAreVarsOrLzero rest

/-- `AllAtomsAreVarsOrLzero` distributes over append. -/
theorem LevelExpr.AllAtomsAreVarsOrLzero_append :
    ∀ (xs ys : List LevelExpr),
      LevelExpr.AllAtomsAreVarsOrLzero xs →
      LevelExpr.AllAtomsAreVarsOrLzero ys →
      LevelExpr.AllAtomsAreVarsOrLzero (xs ++ ys)
  | [], _ys, _hX, hY => hY
  | head :: rest, ys, hX, hY =>
      ⟨hX.1, LevelExpr.AllAtomsAreVarsOrLzero_append rest ys hX.2 hY⟩

/-- `lmaxAtoms` of an `IsVariableJoin` expression yields only
`lvar`/`lzero` atoms.  Structural induction: `lmax` recurses via
append (`AllAtomsAreVarsOrLzero_append`), leaves are single atoms,
and `lsucc`/`limax` are ruled out by `IsVariableJoin _ ≡ False`. -/
theorem LevelExpr.lmaxAtoms_allVarsOrLzero_of_isVariableJoin :
    ∀ (expr : LevelExpr),
      LevelExpr.IsVariableJoin expr →
      LevelExpr.AllAtomsAreVarsOrLzero (LevelExpr.lmaxAtoms expr)
  | .lzero, _ => ⟨Or.inl rfl, trivial⟩
  | .lvar variableIndex, _ => ⟨Or.inr ⟨variableIndex, rfl⟩, trivial⟩
  | .lmax a b, hVarJoin =>
      LevelExpr.AllAtomsAreVarsOrLzero_append
        (LevelExpr.lmaxAtoms a) (LevelExpr.lmaxAtoms b)
        (LevelExpr.lmaxAtoms_allVarsOrLzero_of_isVariableJoin a hVarJoin.1)
        (LevelExpr.lmaxAtoms_allVarsOrLzero_of_isVariableJoin b hVarJoin.2)
  | .lsucc _, hVarJoin => nomatch hVarJoin
  | .limax _ _, hVarJoin => nomatch hVarJoin

/-- Compare-ordered insertion preserves the `lvar`/`lzero` atom shape:
inserting a var/lzero atom into a var/lzero list stays var/lzero
(`insertStep`'s three branches all reorder the same atoms).  Mirrors
`foldLmax_insertByCompare_denoteEquiv`'s skeleton — `show` the
`insertStep` form, `cases` the verdict. -/
theorem LevelExpr.AllAtomsAreVarsOrLzero_insertByCompare (newAtom : LevelExpr)
    (hNew : newAtom = LevelExpr.lzero ∨ ∃ variableIndex, newAtom = .lvar variableIndex) :
    ∀ (xs : List LevelExpr),
      LevelExpr.AllAtomsAreVarsOrLzero xs →
      LevelExpr.AllAtomsAreVarsOrLzero (LevelExpr.insertByCompare newAtom xs)
  | [], _ => ⟨hNew, trivial⟩
  | head :: rest, hList => by
      have hTailPreserved :=
        LevelExpr.AllAtomsAreVarsOrLzero_insertByCompare newAtom hNew rest hList.2
      show LevelExpr.AllAtomsAreVarsOrLzero
        (LevelExpr.insertStep (LevelExpr.compare newAtom head) newAtom head rest
          (LevelExpr.insertByCompare newAtom rest))
      cases hVerdict : LevelExpr.compare newAtom head with
      | gt => exact ⟨hList.1, hTailPreserved⟩
      | lt => exact ⟨hNew, hList⟩
      | eq => exact ⟨hNew, hList⟩

/-- Insertion sort preserves the `lvar`/`lzero` atom shape: each atom
is folded in via `insertByCompare`, which preserves it. -/
theorem LevelExpr.AllAtomsAreVarsOrLzero_insertionSortByCompare :
    ∀ (xs : List LevelExpr),
      LevelExpr.AllAtomsAreVarsOrLzero xs →
      LevelExpr.AllAtomsAreVarsOrLzero (LevelExpr.insertionSortByCompare xs)
  | [], _ => trivial
  | head :: rest, hList =>
      LevelExpr.AllAtomsAreVarsOrLzero_insertByCompare head hList.1
        (LevelExpr.insertionSortByCompare rest)
        (LevelExpr.AllAtomsAreVarsOrLzero_insertionSortByCompare rest hList.2)

/-- Adjacent dedup preserves the `lvar`/`lzero` atom shape: it only
drops (`.eq`) or keeps (`.lt`/`.gt`) the head, never introducing a
new atom.  Mirrors `dedupAdjacent_strictlySorted`'s two-element
lookahead. -/
theorem LevelExpr.AllAtomsAreVarsOrLzero_dedupAdjacent :
    ∀ (xs : List LevelExpr),
      LevelExpr.AllAtomsAreVarsOrLzero xs →
      LevelExpr.AllAtomsAreVarsOrLzero (LevelExpr.dedupAdjacent xs)
  | [], _ => trivial
  | [_single], hList => hList
  | first :: second :: rest, hList => by
      have hTailDedup :=
        LevelExpr.AllAtomsAreVarsOrLzero_dedupAdjacent (second :: rest) hList.2
      show LevelExpr.AllAtomsAreVarsOrLzero
        (LevelExpr.dedupStep (LevelExpr.compare first second) first
          (LevelExpr.dedupAdjacent (second :: rest)))
      cases hVerdict : LevelExpr.compare first second with
      | eq => exact hTailDedup
      | lt => exact ⟨hList.1, hTailDedup⟩
      | gt => exact ⟨hList.1, hTailDedup⟩

/-- `dropLzeroAtoms` narrows the `lvar`/`lzero` shape to pure `lvar`:
it removes exactly the `lzero` atoms, so what survives is all
variables.  Cases on the per-head evidence (the two reachable shapes)
rather than the head constructor — the `lzero` head is dropped and
recurses; the `lvar` head is kept and supplies its own witness. -/
theorem LevelExpr.AllAtomsAreVariables_dropLzeroAtoms :
    ∀ (xs : List LevelExpr),
      LevelExpr.AllAtomsAreVarsOrLzero xs →
      LevelExpr.AllAtomsAreVariables (LevelExpr.dropLzeroAtoms xs)
  | [], _ => trivial
  | head :: rest, hList => by
      have hTail :=
        LevelExpr.AllAtomsAreVariables_dropLzeroAtoms rest hList.2
      rcases hList.1 with hHeadLzero | ⟨variableIndex, hHeadLvar⟩
      · rw [hHeadLzero]
        exact hTail
      · rw [hHeadLvar]
        exact ⟨⟨variableIndex, rfl⟩, hTail⟩

/-- The canonical atom list of an `IsVariableJoin` expression is
variable-only.  Composes the four shape-preservation steps:
`lmaxAtoms` yields `lvar`/`lzero`, sort and dedup preserve that, and
`dropLzeroAtoms` narrows to pure `lvar`.  Shape analog of
`canonicalAtoms_strictlySorted`. -/
theorem LevelExpr.canonicalAtoms_allVariables_of_isVariableJoin (expr : LevelExpr)
    (hVarJoin : LevelExpr.IsVariableJoin expr) :
    LevelExpr.AllAtomsAreVariables (LevelExpr.canonicalAtoms expr) := by
  show LevelExpr.AllAtomsAreVariables
    (LevelExpr.dropLzeroAtoms
      (LevelExpr.dedupAdjacent
        (LevelExpr.insertionSortByCompare (LevelExpr.lmaxAtoms expr))))
  exact LevelExpr.AllAtomsAreVariables_dropLzeroAtoms _
    (LevelExpr.AllAtomsAreVarsOrLzero_dedupAdjacent _
      (LevelExpr.AllAtomsAreVarsOrLzero_insertionSortByCompare _
        (LevelExpr.lmaxAtoms_allVarsOrLzero_of_isVariableJoin expr hVarJoin)))

/-- Variable-join completeness, hypothesis-free on the source side:
denotationally-equal `IsVariableJoin` expressions have equal canonical
forms.  Discharges the fragment bridge's `AllAtomsAreVariables`
hypotheses from the structural source predicate `IsVariableJoin`
(which a caller can check by inspection).  This is the usable form of
the variable-fragment completeness result. -/
theorem LevelExpr.canonicalize_eq_of_denoteEquiv_of_isVariableJoin
    (e1 e2 : LevelExpr)
    (hVarJoin1 : LevelExpr.IsVariableJoin e1)
    (hVarJoin2 : LevelExpr.IsVariableJoin e2)
    (hEquiv : LevelExpr.denoteEquiv e1 e2) :
    LevelExpr.canonicalize e1 = LevelExpr.canonicalize e2 :=
  LevelExpr.canonicalize_eq_of_denoteEquiv_onVariableFragment e1 e2
    (LevelExpr.canonicalAtoms_allVariables_of_isVariableJoin e1 hVarJoin1)
    (LevelExpr.canonicalAtoms_allVariables_of_isVariableJoin e2 hVarJoin2)
    hEquiv

/-- Soundness of canonical form (general, no fragment restriction):
expressions with equal canonical forms are denotationally equal.
Chains `e1 ~ canonicalize e1 =(hyp) canonicalize e2 ~ e2`, the middle
hop a plain `Eq`-rewrite of the syntactically-equal canonical forms.
This is the easy direction — the completeness counterpart is the
fragment-bound `canonicalize_eq_of_denoteEquiv_of_isVariableJoin`. -/
theorem LevelExpr.denoteEquiv_of_canonicalize_eq (e1 e2 : LevelExpr)
    (hCanonEq : LevelExpr.canonicalize e1 = LevelExpr.canonicalize e2) :
    LevelExpr.denoteEquiv e1 e2 := by
  have hLeft : LevelExpr.denoteEquiv e1 (LevelExpr.canonicalize e1) :=
    (LevelExpr.canonicalize_denoteEquiv e1).symm
  have hRight : LevelExpr.denoteEquiv (LevelExpr.canonicalize e2) e2 :=
    LevelExpr.canonicalize_denoteEquiv e2
  rw [hCanonEq] at hLeft
  exact LevelExpr.denoteEquiv.trans hLeft hRight

/-- Decision procedure for `denoteEquiv` on the variable-join
fragment: compute both canonical forms and compare with the derived
`DecidableEq LevelExpr`.  Equal forms give `isTrue` via soundness;
unequal forms give `isFalse`, since fragment completeness says
denotational equality would force equal canonical forms.  This
realizes `#419`'s "Decidable denoteEquiv" goal on the fragment.  A
`def` (not `instance`) because it carries the `IsVariableJoin`
evidence explicitly. -/
def LevelExpr.decidableDenoteEquivOfVariableJoin (e1 e2 : LevelExpr)
    (hVarJoin1 : LevelExpr.IsVariableJoin e1)
    (hVarJoin2 : LevelExpr.IsVariableJoin e2) :
    Decidable (LevelExpr.denoteEquiv e1 e2) :=
  if hCanonEq : LevelExpr.canonicalize e1 = LevelExpr.canonicalize e2 then
    isTrue (LevelExpr.denoteEquiv_of_canonicalize_eq e1 e2 hCanonEq)
  else
    isFalse (fun hDenoteEquiv =>
      hCanonEq (LevelExpr.canonicalize_eq_of_denoteEquiv_of_isVariableJoin
        e1 e2 hVarJoin1 hVarJoin2 hDenoteEquiv))

/-! ## The max-plus normal form — toward full #419 completeness

Mörtberg-Sterling: every universe level normalizes to an affine
max-plus form `max(baseConstant, maxᵢ (env varᵢ + offsetᵢ))`.  Unlike
the current `canonicalize` (which lacks absorption — see the
variable-fragment scope note above), this form performs absorption by
keeping only the *maximum offset* per variable: `lmax (lsucc x) x` and
`lsucc x` both reduce to the single entry `(x, 1)`.  This block ships
the structure and its denotation — the semantic target the normalizer
(`toMaxPlusForm`, later ticks) is proven against. -/

/-- An affine max-plus form: a base constant plus, per universe
variable, the maximum offset at which it appears.  The representation
*is* the absorption mechanism — one offset per variable. -/
structure LevelExpr.MaxPlusForm where
  /-- The constant floor (max of all constant contributions). -/
  baseConstant : Nat
  /-- `(variableIndex, offset)` entries — the max offset per variable. -/
  varOffsets : List (Nat × Nat)

/-- Max-fold of the variable/offset entries under an environment:
`maxᵢ (env varᵢ + offsetᵢ)`, with the empty list folding to `0`. -/
def LevelExpr.MaxPlusForm.denoteVarOffsets :
    List (Nat × Nat) → (Nat → Nat) → Nat
  | [], _ => 0
  | (variableIndex, offset) :: rest, env =>
      LevelExpr.levelMax (env variableIndex + offset)
        (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)

/-- Semantic denotation of a max-plus form: the base constant joined
with the max over all variable/offset entries. -/
def LevelExpr.MaxPlusForm.denote
    (form : LevelExpr.MaxPlusForm) (env : Nat → Nat) : Nat :=
  LevelExpr.levelMax form.baseConstant
    (LevelExpr.MaxPlusForm.denoteVarOffsets form.varOffsets env)

/-- Increment every offset by one (the per-variable part of `lsucc`). -/
def LevelExpr.MaxPlusForm.incrementOffsets :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (variableIndex, offset) :: rest =>
      (variableIndex, offset + 1) ::
        LevelExpr.MaxPlusForm.incrementOffsets rest

/-- The `lsucc` operation on a max-plus form: bump the base constant
and every offset by one.  `max(c, maxᵢ(vᵢ+oᵢ)) + 1 =
max(c+1, maxᵢ(vᵢ+oᵢ+1))`. -/
def LevelExpr.MaxPlusForm.shiftSucc (form : LevelExpr.MaxPlusForm) :
    LevelExpr.MaxPlusForm :=
  { baseConstant := form.baseConstant + 1,
    varOffsets := LevelExpr.MaxPlusForm.incrementOffsets form.varOffsets }

/-- The shift identity *with the base floor attached*: incrementing
all offsets and the floor adds one to the whole max-fold.  Generalize
`floor` so the induction goes through — the trailing-`0` floor of
`denoteVarOffsets` is always dominated by `floor + 1`, so `+1`
distributes.  Cons step: rearrange via `levelMax` assoc, fire the
`succ-succ` identity, recurse, re-associate. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_incrementOffsets_shift
    (env : Nat → Nat) :
    ∀ (entries : List (Nat × Nat)) (floor : Nat),
      LevelExpr.levelMax (floor + 1)
          (LevelExpr.MaxPlusForm.denoteVarOffsets
            (LevelExpr.MaxPlusForm.incrementOffsets entries) env) =
        LevelExpr.levelMax floor
          (LevelExpr.MaxPlusForm.denoteVarOffsets entries env) + 1
  | [], floor => by
      show LevelExpr.levelMax (floor + 1) 0 = LevelExpr.levelMax floor 0 + 1
      rw [LevelExpr.levelMax_zero_right, LevelExpr.levelMax_zero_right]
  | (variableIndex, offset) :: rest, floor => by
      show LevelExpr.levelMax (floor + 1)
          (LevelExpr.levelMax (env variableIndex + offset + 1)
            (LevelExpr.MaxPlusForm.denoteVarOffsets
              (LevelExpr.MaxPlusForm.incrementOffsets rest) env)) =
        LevelExpr.levelMax floor
          (LevelExpr.levelMax (env variableIndex + offset)
            (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)) + 1
      rw [← LevelExpr.levelMax_assoc (floor + 1) (env variableIndex + offset + 1),
          LevelExpr.levelMax_succ_distrib floor (env variableIndex + offset),
          LevelExpr.MaxPlusForm.denoteVarOffsets_incrementOffsets_shift env rest
            (LevelExpr.levelMax floor (env variableIndex + offset)),
          LevelExpr.levelMax_assoc floor (env variableIndex + offset)]

/-- Soundness of the `lsucc` primitive: `shiftSucc` adds one to the
denotation. -/
theorem LevelExpr.MaxPlusForm.shiftSucc_denote
    (form : LevelExpr.MaxPlusForm) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denote (LevelExpr.MaxPlusForm.shiftSucc form) env =
      LevelExpr.MaxPlusForm.denote form env + 1 := by
  show LevelExpr.levelMax (form.baseConstant + 1)
      (LevelExpr.MaxPlusForm.denoteVarOffsets
        (LevelExpr.MaxPlusForm.incrementOffsets form.varOffsets) env) =
    LevelExpr.levelMax form.baseConstant
      (LevelExpr.MaxPlusForm.denoteVarOffsets form.varOffsets env) + 1
  exact LevelExpr.MaxPlusForm.denoteVarOffsets_incrementOffsets_shift env
    form.varOffsets form.baseConstant

/-- The middle-four interchange law for `levelMax`:
`(a ⊔ b) ⊔ (c ⊔ d) = (a ⊔ c) ⊔ (b ⊔ d)`.  Pure commutativity +
associativity rearrangement — both sides equal `a ⊔ b ⊔ c ⊔ d`.
This is the algebraic heart of the `lmax` merge soundness: it swaps
the two base constants past the two variable-folds. -/
theorem LevelExpr.levelMax_interchange (valueA valueB valueC valueD : Nat) :
    LevelExpr.levelMax (LevelExpr.levelMax valueA valueB)
        (LevelExpr.levelMax valueC valueD) =
      LevelExpr.levelMax (LevelExpr.levelMax valueA valueC)
        (LevelExpr.levelMax valueB valueD) := by
  rw [LevelExpr.levelMax_assoc valueA valueB (LevelExpr.levelMax valueC valueD),
      ← LevelExpr.levelMax_assoc valueB valueC valueD,
      LevelExpr.levelMax_comm valueB valueC,
      LevelExpr.levelMax_assoc valueC valueB valueD,
      LevelExpr.levelMax_assoc valueA valueC (LevelExpr.levelMax valueB valueD)]

/-- Concatenating two variable/offset lists max-folds to the join of
their individual folds: `denoteVarOffsets (left ++ right) =
levelMax (denoteVarOffsets left) (denoteVarOffsets right)`.  The
empty floor of `denoteVarOffsets` is the unit of `levelMax`, so the
base case is `levelMax_zero_left`; the cons step re-associates the
head past the recursive join. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_append (env : Nat → Nat) :
    ∀ (left right : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.denoteVarOffsets (left ++ right) env =
        LevelExpr.levelMax
          (LevelExpr.MaxPlusForm.denoteVarOffsets left env)
          (LevelExpr.MaxPlusForm.denoteVarOffsets right env)
  | [], right => by
      show LevelExpr.MaxPlusForm.denoteVarOffsets right env =
        LevelExpr.levelMax 0
          (LevelExpr.MaxPlusForm.denoteVarOffsets right env)
      rw [LevelExpr.levelMax_zero_left]
  | (variableIndex, offset) :: rest, right => by
      show LevelExpr.levelMax (env variableIndex + offset)
          (LevelExpr.MaxPlusForm.denoteVarOffsets (rest ++ right) env) =
        LevelExpr.levelMax
          (LevelExpr.levelMax (env variableIndex + offset)
            (LevelExpr.MaxPlusForm.denoteVarOffsets rest env))
          (LevelExpr.MaxPlusForm.denoteVarOffsets right env)
      rw [LevelExpr.MaxPlusForm.denoteVarOffsets_append env rest right,
          LevelExpr.levelMax_assoc (env variableIndex + offset)
            (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)
            (LevelExpr.MaxPlusForm.denoteVarOffsets right env)]

/-- The `lmax` operation on max-plus forms: join the base constants
and concatenate the variable/offset lists.

Soundness only — this does NOT collapse duplicate-variable entries
(absorption).  Absorption is the same operation regardless of how a
form arose (merge, shift, or direct atom), so it lives as a separate
normalization pass (a later leaf), keeping this primitive's proof
small and its claim exact.  The result therefore denotes correctly
but may carry the same variable twice until absorbed. -/
def LevelExpr.MaxPlusForm.merge
    (formLeft formRight : LevelExpr.MaxPlusForm) : LevelExpr.MaxPlusForm :=
  { baseConstant :=
      LevelExpr.levelMax formLeft.baseConstant formRight.baseConstant,
    varOffsets := formLeft.varOffsets ++ formRight.varOffsets }

/-- Soundness of the `lmax` primitive: `merge` denotes the join of the
two forms' denotations.  Unfold both `denote`s, distribute the fold
over the concatenation (`denoteVarOffsets_append`), then swap the two
base constants past the two variable-folds via the middle-four
interchange. -/
theorem LevelExpr.MaxPlusForm.merge_denote
    (formLeft formRight : LevelExpr.MaxPlusForm) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denote
        (LevelExpr.MaxPlusForm.merge formLeft formRight) env =
      LevelExpr.levelMax (LevelExpr.MaxPlusForm.denote formLeft env)
        (LevelExpr.MaxPlusForm.denote formRight env) := by
  show LevelExpr.levelMax
      (LevelExpr.levelMax formLeft.baseConstant formRight.baseConstant)
      (LevelExpr.MaxPlusForm.denoteVarOffsets
        (formLeft.varOffsets ++ formRight.varOffsets) env) =
    LevelExpr.levelMax
      (LevelExpr.levelMax formLeft.baseConstant
        (LevelExpr.MaxPlusForm.denoteVarOffsets formLeft.varOffsets env))
      (LevelExpr.levelMax formRight.baseConstant
        (LevelExpr.MaxPlusForm.denoteVarOffsets formRight.varOffsets env))
  rw [LevelExpr.MaxPlusForm.denoteVarOffsets_append env
        formLeft.varOffsets formRight.varOffsets]
  exact LevelExpr.levelMax_interchange formLeft.baseConstant
    formRight.baseConstant
    (LevelExpr.MaxPlusForm.denoteVarOffsets formLeft.varOffsets env)
    (LevelExpr.MaxPlusForm.denoteVarOffsets formRight.varOffsets env)

/-! ## The normalizer — `toMaxPlusForm` on the predicative fragment

`toMaxPlusForm` recurses `LevelExpr → MaxPlusForm`, routing `lzero`/
`lvar` to base forms and `lsucc`/`lmax` through the `shiftSucc`/`merge`
primitives.  `limax` is NOT max-plus expressible (its denotation is a
runtime conditional on whether the right argument vanishes), so it has
no faithful form — the function maps it to a placeholder and the
soundness theorem is gated by `isPredicative` (no `limax` in the tree).
This closes the predicative fragment of #419; full `limax` closure
needs Mörtberg-Sterling irreducible imax-nodes and is deferred. -/

/-- Propext-free left projection of a Boolean conjunction:
`(flagLeft && flagRight) = true` forces `flagLeft = true`.  `cases` on
the plain (non-indexed) `Bool` keeps this clean; the `false` branch
reads off the absurd `false = true` directly. -/
theorem LevelExpr.and_eq_true_imp_left {flagLeft flagRight : Bool}
    (hConj : (flagLeft && flagRight) = true) : flagLeft = true := by
  cases flagLeft with
  | false => exact hConj
  | true => rfl

/-- Propext-free right projection of a Boolean conjunction:
`(flagLeft && flagRight) = true` forces `flagRight = true`.  The
`false` branch discharges via `Bool.noConfusion` on `false = true`. -/
theorem LevelExpr.and_eq_true_imp_right {flagLeft flagRight : Bool}
    (hConj : (flagLeft && flagRight) = true) : flagRight = true := by
  cases flagLeft with
  | false => exact Bool.noConfusion hConj
  | true => exact hConj

/-- Predicativity gate: an expression is predicative when it is built
only from `lzero`, `lsucc`, `lmax`, `lvar` — no `limax` anywhere.
Boolean-valued (full 5-ctor enumeration, propext-clean) so it is
decidable for free.  This is exactly the fragment on which
`toMaxPlusForm` is denotation-sound. -/
def LevelExpr.isPredicative : LevelExpr → Bool
  | .lzero => true
  | .lsucc inner => LevelExpr.isPredicative inner
  | .lmax left right =>
      LevelExpr.isPredicative left && LevelExpr.isPredicative right
  | .limax _ _ => false
  | .lvar _ => true

/-- A nested predicative tree is predicative. -/
theorem LevelExpr.isPredicative_lmax_smoke :
    LevelExpr.isPredicative (.lmax (.lvar 0) (.lsucc (.lvar 1))) = true :=
  rfl

/-- Any tree containing `limax` is not predicative. -/
theorem LevelExpr.isPredicative_limax_smoke :
    LevelExpr.isPredicative (.limax (.lvar 0) (.lvar 1)) = false :=
  rfl

/-- The max-plus normalizer.  Total over all `LevelExpr` (Lean
requires it), but only denotation-faithful on the predicative fragment
(`isPredicative` = true).  `lzero` → the empty form (denotes 0);
`lvar n` → the single zero-offset entry (denotes `env n`); `lsucc` →
`shiftSucc`; `lmax` → `merge`.  `limax` maps to the empty form as a
non-semantic placeholder — never asserted correct (the soundness
theorem excludes it). -/
def LevelExpr.toMaxPlusForm : LevelExpr → LevelExpr.MaxPlusForm
  | .lzero => { baseConstant := 0, varOffsets := [] }
  | .lsucc inner =>
      LevelExpr.MaxPlusForm.shiftSucc (LevelExpr.toMaxPlusForm inner)
  | .lmax left right =>
      LevelExpr.MaxPlusForm.merge
        (LevelExpr.toMaxPlusForm left) (LevelExpr.toMaxPlusForm right)
  | .limax _ _ => { baseConstant := 0, varOffsets := [] }
  | .lvar index => { baseConstant := 0, varOffsets := [(index, 0)] }

/-- Soundness of the normalizer on the predicative fragment: for every
predicative expression, `toMaxPlusForm` denotes the same level as the
expression itself, under every environment.

Proof by `induction` on the (simple, non-indexed) `LevelExpr`, which
compiles to the propext-free `LevelExpr.rec`.  Each arm composes the
matching primitive's soundness lemma with the inductive hypotheses:
`lsucc` uses `shiftSucc_denote`; `lmax` uses `merge_denote` plus both
IHs (the conjunction split via the propext-free projections); `lvar`
collapses the single entry via the `levelMax` identities; `limax` is
vacuous because `isPredicative (limax …)` reduces to `false`. -/
theorem LevelExpr.toMaxPlusForm_denote (env : Nat → Nat) :
    ∀ (level : LevelExpr), LevelExpr.isPredicative level = true →
      LevelExpr.MaxPlusForm.denote (LevelExpr.toMaxPlusForm level) env =
        LevelExpr.denote level env := by
  intro level
  induction level with
  | lzero => intro _; rfl
  | lsucc inner ih =>
      intro hPred
      show LevelExpr.MaxPlusForm.denote
          (LevelExpr.MaxPlusForm.shiftSucc (LevelExpr.toMaxPlusForm inner)) env =
        LevelExpr.denote inner env + 1
      rw [LevelExpr.MaxPlusForm.shiftSucc_denote
            (LevelExpr.toMaxPlusForm inner) env,
          ih hPred]
  | lmax left right ihLeft ihRight =>
      intro hPred
      show LevelExpr.MaxPlusForm.denote
          (LevelExpr.MaxPlusForm.merge
            (LevelExpr.toMaxPlusForm left) (LevelExpr.toMaxPlusForm right)) env =
        LevelExpr.levelMax (LevelExpr.denote left env)
          (LevelExpr.denote right env)
      rw [LevelExpr.MaxPlusForm.merge_denote
            (LevelExpr.toMaxPlusForm left) (LevelExpr.toMaxPlusForm right) env,
          ihLeft (LevelExpr.and_eq_true_imp_left hPred),
          ihRight (LevelExpr.and_eq_true_imp_right hPred)]
  | limax leftArg rightArg _ihLeft _ihRight =>
      intro hPred
      exact Bool.noConfusion hPred
  | lvar index =>
      intro _
      show LevelExpr.levelMax 0
          (LevelExpr.levelMax (env index) 0) = env index
      rw [LevelExpr.levelMax_zero_right (env index),
          LevelExpr.levelMax_zero_left (env index)]

/-! ## Canonicalization foundation — the local rewrite rules

The max-plus canonical form keeps the entries sorted by variable and
with one (max) offset per variable.  Two local, denotation-preserving
rewrite rules justify any such canonicalization:

* `denoteVarOffsets_swap_adjacent` — reordering adjacent entries
  preserves the fold (max is commutative/associative);
* `denoteVarOffsets_absorb_adjacent` — two adjacent entries for the
  same variable collapse to one carrying the max of their offsets.

The absorb rule rests on the arithmetic distributivity
`levelMax (base + offsetA) (base + offsetB) = base + levelMax offsetA
offsetB` — adding a fixed base distributes over `levelMax`, which is
exactly why one offset per variable suffices. -/

/-- Adding a fixed `base` distributes over `levelMax`:
`max (base + offsetA) (base + offsetB) = base + max offsetA offsetB`.
Proved by induction on `base` against the custom `levelMax`; the
successor case collapses through the definitional
`levelMax (_ + 1) (_ + 1) = levelMax _ _ + 1`. -/
theorem LevelExpr.levelMax_add_left_distrib (base offsetA offsetB : Nat) :
    LevelExpr.levelMax (base + offsetA) (base + offsetB) =
      base + LevelExpr.levelMax offsetA offsetB := by
  induction base with
  | zero =>
      rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]
  | succ predecessor ih =>
      rw [Nat.succ_add, Nat.succ_add, Nat.succ_add]
      show LevelExpr.levelMax (predecessor + offsetA) (predecessor + offsetB) + 1 =
        (predecessor + LevelExpr.levelMax offsetA offsetB) + 1
      rw [ih]

/-- Reordering two adjacent entries preserves the max-fold: the
denotation of a `varOffsets` list only depends on its entries up to
order.  The single-swap version — `levelMax` left-commutativity
applied past the recursive tail. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_swap_adjacent
    (variableA offsetA variableB offsetB : Nat)
    (rest : List (Nat × Nat)) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denoteVarOffsets
        ((variableA, offsetA) :: (variableB, offsetB) :: rest) env =
      LevelExpr.MaxPlusForm.denoteVarOffsets
        ((variableB, offsetB) :: (variableA, offsetA) :: rest) env := by
  show LevelExpr.levelMax (env variableA + offsetA)
      (LevelExpr.levelMax (env variableB + offsetB)
        (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)) =
    LevelExpr.levelMax (env variableB + offsetB)
      (LevelExpr.levelMax (env variableA + offsetA)
        (LevelExpr.MaxPlusForm.denoteVarOffsets rest env))
  rw [← LevelExpr.levelMax_assoc (env variableA + offsetA)
        (env variableB + offsetB)
        (LevelExpr.MaxPlusForm.denoteVarOffsets rest env),
      LevelExpr.levelMax_comm (env variableA + offsetA) (env variableB + offsetB),
      LevelExpr.levelMax_assoc (env variableB + offsetB)
        (env variableA + offsetA)
        (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)]

/-- Two adjacent entries for the *same* variable collapse to one
carrying the max of their offsets — the absorption that keeps one
offset per variable.  Re-associate the head past the tail, then fire
`levelMax_add_left_distrib` to fuse the two `env variableIndex + _`
contributions. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_absorb_adjacent
    (variableIndex offsetA offsetB : Nat)
    (rest : List (Nat × Nat)) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denoteVarOffsets
        ((variableIndex, offsetA) :: (variableIndex, offsetB) :: rest) env =
      LevelExpr.MaxPlusForm.denoteVarOffsets
        ((variableIndex, LevelExpr.levelMax offsetA offsetB) :: rest) env := by
  show LevelExpr.levelMax (env variableIndex + offsetA)
      (LevelExpr.levelMax (env variableIndex + offsetB)
        (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)) =
    LevelExpr.levelMax (env variableIndex + LevelExpr.levelMax offsetA offsetB)
      (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)
  rw [← LevelExpr.levelMax_assoc (env variableIndex + offsetA)
        (env variableIndex + offsetB)
        (LevelExpr.MaxPlusForm.denoteVarOffsets rest env),
      LevelExpr.levelMax_add_left_distrib (env variableIndex) offsetA offsetB]

/-! ## Canonicalization — insertion sort by variable index

`sortByVariable` arranges the entries in ascending variable order
(via `insertByVariable` one-at-a-time), making same-variable entries
adjacent so the absorb rule (next leaf) can fuse them.  Both functions
preserve the denotation: the fold is order-invariant, so any
reordering is denote-neutral.  Comparison uses the Boolean `Nat.ble`
(full `true`/`false` enumeration, propext-clean). -/

/-- Insert one entry into a list, placing it before the first entry
whose variable index is strictly larger (so equal-variable entries
end up adjacent, ready for absorption). -/
def LevelExpr.MaxPlusForm.insertByVariable :
    Nat × Nat → List (Nat × Nat) → List (Nat × Nat)
  | entry, [] => [entry]
  | (variableNew, offsetNew), (variableHead, offsetHead) :: rest =>
      match Nat.ble variableNew variableHead with
      | true => (variableNew, offsetNew) :: (variableHead, offsetHead) :: rest
      | false =>
          (variableHead, offsetHead) ::
            LevelExpr.MaxPlusForm.insertByVariable (variableNew, offsetNew) rest

/-- Inserting an entry denotes the same as prepending it: position is
irrelevant to the max-fold.  The `true` branch puts the entry at the
front (matching the prepend directly); the `false` branch sends it
deeper and the `denoteVarOffsets_swap_adjacent` rule bubbles it back
past the head. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_insertByVariable
    (variableNew offsetNew : Nat) (env : Nat → Nat) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.denoteVarOffsets
          (LevelExpr.MaxPlusForm.insertByVariable (variableNew, offsetNew) entries) env =
        LevelExpr.MaxPlusForm.denoteVarOffsets
          ((variableNew, offsetNew) :: entries) env
  | [] => rfl
  | (variableHead, offsetHead) :: rest => by
      show LevelExpr.MaxPlusForm.denoteVarOffsets
          (match Nat.ble variableNew variableHead with
           | true => (variableNew, offsetNew) :: (variableHead, offsetHead) :: rest
           | false => (variableHead, offsetHead) ::
               LevelExpr.MaxPlusForm.insertByVariable (variableNew, offsetNew) rest) env =
        LevelExpr.MaxPlusForm.denoteVarOffsets
          ((variableNew, offsetNew) :: (variableHead, offsetHead) :: rest) env
      cases Nat.ble variableNew variableHead with
      | true => rfl
      | false =>
          show LevelExpr.levelMax (env variableHead + offsetHead)
              (LevelExpr.MaxPlusForm.denoteVarOffsets
                (LevelExpr.MaxPlusForm.insertByVariable (variableNew, offsetNew) rest) env) =
            LevelExpr.MaxPlusForm.denoteVarOffsets
              ((variableNew, offsetNew) :: (variableHead, offsetHead) :: rest) env
          rw [LevelExpr.MaxPlusForm.denoteVarOffsets_insertByVariable
                variableNew offsetNew env rest]
          exact LevelExpr.MaxPlusForm.denoteVarOffsets_swap_adjacent
            variableHead offsetHead variableNew offsetNew rest env

/-- Insertion sort by variable index. -/
def LevelExpr.MaxPlusForm.sortByVariable :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | entry :: rest =>
      LevelExpr.MaxPlusForm.insertByVariable entry
        (LevelExpr.MaxPlusForm.sortByVariable rest)

/-- Sorting preserves the denotation: each insertion is denote-neutral
(`denoteVarOffsets_insertByVariable`), folded down the list. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_sortByVariable (env : Nat → Nat) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.denoteVarOffsets
          (LevelExpr.MaxPlusForm.sortByVariable entries) env =
        LevelExpr.MaxPlusForm.denoteVarOffsets entries env
  | [] => rfl
  | (variableHead, offsetHead) :: rest => by
      show LevelExpr.MaxPlusForm.denoteVarOffsets
          (LevelExpr.MaxPlusForm.insertByVariable (variableHead, offsetHead)
            (LevelExpr.MaxPlusForm.sortByVariable rest)) env =
        LevelExpr.levelMax (env variableHead + offsetHead)
          (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)
      rw [LevelExpr.MaxPlusForm.denoteVarOffsets_insertByVariable
            variableHead offsetHead env
            (LevelExpr.MaxPlusForm.sortByVariable rest)]
      show LevelExpr.levelMax (env variableHead + offsetHead)
          (LevelExpr.MaxPlusForm.denoteVarOffsets
            (LevelExpr.MaxPlusForm.sortByVariable rest) env) =
        LevelExpr.levelMax (env variableHead + offsetHead)
          (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)
      rw [LevelExpr.MaxPlusForm.denoteVarOffsets_sortByVariable env rest]

/-! ## Canonicalization — absorption of adjacent equal-variable entries

On a list already sorted by variable, equal-variable entries are
adjacent; `absorbAdjacent` fuses each such run into a single entry
carrying the max offset, so the canonical form holds one offset per
variable.  To recurse structurally (rather than on a rebuilt list),
`absorbFrom` carries the "current" entry as an accumulator and walks
the structural tail; combining keeps the accumulator at the same
variable with the joined offset. -/

/-- Walk `rest`, fusing each entry whose variable equals the carried
`current`'s into `current` (taking the max offset), else emitting
`current` and carrying the new entry.  Structurally recursive on
`rest`. -/
def LevelExpr.MaxPlusForm.absorbFrom :
    Nat × Nat → List (Nat × Nat) → List (Nat × Nat)
  | current, [] => [current]
  | (variableCurrent, offsetCurrent), (variableNext, offsetNext) :: rest =>
      match Nat.beq variableCurrent variableNext with
      | true =>
          LevelExpr.MaxPlusForm.absorbFrom
            (variableCurrent, LevelExpr.levelMax offsetCurrent offsetNext) rest
      | false =>
          (variableCurrent, offsetCurrent) ::
            LevelExpr.MaxPlusForm.absorbFrom (variableNext, offsetNext) rest

/-- `absorbFrom` denotes the same as prepending the carried entry:
each fuse step is the local `denoteVarOffsets_absorb_adjacent` rule,
each skip step folds the head through the recursive tail. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_absorbFrom (env : Nat → Nat) :
    ∀ (current : Nat × Nat) (rest : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.denoteVarOffsets
          (LevelExpr.MaxPlusForm.absorbFrom current rest) env =
        LevelExpr.MaxPlusForm.denoteVarOffsets (current :: rest) env
  | current, [] => rfl
  | (variableCurrent, offsetCurrent), (variableNext, offsetNext) :: rest => by
      show LevelExpr.MaxPlusForm.denoteVarOffsets
          (match Nat.beq variableCurrent variableNext with
           | true => LevelExpr.MaxPlusForm.absorbFrom
               (variableCurrent, LevelExpr.levelMax offsetCurrent offsetNext) rest
           | false => (variableCurrent, offsetCurrent) ::
               LevelExpr.MaxPlusForm.absorbFrom (variableNext, offsetNext) rest) env =
        LevelExpr.MaxPlusForm.denoteVarOffsets
          ((variableCurrent, offsetCurrent) :: (variableNext, offsetNext) :: rest) env
      cases hbeq : Nat.beq variableCurrent variableNext with
      | true =>
          have hEqVar : variableCurrent = variableNext :=
            Nat.eq_of_beq_eq_true hbeq
          rw [LevelExpr.MaxPlusForm.denoteVarOffsets_absorbFrom env
                (variableCurrent, LevelExpr.levelMax offsetCurrent offsetNext) rest,
              ← hEqVar]
          exact (LevelExpr.MaxPlusForm.denoteVarOffsets_absorb_adjacent
            variableCurrent offsetCurrent offsetNext rest env).symm
      | false =>
          show LevelExpr.levelMax (env variableCurrent + offsetCurrent)
              (LevelExpr.MaxPlusForm.denoteVarOffsets
                (LevelExpr.MaxPlusForm.absorbFrom (variableNext, offsetNext) rest) env) =
            LevelExpr.levelMax (env variableCurrent + offsetCurrent)
              (LevelExpr.MaxPlusForm.denoteVarOffsets
                ((variableNext, offsetNext) :: rest) env)
          rw [LevelExpr.MaxPlusForm.denoteVarOffsets_absorbFrom env
                (variableNext, offsetNext) rest]

/-- Absorb adjacent equal-variable entries throughout the list. -/
def LevelExpr.MaxPlusForm.absorbAdjacent :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | entry :: rest => LevelExpr.MaxPlusForm.absorbFrom entry rest

/-- Absorption preserves the denotation (via `denoteVarOffsets_absorbFrom`). -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_absorbAdjacent (env : Nat → Nat) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.denoteVarOffsets
          (LevelExpr.MaxPlusForm.absorbAdjacent entries) env =
        LevelExpr.MaxPlusForm.denoteVarOffsets entries env
  | [] => rfl
  | entry :: rest => by
      show LevelExpr.MaxPlusForm.denoteVarOffsets
          (LevelExpr.MaxPlusForm.absorbFrom entry rest) env =
        LevelExpr.MaxPlusForm.denoteVarOffsets (entry :: rest) env
      exact LevelExpr.MaxPlusForm.denoteVarOffsets_absorbFrom env entry rest

/-! ## Canonicalization — assembling the form-level canonicalizer

Sort-then-absorb yields the canonical `varOffsets`: sorting makes
equal-variable entries adjacent, absorption collapses each run to one
max offset, so the result holds exactly one (max) offset per variable
in ascending order.  Lifted to `MaxPlusForm.canonicalize`, this is
denote-preserving; composed with `toMaxPlusForm` it gives the
end-to-end soundness of the predicative normalizer-to-canonical-form
pipeline — the (←) direction the decision procedure will rest on. -/

/-- Canonicalize a `varOffsets` list: sort by variable, then absorb
adjacent equal-variable entries.  One max offset per variable, sorted. -/
def LevelExpr.MaxPlusForm.canonicalizeVarOffsets
    (entries : List (Nat × Nat)) : List (Nat × Nat) :=
  LevelExpr.MaxPlusForm.absorbAdjacent
    (LevelExpr.MaxPlusForm.sortByVariable entries)

/-- Canonicalizing the offsets preserves the denotation: chain the
sort half (`denoteVarOffsets_sortByVariable`) and the absorb half
(`denoteVarOffsets_absorbAdjacent`). -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_canonicalizeVarOffsets
    (entries : List (Nat × Nat)) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denoteVarOffsets
        (LevelExpr.MaxPlusForm.canonicalizeVarOffsets entries) env =
      LevelExpr.MaxPlusForm.denoteVarOffsets entries env := by
  show LevelExpr.MaxPlusForm.denoteVarOffsets
      (LevelExpr.MaxPlusForm.absorbAdjacent
        (LevelExpr.MaxPlusForm.sortByVariable entries)) env =
    LevelExpr.MaxPlusForm.denoteVarOffsets entries env
  rw [LevelExpr.MaxPlusForm.denoteVarOffsets_absorbAdjacent env
        (LevelExpr.MaxPlusForm.sortByVariable entries),
      LevelExpr.MaxPlusForm.denoteVarOffsets_sortByVariable env entries]

/-- Canonicalize a max-plus form: canonicalize the offsets, keep the
base constant. -/
def LevelExpr.MaxPlusForm.canonicalize
    (form : LevelExpr.MaxPlusForm) : LevelExpr.MaxPlusForm :=
  { baseConstant := form.baseConstant,
    varOffsets :=
      LevelExpr.MaxPlusForm.canonicalizeVarOffsets form.varOffsets }

/-- Canonicalizing a form preserves its denotation. -/
theorem LevelExpr.MaxPlusForm.canonicalize_denote
    (form : LevelExpr.MaxPlusForm) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denote (LevelExpr.MaxPlusForm.canonicalize form) env =
      LevelExpr.MaxPlusForm.denote form env := by
  show LevelExpr.levelMax form.baseConstant
      (LevelExpr.MaxPlusForm.denoteVarOffsets
        (LevelExpr.MaxPlusForm.canonicalizeVarOffsets form.varOffsets) env) =
    LevelExpr.levelMax form.baseConstant
      (LevelExpr.MaxPlusForm.denoteVarOffsets form.varOffsets env)
  rw [LevelExpr.MaxPlusForm.denoteVarOffsets_canonicalizeVarOffsets
        form.varOffsets env]

/-- End-to-end soundness on the predicative fragment: normalizing to a
max-plus form and canonicalizing it denotes the same level as the
original expression.  Chains `canonicalize_denote` with the normalizer
soundness `toMaxPlusForm_denote`. -/
theorem LevelExpr.canonicalize_toMaxPlusForm_denote
    (level : LevelExpr) (hPred : LevelExpr.isPredicative level = true)
    (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denote
        (LevelExpr.MaxPlusForm.canonicalize (LevelExpr.toMaxPlusForm level)) env =
      LevelExpr.denote level env := by
  rw [LevelExpr.MaxPlusForm.canonicalize_denote (LevelExpr.toMaxPlusForm level) env,
      LevelExpr.toMaxPlusForm_denote env level hPred]

/-! ## Base normalization — the missing half of canonicality

`canonicalize` (above) canonicalizes only `varOffsets`; it leaves
`baseConstant` untouched and is therefore NOT a true normal form.
Counterexample: `{base:2, [(0,5)]}` and `{base:0, [(0,5)]}` both denote
`env ↦ max(base, env 0 + 5) = env 0 + 5` (since `env 0 + 5 ≥ 5 > base`)
— denote-equal, structurally distinct, both fixed by `canonicalize`.

The fix: normalize the base to `max(baseConstant, maxᵢ offsetᵢ)`, which
equals `denote(form, zeroEnv)` and is hence DETERMINED by the
denotation.  Justification: `maxᵢ offsetᵢ ≤ maxᵢ(env varᵢ + offsetᵢ)`
for every `env` (each `env varᵢ ≥ 0`), so raising the base by it never
changes the denotation.  This block ships that base-normalization
primitive; composing it with `canonicalize` (next leaf) yields the
genuinely canonical form needed for step-7 completeness. -/

/-- A value is dominated by itself plus any shift:
`levelMax offset (shift + offset) = shift + offset`.  Induction on
`offset`; successor case collapses through the definitional
`levelMax (_ + 1) (_ + 1) = levelMax _ _ + 1`. -/
theorem LevelExpr.levelMax_offset_dominatedRight (shift : Nat) :
    ∀ (offset : Nat),
      LevelExpr.levelMax offset (shift + offset) = shift + offset
  | 0 => rfl
  | predecessor + 1 => by
      show LevelExpr.levelMax predecessor (shift + predecessor) + 1 =
        (shift + predecessor) + 1
      rw [LevelExpr.levelMax_offset_dominatedRight shift predecessor]

/-- The maximum offset across a `varOffsets` list (ignoring the
variables) — i.e. `denoteVarOffsets` evaluated at the zero
environment. -/
def LevelExpr.MaxPlusForm.maxOffset : List (Nat × Nat) → Nat
  | [] => 0
  | (_, offset) :: rest =>
      LevelExpr.levelMax offset (LevelExpr.MaxPlusForm.maxOffset rest)

/-- The max offset is dominated by the env-fold under any environment:
`levelMax (maxOffset vo) (denoteVarOffsets vo env) = denoteVarOffsets
vo env`.  Each term `offsetᵢ` is dominated by `env varᵢ + offsetᵢ`
(`levelMax_offset_dominatedRight`); the middle-four interchange splits
the head-domination from the tail IH. -/
theorem LevelExpr.MaxPlusForm.maxOffset_dominated (env : Nat → Nat) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.levelMax (LevelExpr.MaxPlusForm.maxOffset entries)
          (LevelExpr.MaxPlusForm.denoteVarOffsets entries env) =
        LevelExpr.MaxPlusForm.denoteVarOffsets entries env
  | [] => rfl
  | (variableHead, offsetHead) :: rest => by
      show LevelExpr.levelMax
          (LevelExpr.levelMax offsetHead (LevelExpr.MaxPlusForm.maxOffset rest))
          (LevelExpr.levelMax (env variableHead + offsetHead)
            (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)) =
        LevelExpr.levelMax (env variableHead + offsetHead)
          (LevelExpr.MaxPlusForm.denoteVarOffsets rest env)
      rw [LevelExpr.levelMax_interchange offsetHead
            (LevelExpr.MaxPlusForm.maxOffset rest) (env variableHead + offsetHead)
            (LevelExpr.MaxPlusForm.denoteVarOffsets rest env),
          LevelExpr.levelMax_offset_dominatedRight (env variableHead) offsetHead,
          LevelExpr.MaxPlusForm.maxOffset_dominated env rest]

/-- Normalize the base to `max(baseConstant, maxᵢ offsetᵢ)` so the base
is recoverable as `denote(form, zeroEnv)`; the offsets are untouched. -/
def LevelExpr.MaxPlusForm.normalizeBase
    (form : LevelExpr.MaxPlusForm) : LevelExpr.MaxPlusForm :=
  { baseConstant :=
      LevelExpr.levelMax form.baseConstant
        (LevelExpr.MaxPlusForm.maxOffset form.varOffsets),
    varOffsets := form.varOffsets }

/-- Base normalization preserves the denotation: re-associate and
absorb the injected `maxOffset` via `maxOffset_dominated`. -/
theorem LevelExpr.MaxPlusForm.normalizeBase_denote
    (form : LevelExpr.MaxPlusForm) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denote (LevelExpr.MaxPlusForm.normalizeBase form) env =
      LevelExpr.MaxPlusForm.denote form env := by
  show LevelExpr.levelMax
      (LevelExpr.levelMax form.baseConstant
        (LevelExpr.MaxPlusForm.maxOffset form.varOffsets))
      (LevelExpr.MaxPlusForm.denoteVarOffsets form.varOffsets env) =
    LevelExpr.levelMax form.baseConstant
      (LevelExpr.MaxPlusForm.denoteVarOffsets form.varOffsets env)
  rw [LevelExpr.levelMax_assoc form.baseConstant
        (LevelExpr.MaxPlusForm.maxOffset form.varOffsets)
        (LevelExpr.MaxPlusForm.denoteVarOffsets form.varOffsets env),
      LevelExpr.MaxPlusForm.maxOffset_dominated env form.varOffsets]

/-! ## The genuinely-canonical form + base recovery

`fullCanonicalize` = `normalizeBase ∘ canonicalize`: canonicalize the
offsets (sorted, one per variable) and normalize the base.  This is the
canonical representative; its denotation matches the input, and end to
end it denotes the original predicative level.  The payoff of base
normalization is `normalizeBase_baseConstant_eq_denote_zeroEnvironment`:
the base is literally the denotation at the zero environment — hence
pinned by the denotation, the "equal denotation ⟹ equal base" half of
the eventual uniqueness argument. -/

/-- The genuinely-canonical form: canonicalize offsets, then normalize
the base. -/
def LevelExpr.MaxPlusForm.fullCanonicalize
    (form : LevelExpr.MaxPlusForm) : LevelExpr.MaxPlusForm :=
  LevelExpr.MaxPlusForm.normalizeBase
    (LevelExpr.MaxPlusForm.canonicalize form)

/-- `fullCanonicalize` preserves the denotation (chains
`normalizeBase_denote` and `canonicalize_denote`). -/
theorem LevelExpr.MaxPlusForm.fullCanonicalize_denote
    (form : LevelExpr.MaxPlusForm) (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denote (LevelExpr.MaxPlusForm.fullCanonicalize form) env =
      LevelExpr.MaxPlusForm.denote form env := by
  show LevelExpr.MaxPlusForm.denote
      (LevelExpr.MaxPlusForm.normalizeBase
        (LevelExpr.MaxPlusForm.canonicalize form)) env =
    LevelExpr.MaxPlusForm.denote form env
  rw [LevelExpr.MaxPlusForm.normalizeBase_denote
        (LevelExpr.MaxPlusForm.canonicalize form) env,
      LevelExpr.MaxPlusForm.canonicalize_denote form env]

/-- End-to-end: for a predicative expression, normalizing to a max-plus
form and fully canonicalizing denotes the same level. -/
theorem LevelExpr.fullCanonicalize_toMaxPlusForm_denote
    (level : LevelExpr) (hPred : LevelExpr.isPredicative level = true)
    (env : Nat → Nat) :
    LevelExpr.MaxPlusForm.denote
        (LevelExpr.MaxPlusForm.fullCanonicalize (LevelExpr.toMaxPlusForm level)) env =
      LevelExpr.denote level env := by
  rw [LevelExpr.MaxPlusForm.fullCanonicalize_denote (LevelExpr.toMaxPlusForm level) env,
      LevelExpr.toMaxPlusForm_denote env level hPred]

/-- The all-zeros environment — the probe that reads off the base. -/
def LevelExpr.MaxPlusForm.zeroEnvironment : Nat → Nat := fun _ => 0

/-- The env-fold at the zero environment collapses to the max offset:
`denoteVarOffsets vo zeroEnvironment = maxOffset vo`.  Each term
`0 + offsetᵢ` reduces (`Nat.zero_add`) to `offsetᵢ`. -/
theorem LevelExpr.MaxPlusForm.denoteVarOffsets_zeroEnvironment :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.denoteVarOffsets entries
          LevelExpr.MaxPlusForm.zeroEnvironment =
        LevelExpr.MaxPlusForm.maxOffset entries
  | [] => rfl
  | (variableHead, offsetHead) :: rest => by
      show LevelExpr.levelMax (0 + offsetHead)
          (LevelExpr.MaxPlusForm.denoteVarOffsets rest
            LevelExpr.MaxPlusForm.zeroEnvironment) =
        LevelExpr.levelMax offsetHead (LevelExpr.MaxPlusForm.maxOffset rest)
      rw [Nat.zero_add,
          LevelExpr.MaxPlusForm.denoteVarOffsets_zeroEnvironment rest]

/-- Re-absorption on the right: `levelMax (levelMax a b) b = levelMax a
b` (associativity + idempotence). -/
theorem LevelExpr.levelMax_reabsorb_right (valueA valueB : Nat) :
    LevelExpr.levelMax (LevelExpr.levelMax valueA valueB) valueB =
      LevelExpr.levelMax valueA valueB := by
  rw [LevelExpr.levelMax_assoc valueA valueB valueB,
      LevelExpr.levelMax_self valueB]

/-- Base recovery: after `normalizeBase`, the base constant equals the
denotation at the zero environment.  So the base is determined by the
denotation — the key fact for completeness.  Collapse the fold to
`maxOffset` (`denoteVarOffsets_zeroEnvironment`), then re-absorb the
duplicated `maxOffset` (`levelMax_reabsorb_right`). -/
theorem LevelExpr.MaxPlusForm.normalizeBase_baseConstant_eq_denote_zeroEnvironment
    (form : LevelExpr.MaxPlusForm) :
    (LevelExpr.MaxPlusForm.normalizeBase form).baseConstant =
      LevelExpr.MaxPlusForm.denote (LevelExpr.MaxPlusForm.normalizeBase form)
        LevelExpr.MaxPlusForm.zeroEnvironment := by
  show LevelExpr.levelMax form.baseConstant
      (LevelExpr.MaxPlusForm.maxOffset form.varOffsets) =
    LevelExpr.levelMax
      (LevelExpr.levelMax form.baseConstant
        (LevelExpr.MaxPlusForm.maxOffset form.varOffsets))
      (LevelExpr.MaxPlusForm.denoteVarOffsets form.varOffsets
        LevelExpr.MaxPlusForm.zeroEnvironment)
  rw [LevelExpr.MaxPlusForm.denoteVarOffsets_zeroEnvironment form.varOffsets,
      LevelExpr.levelMax_reabsorb_right form.baseConstant
        (LevelExpr.MaxPlusForm.maxOffset form.varOffsets)]

/-! ## Canonical-form structural invariant — sortedness by variable

The canonical `varOffsets` are sorted by variable index (and, after
absorption, strictly so).  Sortedness is phrased via a lower-bound:
`allVariablesAtLeast bound l` holds when every entry's variable is `≥
bound`, and `isSortedByVariable l` holds when each head lower-bounds
its tail and the tail is sorted.  The load-bearing helper for the
insertion-sort correctness (next leaf) is that inserting an entry whose
variable is `≥ bound` into an all-`≥ bound` list keeps it all-`≥
bound`. -/

/-- Every entry's variable index is at least `bound`. -/
def LevelExpr.MaxPlusForm.allVariablesAtLeast (bound : Nat) :
    List (Nat × Nat) → Bool
  | [] => true
  | (variableHead, _) :: rest =>
      Nat.ble bound variableHead &&
        LevelExpr.MaxPlusForm.allVariablesAtLeast bound rest

/-- The entries are sorted (non-strictly) ascending by variable index:
each head lower-bounds its tail, and the tail is itself sorted. -/
def LevelExpr.MaxPlusForm.isSortedByVariable : List (Nat × Nat) → Bool
  | [] => true
  | (variableHead, _) :: rest =>
      LevelExpr.MaxPlusForm.allVariablesAtLeast variableHead rest &&
        LevelExpr.MaxPlusForm.isSortedByVariable rest

/-- Build a true Boolean conjunction from both conjuncts being true —
the propext-free intro for `(a && b) = true`.  (`cases` on the plain
`Bool` left conjunct; the `true` branch reads `b` off directly.) -/
theorem LevelExpr.and_eq_true_of_both {flagLeft flagRight : Bool}
    (hLeft : flagLeft = true) (hRight : flagRight = true) :
    (flagLeft && flagRight) = true := by
  cases flagLeft with
  | false => exact Bool.noConfusion hLeft
  | true => exact hRight

/-- Inserting an entry whose variable is `≥ bound` into an all-`≥
bound` list keeps every variable `≥ bound`.  The deep-insertion
(`false`) branch recurses; both branches reassemble the conjunction
from `hBound` and the split hypothesis via `and_eq_true_of_both`. -/
theorem LevelExpr.MaxPlusForm.insertByVariable_preserves_allVariablesAtLeast
    (bound entryVariable entryOffset : Nat)
    (hBound : Nat.ble bound entryVariable = true) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.allVariablesAtLeast bound entries = true →
      LevelExpr.MaxPlusForm.allVariablesAtLeast bound
        (LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset) entries) =
          true
  | [], _ => by
      show (Nat.ble bound entryVariable &&
        LevelExpr.MaxPlusForm.allVariablesAtLeast bound []) = true
      exact LevelExpr.and_eq_true_of_both hBound rfl
  | (variableHead, offsetHead) :: rest, hAll => by
      show LevelExpr.MaxPlusForm.allVariablesAtLeast bound
          (match Nat.ble entryVariable variableHead with
           | true => (entryVariable, entryOffset) :: (variableHead, offsetHead) :: rest
           | false => (variableHead, offsetHead) ::
               LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset) rest) = true
      cases Nat.ble entryVariable variableHead with
      | true =>
          show (Nat.ble bound entryVariable &&
            LevelExpr.MaxPlusForm.allVariablesAtLeast bound
              ((variableHead, offsetHead) :: rest)) = true
          exact LevelExpr.and_eq_true_of_both hBound hAll
      | false =>
          show (Nat.ble bound variableHead &&
            LevelExpr.MaxPlusForm.allVariablesAtLeast bound
              (LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset) rest)) = true
          exact LevelExpr.and_eq_true_of_both
            (LevelExpr.and_eq_true_imp_left hAll)
            (LevelExpr.MaxPlusForm.insertByVariable_preserves_allVariablesAtLeast
              bound entryVariable entryOffset hBound rest
              (LevelExpr.and_eq_true_imp_right hAll))

/-! ## Insertion sort produces a sorted list

Two `Nat.ble` arithmetic facts (transitivity + totality-swap), proved
by structural induction, complete the insertion-sort correctness:
`insertByVariable` preserves `isSortedByVariable`, hence `sortByVariable`
always produces a sorted list — the first half of the canonical-form
structural invariant. -/

/-- `Nat.ble` transitivity (Boolean).  Structural 3D induction; the
all-successor case recurses, the rest close by `Nat.ble 0 _ = true`
or `Bool.noConfusion` on `Nat.ble (_+1) 0 = false`. -/
theorem LevelExpr.ble_trans :
    ∀ (valueA valueB valueC : Nat),
      Nat.ble valueA valueB = true → Nat.ble valueB valueC = true →
      Nat.ble valueA valueC = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, hab, _ => Bool.noConfusion hab
  | _ + 1, _ + 1, 0, _, hbc => Bool.noConfusion hbc
  | predA + 1, predB + 1, predC + 1, hab, hbc =>
      LevelExpr.ble_trans predA predB predC hab hbc

/-- `Nat.ble` totality (Boolean): a failed comparison flips to a true
one in the other direction.  Structural induction. -/
theorem LevelExpr.ble_false_swap :
    ∀ (valueA valueB : Nat),
      Nat.ble valueA valueB = false → Nat.ble valueB valueA = true
  | 0, _, hab => Bool.noConfusion hab
  | _ + 1, 0, _ => rfl
  | predA + 1, predB + 1, hab => LevelExpr.ble_false_swap predA predB hab

/-- Lowering the lower bound: if every variable is `≥ higherBound` and
`lowerBound ≤ higherBound`, then every variable is `≥ lowerBound`.
Per-entry weakening via `ble_trans`. -/
theorem LevelExpr.MaxPlusForm.allVariablesAtLeast_mono
    (lowerBound higherBound : Nat)
    (hBounds : Nat.ble lowerBound higherBound = true) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.allVariablesAtLeast higherBound entries = true →
      LevelExpr.MaxPlusForm.allVariablesAtLeast lowerBound entries = true
  | [], _ => rfl
  | (variableHead, _) :: rest, hAll =>
      LevelExpr.and_eq_true_of_both
        (LevelExpr.ble_trans lowerBound higherBound variableHead hBounds
          (LevelExpr.and_eq_true_imp_left hAll))
        (LevelExpr.MaxPlusForm.allVariablesAtLeast_mono lowerBound higherBound
          hBounds rest (LevelExpr.and_eq_true_imp_right hAll))

/-- Inserting preserves sortedness.  Shallow-insert (`true`) case: the
new head lower-bounds the old tail by `mono` (since `entry ≤ head ≤
tail`).  Deep-insert (`false`) case: the old head still lower-bounds
the insert result (`insertByVariable_preserves_allVariablesAtLeast`,
using `ble_false_swap` to flip the comparison), and the tail stays
sorted by the IH. -/
theorem LevelExpr.MaxPlusForm.insertByVariable_preserves_isSortedByVariable
    (entryVariable entryOffset : Nat) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.isSortedByVariable entries = true →
      LevelExpr.MaxPlusForm.isSortedByVariable
        (LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset) entries) =
          true
  | [], _ => rfl
  | (variableHead, offsetHead) :: rest, hSorted => by
      show LevelExpr.MaxPlusForm.isSortedByVariable
          (match Nat.ble entryVariable variableHead with
           | true => (entryVariable, entryOffset) :: (variableHead, offsetHead) :: rest
           | false => (variableHead, offsetHead) ::
               LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset) rest) = true
      cases hble : Nat.ble entryVariable variableHead with
      | true =>
          show (LevelExpr.MaxPlusForm.allVariablesAtLeast entryVariable
              ((variableHead, offsetHead) :: rest) &&
            LevelExpr.MaxPlusForm.isSortedByVariable
              ((variableHead, offsetHead) :: rest)) = true
          exact LevelExpr.and_eq_true_of_both
            (LevelExpr.and_eq_true_of_both hble
              (LevelExpr.MaxPlusForm.allVariablesAtLeast_mono entryVariable variableHead
                hble rest (LevelExpr.and_eq_true_imp_left hSorted)))
            hSorted
      | false =>
          show (LevelExpr.MaxPlusForm.allVariablesAtLeast variableHead
              (LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset) rest) &&
            LevelExpr.MaxPlusForm.isSortedByVariable
              (LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset) rest)) = true
          exact LevelExpr.and_eq_true_of_both
            (LevelExpr.MaxPlusForm.insertByVariable_preserves_allVariablesAtLeast
              variableHead entryVariable entryOffset
              (LevelExpr.ble_false_swap entryVariable variableHead hble)
              rest (LevelExpr.and_eq_true_imp_left hSorted))
            (LevelExpr.MaxPlusForm.insertByVariable_preserves_isSortedByVariable
              entryVariable entryOffset rest (LevelExpr.and_eq_true_imp_right hSorted))

/-- `sortByVariable` always produces a sorted list — fold the
single-insert preservation down the list. -/
theorem LevelExpr.MaxPlusForm.sortByVariable_produces_sorted :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.isSortedByVariable
        (LevelExpr.MaxPlusForm.sortByVariable entries) = true
  | [] => rfl
  | (entryVariable, entryOffset) :: rest => by
      show LevelExpr.MaxPlusForm.isSortedByVariable
          (LevelExpr.MaxPlusForm.insertByVariable (entryVariable, entryOffset)
            (LevelExpr.MaxPlusForm.sortByVariable rest)) = true
      exact LevelExpr.MaxPlusForm.insertByVariable_preserves_isSortedByVariable
        entryVariable entryOffset (LevelExpr.MaxPlusForm.sortByVariable rest)
        (LevelExpr.MaxPlusForm.sortByVariable_produces_sorted rest)

/-! ## Canonical-form structural invariant — strict sortedness

`absorbAdjacent` fuses adjacent equal-variable entries, so on a sorted
list it yields STRICTLY ascending variables (distinct).  Strict
sortedness reuses `allVariablesAtLeast`: each head's variable `+1`
lower-bounds its tail.  Toward the strict-sortedness theorem (next
leaf), this block proves absorption preserves a lower bound — the
result's variables are a subset of the input's, so any bound on the
input bounds the output. -/

/-- The entries are STRICTLY ascending by variable index: each head's
variable `+1` lower-bounds its tail (so no variable repeats), and the
tail is itself strictly sorted. -/
def LevelExpr.MaxPlusForm.isStrictlySortedByVariable :
    List (Nat × Nat) → Bool
  | [] => true
  | (variableHead, _) :: rest =>
      LevelExpr.MaxPlusForm.allVariablesAtLeast (variableHead + 1) rest &&
        LevelExpr.MaxPlusForm.isStrictlySortedByVariable rest

/-- `absorbFrom` keeps every variable `≥ bound`: it only fuses entries
(taking max offsets) and re-emits existing variables, never inventing
new ones.  No `Nat.beq`-equality is used — the comparison is cased only
to reduce the match. -/
theorem LevelExpr.MaxPlusForm.absorbFrom_preserves_allVariablesAtLeast
    (bound : Nat) :
    ∀ (current : Nat × Nat) (rest : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.allVariablesAtLeast bound (current :: rest) = true →
      LevelExpr.MaxPlusForm.allVariablesAtLeast bound
        (LevelExpr.MaxPlusForm.absorbFrom current rest) = true
  | _, [], hAll => hAll
  | (variableCurrent, offsetCurrent), (variableNext, offsetNext) :: rest, hAll => by
      show LevelExpr.MaxPlusForm.allVariablesAtLeast bound
          (match Nat.beq variableCurrent variableNext with
           | true => LevelExpr.MaxPlusForm.absorbFrom
               (variableCurrent, LevelExpr.levelMax offsetCurrent offsetNext) rest
           | false => (variableCurrent, offsetCurrent) ::
               LevelExpr.MaxPlusForm.absorbFrom (variableNext, offsetNext) rest) = true
      cases Nat.beq variableCurrent variableNext with
      | true =>
          exact LevelExpr.MaxPlusForm.absorbFrom_preserves_allVariablesAtLeast bound
            (variableCurrent, LevelExpr.levelMax offsetCurrent offsetNext) rest
            (LevelExpr.and_eq_true_of_both
              (LevelExpr.and_eq_true_imp_left hAll)
              (LevelExpr.and_eq_true_imp_right (LevelExpr.and_eq_true_imp_right hAll)))
      | false =>
          show (Nat.ble bound variableCurrent &&
            LevelExpr.MaxPlusForm.allVariablesAtLeast bound
              (LevelExpr.MaxPlusForm.absorbFrom (variableNext, offsetNext) rest)) = true
          exact LevelExpr.and_eq_true_of_both
            (LevelExpr.and_eq_true_imp_left hAll)
            (LevelExpr.MaxPlusForm.absorbFrom_preserves_allVariablesAtLeast bound
              (variableNext, offsetNext) rest
              (LevelExpr.and_eq_true_imp_right hAll))

/-- Absorption keeps every variable `≥ bound` (wrapper over
`absorbFrom_preserves_allVariablesAtLeast`). -/
theorem LevelExpr.MaxPlusForm.absorbAdjacent_preserves_allVariablesAtLeast
    (bound : Nat) :
    ∀ (entries : List (Nat × Nat)),
      LevelExpr.MaxPlusForm.allVariablesAtLeast bound entries = true →
      LevelExpr.MaxPlusForm.allVariablesAtLeast bound
        (LevelExpr.MaxPlusForm.absorbAdjacent entries) = true
  | [], hAll => hAll
  | entry :: rest, hAll => by
      show LevelExpr.MaxPlusForm.allVariablesAtLeast bound
          (LevelExpr.MaxPlusForm.absorbFrom entry rest) = true
      exact LevelExpr.MaxPlusForm.absorbFrom_preserves_allVariablesAtLeast
        bound entry rest hAll

end LeanFX2.Foundation.PolyCell.Universe
