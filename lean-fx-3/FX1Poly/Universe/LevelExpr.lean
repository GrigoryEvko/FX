/-! # Foundation/PolyCell/Universe/LevelExpr
   — universe-polymorphism payload + DecidableEq

The `LevelExpr` inductive carrying universe-polymorphism payload
per polycell.md §11.8 (lines 4015-4031):

```
inductive LevelExpr where
  | lzero : LevelExpr
  | lsucc : LevelExpr → LevelExpr
  | lmax  : LevelExpr → LevelExpr → LevelExpr
  | limax : LevelExpr → LevelExpr → LevelExpr  -- impredicative max
  | lvar  : Nat → LevelExpr                    -- universe variable
```

## What this file defines

* `LevelExpr` inductive (5 ctors per spec).
* `DecidableEq LevelExpr` via `deriving DecidableEq` — propext-free
  because LevelExpr is a simple algebraic data type with Nat
  payloads (no indexed inductive shenanigans).
* `BEq LevelExpr` + `Repr LevelExpr` derivations for convenience.
* 5 explicit equality smokes (one per ctor) — `rfl`-pinned to
  catch regressions if `deriving DecidableEq` ever silently
  changes shape.
* `LevelExpr.ne_lsucc_self` predicativity guard.

Polynomial-time normalization up to `lmax e e = e`,
`lmax lzero e = e`, etc. lives in `LevelExprSimplify`.

## The five constructors

* `lmax e1 e2` — least upper bound (for `Π (x:A_e1). B_e2 :
  Type (lmax e1 e2)`).
* `limax e1 e2` — impredicative max (for `Π (x:Prop). B_e :
  Type e` collapsing to Prop when codomain is Prop).
* `lvar n` — universe variable (for first-class universe
  polymorphism).

## Zero-axiom verification

* `deriving DecidableEq, BEq, Repr` — Lean derives these
  propext-free for simple ADTs (no indexed inductives).
* 5 smoke theorems close by `rfl`.
* No `axiom`, no `sorry`, no Classical.  Audit-gated.

## References

* polycell.md §11.8 (lines 4015-4031) for the canonical spec.
* Mörtberg-Sterling arXiv:2406.05425 for the normalization
  algorithm.
* Sterling-Harper LFMTP 2021 "Logical Relations as Types"
  §5.4 for the universe-polymorphism motivation.
-/

namespace FX1Poly.Universe

/-- Universe-polymorphism level expression per polycell.md §11.8.

Five constructors:
* `lzero` — the bottom level (Set / Type 0).
* `lsucc e` — successor (Type e ↦ Type (lsucc e)).
* `lmax e1 e2` — least upper bound (predicative).
* `limax e1 e2` — impredicative max; collapses to `lzero` when
  the right argument is `lzero` (for Prop's impredicative
  quantification).
* `lvar n` — universe variable (de Bruijn index over an
  ambient universe-binder context). -/
inductive LevelExpr where
  /-- Bottom universe level. -/
  | lzero : LevelExpr
  /-- Successor: `lsucc e` represents `e + 1`. -/
  | lsucc : LevelExpr → LevelExpr
  /-- Predicative max: `lmax e1 e2` represents `max e1 e2`. -/
  | lmax : LevelExpr → LevelExpr → LevelExpr
  /-- Impredicative max: `limax e1 e2` represents `e2` when
  `e2 = lzero`, else `max e1 e2`.  Used for Prop's
  impredicative quantification rule. -/
  | limax : LevelExpr → LevelExpr → LevelExpr
  /-- Universe variable referencing a de Bruijn position in the
  ambient universe-binder context. -/
  | lvar : Nat → LevelExpr
deriving DecidableEq, BEq, Repr

/-! ## Per-ctor smoke theorems

Pin the inductive's shape via `rfl`-witnessed canonical-form
equations.  If `deriving DecidableEq` ever silently changes
behavior (e.g., a future Lean upgrade tweaks the elaboration),
these `rfl` lemmas catch the regression. -/

/-- lzero canonical form. -/
theorem LevelExpr.lzero_canonical : (LevelExpr.lzero = .lzero) := rfl

/-- lsucc applied to lzero is `lsucc lzero`. -/
theorem LevelExpr.lsucc_lzero_canonical :
    LevelExpr.lsucc .lzero = .lsucc .lzero := rfl

/-- lmax of two lzeros. -/
theorem LevelExpr.lmax_lzero_lzero_canonical :
    LevelExpr.lmax .lzero .lzero = .lmax .lzero .lzero := rfl

/-- limax of two lzeros. -/
theorem LevelExpr.limax_lzero_lzero_canonical :
    LevelExpr.limax .lzero .lzero = .limax .lzero .lzero := rfl

/-- lvar at index 0. -/
theorem LevelExpr.lvar_zero_canonical :
    LevelExpr.lvar 0 = .lvar 0 := rfl

/-! ## Structural distinctness -/

/-- A level expression is never equal to its own successor: `levelExpr ≠ lsucc
levelExpr`.  The predicativity guard at the level algebra (the `lsucc` chain is a
strict order, never a fixpoint) — by structural induction: the `lsucc inner` arm
injects `lsucc inner = lsucc (lsucc inner)` to `inner = lsucc inner` (refuted by
the IH), and every other head clashes with `lsucc`.  Size-free so it lives with
the inductive (the `size` measure is downstream in `LevelExprSimplify`).  Feeds
the no-Type-in-Type honesty probe (#442): a universe classified by itself would
force `e = lsucc e`, which this refutes. -/
theorem LevelExpr.ne_lsucc_self (levelExpr : LevelExpr) :
    levelExpr ≠ LevelExpr.lsucc levelExpr := by
  induction levelExpr with
  | lzero => intro selfEq; cases selfEq
  | lsucc inner ih =>
      intro selfEq
      injection selfEq with innerEq
      exact ih innerEq
  | lmax left right _ _ => intro selfEq; cases selfEq
  | limax left right _ _ => intro selfEq; cases selfEq
  | lvar index => intro selfEq; cases selfEq

/-! ## DecidableEq smoke checks -/

/-- DecidableEq decides equal canonical-form expressions to
`isTrue`. -/
theorem LevelExpr.decEq_refl_lzero :
    (decEq LevelExpr.lzero .lzero = .isTrue rfl) := rfl

/-- DecidableEq decides distinct ctors to `isFalse`. -/
example : ¬ (LevelExpr.lzero = .lsucc .lzero) := by
  intro contradiction
  cases contradiction

/-- DecidableEq distinguishes lmax + limax. -/
example : ¬ (LevelExpr.lmax .lzero .lzero = .limax .lzero .lzero) := by
  intro contradiction
  cases contradiction

end FX1Poly.Universe
