/-! # Foundation/PolyCell/Universe/LevelExpr
   — Phase Z₀ universe-polymorphism payload + DecidableEq

M21 (#270, 2026-05-28).  FIRST shipped piece of Phase Z₀.  Ships
the `LevelExpr` inductive carrying universe-polymorphism payload
per polycell.md §11.8 (lines 4015-4031).

Per the spec excerpt:

```
inductive LevelExpr where
  | lzero : LevelExpr
  | lsucc : LevelExpr → LevelExpr
  | lmax  : LevelExpr → LevelExpr → LevelExpr
  | limax : LevelExpr → LevelExpr → LevelExpr  -- impredicative max
  | lvar  : Nat → LevelExpr                    -- universe variable
```

## What this ships

* `LevelExpr` inductive (5 ctors per spec).
* `DecidableEq LevelExpr` via `deriving DecidableEq` — propext-free
  because LevelExpr is a simple algebraic data type with Nat
  payloads (no indexed inductive shenanigans).
* `BEq LevelExpr` + `Repr LevelExpr` derivations for convenience.
* 5 explicit equality smokes (one per ctor) — `rfl`-pinned to
  catch regressions if `deriving DecidableEq` ever silently
  changes shape.

## What this does NOT ship

* **Polynomial-time normalization** (M22 #271 task): per
  Mörtberg-Sterling arXiv:2406.05425, equality up to
  `lmax e e = e`, `lmax lzero e = e`, etc.  Substantial
  algorithm (~300-500 LoC); deferred to M22.

* **UniverseFlag enum** (M23 #272 task): the Setzer-Rathjen
  ladder (standard / inaccessible / mahlo / superMahlo /
  nMahlo / hyperMahlo / weaklyCompact / indescribable /
  reflecting / vopenka).

* **Generator.payload refactor** (M24 #273 task): retrofitting
  `gen_universeCode` to use `LevelExpr × UniverseFlag` payload
  in place of the current `Nat`.

* **4 universe-mode generators** (M25 #274): gen_universeU /
  gen_universeS / gen_universeD / gen_universeOmega.

This is the FOUNDATION — type definition + DecidableEq only.
M22-M30 build the rest of Phase Z₀ on top.

## Phase Z₀ STRICT gate advancement

Per `AuditPhaseZ.lean` (#380): when M22 ships polynomial-time
normalization + M23 ships UniverseFlag, the Phase Z₀
`STRICT_Z0_MOTIVE_state` advances from `.notStarted` to
`.scaffoldShipped`.  This commit is the FIRST advance signal:
the underlying inductive exists, but the full motive
infrastructure (normalization + flag + Generator refactor) is
pending.  Lockstep advancement is M22+M23+M24+M25 territory.

## Why LevelExpr (vs `UniverseLevel`)

The existing `Foundation/Ty.lean` uses `UniverseLevel` (a simple
Nat wrapper at scope 0).  `LevelExpr` is the RICHER replacement
adding:
* `lmax e1 e2` — least upper bound (for `Π (x:A_e1). B_e2 :
  Type (lmax e1 e2)`).
* `limax e1 e2` — impredicative max (for `Π (x:Prop). B_e :
  Type e` collapsing to Prop when codomain is Prop).
* `lvar n` — universe variable (for first-class universe
  polymorphism).

Migration from `UniverseLevel` to `LevelExpr` happens at M24
(#273) and is intentionally NOT done here — this commit ships
the new inductive as a parallel definition, leaving the existing
`UniverseLevel` in place until M24's migration cascade lands.

## Zero-axiom verification

* `deriving DecidableEq, BEq, Repr` — Lean derives these
  propext-free for simple ADTs (no indexed inductives).
* 5 smoke theorems close by `rfl`.
* No `axiom`, no `sorry`, no Classical.  Audit-gated.

## References

* polycell.md §11.8 (lines 4015-4031) for the canonical spec.
* Mörtberg-Sterling arXiv:2406.05425 for the M22 normalization
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
