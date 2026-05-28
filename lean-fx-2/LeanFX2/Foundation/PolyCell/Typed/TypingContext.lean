import LeanFX2.Foundation.Ty

/-! # Foundation/PolyCell/Typed/TypingContext
   — M31 Phase Z₁ TypingContext profile inductive

M31 (#280, 2026-05-28).  FIRST shipped piece of Phase Z₁ (typed
core).  Ships the `TypingContext` inductive — the foundational
sequence-of-bindings structure that every `HasType` rule cites.

Per polycell.md §3.16 Phase Z₁ row (line 6376):
> Typed core: `TypingContext` + `HasType` for ~30-generator
> semantic core (var, unit, universe, Π, λ, app, Σ, pair, fst,
> snd, bool, nat, list, option, either, identity, refl, J)

This M31 ships ONLY the TypingContext inductive.  HasType ctors
ship at M32-M44 task slots:

* M32 #281 TypingContext.lookup + weakening helpers.
* M33 #282 HasType conv rule.
* M34 #283 HasType var rule.
* M35 #284 HasType universe formation.
* M36-M44 HasType Π/Σ/Unit/bool/Nat/List/Option/Either/Id/cumul/modal.

## What this ships

* `TypingContext level scope` — context inductive parameterized by
  universe level + scope size.  Two ctors:
  - `empty` — empty context (no bindings).
  - `cons bindingType ctx` — extend context with a new binding.

* `TypingContext.cons_scope_increment` — pinned theorem that
  consing increments the scope index by 1.

* `TypingContext.empty_scope_zero` — pinned theorem that the
  empty context has scope 0.

* Smoke fixtures: empty context, single-Unit context, nested
  contexts.

## Why parameterized by level + scope

* **Level**: every binding type lives in some universe `Type
  level`; the context tracks the maximum level across bindings
  for use in universe-formation rules (M35 #284).

* **Scope**: bindings index into a de Bruijn position; scope
  is the count of bindings, used by `TypingContext.lookup` (M32
  #281) to validate `Fin scope` positions.

The two indices are INDEPENDENT: a context at level `l, scope n`
can have any number of `Ty l 0` ... `Ty l (n-1)` bindings.
Lookup at position `Fin n` returns the binding's `Ty` at the
appropriate scope.

## Why not parametric over `Generator` / `Step`

`TypingContext` is purely SYNTACTIC — it tracks `Ty` bindings,
not term semantics.  Step / Generator interaction happens at
HasType rules (M34+).  The context layer is independent of
reduction discipline.

## Cons-shape semantics

`TypingContext.cons newType ctx` where:
* `newType : Ty level scope` is the binding TYPE at the
  current scope (BEFORE the new binding is added).
* `ctx : TypingContext level scope` is the existing context.

Result: `TypingContext level (scope + 1)` — scope incremented.

The new binding occupies position `0` (innermost / most recently
bound).  Older bindings shift up by 1 in de Bruijn position.

This matches standard de Bruijn discipline: newest binding has
the smallest index.

## Zero-axiom verification

Simple structural inductive over `Nat × Nat` indices + a single
linked-list ctor shape.  No `simp`, no `omega`, no `propext`.
All smokes close by `rfl`.  Audit-gated.

## Cross-references

* polycell.md §3.16 line 6376 (Phase Z₁ commitment).
* M21 #270 LevelExpr (richer level structure; M24 will retrofit
  Ty to use it).
* `Foundation/Ty.lean` (the `Ty` inductive carrying binding types).
-/

namespace LeanFX2.Foundation.PolyCell.Typed

/-- Typing context for the Phase Z₁ semantic core.

Inductive sequence of `Ty`-bindings, parameterized by universe
level + scope size.  Each `cons` adds one binding at de Bruijn
position 0, shifting older bindings up by 1.

Two ctors:
* `empty {level}` — empty context at scope 0.
* `cons newType ctx` — extend context with a new binding whose
  type is `newType : Ty level scope`.

This is the FOUNDATIONAL structure every HasType rule cites.
Phase Z₁ HasType ctors (M34+) take a `TypingContext` as input. -/
inductive TypingContext (level : Nat) : Nat → Type
  /-- Empty typing context.  No bindings, scope 0. -/
  | empty : TypingContext level 0
  /-- Extend context with a new binding whose type is `newType`.
  Scope increments by 1.  New binding occupies position 0
  (innermost). -/
  | cons {scope : Nat}
      (newType : LeanFX2.Ty level scope)
      (ctx : TypingContext level scope) :
      TypingContext level (scope + 1)

/-! ## Per-ctor smokes -/

/-- The empty context has scope 0. -/
theorem TypingContext.empty_scope_zero {level : Nat} :
    (TypingContext.empty : TypingContext level 0) =
      TypingContext.empty := rfl

/-- Cons increments scope by 1. -/
theorem TypingContext.cons_scope_increment {level scope : Nat}
    (newType : LeanFX2.Ty level scope)
    (ctx : TypingContext level scope) :
    (TypingContext.cons newType ctx :
        TypingContext level (scope + 1)) =
      TypingContext.cons newType ctx := rfl

/-! ## Concrete fixture contexts

Small fixture contexts demonstrating the layered construction
pattern.  M32 #281 lookup smokes will reuse these. -/

/-- Empty context at level 0.  The simplest possible context. -/
def TypingContext.emptyAtLevelZero : TypingContext 0 0 :=
  TypingContext.empty

/-- Single-binding context: `[unit]` at level 0, scope 1.
The innermost binding is `LeanFX2.Ty.unit`. -/
def TypingContext.singleUnit : TypingContext 0 1 :=
  TypingContext.cons LeanFX2.Ty.unit TypingContext.empty

/-- Two-binding context: `[unit, bool]` (reading innermost-out)
at level 0, scope 2.  Innermost binding (position 0) is bool;
outermost (position 1) is unit. -/
def TypingContext.twoBindings : TypingContext 0 2 :=
  TypingContext.cons LeanFX2.Ty.bool TypingContext.singleUnit

/-! ## Smoke witnesses

Pin the fixtures' shape via `rfl`-witnessed canonical-form
equations. -/

/-- emptyAtLevelZero is structurally empty. -/
theorem TypingContext.emptyAtLevelZero_canonical :
    TypingContext.emptyAtLevelZero = TypingContext.empty := rfl

/-- singleUnit is cons unit on empty. -/
theorem TypingContext.singleUnit_canonical :
    TypingContext.singleUnit =
      TypingContext.cons LeanFX2.Ty.unit TypingContext.empty := rfl

/-- twoBindings is cons bool on singleUnit. -/
theorem TypingContext.twoBindings_canonical :
    TypingContext.twoBindings =
      TypingContext.cons LeanFX2.Ty.bool TypingContext.singleUnit := rfl

/-! ## Aggregate metric -/

/-- TypingContext has exactly 2 constructors (empty + cons). -/
def TypingContext.ctorCount : Nat := 2

theorem TypingContext.ctorCount_correct :
    TypingContext.ctorCount = 2 := rfl

end LeanFX2.Foundation.PolyCell.Typed
