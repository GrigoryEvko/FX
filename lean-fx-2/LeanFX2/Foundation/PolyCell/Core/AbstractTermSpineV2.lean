import LeanFX2.Foundation.PolyCell.Core.GeneratorMetadataV2

/-! # Foundation/PolyCell/Core/AbstractTermSpineV2 — parametric blueprint

This file ships an ABSTRACT, PARAMETRIC child-spine substrate as a
reusable architectural blueprint.  It is NOT the spine type used by
the certified `PolyCellV2.gen` constructor.

## Why two spine types

The polycell.md §4 specification of `PolyCellV2.gen` requires a
spine that is type-INDEXED by the children's raw erasures
(`children : RawTermChildrenV2 generator.binderShifts scope`), so
the `gen` constructor's output `rawCell` can directly reference
`children` as a type-level value:

```
gen : ... → (childSpine : CertifiedTermSpineV2 profile childSpecs scope children) →
      PolyCellV2 profile sort 0 scope () (.termBase (.mkGen generator payload children))
```

That spine type CANNOT be parameterized over an abstract child
carrier — it has to know about both `PolyCellV2` (for the head
type) and `RawTermChildrenV2` (for the index).  So the
spec-aligned `CertifiedTermSpineV2` ships inside the mutual block
with `PolyCellV2` in `PolyCellV2.lean` (Stage L1c.3).

This `AbstractTermSpineV2` (originally drafted as
`CertifiedTermSpineV2` in commit `cf1fe6c1`) is the
carrier-abstraction PATTERN — the same blueprint v1's
`CellChildren` used (parametric over `ChildCarrier`).  It's
preserved here for two reasons:

1. **The convenience layer is shared.** `ChildSpecV2.expectedScope`
   + its six smart-constructor lemmas + `ChildSpecV2.ExpectedCell`
   are useful regardless of which spine type consumes them.  Those
   are kept here as the canonical helpers.

2. **L2 Allais-style folds may want abstract carriers.** When the
   Allais-style `foldV2` (task #177) is built over `RawTermV2`, an
   abstract child-spine over a fold-result carrier could simplify
   the structural recursion.  This is forward-compat scaffolding;
   if the L2 design doesn't ultimately use it, this file can be
   stripped to just the `ChildSpecV2.expectedScope` namespace.

## What's in this file

* `ChildSpecV2.expectedScope` — `parentScope + childSpec.scopeShift`
* Six `expectedScope_*` lemmas (sameScopeDimZero,
  underOneBinderDimZero, four .term/.type pairings)
* `ChildSpecV2.ExpectedCell` — carrier slot type at one spec
* `AbstractTermSpineV2` — the parametric inductive (was named
  `CertifiedTermSpineV2` in `cf1fe6c1`; renamed `2026-05-27` to
  free that name for the spec-aligned concrete version in
  `PolyCellV2.lean`)
* `arity` + `arity_eq_length` + `ForGenerator` + the parallel
  arity-equality lemma

## Architectural pattern citations

The carrier-abstraction trick is the standard "tying the knot via
abstract carrier" pattern used in:

* Allais-McBride-Hamana well-scoped term encodings (Indexed-as-Free
  / Coda 2017): child slots are abstract types parameterized by a
  context.

* Sikkel/BiSikkel CwF semantic typing (POPL'25): presheaves carry
  abstract elements before being instantiated by specific models.

* v1's own `CellChildren` (this file is its direct v2 successor in
  spirit; the actual spine `PolyCellV2.gen` consumes is the
  spec-aligned concrete version in `PolyCellV2.lean`).

## Zero-axiom verification

All declarations use propext-free structural recursion + pattern
matching on Nat constructors / spec-list constructors.  Audit-gated
in `Tools/AuditAll/AuditPolyCell.lean`.

`universe u` for the carrier slot type: most consumers instantiate
at `Type 0`, but the parametric universe leaves room for higher-Type
carriers.
-/

namespace LeanFX2.Foundation.PolyCell.Core

universe u

namespace ChildSpecV2

/-- The scope a child position should be evaluated at, given the
parent's scope.

`expectedScope childSpec parentScope = parentScope + childSpec.scopeShift`.
For same-scope children (`scopeShift = 0`) this is `parentScope`; for
children under one fresh binder (`scopeShift = 1`) this is
`parentScope + 1`.

`@[reducible]` so downstream `rfl`-style proofs can unfold this without
explicit `unfold`. -/
@[reducible] def expectedScope (childSpec : ChildSpecV2)
    (parentScope : Nat) : Nat :=
  parentScope + childSpec.scopeShift

/-- Same-scope dim-zero children compute back to the parent scope.

Closes by `Nat.add_zero` because `sameScopeDimZero` has
`scopeShift = 0`. -/
theorem expectedScope_sameScopeDimZero (parentScope : Nat)
    (sort : CellSort) :
    (sameScopeDimZero sort).expectedScope parentScope = parentScope :=
  Nat.add_zero parentScope

/-- Under-one-binder children compute to parent scope + 1.

Closes by `rfl` because `underOneBinderDimZero` has `scopeShift = 1`. -/
theorem expectedScope_underOneBinderDimZero (parentScope : Nat)
    (sort : CellSort) :
    (underOneBinderDimZero sort).expectedScope parentScope =
      parentScope + 1 :=
  rfl

/-- Same-scope term child has expected scope = parent scope.

Convenience wrapper around `expectedScope_sameScopeDimZero` for the
`.term` instance. -/
theorem expectedScope_termSameScope (parentScope : Nat) :
    termSameScope.expectedScope parentScope = parentScope :=
  Nat.add_zero parentScope

/-- Term-under-binder child has expected scope = parent scope + 1. -/
theorem expectedScope_termUnderBinder (parentScope : Nat) :
    termUnderBinder.expectedScope parentScope = parentScope + 1 :=
  rfl

/-- Same-scope type child has expected scope = parent scope. -/
theorem expectedScope_typeSameScope (parentScope : Nat) :
    typeSameScope.expectedScope parentScope = parentScope :=
  Nat.add_zero parentScope

/-- Type-under-binder child has expected scope = parent scope + 1. -/
theorem expectedScope_typeUnderBinder (parentScope : Nat) :
    typeUnderBinder.expectedScope parentScope = parentScope + 1 :=
  rfl

/-- The carrier slot type expected at one child position.

Given an abstract carrier `ChildCarrier : CellSort → Nat → Nat → Type u`
and a parent scope, the i-th child position demands a value at
`ChildCarrier childSpec.cellSort childSpec.cellDimension
(childSpec.expectedScope parentScope)`.

This is the type used in `AbstractTermSpineV2.cons`'s head
parameter.  Separated into its own named def for downstream
readability. -/
@[reducible] def ExpectedCell
    (ChildCarrier : CellSort → Nat → Nat → Type u)
    (childSpec : ChildSpecV2) (parentScope : Nat) : Type u :=
  ChildCarrier childSpec.cellSort childSpec.cellDimension
    (childSpec.expectedScope parentScope)

end ChildSpecV2

/-- Heterogeneous abstract-child spine, parametric over a carrier.

PARAMETRIC over `ChildCarrier`: the spine doesn't know what a
"child" is.  Useful as an architectural blueprint and for forward-
compat with L2 Allais-style folds.

NOT used by the certified `PolyCellV2.gen` constructor — that
consumes a CONCRETE spine type-indexed by the children's raws,
defined inside the mutual block with `PolyCellV2` in
`PolyCellV2.lean` (Stage L1c.3, task #148).

Indexed by `List ChildSpecV2`: each position `i` in the spec list
demands a child of type `(specs[i]).ExpectedCell ChildCarrier
parentScope`. -/
inductive AbstractTermSpineV2
    (ChildCarrier : CellSort → Nat → Nat → Type u)
    (parentScope : Nat) : List ChildSpecV2 → Type u where
  /-- Empty spine for a nullary generator (zero children). -/
  | nil :
      AbstractTermSpineV2 ChildCarrier parentScope []
  /-- Cons a head child whose carrier slot matches the head spec. -/
  | cons {childSpec : ChildSpecV2} {remainingSpecs : List ChildSpecV2} :
      childSpec.ExpectedCell ChildCarrier parentScope →
      AbstractTermSpineV2 ChildCarrier parentScope remainingSpecs →
      AbstractTermSpineV2 ChildCarrier parentScope
        (childSpec :: remainingSpecs)

namespace AbstractTermSpineV2

/-- Arity (number of children) of an abstract-child spine.

Reads the count off the metadata index `childSpecs`: arity is the
length of the spec list. -/
def arity {ChildCarrier : CellSort → Nat → Nat → Type u}
    {parentScope : Nat} {childSpecs : List ChildSpecV2}
    (_spine : AbstractTermSpineV2 ChildCarrier parentScope childSpecs) :
    Nat :=
  childSpecs.length

/-- Spine arity equals the length of its metadata spec list.

Closes by `rfl` since `arity` is `childSpecs.length` by definition. -/
theorem arity_eq_length
    {ChildCarrier : CellSort → Nat → Nat → Type u}
    {parentScope : Nat} {childSpecs : List ChildSpecV2}
    (spine : AbstractTermSpineV2 ChildCarrier parentScope childSpecs) :
    spine.arity = childSpecs.length :=
  rfl

/-- The abstract-child spine demanded by a generator's metadata.

Specializes `AbstractTermSpineV2` to `generator.childSpecs`. -/
@[reducible] def ForGenerator
    (ChildCarrier : CellSort → Nat → Nat → Type u)
    (parentScope : Nat) (generator : Generator) : Type u :=
  AbstractTermSpineV2 ChildCarrier parentScope generator.childSpecs

/-- Generator abstract-spine arity equals the generator's declared
arity.  Combines `arity_eq_length` with metadata coherence. -/
theorem arity_forGenerator_eq
    {ChildCarrier : CellSort → Nat → Nat → Type u}
    {parentScope : Nat} {generator : Generator}
    (spine : ForGenerator ChildCarrier parentScope generator) :
    spine.arity = generator.arity :=
  Generator.childSpecs_length_eq_arity generator

end AbstractTermSpineV2

end LeanFX2.Foundation.PolyCell.Core
