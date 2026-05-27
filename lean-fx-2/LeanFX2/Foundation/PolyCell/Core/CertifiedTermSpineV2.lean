import LeanFX2.Foundation.PolyCell.Core.GeneratorMetadataV2

/-! # Foundation/PolyCell/Core/CertifiedTermSpineV2 — abstract child spine

This file ships the v2 certified-child-spine substrate.  It is the
direct v2 counterpart to v1's `CellChildren`
(`Foundation/PolyCell/Core/CellChildren.lean`) — a heterogeneous list
of children typed by each entry in a generator's `childSpecs`.

## The carrier-abstraction trick — tying the knot cleanly

The cyclic-dependency problem (the spine references `PolyCellV2`,
but `PolyCellV2.gen` references the spine) is resolved by making the
spine PARAMETRIC over an abstract child carrier
`ChildCarrier : CellSort → Nat → Nat → Type u`.  The spine doesn't
know what a "certified cell" is — it just enforces that the i-th
child position holds a value at the spec'd `cellSort`,
`cellDimension`, and `parentScope + scopeShift`.

This is the same pattern used in:

* Allais-McBride-Hamana well-scoped term encodings (Indexed-as-Free
  / Coda 2017), where the child slots are abstract types parameterized
  by a context.

* Sikkel/BiSikkel CwF semantic typing (POPL'25), where presheaves
  carry abstract elements before being instantiated by specific
  models.

* v1's own `CellChildren` (this file is its direct v2 successor).

`PolyCellV2` (Stage L1c.3, task #148) will instantiate the carrier
via a `Σ' (boundary), Σ' (rawCell), PolyCellV2 ...` existential
package — at which point the abstract spine becomes the concrete
certified spine.

## What's in this file

* `ChildSpecV2.expectedScope` — the convenience function
  `parentScope + childSpec.scopeShift`.  Plus six smart-constructor
  lemmas matching the six `ChildSpecV2` smart constructors.

* `ChildSpecV2.ExpectedCell` — the carrier slot type at one spec.

* `CertifiedTermSpineV2` — the inductive: `.nil` for empty,
  `.cons head tail` to extend.  Indexed by `List ChildSpecV2`.

* `CertifiedTermSpineV2.arity` — the spine's arity (length).

* `CertifiedTermSpineV2.ForGenerator` — convenience type:
  `CertifiedTermSpineV2 ChildCarrier scope generator.childSpecs`.

* Discipline lemmas: spine arity = spec list length = generator
  arity.

## What's NOT in this file

* Per-generator builders.  v1 shipped `lambdaChildren`,
  `piTypeChildren`, `contextConsChildren` (its three seed
  fixtures).  With 194 v2 generators, per-generator builders would
  be ~10-20 lines × 194 = thousands of lines of noise.  Downstream
  code constructs spines via raw `.cons head ... .nil` chains.

* PolyCellV2 itself or any concrete instantiation.  Those are
  Stage L1c.3 (task #148) and beyond.

## Zero-axiom verification

All declarations use propext-free structural recursion + pattern
matching on Nat constructors / spec-list constructors.  Audit-gated
in `Tools/AuditAll/AuditPolyCell.lean`.

`universe u` for the carrier slot type: most consumers instantiate
at `Type 0`, but the parametric universe leaves room for higher-Type
carriers (e.g. proof-relevant carriers needed for L2 Allais ops).
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

Closes by `rfl` because `sameScopeDimZero` has `scopeShift = 0`, and
`parentScope + 0` reduces to `parentScope` definitionally. -/
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

This is the type used in `CertifiedTermSpineV2.cons`'s head
parameter.  Separated into its own named def for downstream
readability (call sites can write `childSpec.ExpectedCell ChildCarrier
parentScope` instead of inlining the three field accesses). -/
@[reducible] def ExpectedCell
    (ChildCarrier : CellSort → Nat → Nat → Type u)
    (childSpec : ChildSpecV2) (parentScope : Nat) : Type u :=
  ChildCarrier childSpec.cellSort childSpec.cellDimension
    (childSpec.expectedScope parentScope)

end ChildSpecV2

/-- Heterogeneous certified-child spine, indexed by `List ChildSpecV2`.

Each position `i` in the spec list demands a child of type
`(specs[i]).ExpectedCell ChildCarrier parentScope` — i.e., a value at
the carrier slot dictated by that position's `cellSort`,
`cellDimension`, and `parentScope + scopeShift`.

PARAMETRIC over `ChildCarrier`: the spine doesn't know what a "child"
is.  Stage L1c.3 (`PolyCellV2`, task #148) instantiates `ChildCarrier`
with an existential Sigma packaging a certified cell + its boundary
+ its raw erasure.

This breaks the cyclic dependency without losing type-level
discipline: the spine still enforces every child's indices match its
spec, but the spine itself can be defined before `PolyCellV2`. -/
inductive CertifiedTermSpineV2
    (ChildCarrier : CellSort → Nat → Nat → Type u)
    (parentScope : Nat) : List ChildSpecV2 → Type u where
  /-- Empty spine for a nullary generator (zero children). -/
  | nil :
      CertifiedTermSpineV2 ChildCarrier parentScope []
  /-- Cons a head child whose carrier slot matches the head spec. -/
  | cons {childSpec : ChildSpecV2} {remainingSpecs : List ChildSpecV2} :
      childSpec.ExpectedCell ChildCarrier parentScope →
      CertifiedTermSpineV2 ChildCarrier parentScope remainingSpecs →
      CertifiedTermSpineV2 ChildCarrier parentScope
        (childSpec :: remainingSpecs)

namespace CertifiedTermSpineV2

/-- Arity (number of children) of a certified-child spine.

Reads the count off the metadata index `childSpecs`: arity is the
length of the spec list.  Doesn't inspect the actual cell values —
the arity is fixed by the type. -/
def arity {ChildCarrier : CellSort → Nat → Nat → Type u}
    {parentScope : Nat} {childSpecs : List ChildSpecV2}
    (_spine : CertifiedTermSpineV2 ChildCarrier parentScope childSpecs) :
    Nat :=
  childSpecs.length

/-- Spine arity equals the length of its metadata spec list.

Closes by `rfl` since `arity` is `childSpecs.length` by definition. -/
theorem arity_eq_length
    {ChildCarrier : CellSort → Nat → Nat → Type u}
    {parentScope : Nat} {childSpecs : List ChildSpecV2}
    (spine : CertifiedTermSpineV2 ChildCarrier parentScope childSpecs) :
    spine.arity = childSpecs.length :=
  rfl

/-- The certified-child spine demanded by a generator's metadata.

Specializes `CertifiedTermSpineV2` to `generator.childSpecs` — the
canonical spine shape that the certified `gen` ctor consumes. -/
@[reducible] def ForGenerator
    (ChildCarrier : CellSort → Nat → Nat → Type u)
    (parentScope : Nat) (generator : Generator) : Type u :=
  CertifiedTermSpineV2 ChildCarrier parentScope generator.childSpecs

/-- Generator child-spine arity equals the generator's declared arity.

Combines `arity_eq_length` with the metadata coherence lemma
`Generator.childSpecs_length_eq_arity` (already proven in
`GeneratorMetadataV2.lean`).

Closes by `Generator.childSpecs_length_eq_arity` since `arity` is
`childSpecs.length` definitionally. -/
theorem arity_forGenerator_eq
    {ChildCarrier : CellSort → Nat → Nat → Type u}
    {parentScope : Nat} {generator : Generator}
    (spine : ForGenerator ChildCarrier parentScope generator) :
    spine.arity = generator.arity :=
  Generator.childSpecs_length_eq_arity generator

end CertifiedTermSpineV2

end LeanFX2.Foundation.PolyCell.Core
