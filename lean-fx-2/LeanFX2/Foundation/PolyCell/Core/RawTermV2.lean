import LeanFX2.Foundation.PolyCell.Core.GeneratorCore

/-! # Foundation/PolyCell/Core/RawTermV2 — the v2 structural raw term layer

Scope-indexed, NOT dim-indexed.  One generic `mkGen` constructor over
the `Generator` enum with structural children via `binderShifts`.
Nested terms are directly representable (the v1-impossible case).
No Term dependency. -/

open LeanFX2.Foundation.PolyCell.Core (Generator)

mutual
  inductive LeanFX2.Foundation.PolyCell.Core.RawTermV2 : Nat → Type where
    | mkGen :
        {scope : Nat} →
        (generator : Generator) →
        (payload : generator.payload scope) →
        (children : LeanFX2.Foundation.PolyCell.Core.RawTermChildrenV2
          generator.binderShifts scope) →
        LeanFX2.Foundation.PolyCell.Core.RawTermV2 scope

  inductive LeanFX2.Foundation.PolyCell.Core.RawTermChildrenV2
      : List Nat → Nat → Type where
    | childNil :
        {scope : Nat} →
        LeanFX2.Foundation.PolyCell.Core.RawTermChildrenV2 [] scope
    | childCons :
        {scope shift : Nat} →
        {restShifts : List Nat} →
        (childHead : LeanFX2.Foundation.PolyCell.Core.RawTermV2 (scope + shift)) →
        (childTail : LeanFX2.Foundation.PolyCell.Core.RawTermChildrenV2
          restShifts scope) →
        LeanFX2.Foundation.PolyCell.Core.RawTermChildrenV2
          (shift :: restShifts) scope
end

namespace LeanFX2.Foundation.PolyCell.Core.RawTermChildrenV2

@[reducible] def empty {scope : Nat} : RawTermChildrenV2 [] scope :=
  .childNil

@[reducible] def single {scope : Nat}
    (child : RawTermV2 scope) : RawTermChildrenV2 [0] scope :=
  .childCons (Nat.add_zero scope ▸ child) .childNil

@[reducible] def singleUnderBinder {scope : Nat}
    (child : RawTermV2 (scope + 1)) : RawTermChildrenV2 [1] scope :=
  .childCons child .childNil

@[reducible] def pairFlat {scope : Nat}
    (first second : RawTermV2 scope) : RawTermChildrenV2 [0, 0] scope :=
  .childCons (Nat.add_zero scope ▸ first)
    (.childCons (Nat.add_zero scope ▸ second) .childNil)

@[reducible] def binderShape {scope : Nat}
    (domain : RawTermV2 scope)
    (codomain : RawTermV2 (scope + 1)) : RawTermChildrenV2 [0, 1] scope :=
  .childCons (Nat.add_zero scope ▸ domain)
    (.childCons codomain .childNil)

@[reducible] def tripleFlat {scope : Nat}
    (first second third : RawTermV2 scope)
    : RawTermChildrenV2 [0, 0, 0] scope :=
  .childCons (Nat.add_zero scope ▸ first)
    (.childCons (Nat.add_zero scope ▸ second)
      (.childCons (Nat.add_zero scope ▸ third) .childNil))

end LeanFX2.Foundation.PolyCell.Core.RawTermChildrenV2
