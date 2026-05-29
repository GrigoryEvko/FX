import FX1Poly.Core.GeneratorCore

/-! # Foundation/PolyCell/Core/RawTerm — the v2 structural raw term layer

Scope-indexed, NOT dim-indexed.  One generic `mkGen` constructor over
the `Generator` enum with structural children via `binderShifts`.
Nested terms are directly representable (the v1-impossible case).
No Term dependency. -/

open FX1Poly.Core (Generator)

mutual
  inductive FX1Poly.Core.RawTerm : Nat → Type where
    | mkGen :
        {scope : Nat} →
        (generator : Generator) →
        (payload : generator.payload scope) →
        (children : FX1Poly.Core.RawTermChildren
          generator.binderShifts scope) →
        FX1Poly.Core.RawTerm scope

  inductive FX1Poly.Core.RawTermChildren
      : List Nat → Nat → Type where
    | childNil :
        {scope : Nat} →
        FX1Poly.Core.RawTermChildren [] scope
    | childCons :
        {scope shift : Nat} →
        {restShifts : List Nat} →
        (childHead : FX1Poly.Core.RawTerm (scope + shift)) →
        (childTail : FX1Poly.Core.RawTermChildren
          restShifts scope) →
        FX1Poly.Core.RawTermChildren
          (shift :: restShifts) scope
end

namespace FX1Poly.Core.RawTermChildren

@[reducible] def empty {scope : Nat} : RawTermChildren [] scope :=
  .childNil

@[reducible] def single {scope : Nat}
    (child : RawTerm scope) : RawTermChildren [0] scope :=
  .childCons (Nat.add_zero scope ▸ child) .childNil

@[reducible] def singleUnderBinder {scope : Nat}
    (child : RawTerm (scope + 1)) : RawTermChildren [1] scope :=
  .childCons child .childNil

@[reducible] def pairFlat {scope : Nat}
    (first second : RawTerm scope) : RawTermChildren [0, 0] scope :=
  .childCons (Nat.add_zero scope ▸ first)
    (.childCons (Nat.add_zero scope ▸ second) .childNil)

@[reducible] def binderShape {scope : Nat}
    (domain : RawTerm scope)
    (codomain : RawTerm (scope + 1)) : RawTermChildren [0, 1] scope :=
  .childCons (Nat.add_zero scope ▸ domain)
    (.childCons codomain .childNil)

@[reducible] def tripleFlat {scope : Nat}
    (first second third : RawTerm scope)
    : RawTermChildren [0, 0, 0] scope :=
  .childCons (Nat.add_zero scope ▸ first)
    (.childCons (Nat.add_zero scope ▸ second)
      (.childCons (Nat.add_zero scope ▸ third) .childNil))

end FX1Poly.Core.RawTermChildren
