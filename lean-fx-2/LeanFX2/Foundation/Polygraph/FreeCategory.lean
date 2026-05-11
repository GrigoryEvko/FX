import LeanFX2.Foundation.Polygraph.Laws

/-! # `FreeOneCategory` + `FreeTwoCategoryAt` — Burroni free-category API.

Per Burroni 1993 / extended-roadmap §2 Definition 2.1, the free
strict ω-category over a polygraph `X` is the quotient of formal
compositions by associativity, unit, and interchange.

Our `HorizontalChain` (K11.5) and `VerticalChain` (K11.4) inductive
types are the canonical normal-form representatives of those
quotient classes:

* `HorizontalChain` is in bijection with formal whiskering composites
  modulo associativity and unit — every such composite reduces to a
  finite sequence of arrows via the cons/identity ctors.
* `VerticalChain` is in bijection with formal vertical composites
  along a fixed `(n+1)`-boundary modulo associativity and unit —
  every such composite reduces to a finite sequence of `(n+2)`-cells.

K11.6 ships the associativity and unit laws as theorems, so the
chains + laws TOGETHER form the freely-generated category structure
in the standard categorical sense (Object / Morphism / id / ∘ / laws).

## What this file ships

* `FreeOneCategory`: bundle the dim-1 path category — objects are
  vertices (`Nat`), morphisms are `HorizontalChain`, composition is
  `append`.  The laws are `compose_assoc`, `identity_left`,
  `identity_right`.  The `fromGenerator` inclusion lifts a single
  dim-1 arrow into a length-1 path.

* `FreeTwoCategoryAt dim sv tv`: bundle the dim-`(n+2)` vertical
  category at fixed globular boundary `(sv, tv)` — objects are
  dim-`(n+1)` cells, morphisms are `VerticalChain`, composition is
  `append`.  Same laws + `fromGenerator` for a single 2-cell.

## What is NOT shipped

* The universal property of the free category (Burroni adjoint
  proper): "for every strict n-category `C` and polygraph morphism
  `f : X → U(C)`, there is a unique strict n-functor `F : X* → C`
  with `U(F) = f`."  Requires abstract definitions of strict
  n-category and polygraph morphism — deferred to K11.7b.

* Interchange of vertical and horizontal at the same dim — requires
  horizontal composition of 2-cells (currently we only have
  horizontal composition of 1-cells), deferred to K11.6b alongside
  full Eckmann-Hilton.

Every shipped declaration is zero-axiom (the bundle just renames
already-shipped theorems via `abbrev` / direct reference). -/

namespace LeanFX2.Foundation.Polygraph

namespace FreeOneCategory

/-- Objects: dim-0 vertices, encoded as `Nat`. -/
abbrev Object := Nat

/-- Morphisms: horizontal chains of dim-1 arrows. -/
abbrev Morphism (sourceObj targetObj : Object) : Type :=
  HorizontalChain sourceObj targetObj

/-- Identity morphism: the empty path at `obj`. -/
abbrev identity (obj : Object) : Morphism obj obj :=
  HorizontalChain.identity obj

/-- Composition: chain concatenation. -/
abbrev compose {sourceObj midObj targetObj : Object}
    (firstMorphism : Morphism sourceObj midObj) (secondMorphism : Morphism midObj targetObj) :
    Morphism sourceObj targetObj :=
  HorizontalChain.append firstMorphism secondMorphism

theorem compose_assoc {sourceObj midOneObj midTwoObj targetObj : Object}
    (firstMorphism : Morphism sourceObj midOneObj)
    (secondMorphism : Morphism midOneObj midTwoObj)
    (thirdMorphism : Morphism midTwoObj targetObj) :
    compose (compose firstMorphism secondMorphism) thirdMorphism =
    compose firstMorphism (compose secondMorphism thirdMorphism) :=
  HorizontalChain.append_assoc firstMorphism secondMorphism thirdMorphism

theorem identity_left {sourceObj targetObj : Object}
    (homArg : Morphism sourceObj targetObj) :
    compose (identity sourceObj) homArg = homArg :=
  HorizontalChain.append_identity_left homArg

theorem identity_right {sourceObj targetObj : Object}
    (homArg : Morphism sourceObj targetObj) :
    compose homArg (identity targetObj) = homArg :=
  HorizontalChain.append_identity_right homArg

/-- Inclusion of a generator: lift a single dim-1 arrow into a
length-1 path morphism. -/
def fromGenerator {sourceVtx targetVtx : Object}
    (singleArrow : PolyCell 1 sourceVtx targetVtx) :
    Morphism sourceVtx targetVtx :=
  HorizontalChain.cons singleArrow (HorizontalChain.identity targetVtx)

theorem fromGenerator_length_eq_one {sourceVtx targetVtx : Object}
    (singleArrow : PolyCell 1 sourceVtx targetVtx) :
    (fromGenerator singleArrow).length = 1 := by
  show (HorizontalChain.cons singleArrow
          (HorizontalChain.identity targetVtx)).length = 1
  rw [HorizontalChain.length_cons_eq_succ_length_tail,
      HorizontalChain.length_identity_eq_zero]

end FreeOneCategory

/- Free vertical category of `(dim+2)`-cells at a fixed globular
boundary `(sourceVtx, targetVtx)` of the underlying `(dim+1)`-cells.
Parameterized by `dim`, `sourceVtx`, `targetVtx` because vertical
composition only makes sense for cells sharing globular boundary at
the next-lower dim. -/
namespace FreeTwoCategoryAt

/-- Objects: dim-`(dim+1)` cells at the fixed boundary. -/
abbrev Object (dim sourceVtx targetVtx : Nat) : Type :=
  PolyCell (dim + 1) sourceVtx targetVtx

/-- Morphisms: vertical chains of dim-`(dim+2)` cells linking two
parallel dim-`(dim+1)` cells. -/
abbrev Morphism {dim sourceVtx targetVtx : Nat}
    (sourceObj targetObj : Object dim sourceVtx targetVtx) : Type :=
  VerticalChain sourceObj targetObj

/-- Identity morphism: the empty chain at `obj`. -/
abbrev identity {dim sourceVtx targetVtx : Nat}
    (obj : Object dim sourceVtx targetVtx) : Morphism obj obj :=
  VerticalChain.identity obj

/-- Composition: chain concatenation. -/
abbrev compose {dim sourceVtx targetVtx : Nat}
    {sourceObj midObj targetObj : Object dim sourceVtx targetVtx}
    (firstMorphism : Morphism sourceObj midObj) (secondMorphism : Morphism midObj targetObj) :
    Morphism sourceObj targetObj :=
  VerticalChain.append firstMorphism secondMorphism

theorem compose_assoc {dim sourceVtx targetVtx : Nat}
    {sourceObj midOneObj midTwoObj targetObj :
       Object dim sourceVtx targetVtx}
    (firstMorphism : Morphism sourceObj midOneObj)
    (secondMorphism : Morphism midOneObj midTwoObj)
    (thirdMorphism : Morphism midTwoObj targetObj) :
    compose (compose firstMorphism secondMorphism) thirdMorphism =
    compose firstMorphism (compose secondMorphism thirdMorphism) :=
  VerticalChain.append_assoc firstMorphism secondMorphism thirdMorphism

theorem identity_left {dim sourceVtx targetVtx : Nat}
    {sourceObj targetObj : Object dim sourceVtx targetVtx}
    (homArg : Morphism sourceObj targetObj) :
    compose (identity sourceObj) homArg = homArg :=
  VerticalChain.append_identity_left homArg

theorem identity_right {dim sourceVtx targetVtx : Nat}
    {sourceObj targetObj : Object dim sourceVtx targetVtx}
    (homArg : Morphism sourceObj targetObj) :
    compose homArg (identity targetObj) = homArg :=
  VerticalChain.append_identity_right homArg

/-- Inclusion of a generator: lift a single dim-`(dim+2)` cell into
a length-1 chain morphism between its source and target. -/
def fromGenerator {dim sourceVtx targetVtx : Nat}
    (twoCellWitness : PolyCell (dim + 2) sourceVtx targetVtx) :
    Morphism (cellSource twoCellWitness) (cellTarget twoCellWitness) :=
  VerticalChain.cons twoCellWitness rfl rfl
    (VerticalChain.identity (cellTarget twoCellWitness))

theorem fromGenerator_length_eq_one {dim sourceVtx targetVtx : Nat}
    (twoCellWitness : PolyCell (dim + 2) sourceVtx targetVtx) :
    (fromGenerator twoCellWitness).length = 1 := by
  show (VerticalChain.cons twoCellWitness rfl rfl
          (VerticalChain.identity (cellTarget twoCellWitness))).length = 1
  rw [VerticalChain.length_cons_eq_succ_length_tail,
      VerticalChain.length_identity_eq_zero]

end FreeTwoCategoryAt

end LeanFX2.Foundation.Polygraph
