import FX1Poly.Axis.Context.AxisObligation
import FX1Poly.Polygraph.Category.RawCategory
import FX1Poly.Polygraph.Category.Pullback
/-!
# Representable Map Categories (Uemura 2023)

A representable map category (CwR) is a category C equipped with a
distinguished class of morphisms R ⊆ Mor(C) — the "representable maps" —
satisfying: closed under pullback, contains all isos, closed under
composition. Objects of CwR ARE type theories; morphisms are extensions.

Type formers (Π, Σ, Id, etc.) are representable natural transformations
in the slice C/U over the universe object.

This is the categorical substrate that ALL PolyCell axes plug into.
The eventual FX generator table should interpret its term and type former
entries as representable maps in the FX CwR.

Reference: Uemura, "A general framework for the semantics of type theory",
MSCS 33(3), 2023, arXiv:1904.04097 §2-3.

The generic category-theory core this layer specialises — `RawCategory`,
`RawFunctor`, `MorphismClass`, `PullbackSquare`, `IsIsomorphism` — lives in the
zero-dependency `FX1Poly.Polygraph.Category.*` files (Init-only); only the
representable-map-specific structures stay here.

Zero external dependencies. Raw Lean 4 + Init only.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

universe u v

/-- A Representable Map Category (CwR): a category with a distinguished
class of "representable maps" satisfying three closure conditions.

This is Uemura's Definition 2.1 (arXiv:1904.04097 §2). -/
structure RepresentableMapCategory where
  /-- The underlying category. -/
  underlying : RawCategory.{u, v}

  /-- The distinguished class R of representable maps. -/
  representableMaps : MorphismClass underlying

  /-- AXIOM 1: Representable maps are closed under pullback.
  If f : A → C is representable and g : B → C is any morphism,
  the pullback of f along g exists and f* is representable. -/
  closedUnderPullback :
    ∀ {objectA objectB objectC : underlying.Object}
      (morphismF : underlying.Morphism objectA objectC)
      (morphismG : underlying.Morphism objectB objectC),
      representableMaps.member morphismF →
      ∃ (square : PullbackSquare underlying morphismF morphismG),
        representableMaps.member square.projectionRight

  /-- AXIOM 2: All isomorphisms are representable. -/
  isomorphismsRepresentable :
    ∀ {objectA objectB : underlying.Object}
      (morphism : underlying.Morphism objectA objectB),
      IsIsomorphism underlying morphism →
      representableMaps.member morphism

  /-- AXIOM 3: Representable maps are closed under composition. -/
  closedUnderComposition :
    ∀ {objectA objectB objectC : underlying.Object}
      (morphismF : underlying.Morphism objectA objectB)
      (morphismG : underlying.Morphism objectB objectC),
      representableMaps.member morphismF →
      representableMaps.member morphismG →
      representableMaps.member (underlying.compose morphismF morphismG)

/-- A CwR-morphism (functor preserving representable maps) — the generic
`RawFunctor` between the two underlying categories PLUS preservation of the
representable class.  Inheriting `RawFunctor`'s four functor fields (rather than
re-spelling them) means the `mapObject` / `mapMorphism` / `preservesIdentity` /
`preservesComposition` projections and the generic functor API apply directly. -/
structure CwRMorphism (sourceCwR targetCwR : RepresentableMapCategory.{u, v})
    extends RawFunctor sourceCwR.underlying targetCwR.underlying where
  /-- PRESERVES REPRESENTABILITY: maps representable to representable. -/
  preservesRepresentable :
    ∀ {objectA objectB : sourceCwR.underlying.Object}
      (morphism : sourceCwR.underlying.Morphism objectA objectB),
    sourceCwR.representableMaps.member morphism →
    targetCwR.representableMaps.member (mapMorphism morphism)

/-- Identity CwR-morphism. -/
def CwRMorphism.identity (cwrCategory : RepresentableMapCategory.{u, v}) :
    CwRMorphism cwrCategory cwrCategory where
  mapObject := id
  mapMorphism := id
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl
  preservesRepresentable := fun _ memberWitness => memberWitness

/-- A CwR-morphism is conservative (= faithful + essentially surjective
on representable maps) when it reflects representable maps. -/
def CwRMorphism.isConservative
    {sourceCwR targetCwR : RepresentableMapCategory.{u, v}}
    (morphism : CwRMorphism sourceCwR targetCwR) : Prop :=
  ∀ {objectA objectB : sourceCwR.underlying.Object}
    (sourceMorphism : sourceCwR.underlying.Morphism objectA objectB),
    targetCwR.representableMaps.member (morphism.mapMorphism sourceMorphism) →
    sourceCwR.representableMaps.member sourceMorphism

end FX1Poly.Axis
