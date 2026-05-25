import LeanFX2.Foundation.PolyCell.Tier0.AxisObligation
/-!
# Representable Map Categories (Uemura 2023)

A representable map category (CwR) is a category C equipped with a
distinguished class of morphisms R ⊆ Mor(C) — the "representable maps" —
satisfying: closed under pullback, contains all isos, closed under
composition. Objects of CwR ARE type theories; morphisms are extensions.

Type formers (Π, Σ, Id, etc.) are representable natural transformations
in the slice C/U over the universe object.

This is the categorical substrate that ALL PolyCell axes plug into.
FX's 78 Generator values are representable maps in the FX CwR.

Reference: Uemura, "A general framework for the semantics of type theory",
MSCS 33(3), 2023, arXiv:1904.04097 §2-3.

Zero external dependencies. Raw Lean 4 + Init only.
-/

namespace LeanFX2.Foundation.PolyCell.Tier0

universe u v

/-- A category: objects + morphisms + composition + identity + laws.
Raw encoding without universe polymorphism issues — we keep it simple. -/
structure RawCategory where
  Object : Type u
  Morphism : Object → Object → Type v
  identity : (objectA : Object) → Morphism objectA objectA
  compose : {objectA objectB objectC : Object} →
            Morphism objectA objectB → Morphism objectB objectC →
            Morphism objectA objectC
  composeAssoc : ∀ {objectA objectB objectC objectD : Object}
    (morphismF : Morphism objectA objectB)
    (morphismG : Morphism objectB objectC)
    (morphismH : Morphism objectC objectD),
    compose (compose morphismF morphismG) morphismH =
    compose morphismF (compose morphismG morphismH)
  identityLeft : ∀ {objectA objectB : Object}
    (morphismF : Morphism objectA objectB),
    compose (identity objectA) morphismF = morphismF
  identityRight : ∀ {objectA objectB : Object}
    (morphismF : Morphism objectA objectB),
    compose morphismF (identity objectB) = morphismF

/-- A distinguished class of morphisms in a category. -/
structure MorphismClass (category : RawCategory.{u, v}) where
  member : {objectA objectB : category.Object} →
           category.Morphism objectA objectB → Prop
  memberDecidable : {objectA objectB : category.Object} →
                    (morphism : category.Morphism objectA objectB) →
                    Decidable (member morphism)

/-- A pullback square in a category:
```
  pullbackObject ---projRight--→ objectB
       |                           |
    projLeft                    morphismG
       |                           |
       ↓                           ↓
    objectA -----morphismF----→ objectC
```
-/
structure PullbackSquare (category : RawCategory.{u, v})
    {objectA objectB objectC : category.Object}
    (morphismF : category.Morphism objectA objectC)
    (morphismG : category.Morphism objectB objectC) where
  pullbackObject : category.Object
  projectionLeft : category.Morphism pullbackObject objectA
  projectionRight : category.Morphism pullbackObject objectB
  commutes : category.compose projectionLeft morphismF =
             category.compose projectionRight morphismG
  isUniversal : ∀ (candidateObject : category.Object)
    (candidateLeft : category.Morphism candidateObject objectA)
    (candidateRight : category.Morphism candidateObject objectB),
    category.compose candidateLeft morphismF =
    category.compose candidateRight morphismG →
    ∃ (mediator : category.Morphism candidateObject pullbackObject),
      category.compose mediator projectionLeft = candidateLeft ∧
      category.compose mediator projectionRight = candidateRight

/-- A morphism is an isomorphism if it has a two-sided inverse. -/
structure IsIsomorphism (category : RawCategory.{u, v})
    {objectA objectB : category.Object}
    (morphism : category.Morphism objectA objectB) where
  inverse : category.Morphism objectB objectA
  leftInverse : category.compose inverse morphism = category.identity objectB
  rightInverse : category.compose morphism inverse = category.identity objectA

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

/-- A CwR-morphism (functor preserving representable maps). -/
structure CwRMorphism (sourceCwR targetCwR : RepresentableMapCategory.{u, v}) where
  /-- Action on objects. -/
  mapObject : sourceCwR.underlying.Object → targetCwR.underlying.Object

  /-- Action on morphisms. -/
  mapMorphism : {objectA objectB : sourceCwR.underlying.Object} →
                sourceCwR.underlying.Morphism objectA objectB →
                targetCwR.underlying.Morphism (mapObject objectA) (mapObject objectB)

  /-- Preserves identity. -/
  preservesIdentity : ∀ (objectA : sourceCwR.underlying.Object),
    mapMorphism (sourceCwR.underlying.identity objectA) =
    targetCwR.underlying.identity (mapObject objectA)

  /-- Preserves composition. -/
  preservesComposition :
    ∀ {objectA objectB objectC : sourceCwR.underlying.Object}
      (morphismF : sourceCwR.underlying.Morphism objectA objectB)
      (morphismG : sourceCwR.underlying.Morphism objectB objectC),
    mapMorphism (sourceCwR.underlying.compose morphismF morphismG) =
    targetCwR.underlying.compose (mapMorphism morphismF) (mapMorphism morphismG)

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

end LeanFX2.Foundation.PolyCell.Tier0
