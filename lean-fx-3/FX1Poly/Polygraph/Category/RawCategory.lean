/-!
# Raw Categories and Functors (generic 2-category core)

The generic, context-free category-theory core: a `RawCategory` (objects +
morphisms + composition + identity + the three category laws) and the generic
`RawFunctor` between two of them, together with the identity functor, functor
composition, and the unit/associativity laws making raw categories and functors
a (large) category.

This is pure category theory over an ARBITRARY `RawCategory` — nothing here
mentions contexts, representable maps, or any PolyCell axis.  The
context-specific Representable-Map-Category layer (`RepresentableMapCategory`,
`CwRMorphism`) lives in `FX1Poly.Tier0.Context.RepresentableMapCategory` and
specialises this core.

Zero external dependencies. Raw Lean 4 + Init only.
-/

namespace FX1Poly.Polygraph

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

/-- A **functor** between two raw categories — maps objects and morphisms,
preserving identity and composition.  This is THE generic functor of the context
axis: `RawEndofunctor` (the lock carrier, `Context.lean`), the renaming ⊂
substitution inclusion (`RenamingInclusion.lean`), and the model functors all
specialise it rather than re-spelling these four fields. -/
structure RawFunctor (sourceCategory targetCategory : RawCategory.{u, v}) where
  /-- Action on objects. -/
  mapObject : sourceCategory.Object → targetCategory.Object
  /-- Action on morphisms. -/
  mapMorphism : {objectA objectB : sourceCategory.Object} →
                sourceCategory.Morphism objectA objectB →
                targetCategory.Morphism (mapObject objectA) (mapObject objectB)
  /-- Preserves identity. -/
  preservesIdentity : ∀ (objectA : sourceCategory.Object),
    mapMorphism (sourceCategory.identity objectA) =
      targetCategory.identity (mapObject objectA)
  /-- Preserves composition. -/
  preservesComposition :
    ∀ {objectA objectB objectC : sourceCategory.Object}
      (morphismF : sourceCategory.Morphism objectA objectB)
      (morphismG : sourceCategory.Morphism objectB objectC),
    mapMorphism (sourceCategory.compose morphismF morphismG) =
      targetCategory.compose (mapMorphism morphismF) (mapMorphism morphismG)

/-- The identity functor on a category — maps objects and morphisms to themselves. -/
def RawFunctor.identity (category : RawCategory.{u, v}) : RawFunctor category category where
  mapObject := fun object => object
  mapMorphism := fun morphism => morphism
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-- **Composition of functors** (DIAGRAMMATIC order, matching `RawCategory.compose`):
`firstFunctor.compose secondFunctor` applies `firstFunctor` then `secondFunctor`.
Both functor laws are PROVED from the two factors'. -/
def RawFunctor.compose {sourceCategory midCategory targetCategory : RawCategory.{u, v}}
    (firstFunctor : RawFunctor sourceCategory midCategory)
    (secondFunctor : RawFunctor midCategory targetCategory) :
    RawFunctor sourceCategory targetCategory where
  mapObject := fun object => secondFunctor.mapObject (firstFunctor.mapObject object)
  mapMorphism := fun morphism => secondFunctor.mapMorphism (firstFunctor.mapMorphism morphism)
  preservesIdentity := fun objectA => by
    rw [firstFunctor.preservesIdentity, secondFunctor.preservesIdentity]
  preservesComposition := fun morphismF morphismG => by
    rw [firstFunctor.preservesComposition, secondFunctor.preservesComposition]

/-- The identity functor is a LEFT unit for composition — strict (`RawFunctor` eta). -/
theorem RawFunctor.identity_compose {sourceCategory targetCategory : RawCategory.{u, v}}
    (functor : RawFunctor sourceCategory targetCategory) :
    (RawFunctor.identity sourceCategory).compose functor = functor := rfl

/-- The identity functor is a RIGHT unit for composition. -/
theorem RawFunctor.compose_identity {sourceCategory targetCategory : RawCategory.{u, v}}
    (functor : RawFunctor sourceCategory targetCategory) :
    functor.compose (RawFunctor.identity targetCategory) = functor := rfl

/-- Functor composition is associative — strict.  With the two unit laws, raw
categories and `RawFunctor`s form a (large) category. -/
theorem RawFunctor.compose_assoc {categoryA categoryB categoryC categoryD : RawCategory.{u, v}}
    (firstFunctor : RawFunctor categoryA categoryB)
    (secondFunctor : RawFunctor categoryB categoryC)
    (thirdFunctor : RawFunctor categoryC categoryD) :
    (firstFunctor.compose secondFunctor).compose thirdFunctor
      = firstFunctor.compose (secondFunctor.compose thirdFunctor) := rfl

end FX1Poly.Polygraph
