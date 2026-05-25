import LeanFX2.Foundation.PolyCell.Tier0.RepresentableMapCategory
/-!
# CwR Extensions and Type-Former Classification (Uemura §4-5)

A CwR extension adds new type formers to an existing type theory.
Uemura's key theorem: type formers biject with representable natural
transformations in the slice category C/U over the universe object.

Adding Π-types = adding one representable nat-trans π : (Σ_{A:U} U^A) → U.
Adding Σ-types = adding one representable nat-trans σ : (Σ_{A:U} U^A) → U.
Adding Id-types = adding one representable nat-trans ι : (Σ_{A:U} A×A) → U.

An extension σ : base → extended is conservative if it reflects
representability (existing typing is preserved).

Reference: arXiv:1904.04097 §4-5.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Tier0

universe u v

/-- The slice category C/U: objects are morphisms into U (= types in context);
morphisms are commutative triangles. -/
structure SliceObject (category : RawCategory.{u, v})
    (universeObject : category.Object) where
  domain : category.Object
  projection : category.Morphism domain universeObject

structure SliceMorphism (category : RawCategory.{u, v})
    {universeObject : category.Object}
    (source target : SliceObject category universeObject) where
  underlying : category.Morphism source.domain target.domain
  commutes : category.compose underlying target.projection = source.projection

/-- A natural transformation between two functors on a slice category,
encoded as a family of morphisms indexed by slice objects. -/
structure SliceNatTrans (category : RawCategory.{u, v})
    {universeObject : category.Object}
    (sourceFamily targetFamily : SliceObject category universeObject → category.Object) where
  component : (sliceObj : SliceObject category universeObject) →
              category.Morphism (sourceFamily sliceObj) (targetFamily sliceObj)
  naturality : ∀ (sliceA sliceB : SliceObject category universeObject)
    (_ : SliceMorphism category sliceA sliceB),
    True  -- naturality square commutes (simplified — full version needs
          -- functorial action on sourceFamily/targetFamily)

/-- A type former in a CwR is a representable natural transformation
in the slice C/U. It classifies a way to form new types from old.

Concretely: given a "parameter shape" (what inputs the type former takes)
and a "result" (the output type), the type former is the universal
map from parameter-families to result-types. -/
structure TypeFormer (cwrCategory : RepresentableMapCategory.{u, v})
    (universeObject : cwrCategory.underlying.Object) where
  /-- The "parameter object" in C/U — describes what data the type
  former consumes. For Π: (A : U, B : U^A). For Σ: same.
  For Id: (A : U, a : A, b : A). -/
  parameterObject : SliceObject cwrCategory.underlying universeObject

  /-- The result morphism: maps the parameter object to the universe
  (= produces a new type from the parameters). -/
  resultMap : cwrCategory.underlying.Morphism parameterObject.domain universeObject

  /-- The result map is representable (in the CwR sense). This is what
  makes it a LEGITIMATE type former — it has the correct universal
  property for dependent elimination. -/
  resultIsRepresentable : cwrCategory.representableMaps.member resultMap

/-- A CwR extension: a conservative CwR-morphism that adds new type formers
to an existing CwR without breaking existing typing. -/
structure CwRExtension (baseCwR : RepresentableMapCategory.{u, v}) where
  /-- The extended CwR (has more type formers than base). -/
  extendedCwR : RepresentableMapCategory.{u, v}

  /-- The inclusion morphism (base embeds into extended). -/
  inclusion : CwRMorphism baseCwR extendedCwR

  /-- The universe object in the extended CwR. -/
  extendedUniverse : extendedCwR.underlying.Object

  /-- The new type formers added by this extension. -/
  newTypeFormers : List (TypeFormer extendedCwR extendedUniverse)

  /-- CONSERVATIVITY: the inclusion reflects representability.
  If a morphism in base becomes representable in extended, it was
  already representable in base. Existing programs don't change type. -/
  isConservative : inclusion.isConservative

/-- Compose two extensions sequentially (adding Π then Σ). -/
def CwRExtension.compose
    {baseCwR : RepresentableMapCategory.{u, v}}
    (firstExtension : CwRExtension baseCwR)
    (secondExtension : CwRExtension firstExtension.extendedCwR) :
    CwRExtension baseCwR where
  extendedCwR := secondExtension.extendedCwR
  inclusion := {
    mapObject := secondExtension.inclusion.mapObject ∘ firstExtension.inclusion.mapObject
    mapMorphism := fun morphism =>
      secondExtension.inclusion.mapMorphism (firstExtension.inclusion.mapMorphism morphism)
    preservesIdentity := fun objectA => by
      unfold Function.comp
      rw [firstExtension.inclusion.preservesIdentity]
      rw [secondExtension.inclusion.preservesIdentity]
    preservesComposition := fun morphismF morphismG => by
      unfold Function.comp
      rw [firstExtension.inclusion.preservesComposition]
      rw [secondExtension.inclusion.preservesComposition]
    preservesRepresentable := fun morphism memberWitness =>
      secondExtension.inclusion.preservesRepresentable _
        (firstExtension.inclusion.preservesRepresentable morphism memberWitness)
  }
  extendedUniverse := secondExtension.extendedUniverse
  newTypeFormers := secondExtension.newTypeFormers
  isConservative := fun sourceMorphism memberInExtended => by
    have memberInMiddle := secondExtension.isConservative
      (firstExtension.inclusion.mapMorphism sourceMorphism) memberInExtended
    exact firstExtension.isConservative sourceMorphism memberInMiddle

/-- The identity extension (adds nothing). -/
def CwRExtension.identity (baseCwR : RepresentableMapCategory.{u, v})
    (universeObject : baseCwR.underlying.Object) :
    CwRExtension baseCwR where
  extendedCwR := baseCwR
  inclusion := CwRMorphism.identity baseCwR
  extendedUniverse := universeObject
  newTypeFormers := []
  isConservative := fun _ memberWitness => memberWitness

/-- An extension is FAITHFUL if distinct base morphisms map to distinct
extended morphisms (no collapsing). -/
def CwRExtension.isFaithful
    {baseCwR : RepresentableMapCategory.{u, v}}
    (extension : CwRExtension baseCwR) : Prop :=
  ∀ {objectA objectB : baseCwR.underlying.Object}
    (morphismF morphismG : baseCwR.underlying.Morphism objectA objectB),
    extension.inclusion.mapMorphism morphismF =
    extension.inclusion.mapMorphism morphismG →
    morphismF = morphismG

/-- Number of type formers added by an extension. -/
def CwRExtension.typeFormerCount
    {baseCwR : RepresentableMapCategory.{u, v}}
    (extension : CwRExtension baseCwR) : Nat :=
  extension.newTypeFormers.length

end LeanFX2.Foundation.PolyCell.Tier0
