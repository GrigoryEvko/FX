import FX1Poly.Tier0.RepresentableMapCategory
/-!
# CwR Extensions and Type-Former Classification (Uemura §4-5)

A CwR extension is intended to add new type formers to an existing type
theory.  Uemura's key theorem says type formers biject with representable
natural transformations in the slice category C/U over the universe object.
This file records the computable slice, natural-transformation, type-former,
and extension records; it does not prove the Uemura bijection theorem or
construct concrete Pi/Sigma/Id extensions.

Adding Π-types = adding one representable nat-trans π : (Σ_{A:U} U^A) → U.
Adding Σ-types = adding one representable nat-trans σ : (Σ_{A:U} U^A) → U.
Adding Id-types = adding one representable nat-trans ι : (Σ_{A:U} A×A) → U.

An extension σ : base → extended is conservative if it reflects
representability (existing typing is preserved).

Reference: arXiv:1904.04097 §4-5.
Zero external dependencies.
-/

namespace FX1Poly.Tier0

universe u v

/-- Construction-level ledger for the current CwR-extension subsystem. -/
inductive CwRExtensionConstructionLevel where
  | sliceInterface
  | naturalTransformationInterface
  | typeFormerRecord
  | extensionComposition
  | concreteTypeFormerInstances
  | uemuraBijectionTheorem
  | conservativeExtensionTheorem
  deriving DecidableEq, Repr

def CwRExtensionConstructionLevel.hasSliceInterface :
    CwRExtensionConstructionLevel → Bool
  | .sliceInterface => true
  | .naturalTransformationInterface => true
  | .typeFormerRecord => true
  | .extensionComposition => true
  | .concreteTypeFormerInstances => true
  | .uemuraBijectionTheorem => true
  | .conservativeExtensionTheorem => true

def CwRExtensionConstructionLevel.hasNaturalTransformationInterface :
    CwRExtensionConstructionLevel → Bool
  | .sliceInterface => false
  | .naturalTransformationInterface => true
  | .typeFormerRecord => true
  | .extensionComposition => true
  | .concreteTypeFormerInstances => true
  | .uemuraBijectionTheorem => true
  | .conservativeExtensionTheorem => true

def CwRExtensionConstructionLevel.hasTypeFormerRecord :
    CwRExtensionConstructionLevel → Bool
  | .sliceInterface => false
  | .naturalTransformationInterface => false
  | .typeFormerRecord => true
  | .extensionComposition => true
  | .concreteTypeFormerInstances => true
  | .uemuraBijectionTheorem => true
  | .conservativeExtensionTheorem => true

def CwRExtensionConstructionLevel.hasExtensionComposition :
    CwRExtensionConstructionLevel → Bool
  | .sliceInterface => false
  | .naturalTransformationInterface => false
  | .typeFormerRecord => false
  | .extensionComposition => true
  | .concreteTypeFormerInstances => true
  | .uemuraBijectionTheorem => true
  | .conservativeExtensionTheorem => true

def CwRExtensionConstructionLevel.hasConcreteTypeFormerInstances :
    CwRExtensionConstructionLevel → Bool
  | .sliceInterface => false
  | .naturalTransformationInterface => false
  | .typeFormerRecord => false
  | .extensionComposition => false
  | .concreteTypeFormerInstances => true
  | .uemuraBijectionTheorem => true
  | .conservativeExtensionTheorem => true

def CwRExtensionConstructionLevel.hasUemuraBijectionTheorem :
    CwRExtensionConstructionLevel → Bool
  | .sliceInterface => false
  | .naturalTransformationInterface => false
  | .typeFormerRecord => false
  | .extensionComposition => false
  | .concreteTypeFormerInstances => false
  | .uemuraBijectionTheorem => true
  | .conservativeExtensionTheorem => true

def CwRExtensionConstructionLevel.hasConservativeExtensionTheorem :
    CwRExtensionConstructionLevel → Bool
  | .sliceInterface => false
  | .naturalTransformationInterface => false
  | .typeFormerRecord => false
  | .extensionComposition => false
  | .concreteTypeFormerInstances => false
  | .uemuraBijectionTheorem => false
  | .conservativeExtensionTheorem => true

/-- Present status: concrete type-former instances (SN-087, `FxBaseSubstTypeFormers.lean`) — the
presheaf-level `piFormerMap`/`sigmaFormerMap` natural transformations carry the genuine Π/Σ former
content, and the literal `TypeFormer`/`CwRExtension` records are inhabited (at the identity shape the
iso representable class admits — see `typeFormer_overRenamingVecRMC_resultIsIsomorphism` for why no
non-degenerate former can inhabit the literal record over the renaming RMC).  The Uemura BIJECTION
and conservative-extension THEOREM remain open (SN-088). -/
def fxCwRExtensionConstructionLevel : CwRExtensionConstructionLevel :=
  .concreteTypeFormerInstances

theorem fxCwRExtensionConstructionLevel_eq :
    fxCwRExtensionConstructionLevel = .concreteTypeFormerInstances := rfl

theorem fxCwRExtension_hasSliceInterface :
    fxCwRExtensionConstructionLevel.hasSliceInterface = true := rfl

theorem fxCwRExtension_hasNaturalTransformationInterface :
    fxCwRExtensionConstructionLevel.hasNaturalTransformationInterface = true := rfl

theorem fxCwRExtension_hasTypeFormerRecord :
    fxCwRExtensionConstructionLevel.hasTypeFormerRecord = true := rfl

theorem fxCwRExtension_hasExtensionComposition :
    fxCwRExtensionConstructionLevel.hasExtensionComposition = true := rfl

theorem fxCwRExtension_hasConcreteTypeFormerInstances :
    fxCwRExtensionConstructionLevel.hasConcreteTypeFormerInstances = true := rfl

theorem fxCwRExtension_hasNoUemuraBijectionTheorem :
    fxCwRExtensionConstructionLevel.hasUemuraBijectionTheorem = false := rfl

theorem fxCwRExtension_hasNoConservativeExtensionTheorem :
    fxCwRExtensionConstructionLevel.hasConservativeExtensionTheorem = false :=
  rfl

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

/-- A functorial object family over the slice category C/U. -/
structure SliceFamily (category : RawCategory.{u, v})
    {universeObject : category.Object} where
  objectAt : SliceObject category universeObject → category.Object
  mapMorphism : {sliceA sliceB : SliceObject category universeObject} →
                SliceMorphism category sliceA sliceB →
                category.Morphism (objectAt sliceA) (objectAt sliceB)

/-- A natural transformation between two functors on a slice category,
encoded as a family of morphisms indexed by slice objects. -/
structure SliceNatTrans (category : RawCategory.{u, v})
    {universeObject : category.Object}
    (sourceFamily targetFamily : SliceFamily category) where
  component : (sliceObj : SliceObject category universeObject) →
              category.Morphism
                (sourceFamily.objectAt sliceObj)
                (targetFamily.objectAt sliceObj)
  naturality : ∀ (sliceA sliceB : SliceObject category universeObject)
    (sliceMorphism : SliceMorphism category sliceA sliceB),
    category.compose
        (sourceFamily.mapMorphism sliceMorphism)
        (component sliceB) =
      category.compose
        (component sliceA)
        (targetFamily.mapMorphism sliceMorphism)

/-- A type-former record in a CwR: a parameter object in the slice C/U and
a result map back to the universe, together with representability evidence
for that result map. -/
structure TypeFormer (cwrCategory : RepresentableMapCategory.{u, v})
    (universeObject : cwrCategory.underlying.Object) where
  /-- The "parameter object" in C/U — describes what data the type
  former consumes. For Π: (A : U, B : U^A). For Σ: same.
  For Id: (A : U, a : A, b : A). -/
  parameterObject : SliceObject cwrCategory.underlying universeObject

  /-- The result morphism: maps the parameter object to the universe
  (= produces a new type from the parameters). -/
  resultMap : cwrCategory.underlying.Morphism parameterObject.domain universeObject

  /-- The result map is representable in the CwR sense.  This records the
  universal-property obligation for the type former. -/
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

/-- Compose two extension records sequentially. -/
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
      dsimp only [Function.comp]
      rw [firstExtension.inclusion.preservesIdentity]
      rw [secondExtension.inclusion.preservesIdentity]
    preservesComposition := fun morphismF morphismG => by
      dsimp only [Function.comp]
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

end FX1Poly.Tier0
