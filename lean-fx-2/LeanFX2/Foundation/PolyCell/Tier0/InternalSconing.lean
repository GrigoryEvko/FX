import LeanFX2.Foundation.PolyCell.Tier0.CwRExtension
/-!
# Internal Sconing (Bocquet-Kaposi-Sattler, FSCD 2023)

Sconing = gluing along the global-sections functor Γ : PSh(C) → Set.
This file currently records the computable interface layer needed to talk
about sconing objects, morphisms, preservation witnesses, and extraction
records.  It does not construct a concrete BKS preservation instance or prove
canonicity, normalization, or parametricity transfer.

A sconing object is (X, S, p) where X is syntactic, S is semantic,
p : S → Γ(X) is the realization connecting semantics to syntax.

Reference: arXiv:2302.05190 §2-3.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Tier0

universe u v w

/-- Construction-level ledger for the current internal-sconing subsystem.

The current file reaches extraction record interfaces.  Concrete preservation
instances and transfer theorems are later Tier-0 milestones. -/
inductive SconingConstructionLevel where
  | globalSectionsInterface
  | objectMorphismInterface
  | preservationWitnessInterface
  | extractionRecordInterfaces
  | concretePreservationInstance
  | canonicityTransferTheorem
  | normalizationTransferTheorem
  | parametricityTransferTheorem
  | bksMetatheoryPackage
  deriving DecidableEq, Repr

def SconingConstructionLevel.hasGlobalSectionsInterface :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => true
  | .objectMorphismInterface => true
  | .preservationWitnessInterface => true
  | .extractionRecordInterfaces => true
  | .concretePreservationInstance => true
  | .canonicityTransferTheorem => true
  | .normalizationTransferTheorem => true
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasObjectMorphismInterface :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => true
  | .preservationWitnessInterface => true
  | .extractionRecordInterfaces => true
  | .concretePreservationInstance => true
  | .canonicityTransferTheorem => true
  | .normalizationTransferTheorem => true
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasPreservationWitnessInterface :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => false
  | .preservationWitnessInterface => true
  | .extractionRecordInterfaces => true
  | .concretePreservationInstance => true
  | .canonicityTransferTheorem => true
  | .normalizationTransferTheorem => true
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasExtractionRecordInterfaces :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => false
  | .preservationWitnessInterface => false
  | .extractionRecordInterfaces => true
  | .concretePreservationInstance => true
  | .canonicityTransferTheorem => true
  | .normalizationTransferTheorem => true
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasConcretePreservationInstance :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => false
  | .preservationWitnessInterface => false
  | .extractionRecordInterfaces => false
  | .concretePreservationInstance => true
  | .canonicityTransferTheorem => true
  | .normalizationTransferTheorem => true
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasCanonicityTransferTheorem :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => false
  | .preservationWitnessInterface => false
  | .extractionRecordInterfaces => false
  | .concretePreservationInstance => false
  | .canonicityTransferTheorem => true
  | .normalizationTransferTheorem => true
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasNormalizationTransferTheorem :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => false
  | .preservationWitnessInterface => false
  | .extractionRecordInterfaces => false
  | .concretePreservationInstance => false
  | .canonicityTransferTheorem => false
  | .normalizationTransferTheorem => true
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasParametricityTransferTheorem :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => false
  | .preservationWitnessInterface => false
  | .extractionRecordInterfaces => false
  | .concretePreservationInstance => false
  | .canonicityTransferTheorem => false
  | .normalizationTransferTheorem => false
  | .parametricityTransferTheorem => true
  | .bksMetatheoryPackage => true

def SconingConstructionLevel.hasBKSMetatheoryPackage :
    SconingConstructionLevel → Bool
  | .globalSectionsInterface => false
  | .objectMorphismInterface => false
  | .preservationWitnessInterface => false
  | .extractionRecordInterfaces => false
  | .concretePreservationInstance => false
  | .canonicityTransferTheorem => false
  | .normalizationTransferTheorem => false
  | .parametricityTransferTheorem => false
  | .bksMetatheoryPackage => true

/-- Present status: interfaces and extraction records only. -/
def fxSconingConstructionLevel : SconingConstructionLevel :=
  .extractionRecordInterfaces

theorem fxSconingConstructionLevel_eq :
    fxSconingConstructionLevel = .extractionRecordInterfaces := rfl

theorem fxSconing_hasGlobalSectionsInterface :
    fxSconingConstructionLevel.hasGlobalSectionsInterface = true := rfl

theorem fxSconing_hasObjectMorphismInterface :
    fxSconingConstructionLevel.hasObjectMorphismInterface = true := rfl

theorem fxSconing_hasPreservationWitnessInterface :
    fxSconingConstructionLevel.hasPreservationWitnessInterface = true := rfl

theorem fxSconing_hasExtractionRecordInterfaces :
    fxSconingConstructionLevel.hasExtractionRecordInterfaces = true := rfl

theorem fxSconing_hasNoConcretePreservationInstance :
    fxSconingConstructionLevel.hasConcretePreservationInstance = false := rfl

theorem fxSconing_hasNoCanonicityTransferTheorem :
    fxSconingConstructionLevel.hasCanonicityTransferTheorem = false := rfl

theorem fxSconing_hasNoNormalizationTransferTheorem :
    fxSconingConstructionLevel.hasNormalizationTransferTheorem = false := rfl

theorem fxSconing_hasNoParametricityTransferTheorem :
    fxSconingConstructionLevel.hasParametricityTransferTheorem = false := rfl

theorem fxSconing_hasNoBKSMetatheoryPackage :
    fxSconingConstructionLevel.hasBKSMetatheoryPackage = false := rfl

/-- Global sections: extracts closed elements from objects.
For a type theory, Γ(A) = closed terms of type A. -/
structure GlobalSections (category : RawCategory.{u, v}) where
  terminalObject : category.Object
  sections : category.Object → Type w
  sectionMap : {objectA objectB : category.Object} →
               category.Morphism objectA objectB →
               sections objectB → sections objectA
  mapsIdentity :
    ∀ (objectA : category.Object) (closedSection : sections objectA),
    sectionMap (category.identity objectA) closedSection = closedSection
  mapsComposition :
    ∀ {objectA objectB objectC : category.Object}
      (morphismF : category.Morphism objectA objectB)
      (morphismG : category.Morphism objectB objectC)
      (closedSection : sections objectC),
    sectionMap (category.compose morphismF morphismG) closedSection =
      sectionMap morphismF (sectionMap morphismG closedSection)

/-- A sconing object: syntactic object + semantic domain + realization. -/
structure SconingObject (category : RawCategory.{u, v})
    (globalSections : GlobalSections.{u, v, w} category) where
  syntacticObject : category.Object
  semanticDomain : Type w
  realizationMap : semanticDomain → globalSections.sections syntacticObject

/-- A sconing morphism: syntactic + semantic maps that commute with realization. -/
structure SconingMorphism {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    (source target : SconingObject category globalSections) where
  syntacticMap : category.Morphism source.syntacticObject target.syntacticObject
  semanticMap : source.semanticDomain → target.semanticDomain
  commutes :
    ∀ (semanticElement : source.semanticDomain),
    globalSections.sectionMap syntacticMap
        (target.realizationMap (semanticMap semanticElement)) =
      source.realizationMap semanticElement

/-- Identity sconing morphism. -/
def SconingMorphism.identity {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    (obj : SconingObject category globalSections) :
    SconingMorphism obj obj where
  syntacticMap := category.identity obj.syntacticObject
  semanticMap := id
  commutes := by
    intro semanticElement
    exact globalSections.mapsIdentity obj.syntacticObject
      (obj.realizationMap semanticElement)

/-- Compose sconing morphisms. -/
def SconingMorphism.comp {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    {objA objB objC : SconingObject category globalSections}
    (morphismF : SconingMorphism objA objB)
    (morphismG : SconingMorphism objB objC) :
    SconingMorphism objA objC where
  syntacticMap := category.compose morphismF.syntacticMap morphismG.syntacticMap
  semanticMap := fun semanticElement =>
    morphismG.semanticMap (morphismF.semanticMap semanticElement)
  commutes := by
    intro semanticElement
    rw [globalSections.mapsComposition]
    rw [morphismG.commutes]
    exact morphismF.commutes semanticElement

/-- The tautological sconing: S = Γ(X), realization = id. -/
def SconingObject.tautological {category : RawCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} category)
    (baseObject : category.Object) :
    SconingObject category globalSections where
  syntacticObject := baseObject
  semanticDomain := globalSections.sections baseObject
  realizationMap := id

/-- Projection functor: forgets semantic component. -/
def SconingObject.project {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    (obj : SconingObject category globalSections) :
    category.Object :=
  obj.syntacticObject

/-- Concrete lift of a base morphism to the sconing category. -/
structure SconingLift
    {baseCwR : RepresentableMapCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} baseCwR.underlying)
    {objectA objectB : baseCwR.underlying.Object}
    (morphism : baseCwR.underlying.Morphism objectA objectB) where
  sourceSemanticDomain : Type w
  targetSemanticDomain : Type w
  sourceRealizationMap : sourceSemanticDomain → globalSections.sections objectA
  targetRealizationMap : targetSemanticDomain → globalSections.sections objectB
  semanticMap : sourceSemanticDomain → targetSemanticDomain
  commutes :
    ∀ (semanticElement : sourceSemanticDomain),
    globalSections.sectionMap morphism
        (targetRealizationMap (semanticMap semanticElement)) =
      sourceRealizationMap semanticElement

/-- Concrete lift of a base pullback object through the sconing projection. -/
structure SconingPullbackLift
    {baseCwR : RepresentableMapCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} baseCwR.underlying)
    {objectA objectB objectC : baseCwR.underlying.Object}
    {morphismF : baseCwR.underlying.Morphism objectA objectC}
    {morphismG : baseCwR.underlying.Morphism objectB objectC}
    (square : PullbackSquare baseCwR.underlying morphismF morphismG) where
  liftedObject : SconingObject baseCwR.underlying globalSections
  projectsToPullback :
    liftedObject.syntacticObject = square.pullbackObject

/-- A sconing preservation witness interface: representable maps in base lift
to the sconing category and pullbacks have lifted objects.

This record is an obligation shape.  Possessing the type alone is not a
metatheory-transfer theorem; a concrete inhabitant for the intended base
category is still required. -/
structure SconingPreservation
    (baseCwR : RepresentableMapCategory.{u, v})
    (globalSections : GlobalSections.{u, v, w} baseCwR.underlying) where
  /-- Every representable map lifts through sconing. -/
  liftsRepresentable :
    ∀ {objectA objectB : baseCwR.underlying.Object}
      (morphism : baseCwR.underlying.Morphism objectA objectB),
    baseCwR.representableMaps.member morphism →
    SconingLift globalSections morphism
  /-- Pullbacks lift through sconing. -/
  liftsPullbacks :
    ∀ {objectA objectB objectC : baseCwR.underlying.Object}
      {morphismF : baseCwR.underlying.Morphism objectA objectC}
      {morphismG : baseCwR.underlying.Morphism objectB objectC}
      (square : PullbackSquare baseCwR.underlying morphismF morphismG),
    SconingPullbackLift globalSections square

/-- Canonicity extraction record: an interface for extracting semantic
canonical witnesses from closed terms of sconed types.

This is not constructed from `SconingPreservation` in the current file. -/
structure CanonicityExtraction
    {category : RawCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} category) where
  /-- For a sconed type with enumerable semantic domain, extract the
  canonical form of any closed term. -/
  extract :
    (sconedType : SconingObject category globalSections) →
    globalSections.sections sconedType.syntacticObject →
    sconedType.semanticDomain
  /-- The extracted canonical form realizes the original closed term. -/
  extractRealizes :
    ∀ (sconedType : SconingObject category globalSections)
      (closedTerm : globalSections.sections sconedType.syntacticObject),
    sconedType.realizationMap (extract sconedType closedTerm) = closedTerm

/-- Normalization extraction record with an explicit normal-form family.

This file records the shape only; it does not prove existence or uniqueness
of normal forms for FX terms. -/
structure NormalizationExtraction
    {category : RawCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} category) where
  /-- Normal-form type (the "renaming mode" semantic domain). -/
  NormalForm : category.Object → Type w
  /-- Every term has a normal form. -/
  normalize :
    ∀ (objectA : category.Object),
    globalSections.sections objectA → NormalForm objectA
  /-- Normal forms inject back into terms. -/
  embed :
    ∀ (objectA : category.Object),
    NormalForm objectA → globalSections.sections objectA
  /-- Normalization is idempotent: normalize ∘ embed = id. -/
  normalizeIdempotent :
    ∀ (objectA : category.Object) (normalForm : NormalForm objectA),
    normalize objectA (embed objectA normalForm) = normalForm

/-- Parametricity extraction record with an explicit relational family.

This file records the shape only; it does not derive free theorems for FX
polymorphic terms. -/
structure ParametricityExtraction
    {category : RawCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} category) where
  /-- Relational interpretation: each type gets a binary relation. -/
  Relation : category.Object → Type w
  /-- Every closed polymorphic term satisfies its relational interpretation. -/
  fundamental :
    ∀ (objectA : category.Object)
      (_closedTerm : globalSections.sections objectA),
    Relation objectA

end LeanFX2.Foundation.PolyCell.Tier0
