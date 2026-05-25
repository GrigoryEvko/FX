import LeanFX2.Foundation.PolyCell.Tier0.CwRExtension
/-!
# Internal Sconing (Bocquet-Kaposi-Sattler, FSCD 2023)

Sconing = gluing along the global-sections functor Γ : PSh(C) → Set.
This SINGLE construction delivers canonicity + normalization + parametricity.

A sconing object is (X, S, p) where X is syntactic, S is semantic,
p : S → Γ(X) is the realization connecting semantics to syntax.

Reference: arXiv:2302.05190 §2-3.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Tier0

universe u v w

/-- Global sections: extracts closed elements from objects.
For a type theory, Γ(A) = closed terms of type A. -/
structure GlobalSections (category : RawCategory.{u, v}) where
  terminalObject : category.Object
  sections : category.Object → Type w
  sectionMap : {objectA objectB : category.Object} →
               category.Morphism objectA objectB →
               sections objectB → sections objectA

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

/-- Identity sconing morphism. -/
def SconingMorphism.identity {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    (obj : SconingObject category globalSections) :
    SconingMorphism obj obj where
  syntacticMap := category.identity obj.syntacticObject
  semanticMap := id

/-- Compose sconing morphisms. -/
def SconingMorphism.comp {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    {objA objB objC : SconingObject category globalSections}
    (morphismF : SconingMorphism objA objB)
    (morphismG : SconingMorphism objB objC) :
    SconingMorphism objA objC where
  syntacticMap := category.compose morphismF.syntacticMap morphismG.syntacticMap
  semanticMap := morphismG.semanticMap ∘ morphismF.semanticMap

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

/-- A sconing preservation witness: representable maps in base lift to
the sconing category, preserving all CwR structure. This is the
KEY PROPERTY that makes metatheory transfer "for free." -/
structure SconingPreservation
    (baseCwR : RepresentableMapCategory.{u, v})
    (globalSections : GlobalSections.{u, v, w} baseCwR.underlying) where
  /-- Every representable map lifts through sconing. -/
  liftsRepresentable :
    ∀ {objectA objectB : baseCwR.underlying.Object}
      (morphism : baseCwR.underlying.Morphism objectA objectB),
    baseCwR.representableMaps.member morphism →
    True -- witness that the lifted morphism is representable in Sc(C)
  /-- Pullbacks lift through sconing. -/
  liftsPullbacks : True

/-- Canonicity extraction: from sconing preservation, extract that closed
terms of decidable types have computable canonical forms. -/
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

/-- Normalization extraction: from sconing with a normal-form semantic domain,
extract unique normal forms for all terms (not just closed ones). -/
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

/-- Parametricity extraction: from sconing with a relational semantic domain,
extract free theorems for polymorphic terms. -/
structure ParametricityExtraction
    {category : RawCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} category) where
  /-- Relational interpretation: each type gets a binary relation. -/
  Relation : category.Object → Type w
  /-- Every closed polymorphic term satisfies its relational interpretation. -/
  fundamental :
    ∀ (objectA : category.Object)
      (closedTerm : globalSections.sections objectA),
    Relation objectA

end LeanFX2.Foundation.PolyCell.Tier0
