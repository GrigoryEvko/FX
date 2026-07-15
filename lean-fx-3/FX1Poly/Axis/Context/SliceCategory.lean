import FX1Poly.Axis.Context.CwRExtension
import FX1Poly.Axis.Context.Instances.Subst.FxBaseSubstCategory

/-! # The slice category C/U + the generic display (`context-2`, the context-side residue)

`context-2`'s headline — Uemura's bijection *type-formers ↔ representable natural transformations* —
is a CROSS-AXIS (`×type`) statement: it pairs the context category's slice/nat-trans structure with
the TYPE-former side, and over the shipped renaming RMC the formers are even forced degenerate
(`typeFormer_overRenamingVecRMC_resultIsIsomorphism`).  That bijection proper is the display-fibration
(`fib-1`) deliverable and is deferred there.

This file ships the strictly CONTEXT-SIDE substrate the bijection lives in — pure category theory over
the context category, no type-former content, Axis-isolated:

  * `sliceCategory category U` — **the slice category C/U is a genuine `RawCategory`**: objects are
    the shipped `SliceObject`s (a context with a chosen type, i.e. a morphism into the universe object
    `U`), morphisms are the commuting triangles `SliceMorphism`, with identity, composition, and the
    three category laws all PROVED (inherited from the base category on the underlying morphisms via
    `SliceMorphism.ext`).
  * `genericDisplayNatTrans` — the canonical natural transformation from the projection family
    (`s ↦ s.domain`) to the constant-universe family, component = each slice object's own projection;
    its NATURALITY is exactly the slice triangle's commute.
  * `SliceFamily.IsFunctorial` + `sliceProjectionFamily_isFunctorial` /
    `universeConstantFamily_isFunctorial` — both families are GENUINE functors (the laws `SliceFamily`
    itself omits, now proved).
  * `UniverseElement` + `sliceToElement` / `elementToSlice` (mutually inverse) — the slice category IS
    the category of ELEMENTS of `U`: `SliceObject ≃ UniverseElement` is the (definitional) Grothendieck
    iso `C/U ≅ ∫ U`.
  * `genericDisplay_component_elementToSlice` / `_eq_classifier` / `_classifier_reconstructs` /
    `_surjective` / `_component_reindex` — the generic display's PROVED universal property: it
    classifies every universe element bijectively and is stable under reindexing.  This earns the word
    "generic" by proof; `_surjective` also machine-checks the honest DEGENERACY (every map into `U` is
    a component, so "representable into `U`" is the whole hom-set here — no information).
  * `SliceNatTrans.idTrans` / `vcomp` (+ componentwise unit laws) — the vertical 2-cell structure on
    slice natural transformations, naturality squares proved.
  * `fxSubstSliceCategory` / `fxSubstGenericDisplay` — the above instantiated over the FX context
    axis's substitution category (`fxBaseSubstCategory`), at an arbitrary scope as the universe object.

The remaining `×type` content — pairing the generic display with the TYPE-former records
(`piFormerMap` / `sigmaFormerMap`) for Uemura's type-former ↔ representable-nat-trans BIJECTION, plus
the genuine representable-maps / pullback refinement (where representability stops being the whole
hom-set) — is `fib-1`, deferred.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

universe u v

/-! ## The slice category C/U -/

/-- **Slice-morphism extensionality.**  Two slice morphisms are equal as soon as their underlying base
morphisms agree — the commute condition is a `Prop`, hence proof-irrelevant. -/
theorem SliceMorphism.ext {category : RawCategory.{u, v}} {universeObject : category.Object}
    {source target : SliceObject category universeObject}
    (morphismF morphismG : SliceMorphism category source target)
    (underlyingsAgree : morphismF.underlying = morphismG.underlying) :
    morphismF = morphismG := by
  cases morphismF; cases morphismG; cases underlyingsAgree; rfl

/-- The identity slice morphism — the base identity, commuting by the left-identity law. -/
def SliceObject.identityMorphism {category : RawCategory.{u, v}}
    {universeObject : category.Object} (sliceObj : SliceObject category universeObject) :
    SliceMorphism category sliceObj sliceObj where
  underlying := category.identity sliceObj.domain
  commutes := category.identityLeft sliceObj.projection

/-- Composition of slice morphisms — compose the underlying base morphisms; the composite triangle
commutes by associativity + the two component commute conditions. -/
def SliceMorphism.compose {category : RawCategory.{u, v}} {universeObject : category.Object}
    {source middle target : SliceObject category universeObject}
    (morphismF : SliceMorphism category source middle)
    (morphismG : SliceMorphism category middle target) :
    SliceMorphism category source target where
  underlying := category.compose morphismF.underlying morphismG.underlying
  commutes := by
    rw [category.composeAssoc, morphismG.commutes, morphismF.commutes]

/-- ★ **The slice category C/U** — objects are types-in-context (`SliceObject`s), morphisms are the
commuting triangles, all three category laws inherited from the base via `SliceMorphism.ext`. -/
def sliceCategory (category : RawCategory.{u, v}) (universeObject : category.Object) :
    RawCategory.{max u v, v} where
  Object := SliceObject category universeObject
  Morphism := fun source target => SliceMorphism category source target
  identity := fun sliceObj => sliceObj.identityMorphism
  compose := fun morphismF morphismG => morphismF.compose morphismG
  composeAssoc := fun morphismF morphismG morphismH =>
    SliceMorphism.ext _ _
      (category.composeAssoc morphismF.underlying morphismG.underlying morphismH.underlying)
  identityLeft := fun morphismF => SliceMorphism.ext _ _ (category.identityLeft morphismF.underlying)
  identityRight := fun morphismF => SliceMorphism.ext _ _ (category.identityRight morphismF.underlying)

/-! ## The universal family (the generic display) -/

/-- The projection family `s ↦ s.domain` on C/U (a slice morphism acts as its underlying map). -/
def sliceProjectionFamily (category : RawCategory.{u, v}) (universeObject : category.Object) :
    SliceFamily category (universeObject := universeObject) where
  objectAt := fun sliceObj => sliceObj.domain
  mapMorphism := fun sliceMorphism => sliceMorphism.underlying

/-- The constant-universe family `s ↦ U` on C/U (every slice morphism acts as the identity of U). -/
def universeConstantFamily (category : RawCategory.{u, v}) (universeObject : category.Object) :
    SliceFamily category (universeObject := universeObject) where
  objectAt := fun _ => universeObject
  mapMorphism := fun _ => category.identity universeObject

/-- ★ **The universal family / generic display** — the canonical natural transformation from the
projection family to the constant-universe family whose component at a type-in-context is that
context's own projection to the universe.  Its naturality square IS the slice triangle's commute
condition: this is the categorical "generic type" the Uemura bijection classifies against. -/
def genericDisplayNatTrans (category : RawCategory.{u, v}) (universeObject : category.Object) :
    SliceNatTrans category
      (sliceProjectionFamily category universeObject)
      (universeConstantFamily category universeObject) where
  component := fun sliceObj => sliceObj.projection
  naturality := fun _sliceA _sliceB sliceMorphism => by
    dsimp only [sliceProjectionFamily, universeConstantFamily]
    rw [category.identityRight]
    exact sliceMorphism.commutes

/-! ## Wired over the FX context axis -/

/-- The slice category over the FX context axis's substitution category, at an arbitrary scope as the
universe object — the context-side home of types-in-context for the FX kernel. -/
def fxSubstSliceCategory (universeScope : Nat) : RawCategory.{0, 0} :=
  sliceCategory fxBaseSubstCategory universeScope

/-- The generic display over the FX context axis. -/
def fxSubstGenericDisplay (universeScope : Nat) :
    SliceNatTrans fxBaseSubstCategory
      (sliceProjectionFamily fxBaseSubstCategory universeScope)
      (universeConstantFamily fxBaseSubstCategory universeScope) :=
  genericDisplayNatTrans fxBaseSubstCategory universeScope

/-- The FX slice category's objects are the types-in-context over the substitution category. -/
theorem fxSubstSliceCategory_object (universeScope : Nat) :
    (fxSubstSliceCategory universeScope).Object =
      SliceObject fxBaseSubstCategory universeScope := rfl

/-! ## The slice families are genuine functors

`SliceFamily` ships no laws, so on its own a "family" is just an object-map plus a morphism-map.
`IsFunctorial` supplies the missing identity/composition preservation, and both families above satisfy
it — paying for the word "functorial". -/

/-- Functoriality of a `SliceFamily`: it preserves the slice category's identities and composites. -/
structure SliceFamily.IsFunctorial {category : RawCategory.{u, v}}
    {universeObject : category.Object}
    (family : SliceFamily category (universeObject := universeObject)) : Prop where
  /-- The family sends an identity slice morphism to the identity base morphism. -/
  preservesIdentity : ∀ (sliceObj : SliceObject category universeObject),
    family.mapMorphism sliceObj.identityMorphism = category.identity (family.objectAt sliceObj)
  /-- The family sends a slice composite to the composite of the images. -/
  preservesComposition : ∀ {sliceA sliceB sliceC : SliceObject category universeObject}
    (sliceF : SliceMorphism category sliceA sliceB)
    (sliceG : SliceMorphism category sliceB sliceC),
    family.mapMorphism (sliceF.compose sliceG)
      = category.compose (family.mapMorphism sliceF) (family.mapMorphism sliceG)

/-- The projection family `s ↦ s.domain` is a genuine functor: it acts as each slice morphism's own
underlying base morphism, so identity/composition preservation are definitional. -/
theorem sliceProjectionFamily_isFunctorial (category : RawCategory.{u, v})
    (universeObject : category.Object) :
    (sliceProjectionFamily category universeObject).IsFunctorial where
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-- The constant-universe family `s ↦ U` is a genuine functor: it sends everything to `id U`, and
`id U ∘ id U = id U` discharges composition preservation. -/
theorem universeConstantFamily_isFunctorial (category : RawCategory.{u, v})
    (universeObject : category.Object) :
    (universeConstantFamily category universeObject).IsFunctorial where
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ =>
    (category.identityLeft (category.identity universeObject)).symm

/-! ## The slice category is the category of elements of `U` (Grothendieck)

A type-in-context is exactly an ELEMENT of the universe — a context paired with a classifying map into
`U`.  `sliceToElement` / `elementToSlice` are mutually inverse, so `SliceObject ≃ UniverseElement` is
the (definitional) Grothendieck iso `C/U ≅ ∫ U`. -/

/-- An element of the universe object: a context together with a classifying map into `U`. -/
@[reducible] def UniverseElement (category : RawCategory.{u, v})
    (universeObject : category.Object) : Type (max u v) :=
  Σ domainObject : category.Object, category.Morphism domainObject universeObject

/-- Read a type-in-context off as the universe element it classifies. -/
def sliceToElement {category : RawCategory.{u, v}} {universeObject : category.Object}
    (sliceObj : SliceObject category universeObject) : UniverseElement category universeObject :=
  ⟨sliceObj.domain, sliceObj.projection⟩

/-- Build the type-in-context that classifies a given universe element. -/
def elementToSlice {category : RawCategory.{u, v}} {universeObject : category.Object}
    (element : UniverseElement category universeObject) : SliceObject category universeObject :=
  ⟨element.1, element.2⟩

/-- Round-trip: every type-in-context is recovered from its universe element. -/
theorem elementToSlice_sliceToElement {category : RawCategory.{u, v}}
    {universeObject : category.Object} (sliceObj : SliceObject category universeObject) :
    elementToSlice (sliceToElement sliceObj) = sliceObj := rfl

/-- Round-trip: every universe element is recovered from its type-in-context. -/
theorem sliceToElement_elementToSlice {category : RawCategory.{u, v}}
    {universeObject : category.Object} (element : UniverseElement category universeObject) :
    sliceToElement (elementToSlice element) = element := rfl

/-! ## The generic display is genuinely generic — its proved universal property

The generic display CLASSIFIES universe elements: its component at the type-in-context built from an
element returns that element's classifying map (surjectivity), and the classifying type-in-context is
recovered from the component (injectivity, via the bijection above).  It is moreover stable under
reindexing.  This earns the word "generic" by proof; the pullback / representable-maps refinement is
deferred to `fib-1`. -/

/-- The generic display reads an element's classifying map back off: surjectivity of classification. -/
theorem genericDisplay_component_elementToSlice {category : RawCategory.{u, v}}
    (universeObject : category.Object) (element : UniverseElement category universeObject) :
    (genericDisplayNatTrans category universeObject).component (elementToSlice element)
      = element.2 := rfl

/-- The generic display's component IS the classifying map of the universe element a type-in-context
denotes: classification and the element-of-`U` data coincide. -/
theorem genericDisplay_component_eq_classifier {category : RawCategory.{u, v}}
    (universeObject : category.Object) (sliceObj : SliceObject category universeObject) :
    (genericDisplayNatTrans category universeObject).component sliceObj
      = (sliceToElement sliceObj).2 := rfl

/-- Every type-in-context is reconstructed from its generic-display component: injectivity of
classification (the classifying slice object is recovered from the classified map). -/
theorem genericDisplay_classifier_reconstructs {category : RawCategory.{u, v}}
    (universeObject : category.Object) (sliceObj : SliceObject category universeObject) :
    elementToSlice ⟨sliceObj.domain,
        (genericDisplayNatTrans category universeObject).component sliceObj⟩ = sliceObj := rfl

/-- HONEST DEGENERACY: every map into the universe arises as a generic-display component, so
"representable into `U`" carves out the whole hom-set here and adds no information.  The non-trivial
content is the bijection + reindex-stability; the genuine representable-maps refinement (where this
stops being everything) is the RMC pullback class, deferred to `fib-1`. -/
theorem genericDisplay_component_surjective {category : RawCategory.{u, v}}
    (universeObject : category.Object) {domainObject : category.Object}
    (classifyingMap : category.Morphism domainObject universeObject) :
    (genericDisplayNatTrans category universeObject).component
        (elementToSlice ⟨domainObject, classifyingMap⟩) = classifyingMap := rfl

/-- Reindex a type-in-context along a base morphism into its context: pull the classifying map back. -/
def SliceObject.reindex {category : RawCategory.{u, v}} {universeObject : category.Object}
    (sliceObj : SliceObject category universeObject) {newDomain : category.Object}
    (reindexMap : category.Morphism newDomain sliceObj.domain) :
    SliceObject category universeObject :=
  ⟨newDomain, category.compose reindexMap sliceObj.projection⟩

/-- The generic display is STABLE under reindexing: the classifying map of a reindexed
type-in-context is the reindex of the classifying map — naturality of classification under
substitution. -/
theorem genericDisplay_component_reindex {category : RawCategory.{u, v}}
    (universeObject : category.Object) (sliceObj : SliceObject category universeObject)
    {newDomain : category.Object} (reindexMap : category.Morphism newDomain sliceObj.domain) :
    (genericDisplayNatTrans category universeObject).component (sliceObj.reindex reindexMap)
      = category.compose reindexMap
          ((genericDisplayNatTrans category universeObject).component sliceObj) := rfl

/-! ## Vertical structure on slice natural transformations

Slice natural transformations carry an identity and a vertical composition, each with its naturality
square proved.  The unit laws hold componentwise (the global functor-category equation would need
`funext`, which would breach the zero-axiom discipline, so it is stated pointwise). -/

/-- The identity natural transformation on a slice family. -/
def SliceNatTrans.idTrans {category : RawCategory.{u, v}} {universeObject : category.Object}
    (family : SliceFamily category (universeObject := universeObject)) :
    SliceNatTrans category family family where
  component := fun sliceObj => category.identity (family.objectAt sliceObj)
  naturality := fun sliceA sliceB sliceMorphism => by
    show category.compose (family.mapMorphism sliceMorphism)
        (category.identity (family.objectAt sliceB))
      = category.compose (category.identity (family.objectAt sliceA))
        (family.mapMorphism sliceMorphism)
    rw [category.identityRight, category.identityLeft]

/-- Vertical composition of slice natural transformations. -/
def SliceNatTrans.vcomp {category : RawCategory.{u, v}} {universeObject : category.Object}
    {familyF familyG familyH : SliceFamily category (universeObject := universeObject)}
    (alpha : SliceNatTrans category familyF familyG)
    (beta : SliceNatTrans category familyG familyH) :
    SliceNatTrans category familyF familyH where
  component := fun sliceObj =>
    category.compose (alpha.component sliceObj) (beta.component sliceObj)
  naturality := fun sliceA sliceB sliceMorphism => by
    show category.compose (familyF.mapMorphism sliceMorphism)
        (category.compose (alpha.component sliceB) (beta.component sliceB))
      = category.compose
        (category.compose (alpha.component sliceA) (beta.component sliceA))
        (familyH.mapMorphism sliceMorphism)
    rw [← category.composeAssoc, alpha.naturality sliceA sliceB sliceMorphism,
        category.composeAssoc, beta.naturality sliceA sliceB sliceMorphism,
        ← category.composeAssoc]

/-- The identity nat-trans acts as the identity component. -/
theorem SliceNatTrans.idTrans_component {category : RawCategory.{u, v}}
    {universeObject : category.Object}
    (family : SliceFamily category (universeObject := universeObject))
    (sliceObj : SliceObject category universeObject) :
    (SliceNatTrans.idTrans family).component sliceObj
      = category.identity (family.objectAt sliceObj) := rfl

/-- Vertical composition acts componentwise. -/
theorem SliceNatTrans.vcomp_component {category : RawCategory.{u, v}}
    {universeObject : category.Object}
    {familyF familyG familyH : SliceFamily category (universeObject := universeObject)}
    (alpha : SliceNatTrans category familyF familyG)
    (beta : SliceNatTrans category familyG familyH)
    (sliceObj : SliceObject category universeObject) :
    (alpha.vcomp beta).component sliceObj
      = category.compose (alpha.component sliceObj) (beta.component sliceObj) := rfl

/-- Left unit law, componentwise. -/
theorem SliceNatTrans.idTrans_vcomp_component {category : RawCategory.{u, v}}
    {universeObject : category.Object}
    {familyF familyG : SliceFamily category (universeObject := universeObject)}
    (alpha : SliceNatTrans category familyF familyG)
    (sliceObj : SliceObject category universeObject) :
    ((SliceNatTrans.idTrans familyF).vcomp alpha).component sliceObj
      = alpha.component sliceObj :=
  category.identityLeft (alpha.component sliceObj)

/-- Right unit law, componentwise. -/
theorem SliceNatTrans.vcomp_idTrans_component {category : RawCategory.{u, v}}
    {universeObject : category.Object}
    {familyF familyG : SliceFamily category (universeObject := universeObject)}
    (alpha : SliceNatTrans category familyF familyG)
    (sliceObj : SliceObject category universeObject) :
    (alpha.vcomp (SliceNatTrans.idTrans familyG)).component sliceObj
      = alpha.component sliceObj :=
  category.identityRight (alpha.component sliceObj)

end FX1Poly.Axis
