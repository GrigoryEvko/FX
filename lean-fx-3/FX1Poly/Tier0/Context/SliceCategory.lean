import FX1Poly.Tier0.Context.CwRExtension
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstCategory

/-! # The slice category C/U + the generic display (`context-2`, the context-side residue)

`context-2`'s headline — Uemura's bijection *type-formers ↔ representable natural transformations* —
is a CROSS-AXIS (`×type`) statement: it pairs the context category's slice/nat-trans structure with
the TYPE-former side, and over the shipped renaming RMC the formers are even forced degenerate
(`typeFormer_overRenamingVecRMC_resultIsIsomorphism`).  That bijection proper is the display-fibration
(`fib-1`) deliverable and is deferred there.

This file ships the strictly CONTEXT-SIDE substrate the bijection lives in — pure category theory over
the context category, no type-former content, Tier0-isolated:

  * `sliceCategory category U` — **the slice category C/U is a genuine `RawCategory`**: objects are
    the shipped `SliceObject`s (a context with a chosen type, i.e. a morphism into the universe object
    `U`), morphisms are the commuting triangles `SliceMorphism`, with identity, composition, and the
    three category laws all PROVED (inherited from the base category on the underlying morphisms via
    `SliceMorphism.ext`).
  * `genericDisplayNatTrans` — **the universal family**: the canonical natural transformation from the
    projection family (`s ↦ s.domain`) to the constant-universe family, whose component is each slice
    object's own projection.  Its NATURALITY is exactly the slice triangle's commute condition — the
    heart of the Uemura framework, on the context side.
  * `fxSubstSliceCategory` / `fxSubstGenericDisplay` — the above instantiated over the FX context
    axis's substitution category (`fxBaseSubstCategory`), at an arbitrary scope as the universe object.

The pairing of `genericDisplayNatTrans` with the TYPE-former records (`piFormerMap` / `sigmaFormerMap`)
to get the BIJECTION is the `×type` step — `fib-1`, deferred.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

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

end FX1Poly.Tier0
