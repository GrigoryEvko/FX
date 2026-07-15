import FX1Poly.Axis.Context.ContextCovariantFibration

/-! # context-37 — the FUNCTORIAL directed Grothendieck classification: an iso of categories

`context-37` (★, on the fib-* arc, →fib-1/4) upgrades `context-35`'s OBJECT-level directed Grothendieck
classification (covariant fibrations ≃ functors into the directed universe — a bijection on objects) to a
FUNCTORIAL one: `straighten` / `unstraighten` act on MORPHISMS too, preserving identity and composition, and
assemble into mutually-inverse FUNCTORS between two genuine categories — a STRICT ISOMORPHISM OF CATEGORIES.

  * On one side, the category `CovFib(C)` of covariant fibrations over `C` and their MORPHISMS (fibered maps
    commuting with the cocartesian lifts).
  * On the other, the FUNCTOR CATEGORY `[C, U]` of functors `C ⟶ U` into the directed universe and their
    NATURAL TRANSFORMATIONS.

The directed Grothendieck construction is the functor `CovFib(C) ⟶ [C, U]` (`straightenFunctor`), with inverse
`[C, U] ⟶ CovFib(C)` (`unstraightenFunctor`); the two composites are the identity functors — BY `rfl`.  That is
the functorial classification: "the (op)Grothendieck construction is an equivalence — here an isomorphism — of
categories", at the strict (1-categorical) level that stays zero-axiom.

## Why this is funext-free (the `context-35` mechanism, one level up)

A fibration morphism `F → G` is a fibrewise family `component_a : F a → G a` commuting with the cocartesian
lift; that is, FIELD FOR FIELD, a natural transformation between the straightened functors `straighten F ⟹
straighten G`.  So `straighten` / `unstraighten` on morphisms are repackagings that round-trip BY `rfl`
(structure eta), exactly as on objects (`context-35`).  And — the `context-25` presheaf-category mechanism
(`PresheafModel.lean`) — BOTH `[C, U]` and `CovFib(C)` are genuine `RawCategory`s whose three laws hold
DEFINITIONALLY: their morphism composition is FUNCTION composition (β/η on components) and their naturality /
lift-commutation witnesses are `Prop`s (proof-irrelevant).  Each law is `rfl`; no `funext`, no `Quot.sound`.

Likewise the two functor laws of `straightenFunctor` / `unstraightenFunctor`, and the two `…_id` composite
identities exhibiting the isomorphism, are all `rfl`.

## What lands here (all zero-axiom)

  * **`DirectedUniverseNatTrans`** + **`directedUniverseFunctorCategory`** — natural transformations of functors
    `C ⟶ U` (component family + naturality), and the functor category `[C, U]` as a `RawCategory` (vertical
    composition; laws `rfl`).
  * **`CovariantFibrationMorphism`** + **`covariantFibrationCategory`** — morphisms of covariant fibrations
    (fibrewise family commuting with cocartesian lifts), and the category `CovFib(C)` as a `RawCategory`.
  * **`straightenMorphism` / `unstraightenMorphism`** — the Grothendieck construction on MORPHISMS, with the two
    `rfl` round-trips (`unstraightenMorphism_straightenMorphism`, `straightenMorphism_unstraightenMorphism`).
  * **`straightenFunctor` / `unstraightenFunctor`** — the construction as FUNCTORS `CovFib(C) ⇄ [C, U]`.
  * ★ **`straightenFunctor_unstraightenFunctor_id` / `unstraightenFunctor_straightenFunctor_id`** — the two
    composites are the identity functors, BY `rfl`: a STRICT ISOMORPHISM OF CATEGORIES.  The functorial directed
    Grothendieck classification.

## What is deferred (the honest wall)

  * The FULL ∞-cosmos / homotopy-coherent straightening–unstraightening as an EQUIVALENCE OF `(∞,1)`-CATEGORIES
    (Riehl–Verity; Riehl–Shulman) — with coherent naturality up to higher cells — is NOT shipped: it needs
    `funext` / `Quot.sound`, the `×type` / type-axis wall `gen_universeD` defers
    (`fxFunctorialGrothendieck_hasFullInfinityCosmosEquivalence = false`).
  * The classification + functoriality here are the SELF-CONTAINED Axis analog, NOT a Core `StepOverTable` iota
    row (`fxFunctorialGrothendieck_isOverCoreIotaTable = false`).

Imports only `ContextCovariantFibration` (its `context-35` sibling — the `CovariantFibration` / `straighten` /
directed-universe substrate).  A Axis design-lock must not import up into `Core/` / `Typed/`.  Zero external
dependencies — raw Lean 4 + Init only.

Reference: Riehl & Verity, "Elements of ∞-Category Theory", CUP 2022; Riehl & Shulman, "A type theory for
synthetic ∞-categories", HHA 2017; the `context-25` presheaf-category mechanism (`PresheafModel.lean`); the
`context-35` object-level classification (`ContextCovariantFibration.lean`).
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## Natural transformations of functors into the directed universe, and the functor category `[C, U]` -/

/-- A **natural transformation** `source ⟹ target` of functors `C ⟶ U` into the directed universe: a fibrewise
component family that commutes with the functors' forward action (naturality).  Components are FORWARD functions
(`decode (source a) → decode (target a)`); naturality is a pointwise `Prop`, so a transformation is determined
(for equality) by its components. -/
structure DirectedUniverseNatTrans {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (source target : DirectedUniverseFunctor base univ) where
  /-- The component at each base object — a forward function between the fibres. -/
  component : (baseObject : base.Object) →
    univ.decode (source.mapObject baseObject) → univ.decode (target.mapObject baseObject)
  /-- Naturality: the components commute with the functors' forward action. -/
  naturality : ∀ {baseSource baseTarget : base.Object} (baseMorphism : base.Morphism baseSource baseTarget)
    (fiberPoint : univ.decode (source.mapObject baseSource)),
    target.mapMorphism baseMorphism (component baseSource fiberPoint)
      = component baseTarget (source.mapMorphism baseMorphism fiberPoint)

/-- The identity natural transformation `source ⟹ source` — identity components, naturality by `rfl`. -/
def DirectedUniverseNatTrans.identityTrans {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (functor : DirectedUniverseFunctor base univ) : DirectedUniverseNatTrans functor functor where
  component := fun _ fiberPoint => fiberPoint
  naturality := fun _ _ => rfl

/-- **Vertical composition** of natural transformations (apply `first`, then `second`); naturality chains the
two squares. -/
def DirectedUniverseNatTrans.vcomp {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {sourceFun midFun targetFun : DirectedUniverseFunctor base univ}
    (first : DirectedUniverseNatTrans sourceFun midFun)
    (second : DirectedUniverseNatTrans midFun targetFun) :
    DirectedUniverseNatTrans sourceFun targetFun where
  component := fun baseObject fiberPoint =>
    second.component baseObject (first.component baseObject fiberPoint)
  naturality := fun baseMorphism fiberPoint =>
    (second.naturality baseMorphism (first.component _ fiberPoint)).trans
      (congrArg (second.component _) (first.naturality baseMorphism fiberPoint))

/-- ★ **The functor category `[C, U]`** as a genuine `RawCategory` — objects are functors `C ⟶ U` into the
directed universe, morphisms are natural transformations, composition is vertical.  All three laws hold
DEFINITIONALLY (β/η on components + proof irrelevance of naturality) — each `rfl`, no `funext` — exactly as the
`context-25` presheaf category. -/
def directedUniverseFunctorCategory (base : RawCategory.{0, 0}) (univ : DirectedUniverseData) : RawCategory where
  Object := DirectedUniverseFunctor base univ
  Morphism := fun source target => DirectedUniverseNatTrans source target
  identity := fun functor => DirectedUniverseNatTrans.identityTrans functor
  compose := fun first second => DirectedUniverseNatTrans.vcomp first second
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-! ## Morphisms of covariant fibrations, and the category `CovFib(C)` -/

/-- A **morphism of covariant fibrations** `source → G`: a fibrewise component family commuting with the
COCARTESIAN LIFTS (a fibered / cartesian-functor map over the base).  This is — field for field — a natural
transformation between the straightened functors (`straightenMorphism`); the commutation is a pointwise `Prop`,
so a morphism is determined (for equality) by its components. -/
structure CovariantFibrationMorphism {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (source target : CovariantFibration base univ) where
  /-- The component at each base object — a forward map between the fibres. -/
  component : (baseObject : base.Object) →
    univ.decode (source.fiber baseObject) → univ.decode (target.fiber baseObject)
  /-- The components COMMUTE WITH THE COCARTESIAN LIFTS — fibered-ness over the base. -/
  commutesWithLift : ∀ {baseSource baseTarget : base.Object}
    (baseMorphism : base.Morphism baseSource baseTarget)
    (fiberPoint : univ.decode (source.fiber baseSource)),
    target.cocartesianLift baseMorphism (component baseSource fiberPoint)
      = component baseTarget (source.cocartesianLift baseMorphism fiberPoint)

/-- The identity fibration morphism — identity components, commutation by `rfl`. -/
def CovariantFibrationMorphism.identityMorphism {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) : CovariantFibrationMorphism fibration fibration where
  component := fun _ fiberPoint => fiberPoint
  commutesWithLift := fun _ _ => rfl

/-- Composition of fibration morphisms (apply `first`, then `second`); the commutation chains the two squares. -/
def CovariantFibrationMorphism.composeMorphism {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {sourceFibration midFibration targetFibration : CovariantFibration base univ}
    (first : CovariantFibrationMorphism sourceFibration midFibration)
    (second : CovariantFibrationMorphism midFibration targetFibration) :
    CovariantFibrationMorphism sourceFibration targetFibration where
  component := fun baseObject fiberPoint =>
    second.component baseObject (first.component baseObject fiberPoint)
  commutesWithLift := fun baseMorphism fiberPoint =>
    (second.commutesWithLift baseMorphism (first.component _ fiberPoint)).trans
      (congrArg (second.component _) (first.commutesWithLift baseMorphism fiberPoint))

/-- ★ **The category `CovFib(C)`** of covariant fibrations over `C` as a genuine `RawCategory` — objects are
covariant fibrations, morphisms are fibration morphisms.  All three laws hold DEFINITIONALLY (β/η on components +
proof irrelevance of the lift-commutation) — each `rfl`, no `funext`. -/
def covariantFibrationCategory (base : RawCategory.{0, 0}) (univ : DirectedUniverseData) : RawCategory where
  Object := CovariantFibration base univ
  Morphism := fun source target => CovariantFibrationMorphism source target
  identity := fun fibration => CovariantFibrationMorphism.identityMorphism fibration
  compose := fun first second => CovariantFibrationMorphism.composeMorphism first second
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-! ## Straightening / unstraightening on MORPHISMS — and the `rfl` round-trips -/

/-- **Straighten a fibration morphism** into a natural transformation of the straightened functors.  The
fibration morphism's components are the transformation's components; the lift-commutation is the naturality.  The
Grothendieck construction on morphisms. -/
def CovariantFibration.straightenMorphism {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {source target : CovariantFibration base univ} (morphism : CovariantFibrationMorphism source target) :
    DirectedUniverseNatTrans source.straighten target.straighten where
  component := morphism.component
  naturality := morphism.commutesWithLift

/-- **Unstraighten a natural transformation** into a morphism of the unstraightened fibrations.  The other half
of the Grothendieck construction on morphisms. -/
def CovariantFibration.unstraightenMorphism {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {sourceFun targetFun : DirectedUniverseFunctor base univ}
    (transformation : DirectedUniverseNatTrans sourceFun targetFun) :
    CovariantFibrationMorphism
      (CovariantFibration.unstraighten sourceFun) (CovariantFibration.unstraighten targetFun) where
  component := transformation.component
  commutesWithLift := transformation.naturality

/-- ★ **Morphism classification (one round-trip).**  Unstraightening a straightened fibration morphism recovers
it — BY `rfl` (structure eta; the object round-trips are definitional, so the hom-sets align). -/
theorem CovariantFibration.unstraightenMorphism_straightenMorphism {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} {source target : CovariantFibration base univ}
    (morphism : CovariantFibrationMorphism source target) :
    CovariantFibration.unstraightenMorphism (CovariantFibration.straightenMorphism morphism) = morphism :=
  rfl

/-- ★ **Morphism classification (other round-trip).**  Straightening an unstraightened natural transformation
recovers it — BY `rfl`. -/
theorem CovariantFibration.straightenMorphism_unstraightenMorphism {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} {sourceFun targetFun : DirectedUniverseFunctor base univ}
    (transformation : DirectedUniverseNatTrans sourceFun targetFun) :
    CovariantFibration.straightenMorphism (CovariantFibration.unstraightenMorphism transformation)
      = transformation :=
  rfl

/-! ## The functorial classification — `straighten` / `unstraighten` as mutually-inverse functors -/

/-- **The directed Grothendieck construction as a functor** `CovFib(C) ⟶ [C, U]`: straightening on objects and
morphisms.  Both functor laws are `rfl` (straightening preserves identity and composition componentwise). -/
def CovariantFibration.straightenFunctor (base : RawCategory.{0, 0}) (univ : DirectedUniverseData) :
    RawFunctor (covariantFibrationCategory base univ) (directedUniverseFunctorCategory base univ) where
  mapObject := fun fibration => fibration.straighten
  mapMorphism := fun morphism => CovariantFibration.straightenMorphism morphism
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-- **The inverse functor** `[C, U] ⟶ CovFib(C)`: unstraightening on objects and morphisms.  Both functor laws
are `rfl`. -/
def CovariantFibration.unstraightenFunctor (base : RawCategory.{0, 0}) (univ : DirectedUniverseData) :
    RawFunctor (directedUniverseFunctorCategory base univ) (covariantFibrationCategory base univ) where
  mapObject := fun functor => CovariantFibration.unstraighten functor
  mapMorphism := fun transformation => CovariantFibration.unstraightenMorphism transformation
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-- ★ **The functorial Grothendieck classification (one composite).**  Straighten-then-unstraighten is the
IDENTITY functor on `CovFib(C)` — BY `rfl`.  Half of the strict isomorphism of categories. -/
theorem CovariantFibration.straightenFunctor_unstraightenFunctor_id (base : RawCategory.{0, 0})
    (univ : DirectedUniverseData) :
    (CovariantFibration.straightenFunctor base univ).compose
        (CovariantFibration.unstraightenFunctor base univ)
      = RawFunctor.identity (covariantFibrationCategory base univ) :=
  rfl

/-- ★ **The functorial Grothendieck classification (other composite).**  Unstraighten-then-straighten is the
IDENTITY functor on `[C, U]` — BY `rfl`.  Together with the previous, `straightenFunctor` / `unstraightenFunctor`
are mutually inverse: a STRICT ISOMORPHISM OF CATEGORIES `CovFib(C) ≅ [C, U]`, the functorial directed
Grothendieck classification. -/
theorem CovariantFibration.unstraightenFunctor_straightenFunctor_id (base : RawCategory.{0, 0})
    (univ : DirectedUniverseData) :
    (CovariantFibration.unstraightenFunctor base univ).compose
        (CovariantFibration.straightenFunctor base univ)
      = RawFunctor.identity (directedUniverseFunctorCategory base univ) :=
  rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The FUNCTORIAL directed Grothendieck classification — `straighten` / `unstraighten` as
mutually-inverse FUNCTORS `CovFib(C) ⇄ [C, U]`, a STRICT ISOMORPHISM OF CATEGORIES (the two composites are the
identity functors by `rfl`) — is shipped.  `= true`. -/
def fxFunctorialGrothendieck_hasStrictCategoryIsomorphism : Bool := true

/-- **Honesty marker.**  The Grothendieck construction acts FUNCTORIALLY on MORPHISMS: fibration morphisms ≃
natural transformations, with `straightenMorphism` / `unstraightenMorphism` round-tripping by `rfl` and the two
functor laws holding strictly.  `= true`. -/
def fxFunctorialGrothendieck_hasFunctorialClassification : Bool := true

/-- **Honesty marker.**  The FULL ∞-cosmos / homotopy-coherent straightening–unstraightening as an EQUIVALENCE
of `(∞,1)`-CATEGORIES (Riehl–Verity; Riehl–Shulman), with coherent naturality up to higher cells, is NOT
shipped: it needs `funext` / `Quot.sound`, the `×type` / type-axis wall `gen_universeD` defers.  `= false`. -/
def fxFunctorialGrothendieck_hasFullInfinityCosmosEquivalence : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis analog of a Core table-native functorial-Grothendieck
row; a Axis design-lock cannot import the Core engine, so the categories, functors, and isomorphism are
re-shipped here as strict (1-categorical) constructions.  Gluing the Axis and Core forms is cross-axis `×type`.
`= false`. -/
def fxFunctorialGrothendieck_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: vertical composition with the identity transformation on the left is the identity — `[C, U]`'s
`identityLeft`, decided by `rfl`. -/
theorem directedUniverseFunctorCategory_identityLeft_smoke {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} {source target : DirectedUniverseFunctor base univ}
    (transformation : DirectedUniverseNatTrans source target) :
    DirectedUniverseNatTrans.vcomp (DirectedUniverseNatTrans.identityTrans source) transformation
      = transformation :=
  rfl

/-- Smoke: straightening the identity fibration morphism is the identity natural transformation — functoriality
of `straightenFunctor` on identities, by `rfl`. -/
theorem straightenMorphism_identity_smoke {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) :
    CovariantFibration.straightenMorphism (CovariantFibrationMorphism.identityMorphism fibration)
      = DirectedUniverseNatTrans.identityTrans fibration.straighten :=
  rfl

end FX1Poly.Axis
