import FX1Poly.Polygraph.Category.RawCategory
import FX1Poly.Tier0.Context.SimplicialModel
import FX1Poly.Tier0.Context.CubicalModel

/-! # context-25 — the general presheaf model (Hofmann–Streicher), context-side residue

`context-25` is the GENERAL PRESHEAF MODEL rung: for any small base category `C` (a "site"), the presheaf
category `[Cᵒᵖ, Set]` is a category-with-families with a universe à la Hofmann–Streicher (the universe of
small presheaves).  This is the AMBIENT semantics — the simplicial (`context-13`, presheaves on `Δ`), cubical
(`context-22`, presheaves on `□`) and the discrete/groupoid models are all INSTANCES, one per base.

## What is context-side here, and what is deferred

The category of CONTEXTS of the presheaf model over `C` is `[Cᵒᵖ, Set]` itself.  That category — GENERIC over
the small site — is pure base data; it is the CONTEXT-SIDE residue shipped here, in full and zero-axiom:

  * **`Presheaf`** — a presheaf on an arbitrary small site `C`: an object-indexed family of sets with a
    contravariant, functorial restriction.  **`presheafCategory`** — `[Cᵒᵖ, Set]` as a genuine `RawCategory`
    (morphisms are natural transformations).  As in `□`/`Δ`, the three category laws hold DEFINITIONALLY —
    β/η on the components + proof irrelevance of naturality — so each is `rfl`, no `funext`, AND (unlike the
    concrete rfl-sites) this holds for ANY site, because the laws are about the MORPHISM composition (which
    is function composition), independent of `C`'s own laws.
  * the representable **`representablePresheaf`** `よ(c) = Hom_C(−, c)` (its functor laws are `C`'s own
    `identityLeft` / `composeAssoc`), and the **Yoneda embedding** `C ⟶ [Cᵒᵖ, Set]`
    (`presheafYonedaObject` / `presheafYonedaMorphism`).
  * **`terminalPresheaf`** — a concrete presheaf object (non-vacuity) with the unique map into it.
  * the SUBSUMPTION witnesses: `fxSimplicialPresheafCategory := presheafCategory simplexCategory` and
    `fxCubicalPresheafCategory := presheafCategory cubeCategory` — the general construction instantiated at
    the two sites `context-13` / `context-22` already shipped, exhibiting them as instances.

HONESTY (the funext boundary): Yoneda FUNCTORIALITY (`よ(id) = id`, `よ(g∘f) = よ(g)∘よ(f)`) is stated
POINTWISE (component-level), via `C`'s `identityRight` / `composeAssoc`.  As a MORPHISM equality it is
funext-blocked for a GENERIC site — the components are pointwise-equal only up to `C`'s propositional laws,
not definitionally — whereas at the concrete rfl-sites of `context-13` / `context-22` it held on the nose.

DEFERRED (the `×type` / full-model core, recorded by `= false` markers):
  * the HOFMANN–STREICHER UNIVERSE — the universe of small presheaves + its size/coherence bookkeeping
    (`blockedBy type-15`) — `hasHofmannStreicherUniverse = false`;
  * the PRESHEAF TYPE STRUCTURE — `Id`/`Π`/`Σ` in presheaves, the presheaf CwF — `hasPresheafTypeStructure
    = false`;
  * the LOCAL CARTESIAN CLOSURE of `[Cᵒᵖ, Set]` (presheaf exponentials / dependent products) —
    `hasPresheafLocalCartesianClosure = false`.

Reference: Hofmann & Streicher, "Lifting Grothendieck universes" (unpublished); Awodey, "Natural models of
homotopy type theory" (2018).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## Presheaves on a small site -/

/-- A **presheaf** on a small site `C` — a presheaf `Cᵒᵖ ⟶ Set`: a family of sets indexed by objects, with a
CONTRAVARIANT restriction that is functorial.  The functor laws are POINTWISE (equalities in a fibre), so
funext-free.  The site is taken at `RawCategory.{0,0}` (a small category — objects and homs in `Type`). -/
structure Presheaf (site : RawCategory.{0, 0}) where
  /-- The fibre over each object (the "`c`-elements"). -/
  obj : site.Object → Type
  /-- Contravariant restriction along a site arrow. -/
  restrict : {source target : site.Object} → site.Morphism source target → obj target → obj source
  /-- Restriction along the identity is the identity (pointwise). -/
  restrictIdentity : ∀ (object : site.Object) (element : obj object),
    restrict (site.identity object) element = element
  /-- Restriction is contravariantly functorial (pointwise). -/
  restrictCompose : ∀ {objectA objectB objectC : site.Object}
    (first : site.Morphism objectA objectB) (second : site.Morphism objectB objectC)
    (element : obj objectC),
    restrict (site.compose first second) element = restrict first (restrict second element)

/-- A **morphism of presheaves** — a natural transformation: a fibrewise family commuting with restriction.
Naturality is a pointwise `Prop`, so a morphism is determined (for equality) by its components. -/
structure PresheafMorphism {site : RawCategory.{0, 0}} (source target : Presheaf site) where
  /-- The component at each object. -/
  component : (object : site.Object) → source.obj object → target.obj object
  /-- Naturality: components commute with restriction. -/
  naturality : ∀ {objectA objectB : site.Object} (reindex : site.Morphism objectA objectB)
    (element : source.obj objectB),
    target.restrict reindex (component objectB element)
      = component objectA (source.restrict reindex element)

/-- The identity presheaf morphism. -/
def PresheafMorphism.identityMorphism {site : RawCategory.{0, 0}} (presheaf : Presheaf site) :
    PresheafMorphism presheaf presheaf where
  component := fun _ element => element
  naturality := fun _ _ => rfl

/-- Composition of presheaf morphisms (apply `first`, then `second`); naturality chains the two squares. -/
def PresheafMorphism.composeMorphism {site : RawCategory.{0, 0}}
    {sourceSheaf midSheaf targetSheaf : Presheaf site}
    (first : PresheafMorphism sourceSheaf midSheaf) (second : PresheafMorphism midSheaf targetSheaf) :
    PresheafMorphism sourceSheaf targetSheaf where
  component := fun object element => second.component object (first.component object element)
  naturality := fun reindex element =>
    (second.naturality reindex (first.component _ element)).trans
      (congrArg (second.component _) (first.naturality reindex element))

/-- ★ **The presheaf category `[Cᵒᵖ, Set]`** as a genuine `RawCategory` — the category of CONTEXTS of the
presheaf model over `C`.  All three laws hold DEFINITIONALLY for ANY site (β/η on components + proof
irrelevance of naturality) — each `rfl`, no `funext` — because they concern the morphism composition, not
`C`'s own laws. -/
def presheafCategory (site : RawCategory.{0, 0}) : RawCategory where
  Object := Presheaf site
  Morphism := fun source target => PresheafMorphism source target
  identity := fun presheaf => PresheafMorphism.identityMorphism presheaf
  compose := fun first second => PresheafMorphism.composeMorphism first second
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-! ## The representable presheaf + the Yoneda embedding -/

/-- The representable presheaf `よ(anchor) = Hom_C(−, anchor)` — its restriction is precomposition; the two
functor laws ARE the site's `identityLeft` / `composeAssoc`. -/
def representablePresheaf (site : RawCategory.{0, 0}) (anchor : site.Object) : Presheaf site where
  obj := fun object => site.Morphism object anchor
  restrict := fun reindex arrow => site.compose reindex arrow
  restrictIdentity := fun _ arrow => site.identityLeft arrow
  restrictCompose := fun first second arrow => site.composeAssoc first second arrow

/-- The Yoneda embedding on objects: `c ↦ よ(c)`. -/
def presheafYonedaObject (site : RawCategory.{0, 0}) (anchor : site.Object) : Presheaf site :=
  representablePresheaf site anchor

/-- ★ The Yoneda embedding on morphisms: a site arrow `anchorSource ⟶ anchorTarget` induces the natural
transformation `よ(anchorSource) ⟶ よ(anchorTarget)` by POSTCOMPOSITION.  Naturality is the site's
`composeAssoc`. -/
def presheafYonedaMorphism {site : RawCategory.{0, 0}} {anchorSource anchorTarget : site.Object}
    (arrow : site.Morphism anchorSource anchorTarget) :
    PresheafMorphism (representablePresheaf site anchorSource) (representablePresheaf site anchorTarget) where
  component := fun _ element => site.compose element arrow
  naturality := fun reindex element => (site.composeAssoc reindex element arrow).symm

/-- ★ Yoneda preserves identities, POINTWISE: `よ(id)` acts as the identity on components (`element ∘ id =
element`, the site's `identityRight`).  As a morphism EQUALITY this is funext-blocked for a generic site (the
components agree only up to `C`'s propositional law). -/
theorem presheafYonedaMorphism_identity_component (site : RawCategory.{0, 0}) (anchor : site.Object)
    (object : site.Object) (element : (representablePresheaf site anchor).obj object) :
    (presheafYonedaMorphism (site.identity anchor)).component object element = element :=
  site.identityRight element

/-- ★ Yoneda preserves composition, POINTWISE: `よ(f ; g)` acts as `よ(g) ∘ よ(f)` on components (the site's
`composeAssoc`).  Together with `presheafYonedaMorphism_identity_component` this is the (pointwise)
FUNCTORIALITY of the Yoneda embedding `C ⟶ [Cᵒᵖ, Set]`. -/
theorem presheafYonedaMorphism_compose_component (site : RawCategory.{0, 0})
    {anchorA anchorB anchorC : site.Object}
    (arrowOne : site.Morphism anchorA anchorB) (arrowTwo : site.Morphism anchorB anchorC)
    (object : site.Object) (element : (representablePresheaf site anchorA).obj object) :
    (presheafYonedaMorphism (site.compose arrowOne arrowTwo)).component object element
      = (presheafYonedaMorphism arrowTwo).component object
          ((presheafYonedaMorphism arrowOne).component object element) :=
  (site.composeAssoc element arrowOne arrowTwo).symm

/-! ## A concrete object + the unit -/

/-- The terminal presheaf (the unit context): a single element over every object — a concrete inhabitant of
`Presheaf`. -/
def terminalPresheaf (site : RawCategory.{0, 0}) : Presheaf site where
  obj := fun _ => Unit
  restrict := fun _ _ => ()
  restrictIdentity := fun _ _ => rfl
  restrictCompose := fun _ _ _ => rfl

/-- The unique presheaf morphism into the terminal presheaf (its universal property's existence half). -/
def terminalPresheafMorphism {site : RawCategory.{0, 0}} (presheaf : Presheaf site) :
    PresheafMorphism presheaf (terminalPresheaf site) where
  component := fun _ _ => ()
  naturality := fun _ _ => rfl

/-! ## Subsumption: the simplicial and cubical models are instances -/

/-- ★ Simplicial sets `= [Δᵒᵖ, Set]` — the general presheaf category at the `context-13` site `simplexCategory`. -/
def fxSimplicialPresheafCategory : RawCategory := presheafCategory simplexCategory

/-- ★ Cubical sets `= [□ᵒᵖ, Set]` — the general presheaf category at the `context-22` site `cubeCategory`. -/
def fxCubicalPresheafCategory : RawCategory := presheafCategory cubeCategory

/-! ## The model datum + honesty markers -/

/-- The context-side datum of the presheaf model over a small site: the site `C` and its presheaf category of
contexts.  The presheaf model is SITE-INDEXED — one model per base `C`. -/
structure PresheafModelData where
  /-- The base site `C`. -/
  site : RawCategory.{0, 0}
  /-- The base of contexts — the presheaf category `[Cᵒᵖ, Set]`. -/
  base : RawCategory.{1, 0}

/-- ★ The FX presheaf-model datum over a site: `[Cᵒᵖ, Set]` as the base.  Parameterized by `C` (the presheaf
model is site-indexed); the faithful, non-degenerate deliverable. -/
def fxPresheafModel (site : RawCategory.{0, 0}) : PresheafModelData where
  site := site
  base := presheafCategory site

/-- **Honesty marker.**  The HOFMANN–STREICHER UNIVERSE — the universe of small presheaves + its size /
coherence bookkeeping (`blockedBy type-15`) — is `×type`, deferred.  `= false`. -/
def fxPresheafModel_hasHofmannStreicherUniverse : Bool := false

/-- **Honesty marker.**  The PRESHEAF TYPE STRUCTURE — `Id`/`Π`/`Σ` in presheaves, the presheaf CwF — is
`×type`, deferred.  `= false`. -/
def fxPresheafModel_hasPresheafTypeStructure : Bool := false

/-- **Honesty marker.**  The LOCAL CARTESIAN CLOSURE of `[Cᵒᵖ, Set]` (presheaf exponentials / dependent
products) is `×type` / heavy, deferred.  `= false`. -/
def fxPresheafModel_hasPresheafLocalCartesianClosure : Bool := false

/-! ## Smoke -/

/-- Smoke: in the representable `よ(anchor)`, restriction along the identity is the identity. -/
theorem representablePresheaf_restrictIdentity_smoke (site : RawCategory.{0, 0}) (anchor object : site.Object)
    (element : (representablePresheaf site anchor).obj object) :
    (representablePresheaf site anchor).restrict (site.identity object) element = element :=
  (representablePresheaf site anchor).restrictIdentity object element

end FX1Poly.Tier0
