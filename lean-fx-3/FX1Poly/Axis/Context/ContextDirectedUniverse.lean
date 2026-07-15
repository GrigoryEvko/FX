import FX1Poly.Axis.Context.ContextUnivalentUniverse

/-! # context-34 — the context category's universe object is a DIRECTED-UNIVALENT wild category

`context-34` (★) is the DIRECTED-UNIVALENCE rung at the context category — the DIRECTED analog of `context-30`
(`ContextUnivalentUniverse.lean`, the funext-free CATEGORICAL univalence of Cavallo–Höfer).  Where `context-30`
makes the universe object a univalent WILD GROUPOID — `idToIso : (A = B) → CategoryIso A B` a two-sided
equivalence, with `CategoryIso` the SYMMETRIC iso (a forward / backward pair) — `context-34` makes it a
univalent DIRECTED wild category: the directed hom `Hom_U(A, B)` (a morphism, NOT an iso) is the object of
interest, and the comparison `homToFun : (A = B) → DirectedCategoryHom A B` is a two-sided equivalence.  Read in
Riehl–Shulman's synthetic-(∞,1) terms this is DIRECTED univalence — the directed hom in the universe IS the
function type — restricted to the funext-free fragment that keeps it zero-axiom.

This file ships the DIRECTED-WILD-CATEGORY apparatus; the operational `Hom_U ↝ Fun` reduction realizing this
univalence BY COMPUTATION is the sibling rung `context-34` reduction core
(`ContextDirectedUnivalence.lean`), which bridges back to the apparatus here.

## Why DIRECTED categorical univalence, and why it is funext-free

The full Riehl–Shulman directed univalence axiom (`Hom_U(A, B) ≃ (A → B)` inside a SEGAL / REZK-complete
universe) entails the same homotopy coherence that the symmetric univalence axiom does — the Segal-fill /
Rezk-completeness data needs `funext` / `Quot.sound`, the fib-5-style wall the directed universe generator
`gen_universeD` defers (Riehl–Shulman, "A type theory for synthetic ∞-categories", 2017).

But the DIRECTED analog of Cavallo–Höfer's move isolates a funext-free fragment.  Replace the homotopy-coherent
directed hom by a WILD directed hom — a bare morphism `A ⟶ B` of a wild category (`RawCategory`), with NO
coherence laws — and ask only that the comparison `homToFun : (A = B) → DirectedCategoryHom A B` be a two-sided
equivalence.  This is "the universe object is a univalent DIRECTED wild category".  At the set-level (discrete)
universe object it holds by definitional proof irrelevance — no funext, no `Quot.sound` — exactly as the
SYMMETRIC `context-30` witness does.

The genuine DIRECTEDNESS, distinguishing this from `context-30`: `DirectedCategoryHom` carries ONLY a forward
morphism.  There is NO `backward`, NO round-trip, NO `symm` — directed homs COMPOSE (`composeHom`: reflexive +
transitive, a category) but do NOT invert (no groupoid structure).  `context-30`'s `CategoryIso` is the
symmetric (invertible) special case.

## What lands here (all zero-axiom)

  * **`DirectedCategoryHom`** — the directed hom `A ⟶ B` in a wild category: a single forward morphism, NO
    inverse (the directed weakening of `CategoryIso`).  Plus the identity hom, composition (`composeHom`:
    a category, not a groupoid — no `symm`), and the underlying-morphism projection `toMorphism` (the literal
    hom-as-function extraction the name `homToFun` realizes).
  * **`homToFun`** — the comparison map `(A = B) → DirectedCategoryHom A B`, sending the reflexive path to the
    identity hom (path induction via `Eq.rec` with an EXPLICIT motive — no funext, no `Quot.sound`).  Realizes a
    path as a directed hom; directed univalence (`Hom_U ↝ Fun`) makes that directed hom precisely a function.
  * **`IsDirectedUnivalentUniverseObject`** — the directed-univalence datum: `homToFun` is a two-sided
    equivalence (an inverse `funToId` with both round-trips).  "The universe object is directed-univalent."
  * **`discreteUniverseObject_isDirectedUnivalent`** — the zero-axiom WITNESS: the set-level (discrete)
    universe object IS directed-univalent.  In a discrete wild category every morphism is an equality, so
    `homToFun` is a bijection — directed univalence holds, by definitional proof irrelevance, exactly as the
    symmetric `context-30` witness (`discreteUniverseObject_isUnivalent`).

## What is deferred (the honest wall)

  * The FULL directed univalence axiom (`Hom_U(A, B) ≃ (A → B)` in a SEGAL / REZK-complete universe) is NOT
    shipped: it entails the Segal-fill / Rezk-completeness coherence, which needs funext / `Quot.sound` — the
    `×type` / type-axis wall the `gen_universeD` directed universe also defers
    (`fxContextDirectedUniverse_hasFullSegalDirectedUA = false`).

Imports only `ContextUnivalentUniverse` (its `context-30` sibling — the `RawCategory` / `discreteUniverseObject`
substrate).  A Axis design-lock must not import up into `Core/` / `Typed/`.  Zero external dependencies — raw
Lean 4 + Init only.

Reference: Riehl & Shulman, "A type theory for synthetic ∞-categories", HHA 2017; Cavallo & Höfer, "Univalence
without function extensionality", MFPS 2026, arXiv:2605.00812; the directed universe generator `gen_universeD`.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## Directed categorical homs — the directed (non-invertible) `A ⟶ B` -/

/-- A **directed categorical hom** `objectA ⟶ objectB` in a wild category (`RawCategory`): a single forward
morphism, with NO inverse, NO round-trip.  This is the DIRECTED weakening of `context-30`'s `CategoryIso` — a
bare morphism rather than an invertible iso.  Directed homs COMPOSE (`composeHom`) and have identities
(`identityHom`) — a category — but do NOT invert: there is no `symm`, the genuine directedness.  In the
universe-as-wild-category the forward morphism IS a function, so this directed hom is exactly a `Fun(A, B)`,
which is what directed univalence (`Hom_U ↝ Fun`) computes it to. -/
structure DirectedCategoryHom (category : RawCategory) (objectA objectB : category.Object) where
  /-- The forward morphism `objectA ⟶ objectB` — the function the directed hom IS.  No backward morphism: the
  directed (non-invertible) content. -/
  forward : category.Morphism objectA objectB

/-- The identity directed hom `objectA ⟶ objectA` — the forward morphism is the identity (reflexivity of the
directed hom relation). -/
def DirectedCategoryHom.identityHom (category : RawCategory) (object : category.Object) :
    DirectedCategoryHom category object object where
  forward := category.identity object

/-- Directed homs COMPOSE (`composeHom firstHom secondHom : objectA ⟶ objectC`) — so `−⟶−` is reflexive
(`identityHom`) and transitive, i.e. a CATEGORY.  There is deliberately NO `symm`: directed homs do not invert.
This is the structural difference from `context-30`'s `CategoryIso`, which is a groupoid. -/
def DirectedCategoryHom.composeHom {category : RawCategory} {objectA objectB objectC : category.Object}
    (firstHom : DirectedCategoryHom category objectA objectB)
    (secondHom : DirectedCategoryHom category objectB objectC) :
    DirectedCategoryHom category objectA objectC where
  forward := category.compose firstHom.forward secondHom.forward

/-- The underlying morphism of a directed hom — the literal "hom as function" extraction.  In the
universe-as-category the morphisms ARE functions, so this is the `Fun(A, B)` a directed hom denotes.  The
bridge to the shipped `RawCategory.Morphism`. -/
def DirectedCategoryHom.toMorphism {category : RawCategory} {objectA objectB : category.Object}
    (directedHom : DirectedCategoryHom category objectA objectB) :
    category.Morphism objectA objectB :=
  directedHom.forward

/-! ## The comparison map `homToFun` and the directed-univalence datum -/

/-- The comparison map `homToFun : (objectA = objectB) → DirectedCategoryHom objectA objectB`, sending the
reflexive path to the identity hom.  Path induction via `Eq.rec` with an EXPLICIT motive (the implicit-motive
`▸` casts the wrong occurrence); no funext, no `Quot.sound`.  Mirrors `context-30`'s `idToIso`, but the target
is a DIRECTED hom (a bare morphism = function), not a symmetric iso: this realizes a path as a function, the
forward direction of directed univalence (`Hom_U ↝ Fun`). -/
def homToFun (category : RawCategory) {objectA objectB : category.Object}
    (path : objectA = objectB) : DirectedCategoryHom category objectA objectB :=
  Eq.rec (motive := fun target _ => DirectedCategoryHom category objectA target)
    (DirectedCategoryHom.identityHom category objectA) path

/-- `homToFun` of the reflexive path is the identity hom, definitionally (the `Eq.rec` base). -/
theorem homToFun_refl (category : RawCategory) (object : category.Object) :
    homToFun category (rfl : object = object) = DirectedCategoryHom.identityHom category object :=
  rfl

/-- **The directed-univalence datum on a universe object.**  A wild category (= a universe object of the
context category, viewed as the wild category of its types and functions) is DIRECTED-UNIVALENT when `homToFun`
is a two-sided equivalence: there is an inverse `funToId` recovering a path from every directed hom, with both
round-trips.  This is the DIRECTED analog of `context-30`'s `IsUnivalentUniverseObject` — "the universe object
is directed-univalent": directed homs `A ⟶ B` are exactly paths `A = B` (at the set level), i.e. functions. -/
structure IsDirectedUnivalentUniverseObject (category : RawCategory) where
  /-- The inverse comparison: every directed hom yields a path between the objects. -/
  funToId : {objectA objectB : category.Object} →
    DirectedCategoryHom category objectA objectB → objectA = objectB
  /-- `homToFun ∘ funToId = id` — every directed hom is `homToFun` of its recovered path. -/
  homToFun_funToId : {objectA objectB : category.Object} →
    (directedHom : DirectedCategoryHom category objectA objectB) →
    homToFun category (funToId directedHom) = directedHom
  /-- `funToId ∘ homToFun = id` — every path is recovered from its directed hom. -/
  funToId_homToFun : {objectA objectB : category.Object} → (path : objectA = objectB) →
    funToId (homToFun category path) = path

/-! ## The zero-axiom witness: the set-level (discrete) universe object is directed-univalent -/

/-- ★ **The set-level universe object is DIRECTED-UNIVALENT.**  In the discrete wild category
(`discreteUniverseObject`, `context-30`) every morphism is the image of an equality (`Morphism a b = PLift
(a = b)`), so a directed hom `A ⟶ B` is exactly a path `A = B`, and `homToFun` is a genuine two-sided
equivalence — its inverse extracts the underlying path, with both round-trips holding by definitional proof
irrelevance.  This is the zero-axiom inhabitant of `IsDirectedUnivalentUniverseObject`: directed univalence at
the simplest universe object, with no funext, no `Quot.sound` — the directed mirror of
`discreteUniverseObject_isUnivalent`. -/
def discreteUniverseObject_isDirectedUnivalent (carrier : Type) :
    IsDirectedUnivalentUniverseObject (discreteUniverseObject carrier) where
  funToId := fun directedHom => directedHom.forward.down
  homToFun_funToId := fun directedHom => by
    obtain ⟨⟨forwardPath⟩⟩ := directedHom
    cases forwardPath
    rfl
  funToId_homToFun := fun path => by
    cases path
    rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The CONTEXT-LEVEL DIRECTED-univalence apparatus (`homToFun` a two-sided equivalence)
is shipped, WITH a zero-axiom witness (the set-level universe object).  This is the funext-free fragment of
DIRECTED univalence (a wild directed category, the directed analog of Cavallo–Höfer `CUA`); the
by-computation realization is the `context-34` reduction (`Hom_U ↝ Fun`).  `= true`. -/
def fxContextDirectedUniverse_hasDirectedUnivalence : Bool := true

/-- **Honesty marker.**  The FULL directed univalence axiom — `Hom_U(A, B) ≃ (A → B)` in a SEGAL /
REZK-complete universe (Riehl–Shulman) — is NOT shipped here: the Segal-fill / Rezk-completeness coherence it
entails needs `Quot.sound` / is an axiom in this raw-Lean zero-dependency metatheory.  That is the `×type` /
type-axis wall the `gen_universeD` directed universe also defers.  `= false`. -/
def fxContextDirectedUniverse_hasFullSegalDirectedUA : Bool := false

/-! ## Smoke -/

/-- Smoke: in the set-level universe object, `homToFun` and `funToId` round-trip on paths — recovering the path
is the identity, the concrete content of directed univalence at a 0-type. -/
theorem discreteUniverseObject_funToId_homToFun_smoke (carrier : Type)
    {objectA objectB : carrier} (path : objectA = objectB) :
    (discreteUniverseObject_isDirectedUnivalent carrier).funToId
        (homToFun (discreteUniverseObject carrier) path)
      = path :=
  (discreteUniverseObject_isDirectedUnivalent carrier).funToId_homToFun path

end FX1Poly.Axis
