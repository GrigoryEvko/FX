import FX1Poly.Tier0.Context.ContextDirectedUniverse

/-! # context-33 — the context universe as a SYNTHETIC ∞-CATEGORY (Segal + Rezk, Riehl–Shulman)

`context-33` (★, on the fib-* arc, the directed-line capstone) puts the SYNTHETIC ∞-CATEGORY structure on
the context category's universe object, in the precise Riehl–Shulman sense: a SEGAL structure (composable
pairs of directed homs have a contractible type of composites) plus REZK-COMPLETENESS (the isomorphisms are
exactly the identity paths).  It is built DIRECTLY on `context-34`'s directed universe
(`ContextDirectedUniverse.lean`): there the directed hom `Hom_U(A, B)` is a single FORWARD morphism
(`DirectedCategoryHom`, NO `symm`) that composes (`composeHom`) into a category; here that directed category
is upgraded to a synthetic ∞-category by adding the two Riehl–Shulman conditions, each piece zero-axiom.

## Why Segal + Rezk, and why the funext-free fragment

In Riehl–Shulman's type theory for synthetic ∞-categories (HHA 2017) a type `A` is a:
  * **pre-∞-category (Segal type)** when every composable pair `(f : hom(x,y), g : hom(y,z))` has a
    CONTRACTIBLE type of composites — a unique `h : hom(x,z)` filling the `Δ²` over the spine `(f, g)`.
    "The Segal condition" = the spine restriction is an equivalence (the (∞,1)-COMPOSITION).
  * **∞-category (Rezk-complete Segal type)** when, in addition, `idToIso : (x = y) → iso(x, y)` is an
    equivalence — COMPLETENESS / directed univalence: isomorphisms are exactly identity paths.

The FULL synthetic ∞-category (homotopy-coherent Segal-fill at every dimension + Rezk-completeness at a
NON-discrete universe) entails the directed Segal-fill / Rezk coherence that needs `funext` / `Quot.sound`
— the fib-5-style wall the directed universe generator `gen_universeD` defers
(`ContextDirectedUniverse.lean`'s `fxContextDirectedUniverse_hasFullSegalDirectedUA = false`).  But the
STRICT / DISCRETE fragment is funext-free, exactly as `context-34`'s discrete directed-univalence witness:

  * a STRICT category IS a Segal type with strict UNIQUE composites — the type of composites of a composable
    pair is a singleton (its only element is `composeHom f g`), contractible BY definitional proof
    irrelevance of the `isComposite` equality.  This holds for EVERY `RawCategory`, by `rfl`.
  * the DISCRETE (set-level) universe object IS Rezk-complete — its only isomorphisms are identities, so
    `idToDirectedIso` is a two-sided equivalence, by definitional proof irrelevance + structure eta (the same
    mechanism as `context-34`'s `discreteUniverseObject_isDirectedUnivalent` and `context-30`'s CUA witness).

This is complementary to `context-14` (`InftyOneCwF.lean`), which presents the (∞,1)-category SIMPLICIALLY
(a Segal SPACE via the spine map on a simplicial set) and HONESTLY WALLS Rezk completeness
(`fxInftyOneCwF_hasRezkCompleteness = false`).  `context-33` works in the DIRECTED-CATEGORY (Riehl–Shulman)
presentation on `context-34`'s `DirectedCategoryHom`, and the genuinely new content over `context-14` is that
it PROVES Rezk-completeness AT THE DISCRETE universe object — the marker that flips to `true`.

## What lands here (all zero-axiom)

  * **`DirectedCategoryHom.ext`** + **`directedComposition_assoc` / `_identityLeft` / `_identityRight`** —
    structure eta for the single-field directed hom, and the STRICT category laws of `composeHom` (the Segal
    composition's associativity + unitality), each reduced to the base category's law on forward morphisms.
  * **`IsContractibleType`** + **`SegalComposite`** + **`RawCategory.segalComposite_isContractible`** ★ — the
    type of composites of a composable pair of directed homs, and the SEGAL CONDITION: that type is
    CONTRACTIBLE, for EVERY `RawCategory`, by definitional proof irrelevance.  Every strict category is a
    Segal type.
  * **`DirectedHomIso`** (+ `identityIso` / `symm` / `ext`) — an ISOMORPHISM of directed homs: a forward and a
    backward directed hom whose composites are the identity homs (the directed Rezk equivalences).
  * **`idToDirectedIso`** + **`IsRezkComplete`** + **`discreteUniverseObject_isRezkComplete`** ★ — the
    comparison `(x = y) → DirectedHomIso x y` (path induction, `Eq.rec` with explicit motive, no funext), the
    Rezk datum (it is a two-sided equivalence), and the zero-axiom WITNESS at the discrete universe object.
  * **`IsSyntheticInfinityCategory`** + **`discreteUniverseObject_isSyntheticInfinityCategory`** ★ — the
    packaged synthetic ∞-category (Segal + Rezk), and the CAPSTONE WITNESS: the discrete universe object is a
    synthetic ∞-category.
  * **`DirectedHomIso.instDecidableEq`** — the decidable-classification witness (isos have decidable equality
    when the underlying morphisms do; the round-trip proofs are proof-irrelevant), mirroring `context-35`.

## What is deferred (the honest wall)

  * The FULL synthetic ∞-category — homotopy-coherent Segal-fill at every dimension + Rezk-completeness at a
    NON-discrete (proof-relevant) universe object — is NOT shipped: it entails the directed Segal-fill / Rezk
    coherence that needs `funext` / `Quot.sound`, the `×type` / type-axis wall the `gen_universeD` directed
    universe defers (`fxSyntheticInfinityCategory_hasFullSyntheticInfinityCategory = false`).
  * The Segal + Rezk structure here is the SELF-CONTAINED Tier0 analog, NOT a Core `StepOverTable` iota row
    (`fxSyntheticInfinityCategory_isOverCoreIotaTable = false`).

Imports only `ContextDirectedUniverse` (its `context-34` sibling — the `RawCategory` / `DirectedCategoryHom` /
`composeHom` / `discreteUniverseObject` substrate).  A Tier0 design-lock must not import up into `Core/` /
`Typed/`.  Zero external dependencies — raw Lean 4 + Init only.

Reference: Riehl & Shulman, "A type theory for synthetic ∞-categories", HHA 2017; Rezk, "A model for the
homotopy theory of homotopy theory" (complete Segal spaces); the `context-14` simplicial presentation
(`InftyOneCwF.lean`); the `context-34` directed universe (`ContextDirectedUniverse.lean`).
-/

namespace FX1Poly.Tier0
open FX1Poly.Polygraph

universe u

/-! ## Structure eta for directed homs, and the strict category laws (Segal composition coherence) -/

/-- **Extensionality of directed homs.**  A `DirectedCategoryHom` is a single-field structure (its `forward`
morphism), so two are equal once their forward morphisms agree.  Funext-free — `Eq` of the field plus
structure eta. -/
theorem DirectedCategoryHom.ext {category : RawCategory} {objectA objectB : category.Object}
    {firstHom secondHom : DirectedCategoryHom category objectA objectB}
    (forwardEq : firstHom.forward = secondHom.forward) : firstHom = secondHom := by
  obtain ⟨firstForward⟩ := firstHom
  obtain ⟨secondForward⟩ := secondHom
  cases forwardEq
  rfl

/-- The Segal composition is ASSOCIATIVE — `composeHom` reassociates, reduced to the base category's
`composeAssoc` on the underlying forward morphisms (via `DirectedCategoryHom.ext`).  The associativity
coherence of the synthetic ∞-category's composition, strict. -/
theorem directedComposition_assoc {category : RawCategory}
    {objectA objectB objectC objectD : category.Object}
    (homF : DirectedCategoryHom category objectA objectB)
    (homG : DirectedCategoryHom category objectB objectC)
    (homH : DirectedCategoryHom category objectC objectD) :
    DirectedCategoryHom.composeHom (DirectedCategoryHom.composeHom homF homG) homH
      = DirectedCategoryHom.composeHom homF (DirectedCategoryHom.composeHom homG homH) :=
  DirectedCategoryHom.ext (category.composeAssoc homF.forward homG.forward homH.forward)

/-- The identity directed hom is a LEFT unit for the Segal composition — reduced to the base category's
`identityLeft`.  Strict unitality. -/
theorem directedComposition_identityLeft {category : RawCategory} {objectA objectB : category.Object}
    (hom : DirectedCategoryHom category objectA objectB) :
    DirectedCategoryHom.composeHom (DirectedCategoryHom.identityHom category objectA) hom = hom :=
  DirectedCategoryHom.ext (category.identityLeft hom.forward)

/-- The identity directed hom is a RIGHT unit for the Segal composition — reduced to the base category's
`identityRight`.  Strict unitality. -/
theorem directedComposition_identityRight {category : RawCategory} {objectA objectB : category.Object}
    (hom : DirectedCategoryHom category objectA objectB) :
    DirectedCategoryHom.composeHom hom (DirectedCategoryHom.identityHom category objectB) = hom :=
  DirectedCategoryHom.ext (category.identityRight hom.forward)

/-! ## Contractibility and the Segal condition -/

/-- A type is **contractible** when it has a center to which every point is equal — a singleton up to `Eq`.
The funext-free notion of "the type of composites is contractible" used by the Segal condition. -/
structure IsContractibleType (carrier : Type u) where
  /-- The center — the canonical inhabitant. -/
  center : carrier
  /-- Every point coincides with the center. -/
  contraction : (point : carrier) → point = center

/-- The **type of composites** of a composable pair of directed homs `(firstHom, secondHom)`: a directed hom
`objectX ⟶ objectZ` together with a proof it IS the composite `composeHom firstHom secondHom`.  This is the
fibre of the spine restriction over `(firstHom, secondHom)` — the `Δ²` fillers over that spine.  The Segal
condition asks this type to be contractible. -/
structure SegalComposite (category : RawCategory) {objectX objectY objectZ : category.Object}
    (firstHom : DirectedCategoryHom category objectX objectY)
    (secondHom : DirectedCategoryHom category objectY objectZ) where
  /-- The candidate composite. -/
  composite : DirectedCategoryHom category objectX objectZ
  /-- It is the (strict) composite of the pair. -/
  isComposite : composite = DirectedCategoryHom.composeHom firstHom secondHom

/-- ★ **The Segal condition — every composable pair has a CONTRACTIBLE type of composites.**  For EVERY
`RawCategory`: the center is `composeHom firstHom secondHom` (the strict composite), and every other composite
coincides with it because its `isComposite` proof IS an equality to that composite — by definitional proof
irrelevance, no funext.  So every strict category is a Segal type (a pre-∞-category). -/
def _root_.FX1Poly.Polygraph.RawCategory.segalComposite_isContractible (category : RawCategory)
    {objectX objectY objectZ : category.Object}
    (firstHom : DirectedCategoryHom category objectX objectY)
    (secondHom : DirectedCategoryHom category objectY objectZ) :
    IsContractibleType (SegalComposite category firstHom secondHom) where
  center := { composite := DirectedCategoryHom.composeHom firstHom secondHom, isComposite := rfl }
  contraction := fun point => by
    obtain ⟨composite, isComposite⟩ := point
    cases isComposite
    rfl

/-! ## Directed isomorphisms — the Rezk equivalences -/

/-- A **directed isomorphism** `objectA ≅ objectB`: a forward and a backward DIRECTED hom whose two
composites are the identity directed homs (BY EQUALITY).  This is the directed-hom-level iso (`context-34`'s
`DirectedCategoryHom` made invertible) whose collapse to identity paths is Rezk-completeness.  Compare
`context-30`'s `CategoryIso`, which lives at the level of bare `RawCategory.Morphism`s. -/
structure DirectedHomIso (category : RawCategory) (objectA objectB : category.Object) where
  /-- The forward directed hom. -/
  forward : DirectedCategoryHom category objectA objectB
  /-- The backward directed hom. -/
  backward : DirectedCategoryHom category objectB objectA
  /-- `forward` then `backward` is the identity directed hom on `objectA`. -/
  forwardBackward : DirectedCategoryHom.composeHom forward backward
    = DirectedCategoryHom.identityHom category objectA
  /-- `backward` then `forward` is the identity directed hom on `objectB`. -/
  backwardForward : DirectedCategoryHom.composeHom backward forward
    = DirectedCategoryHom.identityHom category objectB

/-- The identity directed isomorphism — forward and backward are both the identity directed hom; the
composites are the strict left-unit law. -/
def DirectedHomIso.identityIso (category : RawCategory) (object : category.Object) :
    DirectedHomIso category object object where
  forward := DirectedCategoryHom.identityHom category object
  backward := DirectedCategoryHom.identityHom category object
  forwardBackward := directedComposition_identityLeft (DirectedCategoryHom.identityHom category object)
  backwardForward := directedComposition_identityLeft (DirectedCategoryHom.identityHom category object)

/-- Directed isos are symmetric — swap forward and backward (so directed isos form a groupoid, unlike the
underlying directed homs). -/
def DirectedHomIso.symm {category : RawCategory} {objectA objectB : category.Object}
    (iso : DirectedHomIso category objectA objectB) : DirectedHomIso category objectB objectA where
  forward := iso.backward
  backward := iso.forward
  forwardBackward := iso.backwardForward
  backwardForward := iso.forwardBackward

/-- **Extensionality of directed isos.**  Two directed isos are equal once their forward and backward homs
agree: the two round-trip components are `Eq` proofs (`Prop`), proof-irrelevant.  Funext-free. -/
theorem DirectedHomIso.ext {category : RawCategory} {objectA objectB : category.Object}
    {firstIso secondIso : DirectedHomIso category objectA objectB}
    (forwardEq : firstIso.forward = secondIso.forward)
    (backwardEq : firstIso.backward = secondIso.backward) : firstIso = secondIso := by
  obtain ⟨firstForward, firstBackward, _, _⟩ := firstIso
  obtain ⟨secondForward, secondBackward, _, _⟩ := secondIso
  cases forwardEq
  cases backwardEq
  rfl

/-! ## The comparison map and Rezk-completeness -/

/-- The comparison `idToDirectedIso : (objectA = objectB) → DirectedHomIso objectA objectB`, sending the
reflexive path to the identity directed iso.  Path induction via `Eq.rec` with an EXPLICIT motive (the
implicit-motive `▸` casts the wrong occurrence); no funext, no `Quot.sound`.  The directed analog of
`context-30`'s `idToIso`. -/
def idToDirectedIso (category : RawCategory) {objectA objectB : category.Object}
    (path : objectA = objectB) : DirectedHomIso category objectA objectB :=
  Eq.rec (motive := fun target _ => DirectedHomIso category objectA target)
    (DirectedHomIso.identityIso category objectA) path

/-- `idToDirectedIso` of the reflexive path is the identity directed iso, definitionally (the `Eq.rec`
base). -/
theorem idToDirectedIso_refl (category : RawCategory) (object : category.Object) :
    idToDirectedIso category (rfl : object = object) = DirectedHomIso.identityIso category object :=
  rfl

/-- **Rezk-completeness of a directed category.**  `idToDirectedIso` is a two-sided equivalence: there is an
inverse `directedIsoToId` recovering an identity path from every directed iso, with both round-trips.  This is
the COMPLETENESS condition of a synthetic ∞-category — "isomorphisms are identity paths" — the directed analog
of `context-30`'s `IsUnivalentUniverseObject`. -/
structure IsRezkComplete (category : RawCategory) where
  /-- Every directed iso yields an identity path between its objects. -/
  directedIsoToId : {objectA objectB : category.Object} →
    DirectedHomIso category objectA objectB → objectA = objectB
  /-- `idToDirectedIso ∘ directedIsoToId = id` — every iso is `idToDirectedIso` of its recovered path. -/
  idToDirectedIso_directedIsoToId : {objectA objectB : category.Object} →
    (iso : DirectedHomIso category objectA objectB) →
    idToDirectedIso category (directedIsoToId iso) = iso
  /-- `directedIsoToId ∘ idToDirectedIso = id` — every path is recovered from its iso. -/
  directedIsoToId_idToDirectedIso : {objectA objectB : category.Object} →
    (path : objectA = objectB) → directedIsoToId (idToDirectedIso category path) = path

/-- ★ **The discrete universe object is REZK-COMPLETE.**  In the discrete wild category every directed hom is
the image of an equality (`Morphism a b = PLift (a = b)`), so a directed iso `A ≅ B` is exactly a path
`A = B` — its forward hom's underlying path — and `idToDirectedIso` is a genuine two-sided equivalence, with
both round-trips holding by definitional proof irrelevance + structure eta.  This is the zero-axiom inhabitant
of `IsRezkComplete`: completeness at the simplest universe object, with no funext, no `Quot.sound` — the
content `context-14` honestly walled. -/
def discreteUniverseObject_isRezkComplete (carrier : Type) :
    IsRezkComplete (discreteUniverseObject carrier) where
  directedIsoToId := fun iso => iso.forward.forward.down
  idToDirectedIso_directedIsoToId := fun iso => by
    obtain ⟨⟨⟨forwardPath⟩⟩, _, _, _⟩ := iso
    cases forwardPath
    rfl
  directedIsoToId_idToDirectedIso := fun path => by
    cases path
    rfl

/-! ## The packaged synthetic ∞-category -/

/-- A **synthetic ∞-category** structure on a directed category: the SEGAL condition (every composable pair
of directed homs has a contractible type of composites) plus REZK-COMPLETENESS (`idToDirectedIso` a two-sided
equivalence).  This is the Riehl–Shulman "complete Segal type" packaged over `context-34`'s directed
universe. -/
structure IsSyntheticInfinityCategory (category : RawCategory) where
  /-- The Segal condition: every composable pair has a contractible type of composites. -/
  segalCondition : {objectX objectY objectZ : category.Object} →
    (firstHom : DirectedCategoryHom category objectX objectY) →
    (secondHom : DirectedCategoryHom category objectY objectZ) →
    IsContractibleType (SegalComposite category firstHom secondHom)
  /-- Rezk-completeness: isomorphisms are exactly identity paths. -/
  rezkCompleteness : IsRezkComplete category

/-- ★ **The discrete universe object IS a synthetic ∞-category.**  The CAPSTONE witness: the Segal condition
holds for every `RawCategory` (`segalComposite_isContractible`), and the discrete object is Rezk-complete
(`discreteUniverseObject_isRezkComplete`).  Assembled, the set-level context universe object is a
Riehl–Shulman synthetic ∞-category — zero-axiom. -/
def discreteUniverseObject_isSyntheticInfinityCategory (carrier : Type) :
    IsSyntheticInfinityCategory (discreteUniverseObject carrier) where
  segalCondition := fun firstHom secondHom =>
    RawCategory.segalComposite_isContractible (discreteUniverseObject carrier) firstHom secondHom
  rezkCompleteness := discreteUniverseObject_isRezkComplete carrier

/-! ## The decidable-classification witness -/

/-- ★ **The decidable-classification witness.**  Directed isos have decidable equality exactly when the
underlying forward and backward morphisms do: the morphisms are compared by the assumed deciders, and the
round-trip proofs contribute nothing (proof irrelevance), so equality of the two morphisms decides equality of
the directed iso.  The directed-Rezk mirror of `context-35`'s decidable total-morphism equality. -/
instance DirectedHomIso.instDecidableEq {category : RawCategory} {objectA objectB : category.Object}
    [decForward : DecidableEq (category.Morphism objectA objectB)]
    [decBackward : DecidableEq (category.Morphism objectB objectA)] :
    DecidableEq (DirectedHomIso category objectA objectB) :=
  fun firstIso secondIso =>
    match decForward firstIso.forward.forward secondIso.forward.forward with
    | isTrue forwardEq =>
        match decBackward firstIso.backward.forward secondIso.backward.forward with
        | isTrue backwardEq =>
            isTrue (DirectedHomIso.ext
              (DirectedCategoryHom.ext forwardEq) (DirectedCategoryHom.ext backwardEq))
        | isFalse backwardDistinct =>
            isFalse (fun isoEqual =>
              backwardDistinct (congrArg (fun iso => iso.backward.forward) isoEqual))
    | isFalse forwardDistinct =>
        isFalse (fun isoEqual => forwardDistinct (congrArg (fun iso => iso.forward.forward) isoEqual))

/-! ## Honesty markers -/

/-- **Honesty marker.**  The STRICT SEGAL structure is shipped: the directed homs' `composeHom` is a strict
category (associative + unital, `directedComposition_assoc` / `_identityLeft` / `_identityRight`), and every
composable pair has a CONTRACTIBLE type of composites (`segalComposite_isContractible`) — every strict
category is a Segal type / pre-∞-category.  `= true`. -/
def fxSyntheticInfinityCategory_hasStrictSegalStructure : Bool := true

/-- **Honesty marker.**  REZK-COMPLETENESS is shipped AT THE DISCRETE universe object
(`discreteUniverseObject_isRezkComplete`): its isomorphisms are exactly its identity paths, so the discrete
context universe object is a synthetic ∞-category (`discreteUniverseObject_isSyntheticInfinityCategory`).  This
is the content `context-14` (`InftyOneCwF.lean`) honestly walled.  `= true`. -/
def fxSyntheticInfinityCategory_hasRezkCompletenessAtDiscrete : Bool := true

/-- **Honesty marker.**  The FULL synthetic ∞-category — homotopy-coherent Segal-fill at every dimension +
Rezk-completeness at a NON-discrete (proof-relevant) universe object — is NOT shipped: it entails the directed
Segal-fill / Rezk coherence that needs `funext` / `Quot.sound`, the `×type` / type-axis wall the
`gen_universeD` directed universe also defers.  `= false`. -/
def fxSyntheticInfinityCategory_hasFullSyntheticInfinityCategory : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Tier0 analog of a Core table-native synthetic-∞-category
row; a Tier0 design-lock cannot import the Core engine, so the Segal + Rezk structure is re-shipped here as a
strict (1-categorical) construction.  Gluing the Tier0 and Core forms is cross-axis `×type`.  `= false`. -/
def fxSyntheticInfinityCategory_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: at the discrete universe object, Rezk's `directedIsoToId` recovers the path that `idToDirectedIso`
started from — the round-trip, the concrete content of completeness at a 0-type. -/
theorem discreteUniverseObject_rezk_roundtrip_smoke (carrier : Type)
    {objectA objectB : carrier} (path : objectA = objectB) :
    (discreteUniverseObject_isRezkComplete carrier).directedIsoToId
        (idToDirectedIso (discreteUniverseObject carrier) path)
      = path :=
  (discreteUniverseObject_isRezkComplete carrier).directedIsoToId_idToDirectedIso path

/-- Smoke: the Segal center of a composable pair (at the discrete synthetic ∞-category) is the strict
composite `composeHom firstHom secondHom` — the (∞,1)-composition, by `rfl`. -/
theorem discreteUniverseObject_segal_center_smoke (carrier : Type)
    {objectX objectY objectZ : carrier}
    (firstHom : DirectedCategoryHom (discreteUniverseObject carrier) objectX objectY)
    (secondHom : DirectedCategoryHom (discreteUniverseObject carrier) objectY objectZ) :
    ((discreteUniverseObject_isSyntheticInfinityCategory carrier).segalCondition
        firstHom secondHom).center.composite
      = DirectedCategoryHom.composeHom firstHom secondHom :=
  rfl

end FX1Poly.Tier0
