import FX1Poly.Tier0.Context.RepresentableMapCategory

/-! # context-30 — the context category's universe object is a UNIVALENT wild category (CUA)

`context-30` is the CONTEXT-CATEGORY UNIVALENCE rung.  It states — and ships a zero-axiom witness for —
the statement "the context category's universe object is univalent", in the precise, funext-free form that
makes it zero-axiom-feasible: **categorical univalence** (CUA) in the sense of Cavallo–Höfer.

## Why CATEGORICAL univalence, and why it is funext-free

The standard univalence axiom `UA` (Voevodsky) — `idtoeq : (A =_U B) → (A ≃ B)` is an equivalence, where
`A ≃ B` is the type of HOMOTOPY equivalences — is famously NOT zero-axiom: inside a univalent universe it
ENTAILS function extensionality (and `funext` needs `Quot.sound` / is an axiom in our raw-Lean,
zero-dependency metatheory).  That is the fib-5-style wall the cubical / groupoid context models all defer
to the type axis (`CubicalModel.hasUnivalentUniverse = false`, `GroupoidModel.hasGroupoidUniverse = false`).

Cavallo & Höfer ("Univalence without function extensionality", MFPS 2026, arXiv:2605.00812) isolate the
funext-free fragment.  Following Dorais, they replace homotopy equivalences `A ≃ B` by CATEGORICAL
equivalences `A ≅ B` — maps `f : A → B` with `s, r : B → A` whose round-trips `f ∘ s` and `r ∘ f` are
identities up to EQUALITY (not up to homotopy):

  * **Categorical univalence** `CUA`: `idtoceq : (A =_U B) → (A ≅ B)` is an equivalence — equivalently,
    `U` is a univalent WILD CATEGORY (objects = types, morphisms = functions, isos = categorical equivalences).
  * Their main theorem: `CUA` does NOT imply funext (it holds in Von Glehn polynomial models that refute
    funext).  So `CUA` is strictly weaker than `UA` and carries NO function-extensionality content — it is the
    zero-axiom-feasible univalence.

This file ships the CONTEXT-LEVEL `CUA` apparatus: a universe OBJECT of the context category, viewed as a
wild category (a `RawCategory`), is univalent when `idToIso : (A = B) → CategoryIso A B` is a (two-sided)
equivalence.  This is the context-side analog of the TYPE-axis `type-7` definitional univalence
(`Id_U ↝ Equiv`, shipped zero-axiom over the iota table); the operational `Id_U ↝ Equiv` reduction at the
context level is the sibling rung `context-31` (`ContextDefinitionalUnivalence.lean`), which realizes this
univalence BY COMPUTATION and bridges back to the apparatus here.

## What lands here (all zero-axiom)

  * **`CategoryIso`** — the type `A ≅ B` of categorical isomorphisms in a wild category: a forward / backward
    pair whose two round-trips are identities BY EQUALITY (the funext-free `≅` of CUA).  Plus the identity iso,
    symmetry, and transitivity — `A ≅ −` is itself a groupoid.
  * **`idToIso`** — the comparison map `(A = B) → CategoryIso A B`, sending `rfl` to the identity iso (path
    induction via `Eq.rec` with an explicit motive — no funext, no `Quot.sound`).
  * **`IsUnivalentUniverseObject`** — the CUA datum on a wild category: `idToIso` is a two-sided equivalence
    (an inverse `isoToId` with both round-trips).  "The universe object is univalent" = this is inhabited.
  * **`discreteUniverseObject` / `discreteUniverseObject_isUnivalent`** — the zero-axiom WITNESS: the
    set-level (discrete / 0-truncated) universe object on any carrier IS univalent.  In a discrete wild
    category every iso is an identity, so `idToIso` is a bijection — categorical univalence holds, by
    definitional proof irrelevance (the same mechanism by which `discreteGroupoid` is a setoid, `context-23`).

## What is deferred (the honest wall)

  * The FULL univalence axiom `UA` — `idToEquiv` an equivalence for HOMOTOPY equivalences — is NOT shipped:
    it entails funext, which is the `×type` / type-axis wall (`fxContextUniverse_hasUnivalenceAxiom = false`).
  * A NON-degenerate univalent universe object — one whose isos are not all identities — is realized at
    `context-31` DEFINITIONALLY (the `Id_U ↝ Equiv` reduction), not by a semantic transport here.

Imports only `RepresentableMapCategory` (the `RawCategory` / `IsIsomorphism` substrate).  A Tier0 design-lock
must not import up into `Core/` / `Typed/`.  Zero external dependencies — raw Lean 4 + Init only.

Reference: Cavallo & Höfer, "Univalence without function extensionality", MFPS 2026, arXiv:2605.00812.
-/

namespace FX1Poly.Tier0

/-! ## Categorical isomorphisms — the funext-free `A ≅ B` -/

/-- A **categorical isomorphism** `objectA ≅ objectB` in a wild category (`RawCategory`): a forward and a
backward morphism whose two round-trips are the identities BY EQUALITY.  This is the `≅` of Cavallo–Höfer
categorical univalence — inverses up to EQUALITY (`compose forward backward = identity`), the funext-free
weakening of homotopy equivalence.  (Composition is diagrammatic — `compose first second` applies `first`
then `second` — so `compose forward backward : objectA ⟶ objectA`.) -/
structure CategoryIso (category : RawCategory) (objectA objectB : category.Object) where
  /-- The forward morphism `objectA ⟶ objectB`. -/
  forward : category.Morphism objectA objectB
  /-- The backward morphism `objectB ⟶ objectA`. -/
  backward : category.Morphism objectB objectA
  /-- `forward` then `backward` is the identity on `objectA` — the left round-trip, an EQUALITY. -/
  forwardBackward : category.compose forward backward = category.identity objectA
  /-- `backward` then `forward` is the identity on `objectB` — the right round-trip, an EQUALITY. -/
  backwardForward : category.compose backward forward = category.identity objectB

/-- The identity categorical iso `objectA ≅ objectA` — forward and backward are both the identity, and the
round-trips are the identity law. -/
def CategoryIso.identityIso (category : RawCategory) (object : category.Object) :
    CategoryIso category object object where
  forward := category.identity object
  backward := category.identity object
  forwardBackward := category.identityLeft (category.identity object)
  backwardForward := category.identityLeft (category.identity object)

/-- Categorical isos are symmetric — swap forward and backward.  (So `≅` is symmetric, the groupoid
inverse.) -/
def CategoryIso.symm {category : RawCategory} {objectA objectB : category.Object}
    (isomorphism : CategoryIso category objectA objectB) : CategoryIso category objectB objectA where
  forward := isomorphism.backward
  backward := isomorphism.forward
  forwardBackward := isomorphism.backwardForward
  backwardForward := isomorphism.forwardBackward

/-- A categorical iso has, in particular, an invertible forward morphism — the bridge to the shipped
`IsIsomorphism` (`RepresentableMapCategory.lean`).  Note the inverse roles swap because `IsIsomorphism`'s
`leftInverse` is `compose inverse morphism = identity (target)`. -/
def CategoryIso.toIsIsomorphism {category : RawCategory} {objectA objectB : category.Object}
    (isomorphism : CategoryIso category objectA objectB) :
    IsIsomorphism category isomorphism.forward where
  inverse := isomorphism.backward
  leftInverse := isomorphism.backwardForward
  rightInverse := isomorphism.forwardBackward

/-! ## The comparison map `idToIso` and the univalence datum -/

/-- The comparison map `idToIso : (objectA = objectB) → CategoryIso objectA objectB`, sending the reflexive
path to the identity iso.  Path induction via `Eq.rec` with an EXPLICIT motive (the implicit-motive `▸` casts
the wrong occurrence); no funext, no `Quot.sound`. -/
def idToIso (category : RawCategory) {objectA objectB : category.Object}
    (path : objectA = objectB) : CategoryIso category objectA objectB :=
  Eq.rec (motive := fun target _ => CategoryIso category objectA target)
    (CategoryIso.identityIso category objectA) path

/-- `idToIso` of the reflexive path is the identity iso, definitionally (the `Eq.rec` base). -/
theorem idToIso_refl (category : RawCategory) (object : category.Object) :
    idToIso category (rfl : object = object) = CategoryIso.identityIso category object :=
  rfl

/-- **The categorical-univalence datum on a universe object.**  A wild category (= a universe object of the
context category, viewed as the wild category of its types and functions) is UNIVALENT when `idToIso` is a
two-sided equivalence: there is an inverse `isoToId` recovering a path from every iso, with both round-trips.
This is Cavallo–Höfer `CUA` for this object — "the universe object is univalent". -/
structure IsUnivalentUniverseObject (category : RawCategory) where
  /-- The inverse comparison: every categorical iso yields a path between the objects. -/
  isoToId : {objectA objectB : category.Object} →
    CategoryIso category objectA objectB → objectA = objectB
  /-- `idToIso ∘ isoToId = id` — every iso is `idToIso` of its recovered path. -/
  idToIso_isoToId : {objectA objectB : category.Object} →
    (isomorphism : CategoryIso category objectA objectB) →
    idToIso category (isoToId isomorphism) = isomorphism
  /-- `isoToId ∘ idToIso = id` — every path is recovered from its iso. -/
  isoToId_idToIso : {objectA objectB : category.Object} → (path : objectA = objectB) →
    isoToId (idToIso category path) = path

/-! ## The zero-axiom witness: the set-level (discrete) universe object is univalent -/

/-- The **discrete (set-level) universe object** on a carrier: objects are the carrier's elements, the only
morphisms are equality proofs (`Morphism a b = PLift (a = b)`).  Every category law holds by definitional
proof irrelevance of `Eq` — `rfl`, no `funext`.  This is the 0-truncated universe object: its wild category
has no non-trivial morphisms, so its isos are exactly its identities. -/
def discreteUniverseObject (carrier : Type) : RawCategory where
  Object := carrier
  Morphism := fun objectA objectB => PLift (objectA = objectB)
  identity := fun _ => PLift.up rfl
  compose := fun pathLeft pathRight => PLift.up (pathLeft.down.trans pathRight.down)
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- ★ **The set-level universe object is UNIVALENT (CUA).**  In the discrete wild category every categorical
iso is the image of an equality (its forward morphism's underlying path), and the two round-trips hold by
definitional proof irrelevance — so `idToIso` is a genuine two-sided equivalence.  This is the zero-axiom
inhabitant of `IsUnivalentUniverseObject`: categorical univalence at the simplest universe object, with no
funext, no `Quot.sound`. -/
def discreteUniverseObject_isUnivalent (carrier : Type) :
    IsUnivalentUniverseObject (discreteUniverseObject carrier) where
  isoToId := fun isomorphism => isomorphism.forward.down
  idToIso_isoToId := fun isomorphism => by
    obtain ⟨⟨forwardPath⟩, _, _, _⟩ := isomorphism
    cases forwardPath
    rfl
  isoToId_idToIso := fun path => by
    cases path
    rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The CONTEXT-LEVEL categorical-univalence apparatus (`CUA`: `idToIso` a two-sided
equivalence) is shipped, WITH a zero-axiom witness (the set-level universe object).  This is the funext-free
fragment of univalence (Cavallo–Höfer); the non-degenerate, by-computation realization is `context-31`.
`= true`. -/
def fxContextUniverse_hasCategoricalUnivalence : Bool := true

/-- **Honesty marker.**  The FULL univalence axiom `UA` — `idToEquiv` an equivalence for HOMOTOPY
equivalences — is NOT shipped here: inside a univalent universe it entails function extensionality
(Voevodsky), which needs `Quot.sound` / is an axiom in this raw-Lean zero-dependency metatheory.  That is the
`×type` / type-axis wall the cubical and groupoid context models also defer.  `= false`. -/
def fxContextUniverse_hasUnivalenceAxiom : Bool := false

/-! ## Smoke -/

/-- Smoke: in the set-level universe object, `idToIso` and `isoToId` round-trip on paths — recovering the
path is the identity, the concrete content of categorical univalence at a 0-type. -/
theorem discreteUniverseObject_isoToId_idToIso_smoke (carrier : Type)
    {objectA objectB : carrier} (path : objectA = objectB) :
    (discreteUniverseObject_isUnivalent carrier).isoToId
        (idToIso (discreteUniverseObject carrier) path)
      = path :=
  (discreteUniverseObject_isUnivalent carrier).isoToId_idToIso path

end FX1Poly.Tier0
