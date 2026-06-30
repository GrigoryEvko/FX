import FX1Poly.Polygraph.Category.RawCategory

/-! # context-22 — the cubical set model (Dedekind / monotone cube site), context-side residue

`context-22` is the CUBICAL MODEL rung.  The landmark cubical set models — Cohen–Coquand–Huber–Mörtberg
(CCHM) and the Cartesian cubical model (Angiuli–Brunerie–Coquand–Favonia–Harper–Licata) — interpret
contexts and types as cubical sets, display maps as cubical KAN FIBRATIONS, and exhibit a UNIVALENT universe
where univalence holds *computationally* via the Glue type.

The context-side residue shipped here is the SITE underlying such a model — but in the DEDEKIND (monotone /
distributive-lattice) presentation of the cube category `□`, the funext-free one.  Be precise about WHICH
cube category this is: it is NOT the CCHM site (the De Morgan `□` adds the order-REVERSING involution `¬`,
which is not a monotone map, hence not a `CubeMap` here) and NOT the strict Cartesian site (which DROPS the
`∧`/`∨` connections that ARE present here) — it is the Dedekind site of all monotone vertex maps, which
sits strictly between them.  What separates the three (`¬` vs connection-free vs monotone) — and the
univalence content itself — lives in the DEEP structure (the interval's algebra + Kan/Glue/univalence), the
deferred `×type` core, NOT in the site.  See the SCOPE NOTE below.

## What is context-side here, and what is deferred

Like the simplicial model (`context-13`), the cubical model is built over a SITE — the cube category `□` —
and its presheaves (cubical sets).  The site + the presheaf structure are pure base / category-of-contexts
data; that is the CONTEXT-SIDE residue shipped here, in full and zero-axiom, in the MONOTONE (Dedekind /
distributive-lattice) presentation of `□`:

  * **`cubeCategory`** — `□` as a genuine `RawCategory`.  Objects are dimensions `n` (the `n`-cube has
    vertex set `2ⁿ = (Fin n → Bool)`); morphisms are MONOTONE vertex maps `2ᵐ → 2ⁿ`.  As in Δ, the three
    category laws hold DEFINITIONALLY — associativity by β (function composition), the identity laws by η
    plus definitional proof irrelevance of the monotonicity field — so each is `rfl`, NO `funext`.
  * the cube GENERATORS — the two interval ENDPOINTS `pointFalse`/`pointTrue : [0] ⟶ [1]`, the
    `intervalDegeneracy : [1] ⟶ [0]`, the `diagonal : [1] ⟶ [2]`, and the lattice CONNECTION
    `connectionMin : [2] ⟶ [1]` (the `∧` connection that makes this the Dedekind cube category) — plus a
    cubical identity (`connectionMin ∘ diagonal` is idempotent: `t ∧ t = t`).
  * **`CubicalSet`** — a presheaf on `□` (the model's contexts/types), with the representable cubical set
    `□[k]` (Yoneda) as a genuine witness whose functor laws hold by `rfl`.
  * **`cubicalSetCategory`** — the actual CATEGORY of cubical sets (cSet): `CubicalMap` (natural
    transformations) as morphisms, the three laws again by `rfl`.
  * the **Yoneda embedding** `□ ⟶ cSet` (`yonedaObject` / `yonedaMorphism` + functoriality, all by `rfl`).
  * **`fxCubicalModel`** — the model datum: the site + the representable contexts.

DEFERRED (honestly NOT here, the `×type` / full-model core, recorded by the `= false` markers):
  * KAN FIBRANCY — the cubical composition/transport structure (`hcomp` / `transp`) making display maps
    cubical Kan fibrations — `hasKanFibrancy = false`;
  * the GLUE TYPE — the `Glue` former by which univalence computes — `hasGlueTypes = false`;
  * the UNIVALENT UNIVERSE — the cubical universe of fibrant types with the (computational) univalence
    equivalence — `hasUnivalentUniverse = false`.
  These are the deep semantic content (fibrancy + Glue + univalence), `×type` and the full model, deferred
  to the type axis / `fib`.

SCOPE NOTE: this ships the MONOTONE (Dedekind) cube base, where every law is `rfl`-clean.  The De Morgan
variant (CCHM, which adds the involution `¬` to the interval) and the strict CARTESIAN variant (no
connections) are different bases over the same vertex sets; the monotone presentation is the funext-free one.

Reference: Cohen, Coquand, Huber & Mörtberg, "Cubical Type Theory: a constructive interpretation of the
univalence axiom" (TYPES 2015, arXiv:1611.02108).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## The cube category □ (monotone / Dedekind presentation) -/

/-- A morphism `[source] ⟶ [target]` of the cube category `□`: a MONOTONE map between the cube vertex sets
`2^source = (Fin source → Bool)` and `2^target`, ordered pointwise (`false ≤ true`).  The monotonicity proof
is a `Prop`, so two `CubeMap`s are equal exactly when their underlying vertex functions are — which lets the
category laws hold definitionally (no `funext`). -/
structure CubeMap (source target : Nat) where
  /-- The underlying map on cube vertices. -/
  onVertex : (Fin source → Bool) → (Fin target → Bool)
  /-- The map is monotone for the pointwise order (`false ≤ true`) — what makes it a morphism of `□`. -/
  monotone : ∀ {lower upper : Fin source → Bool},
    (∀ coord, lower coord = true → upper coord = true) →
    ∀ targetCoord, onVertex lower targetCoord = true → onVertex upper targetCoord = true

/-- The identity cube map `[n] ⟶ [n]`. -/
def CubeMap.identityMap (dimension : Nat) : CubeMap dimension dimension where
  onVertex := fun vertex => vertex
  monotone := fun hyp targetCoord htrue => hyp targetCoord htrue

/-- Composition of cube maps `[a] ⟶ [b] ⟶ [c]` (apply `first`, then `second`). -/
def CubeMap.composeMap {dimensionA dimensionB dimensionC : Nat}
    (first : CubeMap dimensionA dimensionB) (second : CubeMap dimensionB dimensionC) :
    CubeMap dimensionA dimensionC where
  onVertex := fun vertex => second.onVertex (first.onVertex vertex)
  monotone := fun hyp targetCoord htrue => second.monotone (first.monotone hyp) targetCoord htrue

/-- ★ **The cube category `□`** as a genuine `RawCategory` (monotone / Dedekind presentation).  Objects are
dimensions; morphisms are monotone vertex maps.  All three category laws hold DEFINITIONALLY: associativity
by β (function composition), the identity laws by η plus definitional proof irrelevance of the monotonicity
field — so `rfl` discharges each, NO `funext`. -/
def cubeCategory : RawCategory where
  Object := Nat
  Morphism := CubeMap
  identity := CubeMap.identityMap
  compose := CubeMap.composeMap
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-! ## The interval object + cube generators -/

/-- The interval endpoint `0 : [0] ⟶ [1]` — the bottom face (constant-`false` vertex). -/
def CubeMap.pointFalse : CubeMap 0 1 where
  onVertex := fun _ _ => false
  monotone := fun _ _ hfalse => hfalse

/-- The interval endpoint `1 : [0] ⟶ [1]` — the top face (constant-`true` vertex). -/
def CubeMap.pointTrue : CubeMap 0 1 where
  onVertex := fun _ _ => true
  monotone := fun _ _ _ => rfl

/-- The interval degeneracy `[1] ⟶ [0]` — the unique map to the point (target has no coordinates). -/
def CubeMap.intervalDegeneracy : CubeMap 1 0 where
  onVertex := fun _ targetCoord => targetCoord.elim0
  monotone := fun _ targetCoord => targetCoord.elim0

/-- The diagonal `[1] ⟶ [2]` — duplicate the single dimension into both (`t ↦ (t, t)`). -/
def CubeMap.diagonal : CubeMap 1 2 where
  onVertex := fun vertex _ => vertex ⟨0, Nat.succ_pos 0⟩
  monotone := fun hyp _ htrue => hyp ⟨0, Nat.succ_pos 0⟩ htrue

/-- ★ The `∧`-CONNECTION `[2] ⟶ [1]` — the meet/min of the two coordinates.  Its monotonicity is what makes
`□` the DEDEKIND (distributive-lattice) cube category. -/
def CubeMap.connectionMin : CubeMap 2 1 where
  onVertex := fun vertex _ => vertex ⟨0, Nat.succ_pos 1⟩ && vertex ⟨1, Nat.lt_succ_self 1⟩
  monotone := fun {lower upper} hyp _ htrue => by
    have ezero : upper ⟨0, Nat.succ_pos 1⟩ = true := by
      cases hzero : lower ⟨0, Nat.succ_pos 1⟩
      · rw [hzero, Bool.false_and] at htrue; exact absurd htrue (by decide)
      · exact hyp ⟨0, Nat.succ_pos 1⟩ hzero
    have eone : upper ⟨1, Nat.lt_succ_self 1⟩ = true := by
      cases hone : lower ⟨1, Nat.lt_succ_self 1⟩
      · rw [hone, Bool.and_false] at htrue; exact absurd htrue (by decide)
      · exact hyp ⟨1, Nat.lt_succ_self 1⟩ hone
    rw [ezero, eone, Bool.and_self]

/-- ★ A cubical identity: the `∧`-connection precomposed with the diagonal is idempotent — `t ∧ t = t`.
Stated POINTWISE at the single coordinate (so funext-free), exercising the lattice structure. -/
theorem CubeMap.connectionMin_diagonal_idempotent (vertex : Fin 1 → Bool) :
    (CubeMap.composeMap CubeMap.diagonal CubeMap.connectionMin).onVertex vertex
        ⟨0, Nat.succ_pos 0⟩
      = (CubeMap.identityMap 1).onVertex vertex ⟨0, Nat.succ_pos 0⟩ :=
  Bool.and_self _

/-! ## Cubical sets (presheaves on □) -/

/-- A **cubical set** — a presheaf on `□`.  Each dimension `n` carries a type of `n`-cubes, and each cube
map `f : [a] ⟶ [b]` acts CONTRAVARIANTLY (restriction) on cubes, functorially.  The functoriality laws are
stated POINTWISE — equalities IN a cube type, not between functions — so they are funext-free. -/
structure CubicalSet where
  /-- The `n`-cubes. -/
  cubes : Nat → Type
  /-- Contravariant restriction along a cube map. -/
  restrict : {source target : Nat} → CubeMap source target → cubes target → cubes source
  /-- Restriction along the identity is the identity (pointwise). -/
  restrictIdentity : ∀ (dimension : Nat) (cube : cubes dimension),
    restrict (CubeMap.identityMap dimension) cube = cube
  /-- Restriction is contravariantly functorial (pointwise). -/
  restrictCompose : ∀ {dimensionA dimensionB dimensionC : Nat}
    (first : CubeMap dimensionA dimensionB) (second : CubeMap dimensionB dimensionC)
    (cube : cubes dimensionC),
    restrict (CubeMap.composeMap first second) cube = restrict first (restrict second cube)

/-- ★ The representable cubical set `□[k] = Hom_□(−, [k])` (Yoneda) — a genuine cubical set whose
restriction is precomposition, with both functor laws by `rfl` (the category laws of `□`). -/
def representableCubicalSet (dimensionK : Nat) : CubicalSet where
  cubes := fun dimension => CubeMap dimension dimensionK
  restrict := fun reindex cube => CubeMap.composeMap reindex cube
  restrictIdentity := fun _ _ => rfl
  restrictCompose := fun _ _ _ => rfl

/-! ## The category of cubical sets (cSet) + the Yoneda embedding -/

/-- A **morphism of cubical sets** — a natural transformation `source ⟶ target`: a family of maps on cubes,
one per dimension, COMMUTING with restriction (naturality, stated pointwise so funext-free). -/
structure CubicalMap (source target : CubicalSet) where
  /-- The component map at each dimension. -/
  component : (dimension : Nat) → source.cubes dimension → target.cubes dimension
  /-- Naturality: the components commute with restriction. -/
  naturality : ∀ {dimensionA dimensionB : Nat} (reindex : CubeMap dimensionA dimensionB)
    (cube : source.cubes dimensionB),
    target.restrict reindex (component dimensionB cube)
      = component dimensionA (source.restrict reindex cube)

/-- The identity morphism of cubical sets. -/
def CubicalMap.identityMap (cubicalSet : CubicalSet) : CubicalMap cubicalSet cubicalSet where
  component := fun _ cube => cube
  naturality := fun _ _ => rfl

/-- Composition of cubical-set morphisms (apply `first`, then `second`); naturality chains the two squares. -/
def CubicalMap.composeMap {sourceSet midSet targetSet : CubicalSet}
    (first : CubicalMap sourceSet midSet) (second : CubicalMap midSet targetSet) :
    CubicalMap sourceSet targetSet where
  component := fun dimension cube => second.component dimension (first.component dimension cube)
  naturality := fun reindex cube =>
    (second.naturality reindex (first.component _ cube)).trans
      (congrArg (second.component _) (first.naturality reindex cube))

/-- ★ **The category of cubical sets, cSet**, as a genuine `RawCategory` — the actual setting of the cubical
model.  As with `□`, all three laws hold DEFINITIONALLY (β/η on components + proof irrelevance of
naturality) — each `rfl`, NO `funext`. -/
def cubicalSetCategory : RawCategory where
  Object := CubicalSet
  Morphism := CubicalMap
  identity := CubicalMap.identityMap
  compose := CubicalMap.composeMap
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- The Yoneda embedding on objects: `[k] ↦ □[k]`. -/
def cubicalYonedaObject (dimensionK : Nat) : CubicalSet := representableCubicalSet dimensionK

/-- ★ The Yoneda embedding on morphisms: a cube map `[k] ⟶ [k']` induces the natural transformation
`□[k] ⟶ □[k']` by POSTCOMPOSITION.  Naturality holds by associativity of `CubeMap` composition (`rfl`). -/
def cubicalYonedaMorphism {dimensionK dimensionK' : Nat} (reindex : CubeMap dimensionK dimensionK') :
    CubicalMap (representableCubicalSet dimensionK) (representableCubicalSet dimensionK') where
  component := fun _ cube => CubeMap.composeMap cube reindex
  naturality := fun _ _ => rfl

/-- ★ Yoneda preserves identities — `よ(id) = id` — by `rfl`. -/
theorem cubicalYonedaMorphism_identity (dimensionK : Nat) :
    cubicalYonedaMorphism (CubeMap.identityMap dimensionK)
      = CubicalMap.identityMap (representableCubicalSet dimensionK) :=
  rfl

/-- ★ Yoneda preserves composition — `よ(g ∘ h) = よ(g) ∘ よ(h)` — by `rfl`.  Together with
`cubicalYonedaMorphism_identity` this is the FUNCTORIALITY of the Yoneda embedding `□ ⟶ cSet`. -/
theorem cubicalYonedaMorphism_compose {dimensionA dimensionB dimensionC : Nat}
    (first : CubeMap dimensionA dimensionB) (second : CubeMap dimensionB dimensionC) :
    cubicalYonedaMorphism (CubeMap.composeMap first second)
      = CubicalMap.composeMap (cubicalYonedaMorphism first) (cubicalYonedaMorphism second) :=
  rfl

/-! ## The model datum + honesty markers -/

/-- The context-side datum of the cubical model: the site `□` and the representable contexts. -/
structure CubicalModelData where
  /-- The site — the cube category `□`. -/
  site : RawCategory
  /-- The representable cubical sets `□[k]` (the basic contexts). -/
  representableContext : Nat → CubicalSet

/-- ★ The FX cubical-model datum: `□` as the site, the representables as the basic contexts. -/
def fxCubicalModel : CubicalModelData where
  site := cubeCategory
  representableContext := representableCubicalSet

/-- **Honesty marker.**  KAN FIBRANCY — the cubical composition/transport structure (`hcomp`/`transp`)
making display maps cubical Kan fibrations — is the deep semantic content (`×type`, the full model); not
shipped here.  `= false`. -/
def fxCubicalModel_hasKanFibrancy : Bool := false

/-- **Honesty marker.**  The GLUE TYPE — the `Glue` former by which univalence computes (CCHM) — is `×type`,
deferred to the type axis / `fib`.  `= false`. -/
def fxCubicalModel_hasGlueTypes : Bool := false

/-- **Honesty marker.**  The UNIVALENT UNIVERSE — the cubical universe of fibrant types with the
(computational) univalence equivalence — is `×type` and the full-model core, deferred.  `= false`. -/
def fxCubicalModel_hasUnivalentUniverse : Bool := false

/-! ## Smoke -/

/-- Smoke: in the representable `□[k]`, restriction along the identity is the identity. -/
theorem representableCubicalSet_restrictIdentity_smoke (dimensionK dimension : Nat)
    (cube : (representableCubicalSet dimensionK).cubes dimension) :
    (representableCubicalSet dimensionK).restrict (CubeMap.identityMap dimension) cube = cube :=
  (representableCubicalSet dimensionK).restrictIdentity dimension cube

end FX1Poly.Tier0
