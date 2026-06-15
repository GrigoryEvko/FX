import FX1Poly.Tier0.Context.RepresentableMapCategory

/-! # context-13 — the simplicial model (Kapulkin–Lumsdaine), context-side residue

`context-13` is the SIMPLICIAL MODEL rung: Kapulkin–Lumsdaine's construction of a model of univalent
foundations in simplicial sets (after Voevodsky).  The model interprets contexts and types as KAN
simplicial sets, display maps as KAN FIBRATIONS, and exhibits a UNIVALENT universe.

## What is context-side here, and what is deferred

The model is built over a SITE — the simplex category Δ — and its presheaves (simplicial sets).  The site
and the presheaf structure are pure base / category-of-contexts data; that is the CONTEXT-SIDE residue
shipped here, in full and zero-axiom:

  * **`simplexCategory`** — Δ as a genuine `RawCategory`: objects are dimensions `[n]` (the `(n+1)`-element
    ordinal), morphisms are MONOTONE maps.  The three category laws hold DEFINITIONALLY — associativity by
    β (function composition is associative on the nose), the identity laws by η plus definitional proof
    irrelevance of the monotonicity field — so each is `rfl`, with NO appeal to `funext`.
  * the simplicial GENERATORS — the cofaces `δ₀`, `δ_last` and the codegeneracy `σ₀` as concrete monotone
    maps, plus a cosimplicial identity (`σ₀ ∘ δ₀ = id`) as a witness.
  * **`SimplicialSet`** — a presheaf on Δ (the model's contexts/types), with the representable simplicial
    set `Δ[k]` (Yoneda) as a genuine witness whose functor laws hold by `rfl`.
  * **`fxSimplicialModel`** — the model datum: the site + the representable contexts.

DEFERRED (honestly NOT here, the `×type` / full-model core, recorded by the `= false` markers):
  * KAN FIBRANCY (the horn-filling structure making the display maps Kan fibrations) —
    `hasKanFibrancy = false`;
  * the UNIVALENT UNIVERSE (Voevodsky's universe of Kan complexes + the univalence equivalence) —
    `hasUnivalentUniverse = false`.  These are the deep semantic content (fibrancy + univalence), `×type`
    and the full model, deferred to the type axis / `fib`.

Reference: Kapulkin & Lumsdaine, "The Simplicial Model of Univalent Foundations (after Voevodsky)",
J. Eur. Math. Soc. 23 (2021) (arXiv:1211.2851).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## The simplex category Δ -/

/-- A morphism `[source] ⟶ [target]` of the simplex category Δ: a MONOTONE map between the finite ordinals
`[source] = {0, …, source}` and `[target] = {0, …, target}`.  The monotonicity proof is a `Prop`, so two
`SimplexMap`s are equal exactly when their underlying functions are — which is what lets the category laws
hold definitionally (no `funext`). -/
structure SimplexMap (source target : Nat) where
  /-- The underlying map on vertices. -/
  onElement : Fin (source + 1) → Fin (target + 1)
  /-- The map is monotone (order-preserving) — what makes it a morphism of Δ. -/
  monotonicity : ∀ (lower upper : Fin (source + 1)), lower ≤ upper → onElement lower ≤ onElement upper

/-- The identity simplex map `[n] ⟶ [n]`. -/
def SimplexMap.identityMap (dimension : Nat) : SimplexMap dimension dimension where
  onElement := fun position => position
  monotonicity := fun _ _ hle => hle

/-- Composition of simplex maps `[a] ⟶ [b] ⟶ [c]` (apply `first`, then `second`). -/
def SimplexMap.composeMap {dimensionA dimensionB dimensionC : Nat}
    (first : SimplexMap dimensionA dimensionB) (second : SimplexMap dimensionB dimensionC) :
    SimplexMap dimensionA dimensionC where
  onElement := fun position => second.onElement (first.onElement position)
  monotonicity := fun lower upper hle =>
    second.monotonicity _ _ (first.monotonicity lower upper hle)

/-- ★ **The simplex category Δ** as a genuine `RawCategory`.  Objects are dimensions (the finite ordinals),
morphisms are monotone maps.  All three category laws hold DEFINITIONALLY: associativity by β (function
composition), the identity laws by η plus definitional proof irrelevance of the monotonicity field — so
`rfl` discharges each, with NO appeal to `funext`. -/
def simplexCategory : RawCategory where
  Object := Nat
  Morphism := SimplexMap
  identity := SimplexMap.identityMap
  compose := SimplexMap.composeMap
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-! ## The simplicial generators (cofaces and a codegeneracy) -/

/-- The coface `δ₀ : [n] ⟶ [n+1]` — the monotone injection skipping vertex `0` (shift up by one). -/
def SimplexMap.coface0 (dimension : Nat) : SimplexMap dimension (dimension + 1) where
  onElement := fun position => ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩
  monotonicity := fun _ _ hle => Nat.succ_le_succ hle

/-- The coface `δ_last : [n] ⟶ [n+1]` — the monotone injection skipping the top vertex (the inclusion). -/
def SimplexMap.cofaceLast (dimension : Nat) : SimplexMap dimension (dimension + 1) where
  onElement := fun position => ⟨position.val, Nat.lt_succ_of_lt position.isLt⟩
  monotonicity := fun _ _ hle => hle

/-- The codegeneracy `σ₀ : [n+1] ⟶ [n]` — the monotone surjection collapsing vertices `0` and `1`
(subtract one, truncated). -/
def SimplexMap.codegeneracy0 (dimension : Nat) : SimplexMap (dimension + 1) dimension where
  onElement := fun position =>
    ⟨position.val - 1,
      Nat.lt_of_le_of_lt (Nat.sub_le_sub_right (Nat.le_of_lt_succ position.isLt) 1)
        (Nat.lt_succ_self dimension)⟩
  monotonicity := fun _ _ hle => Nat.sub_le_sub_right hle 1

/-- ★ A cosimplicial identity: the codegeneracy `σ₀` cancels the coface `δ₀` — `σ₀ ∘ δ₀ = id`.  Stated
POINTWISE (so funext-free): at every vertex, `(x + 1) - 1 = x`. -/
theorem SimplexMap.codegeneracy0_coface0 (dimension : Nat) (position : Fin (dimension + 1)) :
    (SimplexMap.composeMap (SimplexMap.coface0 dimension)
        (SimplexMap.codegeneracy0 dimension)).onElement position
      = (SimplexMap.identityMap dimension).onElement position :=
  Fin.ext rfl

/-! ## Simplicial sets (presheaves on Δ) -/

/-- A **simplicial set** — a presheaf on Δ.  Each dimension `n` carries a type of `n`-simplices, and each
simplex map `f : [a] ⟶ [b]` acts CONTRAVARIANTLY (restriction) on simplices, functorially.  The
functoriality laws are stated POINTWISE — equalities IN a simplex type, not between functions — so they are
funext-free to state and to inhabit. -/
structure SimplicialSet where
  /-- The `n`-simplices. -/
  simplices : Nat → Type
  /-- Contravariant restriction along a simplex map. -/
  restrict : {source target : Nat} → SimplexMap source target → simplices target → simplices source
  /-- Restriction along the identity is the identity (pointwise). -/
  restrictIdentity : ∀ (dimension : Nat) (simplex : simplices dimension),
    restrict (SimplexMap.identityMap dimension) simplex = simplex
  /-- Restriction is contravariantly functorial (pointwise). -/
  restrictCompose : ∀ {dimensionA dimensionB dimensionC : Nat}
    (first : SimplexMap dimensionA dimensionB) (second : SimplexMap dimensionB dimensionC)
    (simplex : simplices dimensionC),
    restrict (SimplexMap.composeMap first second) simplex = restrict first (restrict second simplex)

/-- ★ The representable simplicial set `Δ[k] = Hom_Δ(−, [k])` (Yoneda) — a genuine simplicial set whose
restriction is precomposition, with both functor laws holding by `rfl` (the category laws of Δ). -/
def representableSimplicialSet (dimensionK : Nat) : SimplicialSet where
  simplices := fun dimension => SimplexMap dimension dimensionK
  restrict := fun reindex simplex => SimplexMap.composeMap reindex simplex
  restrictIdentity := fun _ _ => rfl
  restrictCompose := fun _ _ _ => rfl

/-! ## The model datum + honesty markers -/

/-- The context-side datum of the simplicial model: the site Δ and the representable contexts. -/
structure SimplicialModelData where
  /-- The site — the simplex category Δ. -/
  site : RawCategory
  /-- The representable simplicial sets `Δ[k]` (the basic contexts). -/
  representableContext : Nat → SimplicialSet

/-- ★ The FX simplicial-model datum: Δ as the site, the representables as the basic contexts. -/
def fxSimplicialModel : SimplicialModelData where
  site := simplexCategory
  representableContext := representableSimplicialSet

/-- **Honesty marker.**  KAN FIBRANCY — the horn-filling structure making the display maps Kan fibrations —
is the deep semantic content (`×type`, the full model); not shipped here.  `= false`. -/
def fxSimplicialModel_hasKanFibrancy : Bool := false

/-- **Honesty marker.**  The UNIVALENT UNIVERSE — Voevodsky's universe of Kan complexes together with the
univalence equivalence — is `×type` and the full-model core, deferred to the type axis / `fib`.
`= false`. -/
def fxSimplicialModel_hasUnivalentUniverse : Bool := false

/-! ## Smoke -/

/-- Smoke: in the representable `Δ[k]`, restriction along the identity is the identity. -/
theorem representableSimplicialSet_restrictIdentity_smoke (dimensionK dimension : Nat)
    (simplex : (representableSimplicialSet dimensionK).simplices dimension) :
    (representableSimplicialSet dimensionK).restrict (SimplexMap.identityMap dimension) simplex
      = simplex :=
  (representableSimplicialSet dimensionK).restrictIdentity dimension simplex

end FX1Poly.Tier0
