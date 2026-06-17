import FX1Poly.Tier0.Mode.Mode

/-! # mode-17 — the mode theory as a 2-monad + the bi-initial model

A type-theoretic DOCTRINE is presented as a (strict) **2-monad** `T` on a 2-category; its (strict) ALGEBRAS are
the structured categories the doctrine describes, and the SYNTACTIC model is the BI-INITIAL one — the free
algebra on the initial object.  The mode theory of MTT is itself such a 2-monadic doctrine.  `mode-17` ships the
2-monad / algebra / free-algebra machinery and the bi-initial model, at the strict toy level (`Type`-endofunctors
as the "Cat"), funext-free.

## The genuine content — the free-algebra universal property (the Eilenberg–Moore adjunction)

For a 2-monad `T`, the FREE algebra `(T X, μ)` has the universal property `AlgMor(Free X, M) ≅ (X → M.Carrier)`
(the EM adjunction `Free ⊣ Forget`).  BOTH round trips are FUNEXT-FREE: they manipulate a single function via
`map_comp` and the monad laws, never comparing two distinct functions under `map`.  Specializing to the initial
type `Empty` (initial in `Type`), `Free Empty` is the BI-INITIAL algebra: it has a (constructed) morphism to
every algebra.

## What this file ships (each piece zero-axiom)

  * **`TwoMonad`** — a strict 2-monad on `Type`: `Apply` + `map` + the functor laws + `unit` (η) + `mult` (μ) +
    η/μ naturality + the three monad laws (left/right unit, associativity), all pointwise (no funext).
    `identityTwoMonad` + `readerTwoMonad` (`E → -`, the genuine NON-degenerate witness, all laws by `rfl`).
  * **`TwoMonad.Algebra`** / **`AlgebraMorphism`** + **`freeAlgebra`** (the free `T`-algebra `(T X, μ)`).
  * **`freeHomForward`** / **`freeHomBackward`** + **`freeHom_backward_forward`** / **`freeHom_forward_backward`**
    — the EM adjunction HOM-ISO (the free algebra's universal property), funext-free.
  * **`biInitialAlgebra`** (`Free Empty`) + **`biInitialMorphism`** — the bi-initial model + its morphism to
    every algebra (existence).

## What is DEFERRED (markers)

  * the SPECIFIC mode-theory 2-monad whose strict algebras ARE mode theories / strict 2-categories
    (`hasModeTheoryTwoMonad`);
  * the STRICT on-the-nose uniqueness of the bi-initial morphism (needs funext — `Empty`'s initiality as a strict
    equality; the universal property `freeHom_backward_forward` captures the determinacy funext-free)
    (`hasStrictBiInitialUniqueness`);
  * the PSEUDO / lax algebras + pseudo-morphisms + the non-trivial 2-cells of the genuine BICATEGORY of models
    (`hasPseudoAlgebras`);
  * the kernel's syntactic-model-as-initial-algebra connection (cross-axis, `fib`)
    (`hasKernelTwoMonadConnection`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The 2-monad -/

/-- A **strict 2-monad** on `Type` (the toy "Cat") — an endofunctor `Apply` with `map` and the functor laws,
a unit `unit` (η) and multiplication `mult` (μ), the naturality of η / μ, and the three monad laws (left unit,
right unit, associativity).  All laws are stated POINTWISE, so the structure is funext-free. -/
structure TwoMonad where
  /-- The underlying endofunctor. -/
  Apply : Type → Type
  /-- Functorial action on maps. -/
  map : {A B : Type} → (A → B) → Apply A → Apply B
  /-- Functor law `map id = id` (pointwise). -/
  map_id : {A : Type} → (value : Apply A) → map (fun element => element) value = value
  /-- Functor law `map (g ∘ f) = map g ∘ map f` (pointwise). -/
  map_comp : {A B C : Type} → (firstMap : A → B) → (secondMap : B → C) → (value : Apply A) →
    map (fun element => secondMap (firstMap element)) value = map secondMap (map firstMap value)
  /-- The unit `η : A → T A`. -/
  unit : {A : Type} → A → Apply A
  /-- The multiplication `μ : T (T A) → T A`. -/
  mult : {A : Type} → Apply (Apply A) → Apply A
  /-- Naturality of the unit. -/
  unit_natural : {A B : Type} → (mapFunction : A → B) → (value : A) →
    map mapFunction (unit value) = unit (mapFunction value)
  /-- Naturality of the multiplication. -/
  mult_natural : {A B : Type} → (mapFunction : A → B) → (value : Apply (Apply A)) →
    map mapFunction (mult value) = mult (map (map mapFunction) value)
  /-- The left-unit monad law `μ ∘ η_T = id`. -/
  mult_unit : {A : Type} → (value : Apply A) → mult (unit value) = value
  /-- The right-unit monad law `μ ∘ T η = id`. -/
  mult_map_unit : {A : Type} → (value : Apply A) → mult (map unit value) = value
  /-- The associativity monad law `μ ∘ μ_T = μ ∘ T μ`. -/
  mult_mult : {A : Type} → (value : Apply (Apply (Apply A))) → mult (mult value) = mult (map mult value)

/-- The **identity** 2-monad `Id` — every law holds by `rfl`. -/
def identityTwoMonad : TwoMonad where
  Apply := fun carrier => carrier
  map := fun mapFunction value => mapFunction value
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl
  unit := fun value => value
  mult := fun value => value
  unit_natural := fun _mapFunction _value => rfl
  mult_natural := fun _mapFunction _value => rfl
  mult_unit := fun _value => rfl
  mult_map_unit := fun _value => rfl
  mult_mult := fun _value => rfl

/-- ★ The **reader** 2-monad `E → -` over a fixed shape `Shape` — the genuine NON-degenerate witness: every
2-monad law holds by `rfl` (function eta), yet for `Shape` with ≥ 2 elements it is a non-trivial doctrine. -/
def readerTwoMonad (Shape : Type) : TwoMonad where
  Apply := fun carrier => Shape → carrier
  map := fun mapFunction value => fun shapePoint => mapFunction (value shapePoint)
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl
  unit := fun value => fun _shapePoint => value
  mult := fun value => fun shapePoint => value shapePoint shapePoint
  unit_natural := fun _mapFunction _value => rfl
  mult_natural := fun _mapFunction _value => rfl
  mult_unit := fun _value => rfl
  mult_map_unit := fun _value => rfl
  mult_mult := fun _value => rfl

/-! ## Algebras + morphisms -/

/-- A **`T`-algebra** (a model of the doctrine) — a carrier with a structure map `act : T Carrier → Carrier`
satisfying the unit and multiplication algebra laws (pointwise). -/
structure TwoMonad.Algebra (monad : TwoMonad) where
  /-- The carrier. -/
  Carrier : Type
  /-- The structure map. -/
  act : monad.Apply Carrier → Carrier
  /-- The unit algebra law `act ∘ η = id`. -/
  act_unit : (value : Carrier) → act (monad.unit value) = value
  /-- The multiplication algebra law `act ∘ μ = act ∘ T act`. -/
  act_mult : (value : monad.Apply (monad.Apply Carrier)) →
    act (monad.mult value) = act (monad.map act value)

/-- A **`T`-algebra morphism** — a carrier map commuting with the structure maps. -/
structure TwoMonad.AlgebraMorphism (monad : TwoMonad) (source target : monad.Algebra) where
  /-- The underlying carrier map. -/
  carrierMap : source.Carrier → target.Carrier
  /-- Commutation with the structure maps. -/
  commutes : (value : monad.Apply source.Carrier) →
    carrierMap (source.act value) = target.act (monad.map carrierMap value)

/-- The **free `T`-algebra** on a base type — `(T Base, μ)`.  The free model; its `act` is `mult`, and the
algebra laws are the monad's right-unit and associativity laws. -/
def TwoMonad.freeAlgebra (monad : TwoMonad) (Base : Type) : monad.Algebra where
  Carrier := monad.Apply Base
  act := fun value => monad.mult value
  act_unit := fun value => monad.mult_unit value
  act_mult := fun value => monad.mult_mult value

/-! ## The free-algebra universal property (the Eilenberg–Moore adjunction hom-iso) -/

/-- The FORWARD hom-transposition — restrict an algebra morphism `Free Base → M` along the unit, giving a base
map `Base → M.Carrier`. -/
def TwoMonad.freeHomForward {monad : TwoMonad} {Base : Type} {target : monad.Algebra}
    (morphism : monad.AlgebraMorphism (monad.freeAlgebra Base) target) : Base → target.Carrier :=
  fun base => morphism.carrierMap (monad.unit base)

/-- The BACKWARD hom-transposition — a base map `Base → M.Carrier` extends to the algebra morphism
`Free Base → M` whose carrier map is `act ∘ T(baseMap)`.  The `commutes` proof is funext-free (`mult`-naturality
+ the algebra law + `map_comp`). -/
def TwoMonad.freeHomBackward {monad : TwoMonad} {Base : Type} {target : monad.Algebra}
    (baseMap : Base → target.Carrier) : monad.AlgebraMorphism (monad.freeAlgebra Base) target where
  carrierMap := fun freeElement => target.act (monad.map baseMap freeElement)
  commutes := fun value => by
    show target.act (monad.map baseMap (monad.mult value))
      = target.act (monad.map (fun freeElement => target.act (monad.map baseMap freeElement)) value)
    rw [monad.mult_natural baseMap value, target.act_mult (monad.map (monad.map baseMap) value),
      ← monad.map_comp (monad.map baseMap) target.act value]

/-- ★ The hom-iso, one round trip — `backward (forward φ) = φ` (pointwise).  Every algebra morphism out of a
free algebra is RECONSTRUCTED from its restriction along the unit.  Funext-free: `map_comp` + the morphism's
`commutes` + the right-unit law. -/
theorem TwoMonad.freeHom_backward_forward {monad : TwoMonad} {Base : Type} {target : monad.Algebra}
    (morphism : monad.AlgebraMorphism (monad.freeAlgebra Base) target) (element : monad.Apply Base) :
    (monad.freeHomBackward (monad.freeHomForward morphism)).carrierMap element
      = morphism.carrierMap element := by
  have reconstruct : (monad.freeHomBackward (monad.freeHomForward morphism)).carrierMap element
      = morphism.carrierMap (monad.mult (monad.map monad.unit element)) := by
    show target.act (monad.map (fun base => morphism.carrierMap (monad.unit base)) element)
      = morphism.carrierMap (monad.mult (monad.map monad.unit element))
    rw [monad.map_comp monad.unit morphism.carrierMap element]
    exact (morphism.commutes (monad.map monad.unit element)).symm
  rw [reconstruct, monad.mult_map_unit element]

/-- ★ The hom-iso, the other round trip — `forward (backward h) = h` (pointwise).  Funext-free: the unit's
naturality + the algebra's unit law. -/
theorem TwoMonad.freeHom_forward_backward {monad : TwoMonad} {Base : Type} {target : monad.Algebra}
    (baseMap : Base → target.Carrier) (base : Base) :
    monad.freeHomForward (monad.freeHomBackward baseMap) base = baseMap base := by
  show target.act (monad.map baseMap (monad.unit base)) = baseMap base
  rw [monad.unit_natural baseMap base, target.act_unit (baseMap base)]

/-! ## The bi-initial model -/

/-- The **bi-initial algebra** — the free algebra on the initial type `Empty` (`Empty` is initial in `Type`).
By the free-algebra universal property, `AlgMor(biInitial, M) ≅ (Empty → M.Carrier)`, the singleton — so it is
the bi-initial model of the doctrine. -/
def TwoMonad.biInitialAlgebra (monad : TwoMonad) : monad.Algebra := monad.freeAlgebra Empty

/-- ★ The **bi-initial morphism** — the (constructed) algebra morphism from the bi-initial algebra to EVERY
algebra, the transpose of the unique map `Empty → M.Carrier`.  Existence of the morphism into every model. -/
def TwoMonad.biInitialMorphism (monad : TwoMonad) (target : monad.Algebra) :
    monad.AlgebraMorphism monad.biInitialAlgebra target :=
  monad.freeHomBackward (fun emptyElement => emptyElement.elim)

/-- The bi-initial algebra's carrier is `T Empty`. -/
theorem TwoMonad.biInitialAlgebra_carrier (monad : TwoMonad) :
    monad.biInitialAlgebra.Carrier = monad.Apply Empty := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The SPECIFIC mode-theory 2-monad — the one whose strict algebras ARE mode theories
(strict 2-categories), realizing `mode-1`'s `RawTwoCategory` as the `Algebra`s of a concrete `TwoMonad` — needs
the 2-category-of-2-categories structure, deferred.  `= false`. -/
def fxMode_hasModeTheoryTwoMonad : Bool := false

/-- **Honesty marker.**  The STRICT on-the-nose UNIQUENESS of the bi-initial morphism (every algebra morphism out
of `biInitial` equals `biInitialMorphism`) needs `funext` (the on-the-nose initiality of `Empty` in `Type`;
`funext` is banned as it pulls `Quot.sound`).  The universal property `freeHom_backward_forward` captures the
DETERMINACY funext-free; the genuine bicategorical formulation is up to a unique invertible 2-cell.  `= false`. -/
def fxMode_hasStrictBiInitialUniqueness : Bool := false

/-- **Honesty marker.**  The PSEUDO / lax algebras + pseudo-morphisms + the non-trivial 2-cells of the genuine
BICATEGORY of models (beyond the strict 2-monad / strict-algebra toy here) are deferred.  `= false`. -/
def fxMode_hasPseudoAlgebras : Bool := false

/-- **Honesty marker.**  The connection to the kernel's syntactic-model-as-initial-algebra (the syntax IS the
bi-initial `TwoMonad` algebra) is cross-axis (`fib`), deferred.  `= false`. -/
def fxMode_hasKernelTwoMonadConnection : Bool := false

end FX1Poly.Tier0
