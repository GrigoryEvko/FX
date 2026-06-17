import FX1Poly.Tier0.Mode.MultiplierStructureClass

/-! # mode-12 — the multiplier as a general endofunctor: unpointability + dimensional-splitness

`mode-2` classified a multiplier by its cube-ladder STRUCTURE CLASS (affine ⊏ cartesian ⊏ dedekind ⊏ deMorgan)
and deferred "the actual ENDOFUNCTOR … with the unpointability / dimensional-splitness criteria" to `mode-12`
(`fxMode_hasMultiplierEndofunctorRealization`).  This file realizes the multiplier as a general endofunctor and
ships those two Nuyts–Devriese criteria, with witnesses on both sides of each.

## What this file ships (each piece zero-axiom)

  * **`Multiplier`** — a multiplier as a general endofunctor on `Type`: `Apply` + `map` + the two functor laws
    (pointwise, so no funext).  Its DIMENSION is `Apply Unit` (the dimension's global points).
  * **the unpointability criterion** — `IsPointed` (`Nonempty (Apply Unit)`: the dimension has a global point)
    vs `IsUnpointable` (`Apply Unit → False`: no global point — the affine / nominal case).  The two are
    mutually exclusive (`not_pointed_and_unpointable`, choice-free).
  * **the dimensional-splitness criterion** — `SplitData` (a natural iso `Apply A ≃ A × dimension`: the
    multiplier IS product-with-the-dimension) and `IsDimensionallySplit`.
  * **witnesses for the combinations** — `identityMultiplier` (pointed + split), `voidMultiplier` (the void
    dimension: UNPOINTABLE + split — showing the two criteria are independent), `functionMultiplier` (`Bool → -`:
    pointed, a genuinely non-trivial endofunctor).

## What is DEFERRED (markers)

  * each `mode-2` cube class realized as a concrete endofunctor WITH its diagonal / connection / reversal
    OPERATIONS (`hasPerClassEndofunctorRealization`);
  * the PROOF that a concrete multiplier is NOT dimensionally split (the `Bool → -` cardinality argument)
    (`hasNonSplitMultiplierProof`);
  * the genuine PRESHEAF-category multiplier with the full Nuyts axioms (cancellative / semicartesian /
    quantifiable …), beyond the `Type`-endofunctor model here (`hasPresheafMultiplierModel`).

This discharges the criteria half of `mode-2`'s `fxMode_hasMultiplierEndofunctorRealization` deferral.
Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The multiplier as a general endofunctor -/

/-- A **multiplier** as a general endofunctor on `Type` — the fresh-dimension shape a modal dimension is built
on, presented as `Apply` + `map` with the two functor laws (pointwise, free of choice and funext). -/
structure Multiplier where
  /-- The underlying endofunctor. -/
  Apply : Type → Type
  /-- Functorial action on maps. -/
  map : {A B : Type} → (A → B) → Apply A → Apply B
  /-- Functor law: `map id = id` (pointwise). -/
  map_id : {A : Type} → (value : Apply A) → map (fun element => element) value = value
  /-- Functor law: `map (g ∘ f) = map g ∘ map f` (pointwise). -/
  map_comp : {A B C : Type} → (firstMap : A → B) → (secondMap : B → C) → (value : Apply A) →
    map (fun element => secondMap (firstMap element)) value = map secondMap (map firstMap value)

/-- The **dimension** of a multiplier — its global points, `Apply Unit` (the terminal applied). -/
abbrev Multiplier.dimension (multiplier : Multiplier) : Type := multiplier.Apply Unit

/-! ## The unpointability criterion -/

/-- A multiplier is **pointed** when its dimension has a global point. -/
def Multiplier.IsPointed (multiplier : Multiplier) : Prop := Nonempty multiplier.dimension

/-- A multiplier is **unpointable** when its dimension has NO global point — the affine / nominal case. -/
def Multiplier.IsUnpointable (multiplier : Multiplier) : Prop := multiplier.dimension → False

/-- ★ Pointed and unpointable are mutually exclusive — the criterion is a genuine dichotomy.  Choice-free
(`cases` on `Nonempty`, not `Nonempty.some`). -/
theorem Multiplier.not_pointed_and_unpointable (multiplier : Multiplier)
    (pointed : multiplier.IsPointed) (unpointable : multiplier.IsUnpointable) : False := by
  cases pointed with
  | intro dimensionPoint => exact unpointable dimensionPoint

/-! ## The dimensional-splitness criterion -/

/-- **Split data** for a multiplier — a natural isomorphism `Apply A ≃ A × dimension`, witnessing that the
multiplier IS product-with-the-dimension (`(- × 𝕦)`).  This is "dimensionally split": the dimension factors
out as a product. -/
structure Multiplier.SplitData (multiplier : Multiplier) where
  /-- Split a value into its dimension-free part and a dimension point. -/
  split : {A : Type} → multiplier.Apply A → A × multiplier.dimension
  /-- Reassemble. -/
  unsplit : {A : Type} → A × multiplier.dimension → multiplier.Apply A
  /-- The iso, one direction. -/
  split_unsplit : {A : Type} → (pair : A × multiplier.dimension) → split (unsplit pair) = pair
  /-- The iso, the other direction. -/
  unsplit_split : {A : Type} → (value : multiplier.Apply A) → unsplit (split value) = value

/-- A multiplier is **dimensionally split** when it carries split data. -/
def Multiplier.IsDimensionallySplit (multiplier : Multiplier) : Prop := Nonempty multiplier.SplitData

/-! ## Witnesses for the combinations -/

/-- The **identity** multiplier — the trivial (single-point) dimension. -/
def identityMultiplier : Multiplier where
  Apply := fun carrier => carrier
  map := fun mapFunction value => mapFunction value
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl

/-- The identity multiplier is POINTED (its dimension is `Unit`). -/
theorem identityMultiplier_isPointed : identityMultiplier.IsPointed := ⟨()⟩

/-- The identity multiplier is dimensionally SPLIT (`A ≃ A × Unit`). -/
def identityMultiplier_splitData : identityMultiplier.SplitData where
  split := fun value => (value, ())
  unsplit := fun pair => pair.1
  split_unsplit := fun _pair => rfl
  unsplit_split := fun _value => rfl

theorem identityMultiplier_isSplit : identityMultiplier.IsDimensionallySplit :=
  ⟨identityMultiplier_splitData⟩

/-- The **void-dimension** multiplier — the constantly-`Empty` endofunctor.  Its dimension is `Empty`: it is
UNPOINTABLE (the witness that unpointability is realizable) yet still SPLIT, showing the two criteria are
INDEPENDENT. -/
def voidMultiplier : Multiplier where
  Apply := fun _carrier => Empty
  map := fun _mapFunction value => value
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl

/-- The void multiplier is UNPOINTABLE. -/
theorem voidMultiplier_isUnpointable : voidMultiplier.IsUnpointable := Empty.elim

/-- The void multiplier is dimensionally SPLIT (`Empty ≃ A × Empty`) — so unpointable-and-split occurs. -/
def voidMultiplier_splitData : voidMultiplier.SplitData where
  split := fun value => value.elim
  unsplit := fun pair => pair.2
  split_unsplit := fun pair => pair.2.elim
  unsplit_split := fun value => value.elim

theorem voidMultiplier_isSplit : voidMultiplier.IsDimensionallySplit :=
  ⟨voidMultiplier_splitData⟩

/-- A genuinely non-trivial multiplier — `Apply A := Bool → A` (a two-point dimension's function space).  It is
POINTED (the constant function into `Bool → Unit`); whether it is split is the deferred negative. -/
def functionMultiplier : Multiplier where
  Apply := fun carrier => Bool → carrier
  map := fun mapFunction value => fun bit => mapFunction (value bit)
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl

/-- The function multiplier is POINTED. -/
theorem functionMultiplier_isPointed : functionMultiplier.IsPointed := ⟨fun _bit => ()⟩

/-! ## Honesty markers -/

/-- **Honesty marker.**  Each `mode-2` cube class (affine / cartesian / dedekind / deMorgan) realized as a
concrete endofunctor carrying its diagonal / connection / reversal OPERATIONS is deferred; this file ships the
endofunctor + the pointed / split criteria.  `= false`. -/
def fxMode_hasPerClassEndofunctorRealization : Bool := false

/-- **Honesty marker.**  The PROOF that a concrete multiplier is NOT dimensionally split (e.g. `Bool → -` is not
`(- × dimension)`, the cardinality argument) is deferred; this file ships the split criterion + the positive
witnesses.  `= false`. -/
def fxMode_hasNonSplitMultiplierProof : Bool := false

/-- **Honesty marker.**  The genuine PRESHEAF-category multiplier with the full Nuyts axioms (cancellative /
semicartesian / quantifiable …), beyond the `Type`-endofunctor model here, is deferred.  `= false`. -/
def fxMode_hasPresheafMultiplierModel : Bool := false

end FX1Poly.Tier0
