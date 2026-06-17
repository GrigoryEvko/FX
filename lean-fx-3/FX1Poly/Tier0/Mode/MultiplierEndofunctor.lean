import FX1Poly.Tier0.Mode.MultiplierStructureClass

/-! # mode-12 — the multiplier as a general endofunctor: unpointability + dimensional-splitness

`mode-2` classified a multiplier by its cube-ladder STRUCTURE CLASS (affine ⊏ cartesian ⊏ dedekind ⊏ deMorgan)
and deferred "the actual ENDOFUNCTOR … with the unpointability / dimensional-splitness criteria" to `mode-12`
(`fxMode_hasMultiplierEndofunctorRealization`).  This file realizes the multiplier as a general endofunctor and
ships those two Nuyts–Devriese criteria, BOTH sides of BOTH: a pointed AND an unpointable multiplier, and a
SPLIT AND a NOT-split one (`squareMultiplier_not_split`, the cardinality / pigeonhole argument).  It also
realizes the cube classes over the interval `𝕀 = Bool` with their diagonal / connection / reversal operations.

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

## Also shipped

  * the NOT-split negative (`squareMultiplier_not_split`) — discharging `hasNonSplitMultiplierProof = true`;
  * the cube classes realized over the interval `𝕀` (`intervalMultiplier` + the operations + their laws) —
    `hasPerClassEndofunctorRealization` now scoped to the strict per-class typed gating.

## What is DEFERRED (markers)

  * the STRICT per-class typed gating (each class as a separate endofunctor with EXACTLY its operations) + the
    genuine cube-category presheaf (`hasPerClassEndofunctorRealization`);
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

/-! ## The NOT-split negative — a concrete non-split multiplier -/

/-- A genuinely non-trivial CARTESIAN multiplier — the "square" `Apply A := A × A` (the diagonal endofunctor).
Its dimension is `Unit × Unit` (a subsingleton).  POINTED, and the canonical NOT-split witness. -/
def squareMultiplier : Multiplier where
  Apply := fun carrier => carrier × carrier
  map := fun mapFunction value => (mapFunction value.1, mapFunction value.2)
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl

/-- The square multiplier is POINTED. -/
theorem squareMultiplier_isPointed : squareMultiplier.IsPointed := ⟨((), ())⟩

/-- The dimension `Unit × Unit` is a subsingleton — funext-free, by destructuring and casing each `Unit`
component (every value is `((), ())`). -/
theorem unitProd_subsingleton (firstPair secondPair : Unit × Unit) : firstPair = secondPair := by
  obtain ⟨firstLeft, firstRight⟩ := firstPair
  obtain ⟨secondLeft, secondRight⟩ := secondPair
  cases firstLeft; cases firstRight; cases secondLeft; cases secondRight; rfl

/-- Pigeonhole on `Bool`: from `a ≠ b` and `a ≠ c`, the remaining two agree (both `= ¬a`). -/
theorem bool_eq_of_ne_ne {first second third : Bool} (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third) : second = third := by
  cases first <;> cases second <;> cases third <;>
    first
      | rfl
      | exact absurd rfl firstNeSecond
      | exact absurd rfl firstNeThird

/-- ★ **The square multiplier is NOT dimensionally split** — the diagonal `(- × -)` is not `(- × dimension)`.
The cardinality / pigeonhole argument: a split would make the first projection `(Bool × Bool) → Bool` injective
(the second component lands in the subsingleton dimension `Unit × Unit`), but `(false,false)`, `(true,false)`,
`(false,true)` are pairwise distinct, so their three first-projections would be pairwise-distinct `Bool`s —
impossible.  Discharges the not-split NEGATIVE (the same argument applies to `Bool → -`). -/
theorem squareMultiplier_not_split : ¬ squareMultiplier.IsDimensionallySplit := by
  intro splitNonempty
  cases splitNonempty with
  | intro splitData =>
    have firstProj_inj : ∀ (firstPair secondPair : Bool × Bool),
        (splitData.split firstPair).1 = (splitData.split secondPair).1 → firstPair = secondPair := by
      intro firstPair secondPair projEq
      have secondEq : (splitData.split firstPair).2 = (splitData.split secondPair).2 :=
        unitProd_subsingleton _ _
      have splitEq : splitData.split firstPair = splitData.split secondPair := Prod.ext projEq secondEq
      have reassemble := congrArg splitData.unsplit splitEq
      rwa [splitData.unsplit_split, splitData.unsplit_split] at reassemble
    have proj_a_ne_b : (splitData.split (false, false)).1 ≠ (splitData.split (true, false)).1 :=
      fun projEq => (fun pairEq => Bool.noConfusion (congrArg Prod.fst pairEq)) (firstProj_inj _ _ projEq)
    have proj_a_ne_c : (splitData.split (false, false)).1 ≠ (splitData.split (false, true)).1 :=
      fun projEq => (fun pairEq => Bool.noConfusion (congrArg Prod.snd pairEq)) (firstProj_inj _ _ projEq)
    have proj_b_ne_c : (splitData.split (true, false)).1 ≠ (splitData.split (false, true)).1 :=
      fun projEq => (fun pairEq => Bool.noConfusion (congrArg Prod.fst pairEq)) (firstProj_inj _ _ projEq)
    exact proj_b_ne_c (bool_eq_of_ne_ne proj_a_ne_b proj_a_ne_c)

/-! ## Per-class realization — the cube interval endofunctor + its operations

The four `mode-2` cube classes are realized over the 2-point interval `𝕀 = Bool` ({0, 1}): the shared
endofunctor is `(- × 𝕀)`, and the classes DIFFER by the operations on `𝕀` each is equipped with — the cartesian
DIAGONAL, the Dedekind CONNECTIONS (∧ / ∨), the De Morgan REVERSAL (¬) — with their defining laws (all by
finite case analysis, zero-axiom). -/

/-- The 2-point interval `𝕀 = Bool` ({0, 1}) — the cube multiplier's dimension. -/
abbrev cubeInterval : Type := Bool

/-- The **interval-product multiplier** `(- × 𝕀)` — the cube endofunctor common to all four cube classes; what
distinguishes the classes is the OPERATIONS on `𝕀` each is equipped with. -/
def intervalMultiplier : Multiplier where
  Apply := fun carrier => carrier × cubeInterval
  map := fun mapFunction value => (mapFunction value.1, value.2)
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl

/-- The interval multiplier is POINTED (the interval has the endpoint `0`). -/
theorem intervalMultiplier_isPointed : intervalMultiplier.IsPointed := ⟨((), false)⟩

/-- The CARTESIAN operation — the diagonal `𝕀 → 𝕀 × 𝕀` (the contraction the cartesian class adds). -/
def intervalDiagonal : cubeInterval → cubeInterval × cubeInterval := fun point => (point, point)

/-- The DEDEKIND connection `∧` (the monotone meet) on `𝕀`. -/
def intervalMeet : cubeInterval → cubeInterval → cubeInterval := fun first second => first && second

/-- The DEDEKIND connection `∨` (the monotone join) on `𝕀`. -/
def intervalJoin : cubeInterval → cubeInterval → cubeInterval := fun first second => first || second

/-- The DE MORGAN operation — the reversal `¬` on `𝕀`. -/
def intervalReversal : cubeInterval → cubeInterval := fun point => !point

/-- The contraction law: meeting the diagonal recovers the point (`b ∧ b = b`). -/
theorem intervalMeet_diagonal (point : cubeInterval) :
    intervalMeet (intervalDiagonal point).1 (intervalDiagonal point).2 = point := by
  cases point <;> rfl

/-- The connections are commutative (Dedekind). -/
theorem intervalMeet_comm (first second : cubeInterval) :
    intervalMeet first second = intervalMeet second first := by cases first <;> cases second <;> rfl

/-- ★ The DE MORGAN law — reversal swaps the connections: `¬(a ∧ b) = (¬a) ∨ (¬b)`.  The defining identity of
the De Morgan class (the strongest cube). -/
theorem intervalReversal_deMorgan (first second : cubeInterval) :
    intervalReversal (intervalMeet first second)
      = intervalJoin (intervalReversal first) (intervalReversal second) := by
  cases first <;> cases second <;> rfl

/-- The reversal is an involution. -/
theorem intervalReversal_involutive (point : cubeInterval) :
    intervalReversal (intervalReversal point) = point := by cases point <;> rfl

/-- Tie to the `mode-2` classes: the realized REVERSAL belongs to the De Morgan class — `supportsReversal` is
true exactly there (and false at the weaker cartesian class), matching `intervalReversal`'s placement. -/
theorem deMorgan_realizes_reversal :
    MultiplierStructureClass.deMorgan.supportsReversal = true
      ∧ MultiplierStructureClass.cartesian.supportsReversal = false :=
  ⟨rfl, rfl⟩

/-! ## Honesty markers -/

/-- **Honesty marker.**  The cube classes ARE now realized over the interval `𝕀 = Bool`: the shared
`intervalMultiplier` endofunctor `(- × 𝕀)` + the diagonal / connection / reversal OPERATIONS + their defining
laws (De Morgan, involution, commutativity, contraction).  What remains deferred is the STRICT per-class typed
gating (each class as a separate endofunctor carrying EXACTLY its operations) and the genuine cube-category
presheaf.  `= false`. -/
def fxMode_hasPerClassEndofunctorRealization : Bool := false

/-- **Honesty marker.**  SHIPPED: `squareMultiplier_not_split` proves a concrete multiplier (the diagonal
`A × A`, the same cardinality argument as `Bool → -`) is NOT dimensionally split — the not-split negative, via
the subsingleton-dimension pigeonhole.  `= true`. -/
def fxMode_hasNonSplitMultiplierProof : Bool := true

/-- **Honesty marker.**  The genuine PRESHEAF-category multiplier with the full Nuyts axioms (cancellative /
semicartesian / quantifiable …), beyond the `Type`-endofunctor model here, is deferred.  `= false`. -/
def fxMode_hasPresheafMultiplierModel : Bool := false

end FX1Poly.Tier0
