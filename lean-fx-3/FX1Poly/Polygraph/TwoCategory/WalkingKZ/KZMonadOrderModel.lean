import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedSkeletonReps

/-! # WalkingKZ/KZMonadOrderModel — the pointwise POSET order on monotone maps (the KZ hom-order)

The walking monad's hom-categories are the augmented simplex category Delta_+: a 2-cell folds to a MONOTONE MAP
between finite ordinals (`monadMonotoneMapOf`, a weakly-increasing `List Nat`).  The walking IDEMPOTENT monad
forces `mu` iso and collapses every hom to a two-element boolean (`IdempotentMonadModel`, thin).  The walking
lax-idempotent (Kock-Zoberlein / KZ) monad sits STRICTLY BETWEEN: it keeps the full Delta_+ hom-SET but enriches
it with the POINTWISE ORDER on ordinal maps (Street; the recognition criterion arXiv:2512.05631: the KZ structure
"is encoded by the simplicial category extended to a 2-category using the POINTWISE ORDERING").  A KZ 2-cell
`f => g` between parallel 1-cells exists iff `f <= g` pointwise as monotone maps.

This file ships that order model on `List Nat` — `mapLE` (the pointwise order), its zero-axiom decidability, and
the poset laws (`mapLE_refl`, `mapLE_trans`, `mapLE_antisymm`, `mapLE_of_eq`).  Then it proves the three
ORDER-monotonicity closures the KZ soundness induction needs — the order analogs of the shipped map homomorphism
congruence lemmas:

  * **`composeMap_mapLE_left`** — `composeMap` is monotone in its FIRST argument (needs the SECOND map weakly
    increasing, `isWeaklyIncreasing`);
  * **`composeMap_mapLE_right`** — `composeMap` is monotone in its SECOND argument (pointwise, needs the first in
    range, `mapsInto`);
  * **`embedLocalMap_mapLE`** — the whisker ordinal-sum embedding `id_L (+) localMap (+) id_R` is monotone in the
    LOCAL map.

The order is a GENUINE poset, not discrete: `mapLE [0] [1]` holds but `mapLE [1] [0]` does not
(`mapLE01` / `not_mapLE10`) — the strict directionality that distinguishes KZ from the idempotent (thin) case.

Raw Lean 4 + Init; the model is plain `List Nat`, the order is a bounded `forall` decided by `Nat.decidableBallLT`,
the monotonicity lemmas are structural `Nat`/`List` reasoning over the shipped map value-characterizations, so every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The pointwise order on monotone maps -/

/-- The **pointwise order** on monotone-map value-lists: `mapLE xs ys` holds when at every in-range position `xs`'s
value never exceeds `ys`'s.  For PARALLEL cells (equal-length folds) this is the genuine order of the Delta_+ hom
poset; the KZ generating inequality `Tη <= ηT` folds to `mapLE [0] [1]`. -/
def mapLE (xs ys : List Nat) : Prop :=
  ∀ position, position < xs.length → monotoneMapGet xs position ≤ monotoneMapGet ys position

/-- **`mapLE` is decidable, zero-axiom.**  It is a bounded universal over positions `< xs.length` of a decidable
`Nat` comparison — decided outright by `Nat.decidableBallLT` (structural, propext-free). -/
instance decMapLE (xs ys : List Nat) : Decidable (mapLE xs ys) :=
  Nat.decidableBallLT xs.length (fun position _ => monotoneMapGet xs position ≤ monotoneMapGet ys position)

/-! ## The poset laws -/

/-- Reflexivity: `mapLE xs xs`. -/
theorem mapLE_refl (xs : List Nat) : mapLE xs xs :=
  fun _position _ => Nat.le_refl _

/-- From an equality of maps, the order in the forward direction. -/
theorem mapLE_of_eq {xs ys : List Nat} (heq : xs = ys) : mapLE xs ys :=
  heq ▸ mapLE_refl xs

/-- Transitivity along a chain whose first length bounds the second (equal for parallel cells): `mapLE xs ys` and
`mapLE ys zs` give `mapLE xs zs`. -/
theorem mapLE_trans {xs ys zs : List Nat} (hlen : xs.length ≤ ys.length)
    (hxy : mapLE xs ys) (hyz : mapLE ys zs) : mapLE xs zs :=
  fun position hposition =>
    Nat.le_trans (hxy position hposition) (hyz position (Nat.lt_of_lt_of_le hposition hlen))

/-- ★ **Antisymmetry on equal-length maps**: `mapLE xs ys` and `mapLE ys xs` with equal lengths force `xs = ys`.
This is the poset's antisymmetry — the genuine partial-order structure the KZ hom carries (its antisymmetrization is
the walking monad's Delta_+ equality). -/
theorem mapLE_antisymm {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hxy : mapLE xs ys) (hyx : mapLE ys xs) : xs = ys :=
  listExtById xs ys hlen
    (fun position hposition => Nat.le_antisymm (hxy position hposition) (hyx position (hlen ▸ hposition)))

/-! ## Non-triviality: the order is a GENUINE poset, not discrete -/

/-- The KZ generating inequality's fold: `mapLE [0] [1]` (the `t ◁ eta <= eta ▷ t` direction, `[0] <= [1]`). -/
theorem mapLE01 : mapLE [0] [1] := by decide

/-- ★ **The strict directionality**: the reverse `mapLE [1] [0]` FAILS (`1 <= 0` is false).  Together with `mapLE01`
this exhibits a genuine 2-element hom-poset `{[0] < [1]}` — the KZ order is NOT symmetric, distinguishing the walking
KZ monad from the walking idempotent monad (where the two faces are IDENTIFIED). -/
theorem not_mapLE10 : ¬ mapLE [1] [0] := by decide

/-! ## The three ORDER-monotonicity closures (the KZ soundness congruence legs) -/

/-- ★ **`composeMap` is monotone in its FIRST argument.**  If `first <= first'` pointwise (equal length) and the
SECOND map is weakly increasing (with `first'` landing in its domain), then `composeMap first second <= composeMap
first' second`.  The order analog of `monadMonotoneMapOf_vcompCongrLeft`: replacing the left vcomp factor by a
pointwise-larger one enlarges the composite, BECAUSE the post-composed map is monotone. -/
theorem composeMap_mapLE_left (first first' second : List Nat)
    (hlen : first.length = first'.length) (hle : mapLE first first')
    (hrange : mapsInto first' second.length) (hmono : isWeaklyIncreasing second) :
    mapLE (composeMap first second) (composeMap first' second) := by
  intro position hpos
  rw [composeMap_length] at hpos
  have hpos' : position < first'.length := hlen ▸ hpos
  rw [composeMap_get first second position hpos, composeMap_get first' second position hpos']
  exact hmono (monotoneMapGet first position) (monotoneMapGet first' position)
    (hle position hpos) (hrange position hpos')

/-- ★ **`composeMap` is monotone in its SECOND argument.**  If `second <= second'` pointwise (with `first` landing
in `second`'s domain), then `composeMap first second <= composeMap first second'`.  The order analog of
`monadMonotoneMapOf_vcompCongrRight`: replacing the right vcomp factor by a pointwise-larger one enlarges the
composite pointwise (no monotonicity of `first` needed — the incoming map only selects positions). -/
theorem composeMap_mapLE_right (first second second' : List Nat)
    (hle : mapLE second second') (hrange : mapsInto first second.length) :
    mapLE (composeMap first second) (composeMap first second') := by
  intro position hpos
  rw [composeMap_length] at hpos
  rw [composeMap_get first second position hpos, composeMap_get first second' position hpos]
  exact hle (monotoneMapGet first position) (hrange position hpos)

/-- ★ **The whisker embedding is monotone in the LOCAL map.**  The ordinal-sum embedding
`id_[leftLen] (+) localMap (+) id_[rightLen]` preserves the pointwise order on its local block: if `localA <=
localB` (equal length) then the embeddings compare pointwise.  The identity prefix/suffix regions agree exactly; the
middle region shifts the local order up by `leftLen`.  The order analog of `monadMonotoneMapOf_whiskerLeftCongr` /
`_whiskerRightCongr`. -/
theorem embedLocalMap_mapLE (leftLen midLen rightLen : Nat) (localA localB : List Nat)
    (hlen : localA.length = localB.length) (hle : mapLE localA localB) :
    mapLE (embedLocalMap leftLen midLen rightLen localA)
      (embedLocalMap leftLen midLen rightLen localB) := by
  intro position hpos
  rw [embedLocalMap_length] at hpos
  rcases embedRegionSplit leftLen localA.length rightLen position hpos with
    hleft | ⟨offset, hoff, rfl⟩ | ⟨offset, hoff, rfl⟩
  · rw [embedLocalMap_get_left leftLen midLen rightLen localA position hleft,
        embedLocalMap_get_left leftLen midLen rightLen localB position hleft]
    exact Nat.le_refl position
  · rw [embedLocalMap_get_mid leftLen midLen rightLen localA offset hoff,
        embedLocalMap_get_mid leftLen midLen rightLen localB offset (hlen ▸ hoff)]
    exact Nat.add_le_add_left (hle offset hoff) leftLen
  · have hA := embedLocalMap_get_right leftLen midLen rightLen localA offset hoff
    have hB : monotoneMapGet (embedLocalMap leftLen midLen rightLen localB)
        (leftLen + localA.length + offset) = leftLen + midLen + offset := by
      rw [hlen]; exact embedLocalMap_get_right leftLen midLen rightLen localB offset hoff
    rw [hA, hB]
    exact Nat.le_refl (leftLen + midLen + offset)

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The KZ hom-ORDER model on monotone maps is shipped: `mapLE` (the pointwise Delta_+ order) is
zero-axiom DECIDABLE (`decMapLE` via `Nat.decidableBallLT`), a genuine POSET (`mapLE_refl` / `mapLE_trans` /
`mapLE_antisymm` / `mapLE_of_eq`), and NON-DISCRETE (`mapLE01` holds, `not_mapLE10` refutes the reverse — a
2-element hom-poset `{[0] < [1]}`).  The three ORDER-monotonicity closures the KZ soundness induction needs —
`composeMap` monotone in each argument (`composeMap_mapLE_left` / `_right`) and the whisker embedding monotone in
the local map (`embedLocalMap_mapLE`) — are proved, reusing the shipped map value-characterizations.  `= true`. -/
def fxKZ_hasHomOrderModel : Bool := true

end FX1Poly.Polygraph
