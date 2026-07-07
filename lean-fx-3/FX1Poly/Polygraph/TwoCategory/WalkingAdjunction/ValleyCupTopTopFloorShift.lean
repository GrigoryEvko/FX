import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ValleyCupTopTopFloorShift — the offset-space floor-equivariance of `freshShiftAbove` (Piece II tail,
top-top cup-arc partner core)

The sole residual of the cup-side reconstruction is the top-top cup-arc partner agreement `cupTopTopPartner`
(`ValleyCupReconstruct`, cup case 3): for a cup-top port whose whole-valley partner stays at-or-above the floor,
the cup-alone partner (floor `midWidth`) equals `midWidth + (V.partner − bc)`.  The mathematics is a FLOOR SHIFT:
a top-top cup arc's two legs are a connectivity-rigid 2-element component, so its partner VALUE is the sibling leg
whose OFFSET is fixed by the cup NESTING (a fold over the cup-block window positions), identical in both runs; the
two runs then differ only by the floor (`bc` vs `midWidth`), which cancels in OFFSET space.

The engine that transports the partner list under a single cup step is `diagramPartner_stepCupArc`
(`ArcCupStepDrop`), and it is already FLOOR-PARAMETRIC — the floor `seedBoundary` appears there ONLY inside
`freshShiftAbove (seedBoundary + windowPosition) 2` and the short chord `[seedBoundary + windowPosition + 1,
seedBoundary + windowPosition]`.  The single arithmetic fact that lets the floor factor OUT of that transport — the
"value analog of `bleShiftAbove`" the `ValleyCupReconstruct` header cites — is landed here:

  `freshShiftAbove (floor + windowPos) delta value = floor + freshShiftAbove windowPos delta (value − floor)`

for `value ≥ floor` (both cup legs are tops, always at-or-above the floor).  Its offset form
`freshShiftAbove (floor + windowPos) delta value − floor = freshShiftAbove windowPos delta (value − floor)`
is exactly the seed-INDEPENDENCE of the per-cup transport in offset space: every fresh-shift a later cup applies
to an existing top-value acts as `floor + (a floor-independent shift of the offset)`.

## What this file lands (zero-axiom) — and the residual it does NOT discharge

  * ★ `freshShiftAbove_floorEquivariant` — the pointwise floor shift-out (above).
  * ★ `freshShiftAbove_floorEquivariant_offset` — its offset form (subtract the floor).
  * ★ `freshShiftAbove_map_floorEquivariant` — the list-map form: a list of at-or-above-floor values maps
    through `freshShiftAbove (floor + windowPos) delta` the same as mapping through the floor-shifted-out form.

This is the ARITHMETIC CORE of the top-top offset fold, reusable at BOTH seeds (`bc` and `midWidth`).  What is NOT
closed here — hence `cupTopTopPartner` stays a hypothesis of `cupRestrict_reconstructs`, and `valleyAppend_split` /
`valleysWithEqualMatching_spineTraceEquiv` stay gated: the two-run offset FOLD that assembles this identity across
the whole cup block.  That fold needs (i) the WireState ↔ arc-encoding bridge (`matchingOfSpineList` ↔
`extractArc ∘ processArcSpine`), (ii) promoting the general in-valley seed `capState` (non-empty cap links) into
the arc encoding with its `ArcBoundaryCensus` / `ArcStateFresh` / `isUnionFindForest` invariants, and (iii) an
offset-space invariant peel-last induction over `diagramPartner_stepCupArc` run at BOTH floors — a genuine
multi-session brick (the shipped block assembly `dropLastCup_arc_injective` runs the same engine but at a SINGLE
shared seed `List.range bottomCount`).  No gate flag is flipped; fib-3 also carries the independent Piece-I beam
(`MatchingReductsShareSpineTrace`, #1996).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local `Nat` plumbing (propext-free copies) -/

/-- `floor + (value - floor) = value` for `floor ≤ value` (hand-rolled; `Nat.add_sub_cancel'` leaks `propext`). -/
private theorem addSubCancelLocal : (floor value : Nat) → floor ≤ value → floor + (value - floor) = value
  | 0, value, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | floor + 1, 0, atMost => absurd atMost (Nat.not_succ_le_zero floor)
  | floor + 1, value + 1, atMost => by
      have inner := addSubCancelLocal floor value (Nat.le_of_succ_le_succ atMost)
      rw [Nat.succ_sub_succ, Nat.succ_add, inner]

/-- `base + value - base = value` (hand-rolled; `Nat.add_sub_cancel_left` risks a `propext` leak). -/
private theorem addSubCancelLeftLocal : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeftLocal base value

/-! ## The floor shift-out — the value analog of `bleShiftAbove` -/

/-- ★ **`freshShiftAbove` factors the floor out (value form).**  For a value at-or-above the floor
(`floor ≤ value` — every cup leg is a top), the fresh-shift at a floor-offset threshold `floor + windowPos`
equals the floor plus the fresh-shift at the raw threshold `windowPos` applied to the OFFSET `value − floor`:

  `freshShiftAbove (floor + windowPos) delta value = floor + freshShiftAbove windowPos delta (value − floor)`.

Both the threshold comparison (`floor + windowPos ≤ value ⟺ windowPos ≤ value − floor`, by `floor ≤ value`) and
the shifted value (`floor + ((value − floor) + delta) = value + delta`) are floor-equivariant.  This is the single
arithmetic fact that lets the floor `seedBoundary` factor OUT of the floor-parametric per-cup partner transport
`diagramPartner_stepCupArc` — the "value analog of `bleShiftAbove`" the `ValleyCupReconstruct` header cites. -/
theorem freshShiftAbove_floorEquivariant (floor windowPos delta value : Nat) (floorLe : floor ≤ value) :
    freshShiftAbove (floor + windowPos) delta value
      = floor + freshShiftAbove windowPos delta (value - floor) := by
  have floorPlusOffset : floor + (value - floor) = value := addSubCancelLocal floor value floorLe
  rcases Nat.lt_or_ge (value - floor) windowPos with windowGt | windowLe
  · -- below the raw threshold: both sides are fixed
    have thresholdGt : value < floor + windowPos := by
      have step : floor + (value - floor) < floor + windowPos := Nat.add_lt_add_left windowGt floor
      rw [floorPlusOffset] at step
      exact step
    rw [freshShiftAbove_ofNotLe (floor + windowPos) delta value (Nat.not_le_of_gt thresholdGt),
      freshShiftAbove_ofNotLe windowPos delta (value - floor) (Nat.not_le_of_gt windowGt),
      floorPlusOffset]
  · -- at-or-above the raw threshold: both sides shift by `delta`
    have thresholdLe : floor + windowPos ≤ value := by
      have step : floor + windowPos ≤ floor + (value - floor) := Nat.add_le_add_left windowLe floor
      rw [floorPlusOffset] at step
      exact step
    rw [freshShiftAbove_ofLe (floor + windowPos) delta value thresholdLe,
      freshShiftAbove_ofLe windowPos delta (value - floor) windowLe,
      ← Nat.add_assoc floor (value - floor) delta, floorPlusOffset]

/-- ★ **`freshShiftAbove` in offset space is floor-INDEPENDENT.**  Subtracting the floor from
`freshShiftAbove_floorEquivariant`: the fresh-shift of an at-or-above-floor value, read in OFFSET space
(`· − floor`), equals the fresh-shift of the offset at the raw threshold — with the floor entirely gone:

  `freshShiftAbove (floor + windowPos) delta value − floor = freshShiftAbove windowPos delta (value − floor)`.

This is the exact seed-independence a two-run offset fold needs: the SAME cup-block window sequence applied to a
top-value produces the SAME offset-space result at any floor (`bc` or `midWidth`). -/
theorem freshShiftAbove_floorEquivariant_offset (floor windowPos delta value : Nat) (floorLe : floor ≤ value) :
    freshShiftAbove (floor + windowPos) delta value - floor
      = freshShiftAbove windowPos delta (value - floor) := by
  rw [freshShiftAbove_floorEquivariant floor windowPos delta value floorLe,
    addSubCancelLeftLocal floor (freshShiftAbove windowPos delta (value - floor))]

/-! ## The list-map form -/

/-- ★ **The list-map floor shift-out.**  A list of at-or-above-floor values maps through the floor-offset
fresh-shift `freshShiftAbove (floor + windowPos) delta` pointwise as `floor + freshShiftAbove windowPos delta
(· − floor)` — the whole map factors the floor out.  Structural over the list; each element discharged by
`freshShiftAbove_floorEquivariant`.  This is the list-level shape the per-cup partner transport
(`diagramPartner_stepCupArc`, whose old-port segment is `partner.map (freshShiftAbove (seedBoundary +
windowPosition) 2)`) presents, restricted to the top region where every entry is at-or-above the floor. -/
theorem freshShiftAbove_map_floorEquivariant (floor windowPos delta : Nat) :
    (values : List Nat) → (∀ value ∈ values, floor ≤ value) →
    values.map (freshShiftAbove (floor + windowPos) delta)
      = values.map (fun value => floor + freshShiftAbove windowPos delta (value - floor))
  | [], _ => rfl
  | headValue :: restValues, allAtOrAboveFloor => by
      show freshShiftAbove (floor + windowPos) delta headValue
            :: restValues.map (freshShiftAbove (floor + windowPos) delta)
        = (floor + freshShiftAbove windowPos delta (headValue - floor))
            :: restValues.map (fun value => floor + freshShiftAbove windowPos delta (value - floor))
      rw [freshShiftAbove_floorEquivariant floor windowPos delta headValue
          (allAtOrAboveFloor headValue (List.Mem.head restValues)),
        freshShiftAbove_map_floorEquivariant floor windowPos delta restValues
          (fun value valueMem => allAtOrAboveFloor value (List.Mem.tail headValue valueMem))]

/-! ## Honesty marker -/

/-- **Honesty marker — the offset-space floor-equivariance of `freshShiftAbove` (the top-top cup-arc partner
arithmetic core) is LANDED; the two-run offset FOLD around it is the un-shipped residual.**

Landed here, all zero-axiom:

  * `freshShiftAbove_floorEquivariant` — the value floor shift-out `freshShiftAbove (floor + windowPos) delta
    value = floor + freshShiftAbove windowPos delta (value − floor)` for `value ≥ floor`.
  * `freshShiftAbove_floorEquivariant_offset` — its offset form: the shift is floor-INDEPENDENT in offset space.
  * `freshShiftAbove_map_floorEquivariant` — the list-map form, the shape the per-cup partner transport presents.

This is the arithmetic linchpin of the top-top cup-arc partner agreement `cupTopTopPartner` (`ValleyCupReconstruct`,
cup case 3): the floor-parametric per-cup partner transport `diagramPartner_stepCupArc` shifts existing top-values
by `freshShiftAbove (seedBoundary + windowPosition) 2`, and this identity factors `seedBoundary` OUT — so the same
cup-block window fold produces the SAME offset-space partner at any floor.

What this marker does NOT close — `cupTopTopPartner` itself, hence `cupRestrict_reconstructs` (which keeps it as a
hypothesis), and downstream `valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv`: the two-run offset
FOLD that assembles this identity across the whole cup block.  That needs (i) the WireState ↔ arc-encoding bridge
(`matchingOfSpineList` ↔ `extractArc ∘ processArcSpine`), (ii) promoting the general in-valley seed `capState`
(non-empty cap links, scattered survivor bottoms) into the arc encoding with `ArcBoundaryCensus` / `ArcStateFresh`
/ `isUnionFindForest`, and (iii) the offset-space invariant peel-last induction over `diagramPartner_stepCupArc` at
BOTH floors — the shipped assembly `dropLastCup_arc_injective` runs the SAME engine but at a single shared seed
`List.range bottomCount`, so the different-seed offset fold is genuinely new.  A multi-session brick.  No gate flag
is flipped; fib-3 also carries the independent Piece-I beam (`MatchingReductsShareSpineTrace`, #1996).  `= true`. -/
def fxMode_hasCupTopTopFloorShiftCore : Bool := true

end FX1Poly.Polygraph
