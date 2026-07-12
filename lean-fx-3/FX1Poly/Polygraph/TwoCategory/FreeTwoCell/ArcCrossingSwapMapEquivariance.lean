import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingFaithfulStep
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # MODE-COMMUTE r14 (I1) — the adjacent-transposition swap is RENAMING-EQUIVARIANT

`ArcCrossingFaithfulStep` (r7) defines `natListSwapTwoAt openWires position` — remove the pair at
`position` / `position + 1`, then splice the same two ids back in swapped order — the open-wire action of the
faithful `2⇒2` crossing.  `ArcSwapRenameable` (the shipped renaming machinery) already carries the three splice
primitives' equivariance laws — `natListInsertAt_map`, `natListRemoveTwoAt_map` (both over an ARBITRARY
`sigma : Nat → Nat`) — and `MatchingFreshShift` carries the in-range read law `natListGetAt_map_inRange`.  This
file composes those three into the missing swap-level law:

  ★ `natListSwapTwoAt_map` — for an in-window position (`position + 1 < wires.length`), mapping `sigma` over the
    swapped list equals swapping the mapped list: `(natListSwapTwoAt wires position).map sigma
    = natListSwapTwoAt (wires.map sigma) position`.  This is the renaming-EQUIVARIANCE the faithful crossing's
    `stepCrossArc_renameState` needs (the crossing analogue of the shipped `stepArcAtom_renameState`, whose
    cup/cap/box arms `ArcSwapRenameable` already renames) — the map brick a FAITHFUL general-signature partition
    simulation over the crossing permutation consumes (the #2043 / WP-AMALG Mazurkiewicz renaming route, which
    stays walled: this file supplies the brick, not the keystone).

## Why the window is load-bearing (truth-probed, NOT assumed)

`natListGetAt` returns the past-the-end default `0` when read out of range, and the swap re-splices the two reads
`natListGetAt wires position` / `... (position + 1)`.  Out of window (`position + 1 = wires.length` or beyond)
the swap reads that `0` default, and mapping `sigma` over `0` need not equal `sigma`'s image of the (absent)
element unless `sigma 0 = 0`.  A width-6 machine probe confirms: in range the equivariance holds; at
`position = wires.length - 1` (out of window) the two sides DIVERGE.  So `natListSwapTwoAt_map` carries
`position + 1 < wires.length` as a genuine hypothesis, matching the shipped `natListGetAt_natListSwapTwoAt`
window.  The map-inRange sub-lemma discharges the two spliced reads with no `sigma 0 = 0` side condition.

## What this file does NOT do (the pins stay false PERMANENTLY)

It does NOT build a faithful `stepCrossArc_renameState`, does NOT wire the crossing into the general-signature
partition simulation, and does NOT flip the general keystone.  `fxMode_hasArcPeelGeneralSignature` (the arity
ceiling) and the #2043 / WP-AMALG residual `fxMode_hasArcGodementSamePartitionFreshProof` stay `false`; the
shipped `natListSwapTwoAt` / `stepCrossArc` are never edited.  This certificate is strictly ADDITIVE.

Raw Lean 4 + Init; the whole proof is three `rw`s off the shipped equivariance laws (no `omega` / `simp`-AC /
`WellFounded.fix`).  Per-declaration `#assert_no_axioms` AND independent `#print axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The adjacent-transposition swap is renaming-equivariant (in window).**  Mapping any `sigma : Nat → Nat`
over `natListSwapTwoAt wires position` equals swapping over the mapped list, provided the pair is in window
(`position + 1 < wires.length`).  The swap is `natListInsertAt (natListRemoveTwoAt wires position) position`
`[natListGetAt wires (position + 1), natListGetAt wires position]`; `natListInsertAt_map` pushes the map through
the splice, `natListRemoveTwoAt_map` through the removal, and `natListGetAt_map_inRange` (twice, both reads in
window) renames the two spliced reads.  The remaining two-element `List.map` reduces definitionally. -/
theorem natListSwapTwoAt_map (sigma : Nat → Nat) (wires : List Nat) (position : Nat)
    (window : position + 1 < wires.length) :
    (natListSwapTwoAt wires position).map sigma = natListSwapTwoAt (wires.map sigma) position := by
  have positionBelow : position < wires.length := Nat.lt_of_succ_lt window
  show (natListInsertAt (natListRemoveTwoAt wires position) position
        [natListGetAt wires (position + 1), natListGetAt wires position]).map sigma
     = natListInsertAt (natListRemoveTwoAt (wires.map sigma) position) position
        [natListGetAt (wires.map sigma) (position + 1), natListGetAt (wires.map sigma) position]
  rw [natListInsertAt_map sigma (natListRemoveTwoAt wires position) position
      [natListGetAt wires (position + 1), natListGetAt wires position],
    natListRemoveTwoAt_map sigma wires position,
    natListGetAt_map_inRange sigma wires (position + 1) window,
    natListGetAt_map_inRange sigma wires position positionBelow]
  -- the residual `List.map sigma [a, b] = [sigma a, sigma b]` is definitional; close at default transparency
  rfl

/-! ## Non-vacuity — the equivariance fires on a concrete in-window swap -/

/-- ★ **Non-vacuous: the swap equivariance holds on a width-4 in-window instance.**  With `sigma = (· + 100)`,
`wires = [10, 11, 12, 13]`, `position = 1` (window `2 < 4`), both sides compute to `[110, 112, 111, 113]`.  A real
instantiation of `natListSwapTwoAt_map`, not a hand fixture. -/
theorem natListSwapTwoAt_map_seed_confirms :
    (natListSwapTwoAt [10, 11, 12, 13] 1).map (· + 100)
      = natListSwapTwoAt (([10, 11, 12, 13]).map (· + 100)) 1 :=
  natListSwapTwoAt_map (· + 100) [10, 11, 12, 13] 1 (by decide)

/-! ## Honesty markers -/

/-- **Honesty marker — the swap is renaming-equivariant.**  `natListSwapTwoAt_map` proves the faithful crossing's
open-wire action commutes with any id renaming in window (`position + 1 < wires.length`), composed from the shipped
`natListInsertAt_map` / `natListRemoveTwoAt_map` / `natListGetAt_map_inRange`.  Non-vacuous
(`natListSwapTwoAt_map_seed_confirms`).  This is the map brick a FAITHFUL `stepCrossArc_renameState` needs; it does
NOT itself build that renaming step or the general-signature partition simulation.  `= true`. -/
def fxMode_hasArcCrossingSwapMapEquivariance : Bool := true

/-- **Honesty pin — the general-signature peel stays the open keystone.**  The swap equivariance supplies the
crossing's renaming brick, but wiring it into a faithful `stepCrossArc_renameState` + the general-signature
partition simulation is the walled Mazurkiewicz route; `fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcCrossingSwapMapEquivariance_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched** (the Mazurkiewicz renaming
witness).  `fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossingSwapMapEquivariance_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
