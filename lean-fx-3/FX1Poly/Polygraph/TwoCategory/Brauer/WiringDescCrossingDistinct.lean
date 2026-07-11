import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescOpenEndsDistinct
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryComponents
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTracker
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality

/-! # BRAUER r30 B2 (X) — THE CROSSING preserves `BrauerOpenEndsDistinct` (the heaviest per-step lemma)

The zero-loops invariant `BrauerOpenEndsDistinct` (`Brauer/WiringDescOpenEndsDistinct.lean`) must survive the bottom
crossing staircase before the caps fire.  This file ships that: an in-range crossing at `position` preserves the
component-level open-ends distinctness — the recon's named heaviest new lemma, assembled from public parts (NO
private re-derivation).

## The assembly

  * open-wire read: `stepWiringCrossing_openWire_get` — position `pos` reads the fresh left leg `nextFresh`, `pos + 1`
    the fresh right leg `nextFresh + 1`, every other slot the SAME old wire.
  * link update: `stepWiring_crossing_links` — the two-join `join (join links in0 (nf+1)) in1 nf`.
  * connectivity: `crossingJoin_transposition_view` — the crossing's same-component view is the window transposition
    of the base: OLD/OLD unchanged, the left fresh leg reads `in1`'s class, the right fresh leg reads `in0`'s class,
    the two fresh legs share iff the two window strands did.

So each surviving open pair pulls back, through the window transposition, to a base open pair the invariant already
separates — a crossing NEVER merges two distinct base components (it just relabels the two window slots).  Freshness
(`natListGetAt_lt`) bounds every old read below `nextFresh`, and `stepWiring_openWires_length_fits` fixes the length.

## Honest scope

This completes the invariant-PRESERVATION trio (seed, cap, crossing); the full `(processBrauer (brauerSeed bc)
boundaryWord).loops = 0` still needs the crossing loops-zero re-export and the phase-fold assembly, the named r31
residual.  `fxBrauer_hasFoldLoopsCorrectness` stays `false`, NO master flips.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **(X) THE CROSSING preserves the open-ends distinctness invariant.**  An in-range crossing at `position`
relabels only its two window slots (into the two fresh legs, with swapped connectivity) and merges no two distinct
base components, so every surviving open pair stays in distinct components — the pullback of the base invariant along
the window transposition (`crossingJoin_transposition_view`).  Freshness bounds every old read; the fresh legs read
the two window strands' classes, which the invariant separates.  The heaviest per-step lemma of the zero-loops
invariant, assembled entirely from public parts. -/
theorem brauerOpenEndsDistinct_stepWiringCrossing (state : WireState)
    (fresh : WiringDescStateFresh state) (forest : isUnionFindForest state.links) (nfPos : 0 < state.nextFresh)
    (position : Nat) (windowInRange : position + 2 ≤ state.openWires.length)
    (distinct : BrauerOpenEndsDistinct state) :
    BrauerOpenEndsDistinct (stepWiring state position crossingWiring) := by
  intro lowPosition highPosition lowLtHigh highInRange
  -- length preserved
  obtain ⟨rightLen, hRight⟩ := Nat.le.dest windowInRange
  have hFits : state.openWires.length = position + crossingWiring.inputCount + rightLen := by
    show state.openWires.length = position + 2 + rightLen
    exact hRight.symm
  have hNewLen : (stepWiring state position crossingWiring).openWires.length = state.openWires.length := by
    rw [stepWiring_openWires_length_fits state position rightLen crossingWiring hFits]
    show position + 2 + rightLen = state.openWires.length
    exact hRight
  have hiLen : highPosition < state.openWires.length := hNewLen ▸ highInRange
  have loLen : lowPosition < state.openWires.length := Nat.lt_trans lowLtHigh hiLen
  -- position bounds
  have posLt : position < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) windowInRange
  have posSuccLt : position + 1 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowInRange
  -- freshness bounds
  have in0Below : natListGetAt state.openWires position < state.nextFresh :=
    natListGetAt_lt state.nextFresh nfPos state.openWires position fresh.1
  have in1Below : natListGetAt state.openWires (position + 1) < state.nextFresh :=
    natListGetAt_lt state.nextFresh nfPos state.openWires (position + 1) fresh.1
  have loOldBelow : natListGetAt state.openWires lowPosition < state.nextFresh :=
    natListGetAt_lt state.nextFresh nfPos state.openWires lowPosition fresh.1
  have hiOldBelow : natListGetAt state.openWires highPosition < state.nextFresh :=
    natListGetAt_lt state.nextFresh nfPos state.openWires highPosition fresh.1
  -- reads + links + transposition view
  have hReadLo := stepWiringCrossing_openWire_get state position lowPosition windowInRange
  have hReadHi := stepWiringCrossing_openWire_get state position highPosition windowInRange
  have hLinks := stepWiring_crossing_links state position fresh nfPos forest windowInRange
  obtain ⟨hOldOld, hNfOld, hNfSuccOld, hNfNfSucc⟩ :=
    crossingJoin_transposition_view state forest fresh (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) in0Below in1Below
  rw [hReadLo, hReadHi, hLinks]
  -- 9-case dispatch on the two window-slot memberships
  cases Nat.decEq lowPosition position with
  | isTrue loEqP =>
      rw [if_pos loEqP]
      cases Nat.decEq highPosition position with
      | isTrue hiEqP => exact absurd (loEqP.trans hiEqP.symm) (Nat.ne_of_lt lowLtHigh)
      | isFalse hiNeP =>
          rw [if_neg hiNeP]
          cases Nat.decEq highPosition (position + 1) with
          | isTrue hiEqP1 =>
              rw [if_pos hiEqP1, hNfNfSucc, isSameComponent_symm]
              exact distinct position (position + 1) (Nat.lt_succ_self position) posSuccLt
          | isFalse hiNeP1 =>
              rw [if_neg hiNeP1, hNfOld (natListGetAt state.openWires highPosition) hiOldBelow]
              have posLtHi : position < highPosition := loEqP ▸ lowLtHigh
              have posSuccLtHi : position + 1 < highPosition :=
                Nat.lt_of_le_of_ne (Nat.succ_le_of_lt posLtHi) (fun eq => hiNeP1 eq.symm)
              exact distinct (position + 1) highPosition posSuccLtHi hiLen
  | isFalse loNeP =>
      rw [if_neg loNeP]
      cases Nat.decEq lowPosition (position + 1) with
      | isTrue loEqP1 =>
          rw [if_pos loEqP1]
          cases Nat.decEq highPosition position with
          | isTrue hiEqP =>
              have contra : position + 1 < position := by rw [← loEqP1, ← hiEqP]; exact lowLtHigh
              exact absurd contra (Nat.not_lt.mpr (Nat.le_succ position))
          | isFalse hiNeP =>
              rw [if_neg hiNeP]
              cases Nat.decEq highPosition (position + 1) with
              | isTrue hiEqP1 => exact absurd (loEqP1.trans hiEqP1.symm) (Nat.ne_of_lt lowLtHigh)
              | isFalse hiNeP1 =>
                  rw [if_neg hiNeP1, hNfSuccOld (natListGetAt state.openWires highPosition) hiOldBelow]
                  have hSucc : position + 1 < highPosition := by rw [← loEqP1]; exact lowLtHigh
                  have posLtHi : position < highPosition := Nat.lt_trans (Nat.lt_succ_self position) hSucc
                  exact distinct position highPosition posLtHi hiLen
      | isFalse loNeP1 =>
          rw [if_neg loNeP1]
          cases Nat.decEq highPosition position with
          | isTrue hiEqP =>
              rw [if_pos hiEqP, isSameComponent_symm, hNfOld (natListGetAt state.openWires lowPosition) loOldBelow,
                isSameComponent_symm]
              have loLtPos : lowPosition < position := hiEqP ▸ lowLtHigh
              exact distinct lowPosition (position + 1) (Nat.lt_trans loLtPos (Nat.lt_succ_self position)) posSuccLt
          | isFalse hiNeP =>
              rw [if_neg hiNeP]
              cases Nat.decEq highPosition (position + 1) with
              | isTrue hiEqP1 =>
                  rw [if_pos hiEqP1, isSameComponent_symm,
                    hNfSuccOld (natListGetAt state.openWires lowPosition) loOldBelow, isSameComponent_symm]
                  have hLt : lowPosition < position + 1 := by rw [← hiEqP1]; exact lowLtHigh
                  have loLtPos : lowPosition < position := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hLt) loNeP
                  exact distinct lowPosition position loLtPos posLt
              | isFalse hiNeP1 =>
                  rw [if_neg hiNeP1, hOldOld (natListGetAt state.openWires lowPosition)
                    (natListGetAt state.openWires highPosition) loOldBelow hiOldBelow]
                  exact distinct lowPosition highPosition lowLtHigh hiLen

/-- ★★ **Honesty marker — the CROSSING preserves the zero-loops invariant (r30 B2, X).**
`brauerOpenEndsDistinct_stepWiringCrossing` proves, zero-axiom, that an in-range crossing preserves
`BrauerOpenEndsDistinct` — the pullback of the base invariant along the window transposition
(`crossingJoin_transposition_view`), a crossing merging no two distinct base components.  With the seed (S), cap
zero-loop (C1), and cap preservation (C2), this completes the invariant-PRESERVATION trio (seed / cap / crossing).
The full boundary-word-zero still needs the crossing loops-zero re-export + the phase-fold assembly (the named r31
residual), so `fxBrauer_hasFoldLoopsCorrectness` stays `false` and NO master flips.  `= true`. -/
def fxBrauer_hasOpenEndsDistinctCrossing : Bool := true

end FX1Poly.Polygraph
