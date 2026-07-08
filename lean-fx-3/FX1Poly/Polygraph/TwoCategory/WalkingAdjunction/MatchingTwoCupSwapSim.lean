import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingCupSwapRootComm
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyFloorHomogeneous
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable

/-! # MatchingTwoCupSwapSim — brick 2, the cup-bubble `MatchingStepSim` core (POSITIVITY-FREE)

Track B, the load-bearing wiring step.  This is the matching-carrier analog of the arc route's
`arcSwapCorePackage_cupCup`, but built over the plain `WireState` / `stepCup` carrier and — critically —
WITHOUT the positive-fresh-seed hypothesis `0 < state.nextFresh` the arc package requires.

## What it proves

For a fresh forest state `state` and two disjoint-window cup positions (`positionLow` and `gap + …`
above it), the two Godement run orders

  * redex : `stepCup (stepCup state positionLow) (gap + 2 + positionLow)`  (low cup first)
  * reduct: `stepCup (stepCup state (gap + positionLow)) positionLow`      (high cup first)

are related by the single `MatchingStepSim (blockSwap state.nextFresh)` invariant.  Both orders allocate the
IDENTICAL link forest `(nf+2, nf+3) :: (nf, nf+1) :: state.links` (a cup always joins its two FRESH legs,
independent of fire position), so the two states differ ONLY by the block transposition `blockSwap nf` that
swaps the two fresh cup pairs' open-wire positions.  The six fields:

  * `openMap` — the open-wire block transposition, from `natListInsertAt_insertAbove_commute` (the disjoint
    splice commutation) + `natListInsertAt_map` (map/splice naturality) + the four `blockSwap` value laws and
    `blockSwap_fix_lt` (the old wires, all `< nf`, are fixed).  THE geometric heart.
  * `nfEq` / `loopsEq` — both `rfl` (two cups advance `nextFresh` by `4` and add no loops, in either order).
  * `rootComm` — the shipped crux `blockSwap_rootComm` on the common link forest.
  * `forestS` / `forestT` — `isUnionFindForest_stepCup` twice.

## Why POSITIVITY-FREE — and what it does NOT close

`blockSwap_rootComm` (and hence this whole core) never demands `blockSwap nf 0 = 0`; it holds even at `nf = 0`
(the width-0 first-cup seed) where `blockSwap 0 0 = 2 ≠ 0`.  So the SINGLE-STEP cup-bubble invariance is
established positivity-free — the exact obstruction (`ArcSwapCorePackage.sigmaFixesZero`) the arc route hits at
the width-0 seed is bypassed for the core.

What this core does NOT supply: threading the renaming past a NON-EMPTY spine tail
(`matchingStepSim_processSpine` / `matchingRenameRel_full_of_coreSim`) still requires `sigma 0 = 0`, which
`blockSwap nf` satisfies only when `0 < nf`.  So the fold-through past the rest, and the LOCATE induction that
consumes it, remain the standing residual for `WidthZeroPureCupDeterminacy` (see the honesty marker).

Raw Lean 4 + Init; no `omega` / `simp`-AC / `WellFounded.fix` / `propext`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The image of a cup's fresh leg pair `[nf, nf+1]` under `blockSwap nf` is the OTHER pair `[nf+2, nf+3]`. -/
theorem blockSwap_map_lowLegs (nf : Nat) :
    [nf, nf + 1].map (blockSwap nf) = [nf + 2, nf + 3] := by
  show [blockSwap nf nf, blockSwap nf (nf + 1)] = [nf + 2, nf + 3]
  rw [blockSwap_nf, blockSwap_nf1]

/-- The image of the SECOND cup's fresh leg pair `[nf+2, nf+3]` under `blockSwap nf` is the low pair
`[nf, nf+1]`. -/
theorem blockSwap_map_highLegs (nf : Nat) :
    [nf + 2, nf + 3].map (blockSwap nf) = [nf, nf + 1] := by
  show [blockSwap nf (nf + 2), blockSwap nf (nf + 3)] = [nf, nf + 1]
  rw [blockSwap_nf2, blockSwap_nf3]

/-- ★ **Brick 2 — the cup-bubble `MatchingStepSim` core, POSITIVITY-FREE.**  Two disjoint-window cups fired in
the two Godement run orders are `MatchingStepSim (blockSwap state.nextFresh)`-related.  Uses the shipped crux
`blockSwap_rootComm` for the root-commutation field and the disjoint-splice commutation for the open-wire block
transposition.  No `0 < state.nextFresh` — the exact positivity floor the arc `arcSwapCorePackage_cupCup` demands
is not needed for the single-step core. -/
theorem matchingStepSim_twoCupSwap (state : WireState) (fresh : WireStateFresh state)
    (forest : isUnionFindForest state.links) (gap positionLow : Nat)
    (positionBound : gap + positionLow ≤ state.openWires.length) :
    MatchingStepSim (blockSwap state.nextFresh)
      (stepCup (stepCup state positionLow) (gap + 2 + positionLow))
      (stepCup (stepCup state (gap + positionLow)) positionLow) where
  openMap := by
    show (stepCup (stepCup state (gap + positionLow)) positionLow).openWires
       = ((stepCup (stepCup state positionLow) (gap + 2 + positionLow)).openWires).map
           (blockSwap state.nextFresh)
    show natListInsertAt (natListInsertAt state.openWires (gap + positionLow)
            [state.nextFresh, state.nextFresh + 1]) positionLow
            [state.nextFresh + 2, state.nextFresh + 3]
       = (natListInsertAt (natListInsertAt state.openWires positionLow
            [state.nextFresh, state.nextFresh + 1]) (gap + 2 + positionLow)
            [state.nextFresh + 2, state.nextFresh + 3]).map (blockSwap state.nextFresh)
    rw [natListInsertAt_map (blockSwap state.nextFresh), natListInsertAt_map (blockSwap state.nextFresh),
      mapFixedOn (blockSwap state.nextFresh) state.openWires
        (fun wire wireInOpen => blockSwap_fix_lt state.nextFresh wire (fresh.1 wire wireInOpen)),
      blockSwap_map_lowLegs, blockSwap_map_highLegs]
    exact natListInsertAt_insertAbove_commute state.openWires positionLow gap
      [state.nextFresh + 2, state.nextFresh + 3] [state.nextFresh, state.nextFresh + 1] positionBound
  nfEq := rfl
  rootComm := by
    intro identifier
    have redexLinksEq : (stepCup (stepCup state positionLow) (gap + 2 + positionLow)).links
        = (state.nextFresh + 2, state.nextFresh + 3) :: (state.nextFresh, state.nextFresh + 1) :: state.links := by
      rw [stepCup_links_freshCons (stepCup state positionLow) (gap + 2 + positionLow)
          (stepCup_wireStateFresh state positionLow fresh),
        stepCup_links_freshCons state positionLow fresh]
      rfl
    have reductLinksEq : (stepCup (stepCup state (gap + positionLow)) positionLow).links
        = (state.nextFresh + 2, state.nextFresh + 3) :: (state.nextFresh, state.nextFresh + 1) :: state.links := by
      rw [stepCup_links_freshCons (stepCup state (gap + positionLow)) positionLow
          (stepCup_wireStateFresh state (gap + positionLow) fresh),
        stepCup_links_freshCons state (gap + positionLow) fresh]
      rfl
    rw [reductLinksEq, redexLinksEq]
    exact blockSwap_rootComm state.nextFresh state.links fresh.2 forest identifier
  loopsEq := rfl
  forestS := isUnionFindForest_stepCup (stepCup state positionLow) (gap + 2 + positionLow)
    (isUnionFindForest_stepCup state positionLow forest)
  forestT := isUnionFindForest_stepCup (stepCup state (gap + positionLow)) positionLow
    (isUnionFindForest_stepCup state (gap + positionLow) forest)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the cup-bubble `MatchingStepSim` core is SHIPPED, POSITIVITY-FREE (brick 2).**
`matchingStepSim_twoCupSwap` proves the two disjoint-window cup run orders are `MatchingStepSim`-related over the
plain `WireState` carrier, riding the shipped crux `blockSwap_rootComm` for the root-commutation and the
carrier-agnostic disjoint-splice commutation kit for the open-wire block transposition — with NO
`0 < state.nextFresh` (the exact seed the arc `arcSwapCorePackage_cupCup` needs and the width-0 case cannot
supply).  So the SINGLE-STEP matching-invariance of one cup-bubble transposition is now positivity-free.

  What this marker does NOT claim (the standing residual): the FOLD-THROUGH of this core past a non-empty spine
  tail (`matchingStepSim_processSpine` / `matchingRenameRel_full_of_coreSim`) still requires `sigma 0 = 0`, i.e.
  `blockSwap nf 0 = 0`, which holds only when `0 < nf` — genuinely FALSE at the width-0 first-cup seed
  (`blockSwap 0 0 = 2`).  Hence `WidthZeroPureCupDeterminacy` still owes (i) a positivity-free in-range
  fold-through of `blockSwap` past the rest, and (ii) the matching-carrier LOCATE induction (`chordShift`,
  `forwardChordsNotAdjacent`, `emptyMatchingNoForwardChord`, `locateAux`) that consumes it.  `convOfMapEq` and
  the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasMatchingTwoCupSwapSim : Bool := true

end FX1Poly.Polygraph
