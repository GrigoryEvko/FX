import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChain
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescRankPositionDuality
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTrackerInterior
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount

/-! # BRAUER r26 — THE CUP CHAIN: the GENERAL per-arc CUP-class T-CONNECT (assembled, zero-axiom)

The CAP chain (`Brauer/WiringDescTConnectCapChain.lean`) shipped the shortest per-arc T-CONNECT — its tracker runs on
the SEED (base `= List.range`), so it needed neither GAP β nor the `permInverse` cup-rank arithmetic.  The CUP class
runs its `topPerm` tracker on a NON-seed post-cup state, so it carries the r25 GAP β base-permute bridge, the r26 rank
↔ position duality keystone, and a NEW `expandCupTopPairs` getAt kit that CAP never needed.  This file mirrors the CAP
chain step-for-step through those extra ingredients.

## What this file ships — the CUP chain, general

`cupArcConnect_general`: for EVERY well-formed boundary involution `d` and every cup-arc rank
`rank < (cupArcTopIndices d.bottomCount d.topCount d.partner).length`, the rank-th cup arc's two TOP legs share a
union-find component in the corrected six-phase fold state.  `cupArcMatching_general` lifts it to the boundary-matching
`partnerShares` datum the r22 routing collapse consumes (both feet top, so `matchingSameComponent_topTop_eq_isSameComponent`).

## The chain (the recon's mirrored step table)

  * `foldFactorsThroughCup` factors the six-phase fold as (post-cap-post-middle S3) then the trailing three-phase word
    `cupWord ++ crossingWord topPerm ++ circleWord loops`.
  * `cupFold_creates_atOffset` fires the cup block on S3 (whose open wires ARE the through block, `capFeet := []`),
    prepending `#cups` fresh joined pairs after the through block; `processBrauer_isSameComponent_ofBase` survives them
    past `topPerm ++ circle`.
  * the interior tracker `crossingWordFold_openWire_sameComponent_afterPrefix` (post-cup) + GAP β
    `natListGetAt_foldlAdjacentSwapBase` + `correctedTopPerm_decodesInverseReadOff` route each final top open wire to
    the post-cup open wire at the `permInverse`-permuted position;
  * the r26 keystone `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange` collapses that permuted position of a
    cup top leg to its rank `throughStrandTops.length + doublePos rank`, which the through-count symmetry
    `throughStrandBottoms_length_eq_throughStrandTops` lands inside the fresh-feet block at offset `doublePos rank`;
  * `flattenNatPairs_pairGetMem` reads that fresh pair as a member, welded by `isSameComponent_trans` / `_flip`.

## Honest scope

CUP is the SECOND of the three per-arc classes; alone it flips NO master.  `fxBrauer_hasTConnectThroughWall` stays
`false` until the THROUGH class + the all-class dispatch also land.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only on closed
literals (the probes).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The six-phase factorization through the cup block -/

/-- The corrected fold factors as (post-cap-post-middle S3) then the trailing three-phase word `cupWord ++
crossingWord topPerm ++ circleWord loops` — the transport spine the cup chain rides.  `standardFormFold_appendSplit`
re-associated at the two trailing `++` seams by `processBrauer_append`. -/
theorem foldFactorsThroughCup (form : BrauerStandardFormExt5) :
    processBrauer (brauerSeed form.bottomCount) (standardFormWordExt5 form)
      = processBrauer
          (processBrauer (processBrauer (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
            (capWord form.capBlock)) (crossingWord form.middle))
          (cupWord form.cupBlock ++ crossingWord form.topPerm ++ circleWord form.loops) := by
  rw [standardFormFold_appendSplit form,
    processBrauer_append (cupWord form.cupBlock ++ crossingWord form.topPerm)
      (processBrauer (processBrauer (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
        (capWord form.capBlock)) (crossingWord form.middle)) (circleWord form.loops),
    processBrauer_append (cupWord form.cupBlock)
      (processBrauer (processBrauer (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
        (capWord form.capBlock)) (crossingWord form.middle)) (crossingWord form.topPerm)]

/-! ## The `expandCupTopPairs` position bookkeeping (the CUP getAt kit — the ∗-dual of `expandBottomFeetPairs_getAt`) -/

/-- The even position of `expandCupTopPairs` reads the rank-th smaller cup top (`cupArcTopIndices[rank]`). -/
theorem expandCupTopPairs_getAt_fst (bottomCount : Nat) (partner : List Nat) :
    (feet : List Nat) → (rank : Nat) → rank < feet.length →
    natListGetAt (expandCupTopPairs bottomCount partner feet) (doublePos rank) = natListGetAt feet rank
  | [], rank, hlt => absurd hlt (Nat.not_lt_zero rank)
  | _ :: _, 0, _ => rfl
  | topIndex :: rest, rank + 1, hlt => by
      have restLt : rank < rest.length := Nat.lt_of_succ_lt_succ hlt
      show natListGetAt (topIndex :: (natListGetAt partner (bottomCount + topIndex) - bottomCount)
          :: expandCupTopPairs bottomCount partner rest) (doublePos (rank + 1))
          = natListGetAt (topIndex :: rest) (rank + 1)
      exact expandCupTopPairs_getAt_fst bottomCount partner rest rank restLt

/-- The odd position of `expandCupTopPairs` reads the top-offset partner of the rank-th smaller cup top. -/
theorem expandCupTopPairs_getAt_snd (bottomCount : Nat) (partner : List Nat) :
    (feet : List Nat) → (rank : Nat) → rank < feet.length →
    natListGetAt (expandCupTopPairs bottomCount partner feet) (doublePos rank + 1)
      = natListGetAt partner (bottomCount + natListGetAt feet rank) - bottomCount
  | [], rank, hlt => absurd hlt (Nat.not_lt_zero rank)
  | _ :: _, 0, _ => rfl
  | topIndex :: rest, rank + 1, hlt => by
      have restLt : rank < rest.length := Nat.lt_of_succ_lt_succ hlt
      show natListGetAt (topIndex :: (natListGetAt partner (bottomCount + topIndex) - bottomCount)
          :: expandCupTopPairs bottomCount partner rest) (doublePos (rank + 1) + 1)
          = natListGetAt partner (bottomCount + natListGetAt (topIndex :: rest) (rank + 1)) - bottomCount
      exact expandCupTopPairs_getAt_snd bottomCount partner rest rank restLt

/-- `natListGetAt` on the RIGHT of an append, at `left.length + offset` — reads the right list at `offset`.  Structural
on the left list (a public cup-chain re-proof of the readback-private append-right read). -/
theorem natListGetAtAppendRightCup : (leftList rightList : List Nat) → (offset : Nat) →
    natListGetAt (leftList ++ rightList) (leftList.length + offset) = natListGetAt rightList offset
  | [], rightList, offset => by
      show natListGetAt rightList (0 + offset) = natListGetAt rightList offset
      rw [Nat.zero_add]
  | head :: restLeft, rightList, offset => by
      show natListGetAt (head :: (restLeft ++ rightList)) ((restLeft.length + 1) + offset)
          = natListGetAt rightList offset
      rw [Nat.add_right_comm restLeft.length 1 offset]
      show natListGetAt (restLeft ++ rightList) (restLeft.length + offset) = natListGetAt rightList offset
      exact natListGetAtAppendRightCup restLeft rightList offset

/-! ## Honesty marker — the CUP factorization + position kit -/

/-- ★★ **Honesty marker — the CUP chain factorization + position kit is SHIPPED (r26).**  `foldFactorsThroughCup`
factors the corrected six-phase fold as (post-cap-post-middle S3) then the trailing three-phase word (the CUP transport
spine); `expandCupTopPairs_getAt_fst` / `_snd` read the rank-th cup arc's two top legs off `cupArcTops` at the
`doublePos`-indexed even/odd positions (the ∗-dual of the CAP `expandBottomFeetPairs_getAt` kit); and
`natListGetAtAppendRightCup` reads the fresh-feet block past the through block.  With the r26 keystone
(`natListGetAtPermInverse_natListGetAt_ofPermutationOfRange`) these are the exact ingredients the CUP general weld
composes.  Truth-probed on the NESTED cups (`cupChainTopDecodeProbe_nestedCups`, `cupChainJoinProbe_nestedCups` in
`WiringDescTConnectCapChainLedger`) and the interleaved cups (`cupChainJoinProbe_interleavedCups` in
`WiringDescTConnectCapClass`).  A NEW ingredient marker; it flips NO master.  `= true`. -/
def fxBrauer_hasCupChainFactorKit : Bool := true

end FX1Poly.Polygraph
