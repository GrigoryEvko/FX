import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChain
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescRankPositionDuality
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTrackerInterior
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBasePermuteBridge
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandPerm

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

/-! ## The GENERAL per-arc CUP-class T-CONNECT (the weld assembled) -/

/-- `entries ++ [] = entries` for a `Nat` list — a propext-free re-proof (`List.append_nil` leaks `propext`). -/
theorem natListAppendNil : (entries : List Nat) → entries ++ [] = entries
  | [] => rfl
  | head :: rest => by
      show head :: (rest ++ []) = head :: rest
      rw [natListAppendNil rest]

/-- `(leftList ++ rightList).length = leftList.length + rightList.length` for `Nat` lists — a propext-free re-proof
(`List.length_append` leaks `propext`). -/
theorem natListLengthAppend : (leftList rightList : List Nat) →
    (leftList ++ rightList).length = leftList.length + rightList.length
  | [], rightList => (Nat.zero_add rightList.length).symm
  | head :: rest, rightList => by
      show (rest ++ rightList).length + 1 = (rest.length + 1) + rightList.length
      rw [natListLengthAppend rest rightList, Nat.succ_add]

/-- The circle block preserves the open wires: each `[cupAt 0, capAt 0]` iteration creates a fresh cup pair at offset
`0` then caps it away, net-preserving the open-wire list.  Structural on `loops` — the CUP / THROUGH final target reads
`F.openWires`, and the circle phase (after `topPerm`) leaves those wires untouched. -/
theorem circleFold_openWires : (loops : Nat) → (state : WireState) → isUnionFindForest state.links →
    (processBrauer state (circleWord loops)).openWires = state.openWires
  | 0, _, _ => rfl
  | loops + 1, state, forest => by
      have hstep : processBrauer state (circleWord (loops + 1))
          = processBrauer (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0)))
              (circleWord loops) :=
        processBrauer_append (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0)) state (circleWord loops)
      obtain ⟨freshFeet, hLen, hCupOpen, _⟩ :=
        cupFold_creates_atOffset 0 1 state [] state.openWires (by rw [List.nil_append]) rfl forest
      have forestCup : isUnionFindForest (processBrauer state (cupWord (natReplicate 1 0))).links :=
        processBrauer_links_isUnionFindForest (cupWord (natReplicate 1 0)) state forest
      have hCupOpen' : (processBrauer state (cupWord (natReplicate 1 0))).openWires
          = flattenNatPairs freshFeet ++ state.openWires := by rw [hCupOpen, List.nil_append]
      have hLenCap := (capFold_consumes freshFeet (processBrauer state (cupWord (natReplicate 1 0)))
          state.openWires hCupOpen' forestCup).1
      rw [hLen] at hLenCap
      have hOneStep : (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0))).openWires
          = state.openWires := by
        rw [processBrauer_append (cupWord (natReplicate 1 0)) state (capWord (natReplicate 1 0))]; exact hLenCap
      have forestOne : isUnionFindForest
          (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0))).links :=
        processBrauer_links_isUnionFindForest _ state forest
      rw [hstep, circleFold_openWires loops _ forestOne, hOneStep]

/-- ★★★ **The abstract-state CUP chain.**  On the seed-anchored post-cup state
`processBrauer (brauerSeed bc) prefixWord` whose open wires split as `throughBlock ++ flattenNatPairs freshFeet`,
firing the top crossing staircase `topPositions` then `circleWord loops` connects the two final top open wires at the
cup arc's read positions `order[posBase + doublePos rank]` and `order[posBase + doublePos rank + 1]` to the rank-th
fresh cup pair.  The weld: the interior tracker (post-cup) + GAP β (`natListGetAt_foldlAdjacentSwapBase`) + the top
decode `hDecode` route each final top wire to the post-cup wire at the `permInverse`-permuted position, the r26
keystone `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange` collapses that to the cup rank's fresh-block
offset, `natListGetAtAppendRightCup` lands it inside the fresh block, and `flattenNatPairs_pairGetMem` + the cup-fold
join close it, transported to the final state by `processBrauer_isSameComponent_ofBase` and `circleFold_openWires`. -/
theorem cupArcConnectViaState
    (bc : Nat) (bottomPos : 0 < bc) (prefixWord : List BrauerAtom) (topPositions : List Nat)
    (order throughBlock : List Nat) (freshFeet : List (Nat × Nat)) (topCount posBase loops rank : Nat)
    (hstate : (processBrauer (brauerSeed bc) prefixWord).openWires = throughBlock ++ flattenNatPairs freshFeet)
    (hbaseLen : throughBlock.length = posBase)
    (hwidth : (processBrauer (brauerSeed bc) prefixWord).openWires.length = topCount)
    (hOrderPerm : IsPermutationOfRange topCount order)
    (hDecode : permuteOfCrossingWord topCount topPositions = permInverse order)
    (hPosBound : ∀ pos, pos ∈ topPositions → pos + 2 ≤ topCount)
    (freshConn : ∀ pair, pair ∈ freshFeet →
      isSameComponent (processBrauer (brauerSeed bc) prefixWord).links pair.1 pair.2 = true)
    (forestPre : isUnionFindForest (processBrauer (brauerSeed bc) prefixWord).links)
    (rankFresh : rank < freshFeet.length)
    (hPosALt : posBase + doublePos rank < topCount)
    (hPosBLt : posBase + doublePos rank + 1 < topCount) :
    isSameComponent
        (processBrauer (processBrauer (brauerSeed bc) prefixWord)
          (crossingWord topPositions ++ circleWord loops)).links
        (natListGetAt (processBrauer (processBrauer (brauerSeed bc) prefixWord)
          (crossingWord topPositions ++ circleWord loops)).openWires
          (natListGetAt order (posBase + doublePos rank)))
        (natListGetAt (processBrauer (processBrauer (brauerSeed bc) prefixWord)
          (crossingWord topPositions ++ circleWord loops)).openWires
          (natListGetAt order (posBase + doublePos rank + 1))) = true := by
  have hF : processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions ++ circleWord loops)
      = processBrauer (processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions))
          (circleWord loops) :=
    processBrauer_append (crossingWord topPositions) (processBrauer (brauerSeed bc) prefixWord) (circleWord loops)
  have forestS5 : isUnionFindForest (processBrauer (processBrauer (brauerSeed bc) prefixWord)
      (crossingWord topPositions)).links :=
    processBrauer_links_isUnionFindForest (crossingWord topPositions) _ forestPre
  have hFow : (processBrauer (processBrauer (brauerSeed bc) prefixWord)
        (crossingWord topPositions ++ circleWord loops)).openWires
      = (processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions)).openWires := by
    rw [hF]; exact circleFold_openWires loops _ forestS5
  have tracker := crossingWordFold_openWire_sameComponent_afterPrefix bc bottomPos prefixWord topPositions
    (fun pos posMem => by rw [hwidth]; exact hPosBound pos posMem)
  -- widths for GAP beta
  have hCupTopALtWidth : natListGetAt order (posBase + doublePos rank)
      < (processBrauer (brauerSeed bc) prefixWord).openWires.length := by
    rw [hwidth]; exact hOrderPerm.isBounded (posBase + doublePos rank) hPosALt
  have hCupTopBLtWidth : natListGetAt order (posBase + doublePos rank + 1)
      < (processBrauer (brauerSeed bc) prefixWord).openWires.length := by
    rw [hwidth]; exact hOrderPerm.isBounded (posBase + doublePos rank + 1) hPosBLt
  -- the fresh reads
  have hBigA : natListGetAt (topPositions.foldl applyAdjacentSwap
        (processBrauer (brauerSeed bc) prefixWord).openWires) (natListGetAt order (posBase + doublePos rank))
      = natListGetAt (flattenNatPairs freshFeet) (doublePos rank) := by
    rw [natListGetAt_foldlAdjacentSwapBase (processBrauer (brauerSeed bc) prefixWord).openWires topPositions
        (natListGetAt order (posBase + doublePos rank)) hCupTopALtWidth, hwidth, hDecode,
      natListGetAtPermInverse_natListGetAt_ofPermutationOfRange topCount order hOrderPerm
        (posBase + doublePos rank) hPosALt, hstate,
      show posBase + doublePos rank = throughBlock.length + doublePos rank from by rw [hbaseLen]]
    exact natListGetAtAppendRightCup throughBlock (flattenNatPairs freshFeet) (doublePos rank)
  have hBigB : natListGetAt (topPositions.foldl applyAdjacentSwap
        (processBrauer (brauerSeed bc) prefixWord).openWires) (natListGetAt order (posBase + doublePos rank + 1))
      = natListGetAt (flattenNatPairs freshFeet) (doublePos rank + 1) := by
    rw [natListGetAt_foldlAdjacentSwapBase (processBrauer (brauerSeed bc) prefixWord).openWires topPositions
        (natListGetAt order (posBase + doublePos rank + 1)) hCupTopBLtWidth, hwidth, hDecode,
      natListGetAtPermInverse_natListGetAt_ofPermutationOfRange topCount order hOrderPerm
        (posBase + doublePos rank + 1) hPosBLt, hstate,
      show posBase + doublePos rank + 1 = throughBlock.length + (doublePos rank + 1) from by
        rw [hbaseLen, Nat.add_assoc]]
    exact natListGetAtAppendRightCup throughBlock (flattenNatPairs freshFeet) (doublePos rank + 1)
  -- chain A : S5.ow[cupTopA] ~F freshA
  have chainA : isSameComponent
      (processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions ++ circleWord loops)).links
      (natListGetAt (processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions)).openWires
        (natListGetAt order (posBase + doublePos rank)))
      (natListGetAt (flattenNatPairs freshFeet) (doublePos rank)) = true := by
    have htrack := tracker (natListGetAt order (posBase + doublePos rank))
    rw [hBigA] at htrack
    rw [hF]
    exact processBrauer_isSameComponent_ofBase (circleWord loops) _ forestS5 _ _ htrack
  have chainB : isSameComponent
      (processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions ++ circleWord loops)).links
      (natListGetAt (processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions)).openWires
        (natListGetAt order (posBase + doublePos rank + 1)))
      (natListGetAt (flattenNatPairs freshFeet) (doublePos rank + 1)) = true := by
    have htrack := tracker (natListGetAt order (posBase + doublePos rank + 1))
    rw [hBigB] at htrack
    rw [hF]
    exact processBrauer_isSameComponent_ofBase (circleWord loops) _ forestS5 _ _ htrack
  -- join A ~ B
  have pairMem := flattenNatPairs_pairGetMem freshFeet rank rankFresh
  have joinAB : isSameComponent
      (processBrauer (processBrauer (brauerSeed bc) prefixWord) (crossingWord topPositions ++ circleWord loops)).links
      (natListGetAt (flattenNatPairs freshFeet) (doublePos rank))
      (natListGetAt (flattenNatPairs freshFeet) (doublePos rank + 1)) = true :=
    processBrauer_isSameComponent_ofBase (crossingWord topPositions ++ circleWord loops)
      (processBrauer (brauerSeed bc) prefixWord) forestPre _ _ (freshConn _ pairMem)
  -- weld
  rw [hFow]
  exact isSameComponent_trans _ _ _ _
    (isSameComponent_trans _ _ _ _ chainA joinAB)
    (isSameComponent_flip _ _ _ chainB)



theorem natAddLeftCancelCup : (base left right : Nat) → base + left = base + right → left = right
  | 0, left, right, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | base + 1, left, right, h => by
      rw [Nat.succ_add, Nat.succ_add] at h
      exact natAddLeftCancelCup base left right (Nat.succ.inj h)

/-- The post-cap-post-middle state S3 of the corrected fold has open-wire width `= |throughStrandBottoms|`: the bottom
crossing gives width `bottomCount`, the cap block consumes `2·|caps|` front wires (via the `chunkFrontPairs` /
`dropFrontPairs` peel), and the middle crossing preserves width; `capArcFeetTwiceThroughSumsToBottom` closes the
arithmetic. -/
theorem cupChainS3Width (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    (processBrauer
        (processBrauer
          (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires.length
      = (throughStrandBottoms d.bottomCount d.partner).length := by
  have posBoundBottom := permutationToCrossingWord_posBound d.bottomCount
    (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner)
    (readOffBottomOrder_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded
  have forestS1 : isUnionFindForest (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).links :=
    processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil
  have wS1 : (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires.length = d.bottomCount :=
    crossingWordFold_openWires_length d.bottomCount _ (brauerSeed d.bottomCount)
      (brauerSeedOpenWiresLengthWidth d.bottomCount) posBoundBottom
  have capsLe : doublePos (capArcFeetIndices d.bottomCount d.partner).length
      ≤ (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires.length := by
    rw [wS1, doublePos_add]
    exact Nat.le.intro (capArcFeetTwiceThroughSumsToBottom d.bottomCount (d.bottomCount + d.topCount)
      d.partner (Nat.le_add_right d.bottomCount d.topCount) wf)
  have hSplit := chunkFrontPairs_flatten_split (capArcFeetIndices d.bottomCount d.partner).length
    (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires capsLe
  have hChunkLen := chunkFrontPairs_length (capArcFeetIndices d.bottomCount d.partner).length
    (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires capsLe
  have hCapConsume := (capFold_consumes
    (chunkFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)
    (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
    (dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)
    hSplit.symm forestS1).1
  rw [hChunkLen] at hCapConsume
  have hLenSplit : (flattenNatPairs (chunkFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)).length
      + (dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
          (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires).length
      = (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires.length := by
    rw [← natListLengthAppend, hSplit]
  have hFlatLen : (flattenNatPairs (chunkFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)).length
      = (capArcFeetIndices d.bottomCount d.partner).length + (capArcFeetIndices d.bottomCount d.partner).length := by
    rw [flattenNatPairs_length_doublePos, hChunkLen, doublePos_add]
  have hSum : (capArcFeetIndices d.bottomCount d.partner).length
      + (capArcFeetIndices d.bottomCount d.partner).length
      + (throughStrandBottoms d.bottomCount d.partner).length = d.bottomCount :=
    capArcFeetTwiceThroughSumsToBottom d.bottomCount (d.bottomCount + d.topCount) d.partner
      (Nat.le_add_right d.bottomCount d.topCount) wf
  have hDropLen : (dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires).length
      = (throughStrandBottoms d.bottomCount d.partner).length := by
    rw [hFlatLen] at hLenSplit
    apply natAddLeftCancelCup ((capArcFeetIndices d.bottomCount d.partner).length
      + (capArcFeetIndices d.bottomCount d.partner).length)
    rw [hLenSplit, wS1]
    exact hSum.symm
  have posBoundMiddle := permutationToCrossingWord_posBound (throughStrandBottoms d.bottomCount d.partner).length
    (throughStrandPerm d.bottomCount d.topCount d.partner)
    (throughStrandPerm_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded
  have hS2width : (processBrauer
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires.length
      = (throughStrandBottoms d.bottomCount d.partner).length := by
    show (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))).openWires.length
        = (throughStrandBottoms d.bottomCount d.partner).length
    rw [hCapConsume, hDropLen]
  show (processBrauer
      (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (permutationToCrossingWord (throughStrandBottoms d.bottomCount d.partner).length
        (throughStrandPerm d.bottomCount d.topCount d.partner)))).openWires.length
    = (throughStrandBottoms d.bottomCount d.partner).length
  exact crossingWordFold_openWires_length (throughStrandBottoms d.bottomCount d.partner).length _
    (processBrauer (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (capWord (reconstructStandardFormExt5Corrected d).capBlock)) hS2width posBoundMiddle



/-- ★★★ **THE CUP-CLASS PER-ARC T-CONNECT (GENERAL).**  For EVERY well-formed boundary involution `d` (with
`0 < d.bottomCount`) and every cup-arc rank `rank < |cupArcTopIndices|`, the rank-th cup arc's two TOP legs
(`cupArcTops[doublePos rank]`, `cupArcTops[doublePos rank + 1]`) share a union-find component in the corrected
six-phase fold state.  Instantiates `cupArcConnectViaState` on the corrected reconstruction: `cupChainS3Width` +
`cupFold_creates_atOffset` supply the post-cup open-wire split, `correctedTopPerm_decodesInverseReadOff` the decode,
`readOffTopOrder_isPermutationOfRange` the range-permutation, the ∗-dual crux `cupArcTwiceThroughSumsToTop` +
`throughStrandBottoms_length_eq_throughStrandTops` the width. -/
theorem cupArcConnect_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (rank : Nat) (rankLt : rank < (cupArcTopIndices d.bottomCount d.topCount d.partner).length) :
    isSameComponent
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (natListGetAt (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires
          (natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank)))
        (natListGetAt (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires
          (natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank + 1))) = true := by
  -- S3 width
  have hS3len := cupChainS3Width d wf
  have forestS3 : isUnionFindForest (processBrauer
      (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle)).links :=
    processBrauer_links_isUnionFindForest _ _ (processBrauer_links_isUnionFindForest _ _
      (processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil))
  -- cup fold on S3
  obtain ⟨freshFeet, hFreshLen, hS4ow, freshConn⟩ :=
    cupFold_creates_atOffset (throughStrandBottoms d.bottomCount d.partner).length
      (cupArcTopIndices d.bottomCount d.topCount d.partner).length
      (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
      (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires []
      (natListAppendNil _).symm hS3len forestS3
  -- prefix split: processBrauer seed prefixWord = processBrauer S3 (cupWord cupBlock)
  have hPrefix : processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
          ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
          ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock)
      = processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock) := by
    rw [processBrauer_append (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
        ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
        ++ crossingWord (reconstructStandardFormExt5Corrected d).middle) (brauerSeed d.bottomCount)
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock),
      processBrauer_append (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
        ++ capWord (reconstructStandardFormExt5Corrected d).capBlock) (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).middle),
      processBrauer_append (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)
        (brauerSeed d.bottomCount) (capWord (reconstructStandardFormExt5Corrected d).capBlock)]
  have hCupBlock : (reconstructStandardFormExt5Corrected d).cupBlock
      = natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length
          (throughStrandBottoms d.bottomCount d.partner).length := rfl
  rw [← hCupBlock] at hS4ow freshConn
  rw [← hPrefix] at hS4ow freshConn
  -- forest of post-cup (prefix) state
  have forestPre : isUnionFindForest (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
        ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
        ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
        ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).links :=
    processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil
  -- hstate
  have hstate : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
          ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
          ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires
      = (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
            (capWord (reconstructStandardFormExt5Corrected d).capBlock))
            (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires
        ++ flattenNatPairs freshFeet := by
    rw [hS4ow, natListAppendNil]
  -- hbaseLen
  have hbaseLen : (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires.length
      = (throughStrandTops d.bottomCount d.topCount d.partner).length := by
    rw [hS3len]
    exact throughStrandBottoms_length_eq_throughStrandTops d.bottomCount d.topCount d.partner wf
  -- hwidth
  have hwidth : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
          ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
          ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires.length
      = d.topCount := by
    rw [hstate, natListLengthAppend, flattenNatPairs_length_doublePos, hFreshLen, hS3len, doublePos_add,
      throughStrandBottoms_length_eq_throughStrandTops d.bottomCount d.topCount d.partner wf, Nat.add_comm]
    exact cupArcTwiceThroughSumsToTop d.bottomCount d.topCount d.partner wf
  -- hFEq : the weld state IS the full fold F
  have hFEq : processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
          ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
          ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).topPerm
          ++ circleWord (reconstructStandardFormExt5Corrected d).loops)
      = processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)) := by
    rw [hPrefix, processBrauer_append (crossingWord (reconstructStandardFormExt5Corrected d).topPerm)
        (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
        (circleWord (reconstructStandardFormExt5Corrected d).loops),
      ]
    exact (standardFormFold_appendSplit (reconstructStandardFormExt5Corrected d)).symm
  -- index conversions cupArcTops -> order
  have hIdxA : natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank)
      = natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner
          ++ cupArcTops d.bottomCount d.topCount d.partner)
          ((throughStrandTops d.bottomCount d.topCount d.partner).length + doublePos rank) :=
    (natListGetAtAppendRightCup (throughStrandTops d.bottomCount d.topCount d.partner)
      (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank)).symm
  have hIdxB : natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank + 1)
      = natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner
          ++ cupArcTops d.bottomCount d.topCount d.partner)
          ((throughStrandTops d.bottomCount d.topCount d.partner).length + doublePos rank + 1) := by
    rw [Nat.add_assoc]
    exact (natListGetAtAppendRightCup (throughStrandTops d.bottomCount d.topCount d.partner)
      (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank + 1)).symm
  -- arithmetic bounds
  have hPosALt : (throughStrandTops d.bottomCount d.topCount d.partner).length + doublePos rank < d.topCount := by
    have hlt : doublePos rank < (cupArcTopIndices d.bottomCount d.topCount d.partner).length
        + (cupArcTopIndices d.bottomCount d.topCount d.partner).length := by
      rw [← doublePos_add]
      exact doublePos_lt_doublePos rank (cupArcTopIndices d.bottomCount d.topCount d.partner).length rankLt
    have hstep : (throughStrandTops d.bottomCount d.topCount d.partner).length + doublePos rank
        < (throughStrandTops d.bottomCount d.topCount d.partner).length
          + ((cupArcTopIndices d.bottomCount d.topCount d.partner).length
            + (cupArcTopIndices d.bottomCount d.topCount d.partner).length) :=
      Nat.add_lt_add_left hlt _
    have htc : (throughStrandTops d.bottomCount d.topCount d.partner).length
        + ((cupArcTopIndices d.bottomCount d.topCount d.partner).length
          + (cupArcTopIndices d.bottomCount d.topCount d.partner).length) = d.topCount := by
      rw [Nat.add_comm]
      exact cupArcTwiceThroughSumsToTop d.bottomCount d.topCount d.partner wf
    rw [htc] at hstep; exact hstep
  have hPosBLt : (throughStrandTops d.bottomCount d.topCount d.partner).length + doublePos rank + 1 < d.topCount := by
    have hlt : doublePos rank + 1 < (cupArcTopIndices d.bottomCount d.topCount d.partner).length
        + (cupArcTopIndices d.bottomCount d.topCount d.partner).length := by
      rw [← doublePos_add]
      exact doublePos_succ_lt_doublePos rank (cupArcTopIndices d.bottomCount d.topCount d.partner).length rankLt
    have hstep : (throughStrandTops d.bottomCount d.topCount d.partner).length + (doublePos rank + 1)
        < (throughStrandTops d.bottomCount d.topCount d.partner).length
          + ((cupArcTopIndices d.bottomCount d.topCount d.partner).length
            + (cupArcTopIndices d.bottomCount d.topCount d.partner).length) :=
      Nat.add_lt_add_left hlt _
    have htc : (throughStrandTops d.bottomCount d.topCount d.partner).length
        + ((cupArcTopIndices d.bottomCount d.topCount d.partner).length
          + (cupArcTopIndices d.bottomCount d.topCount d.partner).length) = d.topCount := by
      rw [Nat.add_comm]
      exact cupArcTwiceThroughSumsToTop d.bottomCount d.topCount d.partner wf
    rw [htc, ← Nat.add_assoc] at hstep; exact hstep
  -- convert target and apply the weld
  rw [hIdxA, hIdxB, ← hFEq]
  exact cupArcConnectViaState d.bottomCount bottomPos
    (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
      ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
      ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
      ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock)
    (reconstructStandardFormExt5Corrected d).topPerm
    (throughStrandTops d.bottomCount d.topCount d.partner ++ cupArcTops d.bottomCount d.topCount d.partner)
    (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires
    freshFeet d.topCount (throughStrandTops d.bottomCount d.topCount d.partner).length
    (reconstructStandardFormExt5Corrected d).loops rank
    hstate hbaseLen hwidth
    (readOffTopOrder_isPermutationOfRange d.bottomCount d.topCount d.partner wf)
    (correctedTopPerm_decodesInverseReadOff d wf)
    (permutationToCrossingWord_posBound d.topCount
      (permInverse (throughStrandTops d.bottomCount d.topCount d.partner
        ++ cupArcTops d.bottomCount d.topCount d.partner))
      (readOffTopOrderInverse_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded)
    freshConn forestPre (by rw [hFreshLen]; exact rankLt) hPosALt hPosBLt



/-- ★★★ **The CUP-class per-arc T-CONNECT, in the boundary-matching form (the `partnerShares` datum).**  Both feet of
a cup arc are top ports, so `matchingSameComponent d.bottomCount F (bottomCount + a) (bottomCount + b)` reduces to node
connectivity (`matchingSameComponent_topTop_eq_isSameComponent`), which `cupArcConnect_general` supplies — the exact
per-arc datum the r22 routing collapse consumes, discharged in general for the CUP class. -/
theorem cupArcMatching_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (rank : Nat) (rankLt : rank < (cupArcTopIndices d.bottomCount d.topCount d.partner).length) :
    matchingSameComponent d.bottomCount
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
        (d.bottomCount + natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank))
        (d.bottomCount + natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank + 1)) = true := by
  rw [matchingSameComponent_topTop_eq_isSameComponent d.bottomCount
    (processBrauer (brauerSeed d.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
    (natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank))
    (natListGetAt (cupArcTops d.bottomCount d.topCount d.partner) (doublePos rank + 1))]
  exact cupArcConnect_general d bottomPos wf rank rankLt

-- firing probe on adversarial-B (cup arc 3<->5, rank 0)
/-- ★★ **The GENERAL CUP matching form FIRES on the adversarial-B witness (cup arc `3↔5`, rank `0`).**
`cupArcMatching_general` exercised (not `decide`d) on a genuine crossing-cup witness. -/
theorem cupArcMatching_firesAdversarialB :
    matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram)))
        (3 + natListGetAt (cupArcTops 3 3 adversarialBDiagram.partner) (doublePos 0))
        (3 + natListGetAt (cupArcTops 3 3 adversarialBDiagram.partner) (doublePos 0 + 1)) = true :=
  cupArcMatching_general adversarialBDiagram (by decide) isBoundaryInvolution_adversarialBDiagram 0 (by decide)

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

/-- ★★★ **Honesty marker — the GENERAL per-arc CUP-class T-CONNECT is SHIPPED (r26, the cup chain assembled).**
`cupArcConnect_general` proves, zero-axiom and structural, that for EVERY well-formed boundary involution (with
`0 < bottomCount`) the rank-th cup arc's two TOP legs share a union-find component in the corrected six-phase fold;
`cupArcMatching_general` lifts it to the boundary-matching `partnerShares` datum the r22 routing collapse consumes.
The assembly is the recon's cup chain: `cupChainS3Width` + `cupFold_creates_atOffset` (post-cup open-wire split) + the
r23 interior tracker (`crossingWordFold_openWire_sameComponent_afterPrefix`) + the r25 GAP β base-permute bridge + the
r19 `correctedTopPerm_decodesInverseReadOff` + the r26 rank↔position keystone
(`natListGetAtPermInverse_natListGetAt_ofPermutationOfRange`), with `circleFold_openWires` carrying the final target
past the circle phase.  This is the SECOND of the three per-arc classes (after CAP); alone it flips NO master —
`fxBrauer_hasTConnectThroughWall` stays `false` until the THROUGH class and the all-class dispatch also land.
Fired on the adversarial-B cup arc `3↔5` (`cupArcMatching_firesAdversarialB`).  `= true`. -/
def fxBrauer_hasCupClassTConnect : Bool := true

end FX1Poly.Polygraph
