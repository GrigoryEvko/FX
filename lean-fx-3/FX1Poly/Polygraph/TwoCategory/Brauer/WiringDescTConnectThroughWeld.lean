import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughChain

/-! # BRAUER r28 — THE THROUGH WELD: the five-phase node-survival chain + the general THROUGH per-arc T-CONNECT

The r27 ledger (`Brauer/WiringDescBrauerR27Ledger.lean`) named the residual verbatim: with the P1 seam decode leg
(`throughReadOffBottom_reads_throughFoot`) shipped general, the THROUGH per-arc T-CONNECT is blocked only at the
FIVE-PHASE node-survival WELD.  The through wire's node must survive a never-severed connectivity chain from the seed
bottom foot `i = partner[bottomCount + t]` to its read top port `F.openWires[t]`, across all five phases:

    i  ~[P1 seed tracker + P1 decode]        S1.openWires[|capArcFeet| + r]
       =[P2 cap-survival append-right read]  S2.openWires[r]
       ~[P3 middle tracker + GAP β + middle decode + rank glue] S3.openWires[topRank]   (r = throughStrandPerm[topRank])
       =[P4 cup-survival append-left read]   S4.openWires[topRank]
       ~[P5 top tracker + GAP β + top decode + r26 keystone]    F.openWires[t]          (t = throughStrandTops[topRank])

This file assembles that chain, seam by seam, then welds it by `isSameComponent_trans` / `_flip` — a direct scale of
`cupArcConnectViaState`'s two-tier weld, but with a FIXED SEED NODE `i` at the left endpoint (not an open wire) and a
THROUGH-BLOCK (append-LEFT) read at the right, so it is a genuine sibling, not an instance of the CUP weld.

Every per-seam ingredient is shipped: the seed tracker (`crossingWordFold_openWire_sameComponent_incomingPort_seed`),
the interior tracker (`crossingWordFold_openWire_sameComponent_afterPrefix`), GAP β
(`natListGetAt_foldlAdjacentSwapBase`), the two decodes (`correctedMiddle_decodesReadOff`,
`correctedTopPerm_decodesInverseReadOff`), the r26 keystone
(`natListGetAtPermInverse_natListGetAt_ofPermutationOfRange`), the phase folds (`capFold_consumes`,
`cupFold_creates_atOffset`), the append reads (`natListGetAtAppendRightCup`, `natListGetAtAppendLeftCap`), the width
chain (`cupChainS3Width`), and `circleFold_openWires`.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only on closed
literals (the probes).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The post-cap state S2 width (the shared width the recon named `capChainS2Width`) -/

/-- The post-bottomPerm-post-cap state S2 of the corrected fold has open-wire width `= |throughStrandBottoms|`: the
bottom crossing gives width `bottomCount`, and the cap block consumes `2·|caps|` front wires (via the `chunkFrontPairs`
/ `dropFrontPairs` peel), so what remains is exactly the through block.  The truncation of `cupChainS3Width` at the
post-cap seam — shared by the P2 / P3 seams of the THROUGH weld. -/
theorem capChainS2Width (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    (processBrauer
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires.length
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
  show (processBrauer (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
    (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))).openWires.length
      = (throughStrandBottoms d.bottomCount d.partner).length
  rw [hCapConsume, hDropLen]

/-! ## P2 — the cap-survival append-right read (the r-th through wire survives the cap block) -/

/-- ★★★ **P2 — the cap-survival read.**  The bottom-crossing open wire at slot `|capArcFeet| + rIdx` of S1 is the SAME
wire id read at slot `rIdx` of the post-cap state S2 — the cap block consumes the front `2·|caps|` wires
(`capFold_consumes`), leaving the through block, and the append-right read `natListGetAtAppendRightCup` past the flattened
cap-foot pairs lands slot `rIdx` of the tail.  The P2 seam of the five-phase THROUGH weld — an EQUALITY of wire ids (no
bound on `rIdx` needed). -/
theorem throughCapSurvival (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) (rIdx : Nat) :
    natListGetAt (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires
        ((capArcFeet d.bottomCount d.partner).length + rIdx)
      = natListGetAt (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires rIdx := by
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
  have hCapConsume : (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))).openWires
      = dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
          (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires := by
    have h := (capFold_consumes
      (chunkFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)
      hSplit.symm forestS1).1
    rw [hChunkLen] at h
    exact h
  have hFeetLenEq : (capArcFeet d.bottomCount d.partner).length
      = (flattenNatPairs (chunkFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
          (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)).length := by
    rw [flattenNatPairs_length_doublePos, hChunkLen, doublePos_add]
    exact expandBottomFeetPairs_length d.partner (capArcFeetIndices d.bottomCount d.partner)
  have step : natListGetAt (flattenNatPairs (chunkFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)
        ++ dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
          (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires)
        ((capArcFeet d.bottomCount d.partner).length + rIdx)
      = natListGetAt (dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
          (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires) rIdx := by
    rw [hFeetLenEq]
    exact natListGetAtAppendRightCup
      (flattenNatPairs (chunkFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires))
      (dropFrontPairs (capArcFeetIndices d.bottomCount d.partner).length
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires) rIdx
  rw [hSplit] at step
  show natListGetAt (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires
      ((capArcFeet d.bottomCount d.partner).length + rIdx)
    = natListGetAt (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0))).openWires rIdx
  rw [hCapConsume]
  exact step

/-! ## P4 — the cup-survival append-left read (the through wire survives the interior cup block) -/

/-- ★★★ **P4 — the cup-survival read.**  The through wire at slot `idx < |throughStrandBottoms|` of the post-middle
state S3 is the SAME wire id read at slot `idx` of the post-cup state S4 — the interior cup block fires at offset
`|throughBottoms|` (`cupFold_creates_atOffset`, `front = S3.openWires`, `back = []`), prepending fresh pairs AFTER the
through block, so `S4.openWires = S3.openWires ++ fresh` and the append-LEFT read `natListGetAtAppendLeftCap` lands
inside the through block.  The P4 seam of the five-phase THROUGH weld. -/
theorem throughCupSurvival (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (idx : Nat) (idxLt : idx < (throughStrandBottoms d.bottomCount d.partner).length) :
    natListGetAt (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires idx
      = natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires idx := by
  have hS3len := cupChainS3Width d wf
  have forestS3 : isUnionFindForest (processBrauer
      (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle)).links :=
    processBrauer_links_isUnionFindForest _ _ (processBrauer_links_isUnionFindForest _ _
      (processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil))
  obtain ⟨freshFeet, _hFreshLen, hS4ow, _freshConn⟩ :=
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
  have hCupBlock : (reconstructStandardFormExt5Corrected d).cupBlock
      = natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length
          (throughStrandBottoms d.bottomCount d.partner).length := rfl
  have idxLtS3 : idx < (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires.length := by
    rw [hS3len]; exact idxLt
  rw [hCupBlock, hS4ow]
  exact (natListGetAtAppendLeftCap
    (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires
    (flattenNatPairs freshFeet ++ []) idx idxLtS3).symm

/-! ## B1 truth-probes — the survival seams FIRE on the monster and the empty-block 3-through -/

/-- ★ **P2 FIRES on the width-12 monster** (through rank `0`: `|capArcFeet| = 4`, `throughStrandPerm[0] = 0`). -/
theorem throughCapSurvival_firesMonster :
    natListGetAt (processBrauer (brauerSeed 6)
        (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm)).openWires
        ((capArcFeet 6 monsterDiagram.partner).length
          + natListGetAt (throughStrandPerm 6 6 monsterDiagram.partner) 0)
      = natListGetAt (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock)).openWires
          (natListGetAt (throughStrandPerm 6 6 monsterDiagram.partner) 0) :=
  throughCapSurvival monsterDiagram monster_isBoundaryInvolution
    (natListGetAt (throughStrandPerm 6 6 monsterDiagram.partner) 0)

/-- ★ **P2 FIRES on the empty-cap 3-through** (`capArcFeetIndices = []`, so the cap block is a no-op — the base case). -/
theorem throughCapSurvival_firesThreeThrough :
    natListGetAt (processBrauer (brauerSeed 3)
        (crossingWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).bottomPerm)).openWires
        ((capArcFeet 3 threeThroughCrossingDiagram.partner).length + 2)
      = natListGetAt (processBrauer (processBrauer (brauerSeed 3)
          (crossingWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).capBlock)).openWires 2 :=
  throughCapSurvival threeThroughCrossingDiagram isBoundaryInvolution_threeThroughCrossing 2

/-- ★ **P4 FIRES on the width-12 monster** (through rank `0`, `topRank = 0 < |throughStrandBottoms| = 2`). -/
theorem throughCupSurvival_firesMonster :
    natListGetAt (processBrauer (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).middle)).openWires 0
      = natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).middle))
          (cupWord (reconstructStandardFormExt5Corrected monsterDiagram).cupBlock)).openWires 0 :=
  throughCupSurvival monsterDiagram monster_isBoundaryInvolution 0 (by decide)

/-- ★ **P4 FIRES on the empty-cup 3-through** (`cupArcTopIndices = []`, so the cup block is a no-op — the base case). -/
theorem throughCupSurvival_firesThreeThrough :
    natListGetAt (processBrauer (processBrauer (processBrauer (brauerSeed 3)
          (crossingWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).middle)).openWires 1
      = natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed 3)
          (crossingWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).middle))
          (cupWord (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram).cupBlock)).openWires 1 :=
  throughCupSurvival threeThroughCrossingDiagram isBoundaryInvolution_threeThroughCrossing 1 (by decide)

/-- ★★ **Honesty marker — the THROUGH survival seams P2 / P4 are SHIPPED (r28 B1).**  `throughCapSurvival` (the
cap-survival append-right read: the through wire at S1 slot `|capArcFeet| + r` survives the cap block to S2 slot `r`)
and `throughCupSurvival` (the cup-survival append-left read: the through wire at S3 slot `topRank` survives the interior
cup block to S4 slot `topRank`) are the two EQUALITY seams of the five-phase THROUGH node-survival weld, plus the shared
`capChainS2Width`.  Fired on the width-12 monster and the empty-block 3-through.  A NEW ingredient marker; it flips NO
master.  `= true`. -/
def fxBrauer_hasThroughSurvivalSeams : Bool := true

/-! ## The post-cup state S4 width (needed for the P5 top-tracker GAP β) -/

/-- The post-cup state S4 of the corrected fold has open-wire width `= topCount`: the through block (`|throughBottoms|
= |throughStrandTops|`) plus the `2·|cups|` fresh cup wires (`cupArcTwiceThroughSumsToTop`).  Mirrors the `hwidth`
derivation inside `cupArcConnect_general`. -/
theorem cupChainS4Width (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires.length
      = d.topCount := by
  have hS3len := cupChainS3Width d wf
  have forestS3 : isUnionFindForest (processBrauer
      (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle)).links :=
    processBrauer_links_isUnionFindForest _ _ (processBrauer_links_isUnionFindForest _ _
      (processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil))
  obtain ⟨freshFeet, hFreshLen, hS4ow, _freshConn⟩ :=
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
  have hCupBlock : (reconstructStandardFormExt5Corrected d).cupBlock
      = natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length
          (throughStrandBottoms d.bottomCount d.partner).length := rfl
  rw [hCupBlock, hS4ow, natListAppendNil, natListLengthAppend, flattenNatPairs_length_doublePos, hFreshLen,
    hS3len, doublePos_add, throughStrandBottoms_length_eq_throughStrandTops d.bottomCount d.topCount d.partner wf,
    Nat.add_comm]
  exact cupArcTwiceThroughSumsToTop d.bottomCount d.topCount d.partner wf

/-! ## P3 — the middle-phase tracker (the through wire tracked across the interior middle crossing) -/

/-- ★★★ **P3 — the middle-phase tracker.**  The post-middle open wire at S3 slot `idx < |throughStrandBottoms|` shares
a union-find component with the post-cap open wire at S2 slot `throughStrandPerm[idx]` — the interior `middle` tracker
(`crossingWordFold_openWire_sameComponent_afterPrefix` after the `bottomPerm ++ cap` prefix) routes S3's open wire to
S2's open wire at the GAP β permuted position, and the middle decode `correctedMiddle_decodesReadOff` identifies that
permutation as `throughStrandPerm`.  The P3 connectivity seam of the five-phase THROUGH weld. -/
theorem throughMiddleTracker (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (idx : Nat) (idxLt : idx < (throughStrandBottoms d.bottomCount d.partner).length) :
    isSameComponent (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle)).links
        (natListGetAt (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires idx)
        (natListGetAt (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires
          (natListGetAt (throughStrandPerm d.bottomCount d.topCount d.partner) idx)) = true := by
  have hS2width := capChainS2Width d wf
  have hPrefixEq : processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
          ++ capWord (reconstructStandardFormExt5Corrected d).capBlock)
      = processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock) :=
    processBrauer_append (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)
      (brauerSeed d.bottomCount) (capWord (reconstructStandardFormExt5Corrected d).capBlock)
  have hPrefixWidth : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
          ++ capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires.length
      = (throughStrandBottoms d.bottomCount d.partner).length := by
    rw [hPrefixEq]; exact hS2width
  have trackerRaw := crossingWordFold_openWire_sameComponent_afterPrefix d.bottomCount bottomPos
    (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
      ++ capWord (reconstructStandardFormExt5Corrected d).capBlock)
    (reconstructStandardFormExt5Corrected d).middle
    (fun pos posMem => by
      rw [hPrefixWidth]
      exact permutationToCrossingWord_posBound (throughStrandBottoms d.bottomCount d.partner).length
        (throughStrandPerm d.bottomCount d.topCount d.partner)
        (throughStrandPerm_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded pos posMem)
  rw [hPrefixEq] at trackerRaw
  have hIdxLtS2 : idx < (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires.length := by
    rw [hS2width]; exact idxLt
  have hRead3 : natListGetAt ((reconstructStandardFormExt5Corrected d).middle.foldl applyAdjacentSwap
        (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires) idx
      = natListGetAt (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires
          (natListGetAt (throughStrandPerm d.bottomCount d.topCount d.partner) idx) := by
    rw [natListGetAt_foldlAdjacentSwapBase (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires
        (reconstructStandardFormExt5Corrected d).middle idx hIdxLtS2,
      hS2width, correctedMiddle_decodesReadOff d wf]
  have hst := trackerRaw idx
  rw [hRead3] at hst
  exact hst

/-! ## P5 — the top-phase tracker (the read top port tracked back to the through block) -/

/-- ★★★ **P5 — the top-phase tracker.**  The final post-topPerm open wire at S5 slot `throughStrandTops[idx]` shares a
union-find component with the post-cup open wire at S4 slot `idx` — the interior `topPerm` tracker (after the
`bottomPerm ++ cap ++ middle ++ cup` prefix) routes S5's open wire to S4's open wire at the GAP β permuted position,
`correctedTopPerm_decodesInverseReadOff` identifies that as `permInverse (throughStrandTops ++ cupArcTops)`, and the
r26 keystone `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange` collapses the inverse read at
`(throughStrandTops ++ cupArcTops)[idx] = throughStrandTops[idx]` (append-left) back to `idx`.  The P5 connectivity
seam of the five-phase THROUGH weld — the append-LEFT mirror of the CUP P5. -/
theorem throughTopTracker (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (idx : Nat) (idxLt : idx < (throughStrandTops d.bottomCount d.topCount d.partner).length) :
    isSameComponent (processBrauer (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).topPerm)).links
        (natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).topPerm)).openWires
          (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) idx))
        (natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires idx) = true := by
  have hS4width := cupChainS4Width d wf
  have hOrderPerm := readOffTopOrder_isPermutationOfRange d.bottomCount d.topCount d.partner wf
  have hTopsLe : (throughStrandTops d.bottomCount d.topCount d.partner).length ≤ d.topCount := by
    have hlen : (throughStrandTops d.bottomCount d.topCount d.partner).length
        + (cupArcTops d.bottomCount d.topCount d.partner).length = d.topCount := by
      rw [← natListLengthAppend]; exact hOrderPerm.hasWidthLength
    exact Nat.le.intro hlen
  have hIdxLtTop : idx < d.topCount := Nat.lt_of_lt_of_le idxLt hTopsLe
  have hOrderIdx : natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner
        ++ cupArcTops d.bottomCount d.topCount d.partner) idx
      = natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) idx :=
    natListGetAtAppendLeftCap (throughStrandTops d.bottomCount d.topCount d.partner)
      (cupArcTops d.bottomCount d.topCount d.partner) idx idxLt
  have hTLtS4 : natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) idx
      < (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires.length := by
    rw [hS4width, ← hOrderIdx]
    exact hOrderPerm.isBounded idx hIdxLtTop
  have hPrefixEq4 : processBrauer (brauerSeed d.bottomCount)
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
  have hPrefixWidth4 : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
          ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
          ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires.length = d.topCount := by
    rw [hPrefixEq4]; exact hS4width
  have trackerRaw := crossingWordFold_openWire_sameComponent_afterPrefix d.bottomCount bottomPos
    (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm
      ++ capWord (reconstructStandardFormExt5Corrected d).capBlock
      ++ crossingWord (reconstructStandardFormExt5Corrected d).middle
      ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock)
    (reconstructStandardFormExt5Corrected d).topPerm
    (fun pos posMem => by
      rw [hPrefixWidth4]
      exact permutationToCrossingWord_posBound d.topCount
        (permInverse (throughStrandTops d.bottomCount d.topCount d.partner
          ++ cupArcTops d.bottomCount d.topCount d.partner))
        (readOffTopOrderInverse_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded pos posMem)
  rw [hPrefixEq4] at trackerRaw
  have hRead5 : natListGetAt ((reconstructStandardFormExt5Corrected d).topPerm.foldl applyAdjacentSwap
        (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires)
        (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) idx)
      = natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires idx := by
    rw [natListGetAt_foldlAdjacentSwapBase (processBrauer (processBrauer (processBrauer (processBrauer
        (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires
        (reconstructStandardFormExt5Corrected d).topPerm
        (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) idx) hTLtS4,
      hS4width, correctedTopPerm_decodesInverseReadOff d wf, ← hOrderIdx,
      natListGetAtPermInverse_natListGetAt_ofPermutationOfRange d.topCount
        (throughStrandTops d.bottomCount d.topCount d.partner
          ++ cupArcTops d.bottomCount d.topCount d.partner) hOrderPerm idx hIdxLtTop]
  have hst := trackerRaw (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) idx)
  rw [hRead5] at hst
  exact hst

/-! ## B2 truth-probes — the connectivity seams P3 / P5 FIRE on the monster and the 3-through -/

/-- ★ **P3 FIRES on the width-12 monster** (through rank `0`, `idx = 0 < |throughStrandBottoms| = 2`). -/
theorem throughMiddleTracker_firesMonster :
    isSameComponent (processBrauer (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).middle)).links
        (natListGetAt (processBrauer (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).middle)).openWires 0)
        (natListGetAt (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock)).openWires
          (natListGetAt (throughStrandPerm 6 6 monsterDiagram.partner) 0)) = true :=
  throughMiddleTracker monsterDiagram (by decide) monster_isBoundaryInvolution 0 (by decide)

/-- ★ **P5 FIRES on the width-12 monster** (through rank `1`, `idx = 1 < |throughStrandTops| = 2`). -/
theorem throughTopTracker_firesMonster :
    isSameComponent (processBrauer (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).middle))
          (cupWord (reconstructStandardFormExt5Corrected monsterDiagram).cupBlock))
        (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).topPerm)).links
        (natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).middle))
          (cupWord (reconstructStandardFormExt5Corrected monsterDiagram).cupBlock))
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).topPerm)).openWires
          (natListGetAt (throughStrandTops 6 6 monsterDiagram.partner) 1))
        (natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed 6)
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected monsterDiagram).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected monsterDiagram).middle))
          (cupWord (reconstructStandardFormExt5Corrected monsterDiagram).cupBlock)).openWires 1) = true :=
  throughTopTracker monsterDiagram (by decide) monster_isBoundaryInvolution 1 (by decide)

/-- ★★ **Honesty marker — the THROUGH connectivity seams P3 / P5 are SHIPPED (r28 B2).**  `throughMiddleTracker` (the
interior `middle` tracker + GAP β + middle decode: S3's through wire ~ S2's wire at `throughStrandPerm[idx]`) and
`throughTopTracker` (the interior `topPerm` tracker + GAP β + top decode + r26 keystone: S5's read top port ~ S4's
through wire at `idx`) are the two CONNECTIVITY seams of the five-phase THROUGH node-survival weld, plus the shared
`cupChainS4Width`.  Fired on the width-12 monster.  A NEW ingredient marker; it flips NO master.  `= true`. -/
def fxBrauer_hasThroughTrackerSeams : Bool := true

/-! ## THE WELD — the general per-arc THROUGH-class T-CONNECT (five phases chained) -/

/-- ★★★ **THE THROUGH-CLASS PER-ARC T-CONNECT (GENERAL).**  For EVERY well-formed boundary involution `d` (with
`0 < d.bottomCount`) and every through-top rank `topRank < |throughStrandTops|`, the through arc's bottom foot
`i = partner[bottomCount + throughStrandTops[topRank]]` and its read top open wire `F.openWires[throughStrandTops[topRank]]`
share a union-find component in the corrected six-phase fold state `F`.  The five-phase node-survival WELD: the seed
`bottomPerm` tracker + P1 decode (`throughReadOffBottom_reads_throughFoot`) land `i` on S1's slot `|capArcFeet| + r`;
`throughCapSurvival` (P2) survives it across the cap block to S2's slot `r`; `throughMiddleTracker` (P3) routes S3's
through wire to S2's slot `r`; `throughCupSurvival` (P4) survives S3's slot `topRank` across the interior cup block to
S4; `throughTopTracker` (P5) routes S5's read top port back to S4's slot `topRank`; and `circleFold_openWires` carries
the target past the circle phase.  Every fact transported to `F.links` by `processBrauer_isSameComponent_ofBase`
through `foldFactorsThroughCap` / `foldFactorsThroughCup` / `standardFormFold_appendSplit`, then welded by
`isSameComponent_trans` / `_flip`.  The THIRD (and last) of the three per-arc classes, with a FIXED SEED NODE at the
left endpoint — the append-LEFT sibling of the CUP weld. -/
theorem throughArcConnect_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (topRank : Nat) (topRankLt : topRank < (throughStrandTops d.bottomCount d.topCount d.partner).length) :
    isSameComponent
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (natListGetAt d.partner
          (d.bottomCount + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank))
        (natListGetAt (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires
          (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank)) = true := by
  have hTopRankLtBottoms : topRank < (throughStrandBottoms d.bottomCount d.partner).length := by
    rw [throughStrandBottoms_length_eq_throughStrandTops d.bottomCount d.topCount d.partner wf]
    exact topRankLt
  -- forests
  have forestS1 : isUnionFindForest (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).links :=
    processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil
  have forestS3 : isUnionFindForest (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle)).links :=
    processBrauer_links_isUnionFindForest _ _ (processBrauer_links_isUnionFindForest _ _
      (processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil))
  have forestS5 : isUnionFindForest (processBrauer (processBrauer (processBrauer (processBrauer
      (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (capWord (reconstructStandardFormExt5Corrected d).capBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle))
      (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
      (crossingWord (reconstructStandardFormExt5Corrected d).topPerm)).links :=
    processBrauer_links_isUnionFindForest _ _ (processBrauer_links_isUnionFindForest _ _
      (processBrauer_links_isUnionFindForest _ _ (processBrauer_links_isUnionFindForest _ _
        (processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil))))
  -- transport equalities to F
  have hFS1 : processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock
          ++ (crossingWord (reconstructStandardFormExt5Corrected d).middle
            ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock
            ++ crossingWord (reconstructStandardFormExt5Corrected d).topPerm
            ++ circleWord (reconstructStandardFormExt5Corrected d).loops))
      = processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)) := by
    rw [processBrauer_append (capWord (reconstructStandardFormExt5Corrected d).capBlock)
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
      (crossingWord (reconstructStandardFormExt5Corrected d).middle
        ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock
        ++ crossingWord (reconstructStandardFormExt5Corrected d).topPerm
        ++ circleWord (reconstructStandardFormExt5Corrected d).loops)]
    exact (foldFactorsThroughCap (reconstructStandardFormExt5Corrected d)).symm
  have hFS3 : processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).topPerm
          ++ circleWord (reconstructStandardFormExt5Corrected d).loops)
      = processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)) :=
    (foldFactorsThroughCup (reconstructStandardFormExt5Corrected d)).symm
  have hFS5 : processBrauer (processBrauer (processBrauer (processBrauer (processBrauer
          (processBrauer (brauerSeed d.bottomCount)
            (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).topPerm))
        (circleWord (reconstructStandardFormExt5Corrected d).loops)
      = processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)) :=
    (standardFormFold_appendSplit (reconstructStandardFormExt5Corrected d)).symm
  -- P1 at S1 : S1.ow[|capArcFeet| + r] ~ i
  have hP1 : isSameComponent (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).links
        (natListGetAt (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires
          ((capArcFeet d.bottomCount d.partner).length
            + natListGetAt (throughStrandPerm d.bottomCount d.topCount d.partner) topRank))
        (natListGetAt d.partner
          (d.bottomCount + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank)) = true := by
    have hseed := crossingWordFold_openWire_sameComponent_incomingPort_seed d.bottomCount bottomPos
      (reconstructStandardFormExt5Corrected d).bottomPerm
      (fun pos posMem => permutationToCrossingWord_posBound d.bottomCount
        (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner)
        (readOffBottomOrder_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded pos posMem)
      ((capArcFeet d.bottomCount d.partner).length
        + natListGetAt (throughStrandPerm d.bottomCount d.topCount d.partner) topRank)
    rw [correctedBottomPerm_decodesReadOff d wf,
      throughReadOffBottom_reads_throughFoot d wf topRank topRankLt] at hseed
    exact hseed
  -- transport P1 to F
  have fA0 : isSameComponent (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (natListGetAt (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires
          ((capArcFeet d.bottomCount d.partner).length
            + natListGetAt (throughStrandPerm d.bottomCount d.topCount d.partner) topRank))
        (natListGetAt d.partner
          (d.bottomCount + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank)) = true := by
    rw [← hFS1]
    exact processBrauer_isSameComponent_ofBase (capWord (reconstructStandardFormExt5Corrected d).capBlock
        ++ (crossingWord (reconstructStandardFormExt5Corrected d).middle
          ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).topPerm
          ++ circleWord (reconstructStandardFormExt5Corrected d).loops))
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)) forestS1 _ _ hP1
  -- P2 equality
  have hP2 := throughCapSurvival d wf (natListGetAt (throughStrandPerm d.bottomCount d.topCount d.partner) topRank)
  rw [hP2] at fA0
  have fA := isSameComponent_flip _ _ _ fA0
  -- P3 at S3, transport to F
  have hP3 := throughMiddleTracker d bottomPos wf topRank hTopRankLtBottoms
  have fB0 : isSameComponent (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (natListGetAt (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle)).openWires topRank)
        (natListGetAt (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock)).openWires
          (natListGetAt (throughStrandPerm d.bottomCount d.topCount d.partner) topRank)) = true := by
    rw [← hFS3]
    exact processBrauer_isSameComponent_ofBase (cupWord (reconstructStandardFormExt5Corrected d).cupBlock
        ++ crossingWord (reconstructStandardFormExt5Corrected d).topPerm
        ++ circleWord (reconstructStandardFormExt5Corrected d).loops)
      (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle)) forestS3 _ _ hP3
  have fB := isSameComponent_flip _ _ _ fB0
  -- P4 equality, P5 at S5 transport to F
  have hP4 := throughCupSurvival d wf topRank hTopRankLtBottoms
  have hP5 := throughTopTracker d bottomPos wf topRank topRankLt
  have fC0 : isSameComponent (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).topPerm)).openWires
          (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank))
        (natListGetAt (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
          (capWord (reconstructStandardFormExt5Corrected d).capBlock))
          (crossingWord (reconstructStandardFormExt5Corrected d).middle))
          (cupWord (reconstructStandardFormExt5Corrected d).cupBlock)).openWires topRank) = true := by
    rw [← hFS5]
    exact processBrauer_isSameComponent_ofBase (circleWord (reconstructStandardFormExt5Corrected d).loops)
      (processBrauer (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).topPerm)) forestS5 _ _ hP5
  rw [← hP4] at fC0
  have fC := isSameComponent_flip _ _ _ fC0
  -- circle carries F.openWires = S5.openWires
  have hFow : (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires
      = (processBrauer (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).topPerm)).openWires :=
    (congrArg (fun state => state.openWires) hFS5).symm.trans
      (circleFold_openWires (reconstructStandardFormExt5Corrected d).loops _ forestS5)
  rw [hFow]
  exact isSameComponent_trans _ _ _ _ (isSameComponent_trans _ _ _ _ fA fB) fC

/-- ★★★ **The THROUGH-class per-arc T-CONNECT, in the boundary-matching form (the `partnerShares` datum).**  A through
arc has one bottom foot `i = partner[bottomCount + t] < bottomCount` (its partner `t = throughStrandTops[topRank]` is a
top port, so `i` is a through bottom) and one top foot `bottomCount + t`, so
`matchingSameComponent bottomCount F i (bottomCount + t)` reduces to node connectivity
(`matchingSameComponent_bottomTop_eq_isSameComponent`), which `throughArcConnect_general` supplies — the exact per-arc
datum the r22 routing collapse consumes, discharged in general for the THROUGH class. -/
theorem throughArcMatching_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (topRank : Nat) (topRankLt : topRank < (throughStrandTops d.bottomCount d.topCount d.partner).length) :
    matchingSameComponent d.bottomCount
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
        (natListGetAt d.partner
          (d.bottomCount + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank))
        (d.bottomCount + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank) = true := by
  have tMem : natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank
      ∈ throughStrandTops d.bottomCount d.topCount d.partner :=
    natListGetAtMemCap (throughStrandTops d.bottomCount d.topCount d.partner) topRank topRankLt
  have iMem : natListGetAt d.partner (d.bottomCount
        + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank)
      ∈ throughStrandBottoms d.bottomCount d.partner :=
    throughStrandTop_partner_memThroughBottoms d.bottomCount d.topCount d.partner wf
      (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank) tMem
  have iLt : natListGetAt d.partner (d.bottomCount
        + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank) < d.bottomCount :=
    (throughStrandBottoms_mem_sound d.bottomCount d.partner _ iMem).1
  rw [matchingSameComponent_bottomTop_eq_isSameComponent d.bottomCount
    (processBrauer (brauerSeed d.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
    (natListGetAt d.partner
      (d.bottomCount + natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank))
    (natListGetAt (throughStrandTops d.bottomCount d.topCount d.partner) topRank) iLt]
  exact throughArcConnect_general d bottomPos wf topRank topRankLt

/-! ## B3 firings — the general THROUGH weld FIRES on the width-12 monster (both throughs) -/

/-- ★★ **The GENERAL THROUGH weld FIRES on the monster through rank `0`** (`throughStrandTops[0] = 0`,
`partner[6] = 4` = the bottom foot) — the arc `4↔top0` (`monsterWidth12Arcs` conjunct `(4, 6)`), exercised (not
`decide`d) through all five seams of the general weld. -/
theorem throughArcMatching_firesMonster_zero :
    matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram)))
      (natListGetAt monsterDiagram.partner (6 + natListGetAt (throughStrandTops 6 6 monsterDiagram.partner) 0))
      (6 + natListGetAt (throughStrandTops 6 6 monsterDiagram.partner) 0) = true :=
  throughArcMatching_general monsterDiagram (by decide) monster_isBoundaryInvolution 0 (by decide)

/-- ★★ **The GENERAL THROUGH weld FIRES on the monster through rank `1`** (`throughStrandTops[1] = 1`,
`partner[7] = 5`) — the arc `5↔top1` (`monsterWidth12Arcs` conjunct `(5, 7)`), the second through strand. -/
theorem throughArcMatching_firesMonster_one :
    matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram)))
      (natListGetAt monsterDiagram.partner (6 + natListGetAt (throughStrandTops 6 6 monsterDiagram.partner) 1))
      (6 + natListGetAt (throughStrandTops 6 6 monsterDiagram.partner) 1) = true :=
  throughArcMatching_general monsterDiagram (by decide) monster_isBoundaryInvolution 1 (by decide)

/-- ★★ **The GENERAL THROUGH weld FIRES on the mutually-crossing 3-through diagram, rank `2`** (a genuine 3-cycle
middle permutation) — the append-LEFT weld exercised on a NON-trivial through routing. -/
theorem throughArcMatching_fires3Through_two :
    matchingSameComponent 3 (processBrauer (brauerSeed 3)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected threeThroughCrossingDiagram)))
      (natListGetAt threeThroughCrossingDiagram.partner
        (3 + natListGetAt (throughStrandTops 3 3 threeThroughCrossingDiagram.partner) 2))
      (3 + natListGetAt (throughStrandTops 3 3 threeThroughCrossingDiagram.partner) 2) = true :=
  throughArcMatching_general threeThroughCrossingDiagram (by decide) isBoundaryInvolution_threeThroughCrossing
    2 (by decide)

/-- ★★★ **Honesty marker — the GENERAL per-arc THROUGH-class T-CONNECT is SHIPPED (r28 B3, the weld assembled).**
`throughArcConnect_general` proves, zero-axiom and structural, that for EVERY well-formed boundary involution (with
`0 < bottomCount`) the through arc's bottom foot and its read top open wire share a union-find component in the
corrected six-phase fold; `throughArcMatching_general` lifts it to the boundary-matching `partnerShares` datum the r22
routing collapse consumes.  The assembly is the five-phase node-survival WELD — the seed tracker + P1 decode, the P2
cap-survival read, the P3 middle tracker, the P4 cup-survival read, the P5 top tracker + r26 keystone — every fact
transported to `F.links` and welded by `isSameComponent_trans` / `_flip`, a direct scale of `cupArcConnectViaState`
with a FIXED SEED NODE left endpoint and an append-LEFT through-block right read.  This is the THIRD (and last) of the
three per-arc classes (after CAP r24 and CUP r26); with all three `…ArcMatching_general` now shipped, the all-class
dispatch is the natural same/next-round consumer.  Fired on both monster through strands and the 3-cycle 3-through.
This marker supersedes the FROZEN r27 snapshot `fxBrauer_hasThroughClassGeneral` (kept `false` to preserve
`fxBrauer_r27GrandLedger`).  A NEW ingredient marker; it flips NO master — `fxBrauer_hasTConnectThroughWall` stays
`false` until the all-class dispatch lands, and `#2013` closes only after T-CLOSE(b).  `= true`. -/
def fxBrauer_hasThroughArcGeneral : Bool := true

end FX1Poly.Polygraph
