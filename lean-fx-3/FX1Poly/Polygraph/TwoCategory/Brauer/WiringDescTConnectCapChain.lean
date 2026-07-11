import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTracker
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldGlue
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapClass
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcEnumeration

/-! # BRAUER r24 — THE CAP CHAIN: the GENERAL per-arc CAP-class T-CONNECT (assembled, zero-axiom)

The r23 ledger (`Brauer/WiringDescCrossingTrackerLedger.lean:29`) named the CAP-class residual verbatim: *"pair the
bottomPerm-phase open wires as `flattenNatPairs feetPairs ++ throughBlock`, connect each consecutive pair by
`capFold_consumes`, align `capArcFeet` (`correctedBottomPerm_decodesReadOff`) through
`crossingWordFold_openWire_sameComponent_incomingPort_seed`, transport by `capThenCupFold_connects_survivesTail`;
… T-ENUM position bookkeeping."*  This file ASSEMBLES exactly that — the general CAP-class per-arc T-CONNECT is now a
machine-checked, zero-axiom theorem.

## What this file ships — the CAP chain, general

`capArcConnect_general`: for EVERY well-formed boundary involution `d` and every cap-arc rank
`rank < (capArcFeetIndices d.bottomCount d.partner).length`, the rank-th cap arc's two bottom feet
`capArcFeetIndices[rank]` and `partner (capArcFeetIndices[rank])` share a union-find component in the corrected
six-phase fold state `F = processBrauer (brauerSeed d.bottomCount) (standardFormWordExt5
(reconstructStandardFormExt5Corrected d))`.  `capArcMatching_general` lifts that to the boundary-matching form
`matchingSameComponent d.bottomCount F (capArcFeetIndices[rank]) (partner (…)) = true` (both feet are bottom ports, so
each boundary read is the seed node itself — `matchingSameComponent_bottomBottom_eq_isSameComponent`).  That
`matchingSameComponent` fact IS the per-arc `partnerShares` datum the r22 routing collapse
`partnerIndexOf_reads_arc_general` (`Brauer/WiringDescTConnectCapClass.lean`) consumes — for the CAP class it is now
discharged in general.

## The assembly — the exact chain the recon traced

`capArcConnectViaState` abstracts the state: given any forest state whose open wires are tracked pointwise to a
read-off order `feet ++ tb`, firing `capWord (natReplicate caps 0)` and any trailing word connects the rank-th
front pair's abstract feet.  The proof:

  * **T-ENUM position bookkeeping** (the "modest structural" GAP the ledger named): `chunkFrontPairs` /
    `dropFrontPairs` peel the front `2·caps` open wires into consecutive pairs (`chunkFrontPairs_flatten_split`,
    `chunkFrontPairs_length`), and `flattenNatPairs_pairGetMem` reads the rank-th pair as a genuine member (with even
    positions indexed by `doublePos`, a clean 2-cons peel that never touches `2 * k` arithmetic).
  * **the join** `capFold_consumes` connects that member pair in the post-cap state;
  * **the decode alignment** `correctedBottomPerm_decodesReadOff` identifies `permuteOfCrossingWord bottomCount
    bottomPerm` with `capArcFeet ++ throughStrandBottoms`, and `expandBottomFeetPairs_getAt_fst` / `_snd` read
    `capArcFeet[2·rank] = capArcFeetIndices[rank]`, `capArcFeet[2·rank+1] = partner (…)`;
  * **the seed tracker** `crossingWordFold_openWire_sameComponent_incomingPort_seed` (r23) links each front open wire
    to its read-off foot;
  * **the transport** `processBrauer_isSameComponent_ofBase` carries every S1 / post-cap connection through the
    remaining middle / cup / topPerm / circle phases, whose six-phase factorization is `foldFactorsThroughCap`
    (`standardFormFold_appendSplit` + `processBrauer_append`).

## Honest scope — CAP is landed; CUP / THROUGH and the master flips are NOT

This is the CAP class ONLY — the recon's shortest chain, which needs no base ≠ range crossing-tracker bridge (its
tracker runs on the seed, base `= List.range`).  The CUP and THROUGH classes additionally need the base-permute
bridge (GAP β) and, for THROUGH, the `throughStrandPerm` range-permutation (GAP γ); those stay the named residual.
So `fxBrauer_hasTConnectCapClass` is a NEW INGREDIENT marker (`= true`), and it flips NO master:
`fxBrauer_hasTConnectThroughWall`, `fxBrauer_hasFoldAlignmentE3`, `fxBrauer_hasFoldTargetHonestAssembly`, the
tag-correspondence masters and the completeness masters all stay `false`; #2013 does NOT close.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only
on closed literals (the probes).  Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms`
clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free arithmetic + list kit (structural) -/

/-- `rank + rank`, structural so `doublePos (rank + 1) = (doublePos rank).succ.succ` holds definitionally — a clean
two-cons peel for pair-list indexing that never touches `2 * rank` arithmetic. -/
def doublePos : Nat → Nat
  | 0 => 0
  | rank + 1 => (doublePos rank).succ.succ

/-- `doublePos rank = rank + rank` — the bridge to the shipped `expandBottomFeetPairs_length` /
`capArcFeetTwiceThroughSumsToBottom` count facts (both phrased with `n + n`). -/
theorem doublePos_add : (n : Nat) → doublePos n = n + n
  | 0 => rfl
  | k + 1 => by
      show Nat.succ (Nat.succ (doublePos k)) = (k + 1) + (k + 1)
      rw [doublePos_add k, Nat.succ_add k (k + 1), Nat.add_succ k k]

/-- `doublePos` is strictly monotone: distinct ranks land at distinct even positions. -/
theorem doublePos_lt_doublePos (rank m : Nat) (hlt : rank < m) : doublePos rank < doublePos m := by
  rw [doublePos_add rank, doublePos_add m]; exact Nat.add_lt_add hlt hlt

/-- The odd position of an earlier rank precedes the even position of a strictly later rank. -/
theorem doublePos_succ_lt_doublePos (rank m : Nat) (hlt : rank < m) : doublePos rank + 1 < doublePos m := by
  rw [doublePos_add rank, doublePos_add m]
  have step : rank + (rank + 1) ≤ rank + m := Nat.add_le_add_left (Nat.succ_le_of_lt hlt) rank
  exact Nat.lt_of_le_of_lt step (Nat.add_lt_add_right hlt m)

/-- Peel the front `n` pairs of a `Nat` list into a pair list — the S1-side cap feet the cap block consumes.
Structural on the count then the list (the two short-list arms are the `2·n ≤ length` underflow guards). -/
def chunkFrontPairs : Nat → List Nat → List (Nat × Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, [_] => []
  | n + 1, first :: second :: rest => (first, second) :: chunkFrontPairs n rest

/-- The tail left after peeling the front `n` pairs (the through block the cap block does not touch). -/
def dropFrontPairs : Nat → List Nat → List Nat
  | 0, wires => wires
  | _ + 1, [] => []
  | _ + 1, [single] => [single]
  | n + 1, _ :: _ :: rest => dropFrontPairs n rest

/-- Reassemble: the flattened front pairs then the drop tail recover the whole list (given `doublePos n ≤ length`, so
the `n` pairs fit).  Structural on `n` then the list. -/
theorem chunkFrontPairs_flatten_split : (n : Nat) → (wires : List Nat) → doublePos n ≤ wires.length →
    flattenNatPairs (chunkFrontPairs n wires) ++ dropFrontPairs n wires = wires
  | 0, _, _ => rfl
  | _ + 1, [], hle => absurd hle (Nat.not_succ_le_zero _)
  | _ + 1, [_single], hle => absurd hle (fun h => Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ h))
  | n + 1, first :: second :: rest, hle => by
      have restLe : doublePos n ≤ rest.length := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hle)
      show first :: second :: (flattenNatPairs (chunkFrontPairs n rest) ++ dropFrontPairs n rest)
          = first :: second :: rest
      rw [chunkFrontPairs_flatten_split n rest restLe]

/-- The peeled front-pair list has exactly `n` pairs (given `doublePos n ≤ length`). -/
theorem chunkFrontPairs_length : (n : Nat) → (wires : List Nat) → doublePos n ≤ wires.length →
    (chunkFrontPairs n wires).length = n
  | 0, _, _ => rfl
  | _ + 1, [], hle => absurd hle (Nat.not_succ_le_zero _)
  | _ + 1, [_single], hle => absurd hle (fun h => Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ h))
  | n + 1, first :: second :: rest, hle => by
      have restLe : doublePos n ≤ rest.length := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hle)
      show (chunkFrontPairs n rest).length + 1 = n + 1
      rw [chunkFrontPairs_length n rest restLe]

/-- Flattening a pair list doubles its length — the window bound for the append-left reads. -/
theorem flattenNatPairs_length_doublePos : (pairs : List (Nat × Nat)) →
    (flattenNatPairs pairs).length = doublePos pairs.length
  | [] => rfl
  | (_, _) :: rest => by
      show (flattenNatPairs rest).length + 1 + 1 = (doublePos rest.length).succ.succ
      rw [flattenNatPairs_length_doublePos rest]

/-- Reading the flattened pair list at an even position and its successor recovers the rank-th pair — as a genuine
member.  Structural on the pair list then the rank (the `doublePos` index peels two cons cleanly). -/
theorem flattenNatPairs_pairGetMem : (pairs : List (Nat × Nat)) → (rank : Nat) → rank < pairs.length →
    (natListGetAt (flattenNatPairs pairs) (doublePos rank),
     natListGetAt (flattenNatPairs pairs) (doublePos rank + 1)) ∈ pairs
  | [], rank, hlt => absurd hlt (Nat.not_lt_zero rank)
  | (_, _) :: rest, 0, _ => List.Mem.head rest
  | (firstFoot, secondFoot) :: rest, rank + 1, hlt => by
      have restLt : rank < rest.length := Nat.lt_of_succ_lt_succ hlt
      show (natListGetAt (firstFoot :: secondFoot :: flattenNatPairs rest) (doublePos (rank + 1)),
            natListGetAt (firstFoot :: secondFoot :: flattenNatPairs rest) (doublePos (rank + 1) + 1))
          ∈ (firstFoot, secondFoot) :: rest
      exact List.Mem.tail _ (flattenNatPairs_pairGetMem rest rank restLt)

/-- The even position of `expandBottomFeetPairs` reads the rank-th smaller cap foot (`capArcFeetIndices[rank]`). -/
theorem expandBottomFeetPairs_getAt_fst (partner : List Nat) :
    (feet : List Nat) → (rank : Nat) → rank < feet.length →
    natListGetAt (expandBottomFeetPairs partner feet) (doublePos rank) = natListGetAt feet rank
  | [], rank, hlt => absurd hlt (Nat.not_lt_zero rank)
  | _ :: _, 0, _ => rfl
  | idx :: rest, rank + 1, hlt => by
      have restLt : rank < rest.length := Nat.lt_of_succ_lt_succ hlt
      show natListGetAt (idx :: natListGetAt partner idx :: expandBottomFeetPairs partner rest)
          (doublePos (rank + 1)) = natListGetAt (idx :: rest) (rank + 1)
      exact expandBottomFeetPairs_getAt_fst partner rest rank restLt

/-- The odd position of `expandBottomFeetPairs` reads the partner of the rank-th smaller cap foot. -/
theorem expandBottomFeetPairs_getAt_snd (partner : List Nat) :
    (feet : List Nat) → (rank : Nat) → rank < feet.length →
    natListGetAt (expandBottomFeetPairs partner feet) (doublePos rank + 1)
      = natListGetAt partner (natListGetAt feet rank)
  | [], rank, hlt => absurd hlt (Nat.not_lt_zero rank)
  | _ :: _, 0, _ => rfl
  | idx :: rest, rank + 1, hlt => by
      have restLt : rank < rest.length := Nat.lt_of_succ_lt_succ hlt
      show natListGetAt (idx :: natListGetAt partner idx :: expandBottomFeetPairs partner rest)
          (doublePos (rank + 1) + 1) = natListGetAt partner (natListGetAt (idx :: rest) (rank + 1))
      exact expandBottomFeetPairs_getAt_snd partner rest rank restLt

/-- `natListGetAt` on the left of an append, below the left length (a public cap-chain re-proof of the
readback-private `natListGetAt_append_left`).  Structural on the list then index. -/
theorem natListGetAtAppendLeftCap : (leftList rightList : List Nat) → (index : Nat) →
    index < leftList.length → natListGetAt (leftList ++ rightList) index = natListGetAt leftList index
  | [], _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: restLeft, rightList, index + 1, indexBelow =>
      natListGetAtAppendLeftCap restLeft rightList index (Nat.lt_of_succ_lt_succ indexBelow)

/-- An in-range `natListGetAt` read is a genuine member (a public cap-chain re-proof of the conjugator-private
`getAtMemConj`).  Feeds `capArcFeetIndices_mem_sound` at the rank-th smaller foot. -/
theorem natListGetAtMemCap : (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt entries index ∈ entries
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | head :: rest, index + 1, indexBelow =>
      List.Mem.tail head (natListGetAtMemCap rest index (Nat.lt_of_succ_lt_succ indexBelow))

/-! ## The six-phase factorization through the cap block -/

/-- The corrected fold factors as (post-bottomPerm, post-cap) then the trailing four-phase word — the transport spine
the cap chain rides.  `standardFormFold_appendSplit` re-associated at the four trailing `++` seams by
`processBrauer_append`. -/
theorem foldFactorsThroughCap (form : BrauerStandardFormExt5) :
    processBrauer (brauerSeed form.bottomCount) (standardFormWordExt5 form)
      = processBrauer
          (processBrauer (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
            (capWord form.capBlock))
          (crossingWord form.middle ++ cupWord form.cupBlock ++ crossingWord form.topPerm
            ++ circleWord form.loops) := by
  rw [standardFormFold_appendSplit form,
    processBrauer_append (crossingWord form.middle ++ cupWord form.cupBlock ++ crossingWord form.topPerm)
      (processBrauer (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
        (capWord form.capBlock)) (circleWord form.loops),
    processBrauer_append (crossingWord form.middle ++ cupWord form.cupBlock)
      (processBrauer (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
        (capWord form.capBlock)) (crossingWord form.topPerm),
    processBrauer_append (crossingWord form.middle)
      (processBrauer (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
        (capWord form.capBlock)) (cupWord form.cupBlock)]

/-! ## The abstract-state cap-arc connectivity -/

/-- ★★ **The abstract-state CAP chain.**  Given any forest state whose open wires track pointwise to a read-off order
`feet ++ tb` (with `feet.length = doublePos caps`, and `doublePos caps ≤` the open-wire count), firing
`capWord (natReplicate caps 0)` — one cap at position `0` per rank — and then any trailing word connects the rank-th
front pair's abstract feet `feet[doublePos rank]` and `feet[doublePos rank + 1]`.  The chain: `chunkFrontPairs` peels
the front pairs, `capFold_consumes` connects the rank-th member pair, the tracker links each front open wire to its
read-off foot, and `processBrauer_isSameComponent_ofBase` transports both through the cap and the trailing word. -/
theorem capArcConnectViaState (state : WireState) (feet tb : List Nat) (caps : Nat)
    (tailWord : List BrauerAtom) (rank : Nat)
    (forest : isUnionFindForest state.links)
    (feetLen : feet.length = doublePos caps)
    (capsLe : doublePos caps ≤ state.openWires.length)
    (tracker : ∀ index, isSameComponent state.links
        (natListGetAt state.openWires index) (natListGetAt (feet ++ tb) index) = true)
    (rankLt : rank < caps) :
    isSameComponent
        (processBrauer (processBrauer state (capWord (natReplicate caps 0))) tailWord).links
        (natListGetAt feet (doublePos rank)) (natListGetAt feet (doublePos rank + 1)) = true := by
  have hsplit : state.openWires
      = flattenNatPairs (chunkFrontPairs caps state.openWires) ++ dropFrontPairs caps state.openWires :=
    (chunkFrontPairs_flatten_split caps state.openWires capsLe).symm
  have hFeetLen : (chunkFrontPairs caps state.openWires).length = caps :=
    chunkFrontPairs_length caps state.openWires capsLe
  have flatLen : (flattenNatPairs (chunkFrontPairs caps state.openWires)).length = doublePos caps := by
    rw [flattenNatPairs_length_doublePos, hFeetLen]
  have windowFst : doublePos rank < (flattenNatPairs (chunkFrontPairs caps state.openWires)).length := by
    rw [flatLen]; exact doublePos_lt_doublePos rank caps rankLt
  have windowSnd : doublePos rank + 1 < (flattenNatPairs (chunkFrontPairs caps state.openWires)).length := by
    rw [flatLen]; exact doublePos_succ_lt_doublePos rank caps rankLt
  have eqFst : natListGetAt state.openWires (doublePos rank)
      = natListGetAt (flattenNatPairs (chunkFrontPairs caps state.openWires)) (doublePos rank) := by
    have hread := natListGetAtAppendLeftCap (flattenNatPairs (chunkFrontPairs caps state.openWires))
      (dropFrontPairs caps state.openWires) (doublePos rank) windowFst
    rw [← hsplit] at hread
    exact hread
  have eqSnd : natListGetAt state.openWires (doublePos rank + 1)
      = natListGetAt (flattenNatPairs (chunkFrontPairs caps state.openWires)) (doublePos rank + 1) := by
    have hread := natListGetAtAppendLeftCap (flattenNatPairs (chunkFrontPairs caps state.openWires))
      (dropFrontPairs caps state.openWires) (doublePos rank + 1) windowSnd
    rw [← hsplit] at hread
    exact hread
  have capConn := capFold_consumes (chunkFrontPairs caps state.openWires) state
      (dropFrontPairs caps state.openWires) hsplit forest
  have pairMem := flattenNatPairs_pairGetMem (chunkFrontPairs caps state.openWires) rank
      (by rw [hFeetLen]; exact rankLt)
  have capPairConn := capConn.2 _ pairMem
  rw [hFeetLen] at capPairConn
  have capS2 : isSameComponent (processBrauer state (capWord (natReplicate caps 0))).links
      (natListGetAt state.openWires (doublePos rank)) (natListGetAt state.openWires (doublePos rank + 1)) = true := by
    rw [eqFst, eqSnd]; exact capPairConn
  have forestCap : isUnionFindForest (processBrauer state (capWord (natReplicate caps 0))).links :=
    processBrauer_links_isUnionFindForest (capWord (natReplicate caps 0)) state forest
  have capF : isSameComponent
      (processBrauer (processBrauer state (capWord (natReplicate caps 0))) tailWord).links
      (natListGetAt state.openWires (doublePos rank)) (natListGetAt state.openWires (doublePos rank + 1)) = true :=
    processBrauer_isSameComponent_ofBase tailWord (processBrauer state (capWord (natReplicate caps 0)))
      forestCap _ _ capS2
  have windowFeetFst : doublePos rank < feet.length := by
    rw [feetLen]; exact doublePos_lt_doublePos rank caps rankLt
  have windowFeetSnd : doublePos rank + 1 < feet.length := by
    rw [feetLen]; exact doublePos_succ_lt_doublePos rank caps rankLt
  have trackFst : isSameComponent state.links
      (natListGetAt state.openWires (doublePos rank)) (natListGetAt feet (doublePos rank)) = true := by
    have h := tracker (doublePos rank)
    rw [natListGetAtAppendLeftCap feet tb (doublePos rank) windowFeetFst] at h
    exact h
  have trackSnd : isSameComponent state.links
      (natListGetAt state.openWires (doublePos rank + 1)) (natListGetAt feet (doublePos rank + 1)) = true := by
    have h := tracker (doublePos rank + 1)
    rw [natListGetAtAppendLeftCap feet tb (doublePos rank + 1) windowFeetSnd] at h
    exact h
  have toFof : ∀ nodeA nodeB, isSameComponent state.links nodeA nodeB = true →
      isSameComponent (processBrauer (processBrauer state (capWord (natReplicate caps 0))) tailWord).links
        nodeA nodeB = true := by
    intro nodeA nodeB h
    have hstep := processBrauer_isSameComponent_ofBase (capWord (natReplicate caps 0) ++ tailWord) state
      forest nodeA nodeB h
    rw [processBrauer_append (capWord (natReplicate caps 0)) state tailWord] at hstep
    exact hstep
  have feetFst : isSameComponent
      (processBrauer (processBrauer state (capWord (natReplicate caps 0))) tailWord).links
      (natListGetAt feet (doublePos rank)) (natListGetAt state.openWires (doublePos rank)) = true :=
    isSameComponent_flip _ _ _ (toFof _ _ trackFst)
  have feetSnd : isSameComponent
      (processBrauer (processBrauer state (capWord (natReplicate caps 0))) tailWord).links
      (natListGetAt state.openWires (doublePos rank + 1)) (natListGetAt feet (doublePos rank + 1)) = true :=
    toFof _ _ trackSnd
  exact isSameComponent_trans _ _ _ _ (isSameComponent_trans _ _ _ _ feetFst capF) feetSnd

/-! ## The GENERAL per-arc CAP-class T-CONNECT -/

/-- ★★★ **THE CAP-CLASS PER-ARC T-CONNECT (GENERAL).**  For EVERY well-formed boundary involution `d` and every
cap-arc rank `rank < (capArcFeetIndices d.bottomCount d.partner).length`, the rank-th cap arc's two bottom feet
`capArcFeetIndices[rank]` and its partner share a union-find component in the corrected six-phase fold state.  The
recon's cap chain, assembled: the seed tracker (r23) + `correctedBottomPerm_decodesReadOff` (r19) + `capFold_consumes`
(R3-A) + `processBrauer_isSameComponent_ofBase`, aligned by the `doublePos`-indexed `flattenNatPairs` /
`expandBottomFeetPairs` position bookkeeping (T-ENUM), transported through the six-phase `foldFactorsThroughCap`. -/
theorem capArcConnect_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (rank : Nat) (rankLt : rank < (capArcFeetIndices d.bottomCount d.partner).length) :
    isSameComponent
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank)
        (natListGetAt d.partner (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank)) = true := by
  have permBounded := (readOffBottomOrder_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded
  have posBound := permutationToCrossingWord_posBound d.bottomCount
      (capArcFeet d.bottomCount d.partner ++ throughStrandBottoms d.bottomCount d.partner) permBounded
  have forestS1 : isUnionFindForest (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).links :=
    processBrauer_links_isUnionFindForest _ (brauerSeed d.bottomCount) isUnionFindForest_nil
  have wS1 : (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires.length = d.bottomCount :=
    crossingWordFold_openWires_length d.bottomCount _ (brauerSeed d.bottomCount)
      (brauerSeedOpenWiresLengthWidth d.bottomCount) posBound
  have feetLen : (capArcFeet d.bottomCount d.partner).length
      = doublePos (capArcFeetIndices d.bottomCount d.partner).length := by
    rw [doublePos_add]
    exact expandBottomFeetPairs_length d.partner (capArcFeetIndices d.bottomCount d.partner)
  have capsLe : doublePos (capArcFeetIndices d.bottomCount d.partner).length
      ≤ (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires.length := by
    rw [wS1, doublePos_add]
    exact Nat.le.intro (capArcFeetTwiceThroughSumsToBottom d.bottomCount (d.bottomCount + d.topCount)
      d.partner (Nat.le_add_right d.bottomCount d.topCount) wf)
  have tracker : ∀ index, isSameComponent
      (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).links
      (natListGetAt (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm)).openWires index)
      (natListGetAt (capArcFeet d.bottomCount d.partner
        ++ throughStrandBottoms d.bottomCount d.partner) index) = true := by
    intro index
    have h := crossingWordFold_openWire_sameComponent_incomingPort_seed d.bottomCount bottomPos
      (reconstructStandardFormExt5Corrected d).bottomPerm posBound index
    rw [correctedBottomPerm_decodesReadOff d wf] at h
    exact h
  have helperResult := capArcConnectViaState
    (processBrauer (brauerSeed d.bottomCount)
      (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
    (capArcFeet d.bottomCount d.partner) (throughStrandBottoms d.bottomCount d.partner)
    (capArcFeetIndices d.bottomCount d.partner).length
    (crossingWord (reconstructStandardFormExt5Corrected d).middle
      ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock
      ++ crossingWord (reconstructStandardFormExt5Corrected d).topPerm
      ++ circleWord (reconstructStandardFormExt5Corrected d).loops)
    rank forestS1 feetLen capsLe tracker rankLt
  have hstateEq : processBrauer (processBrauer
        (processBrauer (brauerSeed d.bottomCount)
          (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0)))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle
          ++ cupWord (reconstructStandardFormExt5Corrected d).cupBlock
          ++ crossingWord (reconstructStandardFormExt5Corrected d).topPerm
          ++ circleWord (reconstructStandardFormExt5Corrected d).loops)
      = processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)) :=
    (foldFactorsThroughCap (reconstructStandardFormExt5Corrected d)).symm
  rw [hstateEq] at helperResult
  rw [← expandBottomFeetPairs_getAt_snd d.partner (capArcFeetIndices d.bottomCount d.partner) rank rankLt,
      ← expandBottomFeetPairs_getAt_fst d.partner (capArcFeetIndices d.bottomCount d.partner) rank rankLt]
  exact helperResult

/-- ★★★ **The CAP-class per-arc T-CONNECT, in the boundary-matching form (the `partnerShares` datum).**  Both feet of
a cap arc are bottom ports, so `matchingSameComponent d.bottomCount F i (partner i)` reduces to node connectivity
(`matchingSameComponent_bottomBottom_eq_isSameComponent`), which `capArcConnect_general` supplies.  This is EXACTLY the
per-arc `partnerShares` the r22 routing collapse `partnerIndexOf_reads_arc_general` consumes — discharged in general
for the CAP class. -/
theorem capArcMatching_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (rank : Nat) (rankLt : rank < (capArcFeetIndices d.bottomCount d.partner).length) :
    matchingSameComponent d.bottomCount
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
        (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank)
        (natListGetAt d.partner (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank)) = true := by
  have iMem : natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank
      ∈ capArcFeetIndices d.bottomCount d.partner :=
    natListGetAtMemCap (capArcFeetIndices d.bottomCount d.partner) rank rankLt
  have bounds := capArcFeetIndices_mem_sound d.bottomCount d.partner
    (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank) iMem
  rw [matchingSameComponent_bottomBottom_eq_isSameComponent d.bottomCount _
    (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank)
    (natListGetAt d.partner (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank))
    bounds.1 bounds.2.1]
  exact capArcConnect_general d bottomPos wf rank rankLt

/-! ## B1 — the concrete truth-probe: the decode + join on the all-caps 2-cap witness (eval FIRST) -/

/-- ★ **CAP-chain DECODE probe (all-caps `{4,0,[3,2,1,0]}`).**  The corrected `bottomPerm` staircase decodes to
`capArcFeet ++ throughStrandBottoms = [0, 3, 1, 2] ++ [] = [0, 3, 1, 2]` — the read-off order that routes the two cap
feet pairs `(0,3)`, `(1,2)` into the front open-wire positions the cap block consumes.  Kernel-decided. -/
theorem capChainDecodeProbe_allCaps :
    permuteOfCrossingWord 4 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram).bottomPerm
      = capArcFeet 4 capClassAllCapsDiagram.partner
          ++ throughStrandBottoms 4 capClassAllCapsDiagram.partner := by decide

/-- ★ **CAP-chain JOIN probe (all-caps).**  The two front cap pairs `(0,3)` and `(1,2)` are each same-component in the
corrected six-phase fold — the decode + `capFold_consumes` join, kernel-decided on the closed literal (the concrete
instance the general `capArcConnect_general` proves for every rank). -/
theorem capChainJoinProbe_allCaps :
    (isSameComponent (processBrauer (brauerSeed 4)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).links 0 3 = true)
    ∧ (isSameComponent (processBrauer (brauerSeed 4)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).links 1 2 = true) :=
  ⟨by decide, by decide⟩

/-- ★★ **The GENERAL cap chain FIRES on the all-caps witness (rank `0`, the arc `0↔3`).**  Instantiating
`capArcConnect_general` at `capClassAllCapsDiagram`, rank `0`: `capArcFeetIndices[0] = 0` and its partner `3` are
connected in the fold — the general theorem, exercised (not `decide`d), on a genuine witness. -/
theorem capArcConnect_firesAllCaps_zero :
    isSameComponent (processBrauer (brauerSeed 4)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).links
      (natListGetAt (capArcFeetIndices 4 capClassAllCapsDiagram.partner) 0)
      (natListGetAt capClassAllCapsDiagram.partner
        (natListGetAt (capArcFeetIndices 4 capClassAllCapsDiagram.partner) 0)) = true :=
  capArcConnect_general capClassAllCapsDiagram (by decide) isBoundaryInvolution_allCapsBoundary 0 (by decide)

/-- ★★ **The GENERAL matching form FIRES on the all-caps witness (rank `1`, the arc `1↔2`).**  `capArcMatching_general`
routed to the boundary-matching `partnerShares` datum on the second cap arc — the exact input the routing collapse
consumes, produced by the general CAP theorem. -/
theorem capArcMatching_firesAllCaps_one :
    matchingSameComponent 4 (processBrauer (brauerSeed 4)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram)))
      (natListGetAt (capArcFeetIndices 4 capClassAllCapsDiagram.partner) 1)
      (natListGetAt capClassAllCapsDiagram.partner
        (natListGetAt (capArcFeetIndices 4 capClassAllCapsDiagram.partner) 1)) = true :=
  capArcMatching_general capClassAllCapsDiagram (by decide) isBoundaryInvolution_allCapsBoundary 1 (by decide)

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the GENERAL CAP-class per-arc T-CONNECT is SHIPPED (r24, the cap chain assembled).**
`capArcConnect_general` proves, zero-axiom and structural, that for EVERY well-formed boundary involution the rank-th
cap arc's two bottom feet share a union-find component in the corrected six-phase fold; `capArcMatching_general` lifts
it to the boundary-matching `partnerShares` datum the r22 routing collapse consumes.  The assembly is the recon's cap
chain: the r23 seed tracker + the r19 `correctedBottomPerm_decodesReadOff` + the R3-A `capFold_consumes` +
`processBrauer_isSameComponent_ofBase`, aligned by the `doublePos`-indexed `flattenNatPairs` / `expandBottomFeetPairs`
position bookkeeping (T-ENUM), transported through `foldFactorsThroughCap`.  This is the CAP class ONLY — the recon's
shortest chain (its tracker runs on the seed, base `= List.range`, so it needs no base ≠ range crossing-tracker
bridge).  It is ONE ingredient of the general per-arc T-CONNECT; it flips NO master.  The CUP and THROUGH classes
still need the base-permute bridge (GAP β) and, for THROUGH, the `throughStrandPerm` range-permutation (GAP γ), so
`fxBrauer_hasTConnectThroughWall`, `fxBrauer_hasFoldAlignmentE3`, `fxBrauer_hasFoldTargetHonestAssembly` and the
tag-correspondence / completeness masters stay `false`; #2013 does NOT close.  `= true`. -/
def fxBrauer_hasTConnectCapClass : Bool := true

end FX1Poly.Polygraph
