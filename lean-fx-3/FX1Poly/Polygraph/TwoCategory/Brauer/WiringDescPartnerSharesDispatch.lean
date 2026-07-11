import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughWeld
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescMatchingSymm

/-! # BRAUER r29 — the UNCONDITIONAL `partnerShares_general` (the 6-way dispatch) + the unconditional read-off

The r22 routing collapse `partnerIndexOf_reads_arc_general` reduced the entire six-phase endgame to ONE per-arc
datum: `matchingSameComponent d.bottomCount F probeIndex (partner probeIndex) = true` (= T-CONNECT).  r24/r26/r28
shipped the three per-arc-class generals (`capArcMatching_general`, `cupArcMatching_general`,
`throughArcMatching_general`), each producing that datum for its arc class BY RANK.  This file assembles them into
the **unconditional** `partnerShares_general`: for EVERY well-formed boundary involution and EVERY boundary port, the
per-arc datum holds — the classification `partitionThree_of_involution` / `…_top` splits the port into one of six
arms, each arm recovers the rank by value→rank inversion on the arc-enumeration list, fires the class general at that
rank, and (for the three larger-foot / top arms) flips the orientation via `matchingSameComponent_symm`.

## The six arms (per the recon)

| # | port + guard | class general | rank recovery on | orientation |
|---|--------------|---------------|------------------|-------------|
| 1 | bottom, `capSmallerGuard` | `capArcMatching_general` | probeIndex ∈ `capArcFeetIndices` | canonical |
| 2 | bottom, `capLargerGuard`  | `capArcMatching_general` | `partner probeIndex` ∈ `capArcFeetIndices` | FLIP |
| 3 | bottom, `throughBottomGuard` | `throughArcMatching_general` | `partner probeIndex − bc` ∈ `throughStrandTops` | canonical |
| 4 | top, `cupSmallerGuard` | `cupArcMatching_general` | `off` ∈ `cupArcTopIndices` | canonical |
| 5 | top, `cupLargerGuard`  | `cupArcMatching_general` | `partner probeIndex − bc` ∈ `cupArcTopIndices` | FLIP |
| 6 | top, `throughTopGuard` | `throughArcMatching_general` | `off` ∈ `throughStrandTops` | FLIP |

Rank recovery routes each guard-`true` port through `memFilterMapGuardComplete` (the port is a genuine member of the
arc list, the guards being definitionally the `filterMap` predicates) then `natIndexOfValueRoundtrip` (the r29
exposure) to name its rank.  The FLIP arms use the involution `partner (partner probeIndex) = probeIndex`
(`wf.isSelfInverse`) to land the general's canonical orientation on the swapped port, then reorient by
`matchingSameComponent_flipTrue`.

## The consumer — the UNCONDITIONAL read-off

`partnerIndexOf_reads_arc_unconditional` feeds `partnerShares_general` into `partnerIndexOf_reads_arc_general`: for
every well-formed involution and every in-range port, the extractor's partner map reads exactly `partner probeIndex`
off the fold — no per-arc `decide`, no per-witness hypothesis.  The width `F.openWires.length = d.topCount`
(`foldOpenWiresWidth_correctedWord`, the cheap circle-past + topPerm-preserving + `cupChainS4Width` assembly)
converts the range premises.

## Honest scope — the frozen wall marker + the additive flip

The wall `fxBrauer_hasTConnectThroughWall` (`WiringDescTConnectCapClass`) named the general per-arc T-CONNECT PROOF
as UNBUILT; its `= false` boolean anchors the r22/r25/r26/r27/r28 grand ledgers (a shipped-`rfl` conjunction each).
Per the r28 additive-flip precedent (`fxBrauer_hasThroughArcGeneral = true` shipped NEW, superseding the frozen r27
`fxBrauer_hasThroughClassGeneral` kept `false`), r29 KEEPS `fxBrauer_hasTConnectThroughWall = false` (the ledger
anchor) and ships the NEW marker `fxBrauer_hasUnconditionalPartnerShares = true`: the wall's semantic content is now
DISCHARGED (the general per-arc T-CONNECT is built), but no shipped ledger's `rfl` is disturbed and #2013 still owes
T-CLOSE(b) (the `loops` field, B3).

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only on the
closed literal firing witnesses.  Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms`
clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 0 — the local Nat / membership / arithmetic kit (propext-free, structural) -/

/-- `Nat.ble a b = true ↔` `a ≤ b`, forward. -/
private theorem natLeOfBleDispatch : (a b : Nat) → Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (natLeOfBleDispatch a b h)

/-- `a ≤ b → Nat.ble a b = true`. -/
private theorem natBleOfLeDispatch : (a b : Nat) → a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | _ + 1, 0, le => absurd le (Nat.not_succ_le_zero _)
  | a + 1, b + 1, le => natBleOfLeDispatch a b (Nat.le_of_succ_le_succ le)

/-- `Nat.blt a b = true → a < b`. -/
private theorem natLtOfBltDispatch (a b : Nat) (h : Nat.blt a b = true) : a < b :=
  natLeOfBleDispatch (a + 1) b h

/-- `a < b → Nat.blt a b = true`. -/
private theorem natBltOfLtDispatch (a b : Nat) (h : a < b) : Nat.blt a b = true :=
  natBleOfLeDispatch (a + 1) b h

/-- Left conjunct of a `Bool` conjunction that is `true`. -/
private theorem boolAndLeftDispatch : (x y : Bool) → (x && y) = true → x = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- Right conjunct of a `Bool` conjunction that is `true`. -/
private theorem boolAndRightDispatch : (x y : Bool) → (x && y) = true → y = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- Membership in `acc` survives the range-loop fold. -/
private theorem memRangeLoopOfMemAccDispatch : (count : Nat) → (acc : List Nat) → (value : Nat) →
    value ∈ acc → value ∈ List.range.loop count acc
  | 0, _, _, hv => hv
  | count + 1, acc, value, hv => memRangeLoopOfMemAccDispatch count (count :: acc) value (List.Mem.tail count hv)

/-- Every index below `count` occurs in `List.range.loop count acc`. -/
private theorem memRangeLoopOfLtDispatch : (count : Nat) → (acc : List Nat) → (index : Nat) → index < count →
    index ∈ List.range.loop count acc
  | 0, _, index, h => absurd h (Nat.not_lt_zero index)
  | count + 1, acc, index, h => by
      cases Nat.lt_or_ge index count with
      | inl lt => exact memRangeLoopOfLtDispatch count (count :: acc) index lt
      | inr ge =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ h) ge
          exact indexEq ▸ memRangeLoopOfMemAccDispatch count (count :: acc) count (List.Mem.head acc)

/-- `index < count → index ∈ List.range count` — the `propext`-free `List.mem_range.mpr`. -/
private theorem memRangeOfLtDispatch (index count : Nat) (lt : index < count) : index ∈ List.range count :=
  memRangeLoopOfLtDispatch count [] index lt

/-- `base ≤ value → base + (value − base) = value` — structural, `propext`-free. -/
private theorem addSubCancelDispatch : (base value : Nat) → base ≤ value → base + (value - base) = value
  | 0, value, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, 0, le => absurd le (Nat.not_succ_le_zero base)
  | base + 1, value + 1, le => by
      rw [show (value + 1) - (base + 1) = value - base from Nat.succ_sub_succ value base,
        Nat.add_right_comm base 1 (value - base)]
      exact congrArg (· + 1) (addSubCancelDispatch base value (Nat.le_of_succ_le_succ le))

/-! ## Section 1 — the full-word open-wire width `F.openWires.length = d.topCount` (the cheap assembly) -/

/-- ★★ **The corrected six-phase fold has open-wire width `= d.topCount`.**  The circle phase preserves the open
wires (`circleFold_openWires`, past the `standardFormFold_appendSplit`), the `topPerm` crossing phase preserves their
count (`crossingWordFold_openWires_length`, its positions bounded by `permutationToCrossingWord_posBound` on the
inverted top read-off range-permutation), and the post-cup state S4 already has width `d.topCount` (`cupChainS4Width`).
The cheap width the read-off range premises and the T-CLOSE(b) `topCount` field both consume. -/
theorem foldOpenWiresWidth_correctedWord (d : DiagramType)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length = d.topCount := by
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
  exact crossingWordFold_openWires_length d.topCount (reconstructStandardFormExt5Corrected d).topPerm
    (processBrauer (processBrauer (processBrauer (processBrauer (brauerSeed d.bottomCount)
        (crossingWord (reconstructStandardFormExt5Corrected d).bottomPerm))
        (capWord (reconstructStandardFormExt5Corrected d).capBlock))
        (crossingWord (reconstructStandardFormExt5Corrected d).middle))
        (cupWord (reconstructStandardFormExt5Corrected d).cupBlock))
    (cupChainS4Width d wf)
    (permutationToCrossingWord_posBound d.topCount
      (permInverse (throughStrandTops d.bottomCount d.topCount d.partner
        ++ cupArcTops d.bottomCount d.topCount d.partner))
      (readOffTopOrderInverse_isPermutationOfRange d.bottomCount d.topCount d.partner wf).isBounded)

/-! ## Section 2 — the six-arm unconditional `partnerShares_general` -/

/-- ★★★ **THE UNCONDITIONAL PER-ARC T-CONNECT (`partnerShares_general`).**  For EVERY well-formed boundary
involution `d` (with `0 < d.bottomCount`) and EVERY boundary port `probeIndex < d.bottomCount + d.topCount`, the port
and its partner share a union-find component in the corrected six-phase fold — the exact `partnerShares` datum the
r22 routing collapse consumes, discharged UNCONDITIONALLY by the six-arm dispatch over the three shipped per-arc
generals.  The port is classified (`partitionThree_of_involution` on the bottom side, `…_top` on the top side) into
one of six arms; each recovers the arm's rank (value→rank on the arc-enumeration list via
`natIndexOfValueRoundtrip`), fires the class general, and — for the larger-foot / top arms — reorients via
`matchingSameComponent_flipTrue` through the involution.  This is the SPINE of the #2013 endgame: it discharges the
wall `fxBrauer_hasTConnectThroughWall` named in general. -/
theorem partnerShares_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (probeIndex : Nat) (probeLt : probeIndex < d.bottomCount + d.topCount) :
    matchingSameComponent d.bottomCount
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
        probeIndex (natListGetAt d.partner probeIndex) = true := by
  have invPP : natListGetAt d.partner (natListGetAt d.partner probeIndex) = probeIndex :=
    wf.isSelfInverse probeIndex probeLt
  cases Nat.lt_or_ge probeIndex d.bottomCount with
  | inl probeBelow =>
      -- BOTTOM port: cap-smaller / cap-larger / through-bottom
      have cls := partitionThree_of_involution d.bottomCount (d.bottomCount + d.topCount) d.partner
        (Nat.le_add_right d.bottomCount d.topCount) wf probeIndex probeBelow
      dsimp only [onlyOneTrueThree] at cls
      rcases cls with ⟨hS, _, _⟩ | ⟨_, hL, _⟩ | ⟨_, _, hT⟩
      · -- Arm 1: cap-smaller (canonical)
        have memP : probeIndex ∈ capArcFeetIndices d.bottomCount d.partner :=
          memFilterMapGuardComplete (capSmallerGuard d.bottomCount d.partner) (List.range d.bottomCount)
            probeIndex (memRangeOfLtDispatch probeIndex d.bottomCount probeBelow) hS
        have rt := natIndexOfValueRoundtrip (capArcFeetIndices d.bottomCount d.partner) probeIndex memP
        have gen := capArcMatching_general d bottomPos wf
          (natIndexOfValue (capArcFeetIndices d.bottomCount d.partner) probeIndex) rt.2
        rw [rt.1] at gen
        exact gen
      · -- Arm 2: cap-larger (FLIP)
        have ppLtBc : natListGetAt d.partner probeIndex < d.bottomCount :=
          natLtOfBltDispatch _ _ (boolAndLeftDispatch _ _ hL)
        have ppLtProbe : natListGetAt d.partner probeIndex < probeIndex :=
          natLtOfBltDispatch _ _ (boolAndRightDispatch _ _ hL)
        have smallerTrue : capSmallerGuard d.bottomCount d.partner (natListGetAt d.partner probeIndex) = true := by
          show (Nat.blt (natListGetAt d.partner (natListGetAt d.partner probeIndex)) d.bottomCount
            && Nat.blt (natListGetAt d.partner probeIndex)
              (natListGetAt d.partner (natListGetAt d.partner probeIndex))) = true
          rw [invPP, natBltOfLtDispatch _ _ probeBelow, natBltOfLtDispatch _ _ ppLtProbe]
          rfl
        have memP : natListGetAt d.partner probeIndex ∈ capArcFeetIndices d.bottomCount d.partner :=
          memFilterMapGuardComplete (capSmallerGuard d.bottomCount d.partner) (List.range d.bottomCount)
            (natListGetAt d.partner probeIndex)
            (memRangeOfLtDispatch (natListGetAt d.partner probeIndex) d.bottomCount ppLtBc) smallerTrue
        have rt := natIndexOfValueRoundtrip (capArcFeetIndices d.bottomCount d.partner)
          (natListGetAt d.partner probeIndex) memP
        have gen := capArcMatching_general d bottomPos wf
          (natIndexOfValue (capArcFeetIndices d.bottomCount d.partner) (natListGetAt d.partner probeIndex)) rt.2
        rw [rt.1, invPP] at gen
        exact matchingSameComponent_flipTrue _ _ _ _ gen
      · -- Arm 3: through-bottom (canonical)
        have bcLePP : d.bottomCount ≤ natListGetAt d.partner probeIndex :=
          natLeOfBleDispatch _ _ hT
        have ppLtTotal : natListGetAt d.partner probeIndex < d.bottomCount + d.topCount :=
          wf.mapsInRange probeIndex probeLt
        have keyEq : d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount)
            = natListGetAt d.partner probeIndex := addSubCancelDispatch _ _ bcLePP
        have topTrue : throughTopGuard d.bottomCount d.partner
            (natListGetAt d.partner probeIndex - d.bottomCount) = true := by
          show Nat.blt (natListGetAt d.partner
            (d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount))) d.bottomCount = true
          rw [keyEq, invPP]; exact natBltOfLtDispatch _ _ probeBelow
        have offLtTop : natListGetAt d.partner probeIndex - d.bottomCount < d.topCount := by
          have step : d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount)
              < d.bottomCount + d.topCount := by rw [keyEq]; exact ppLtTotal
          exact Nat.lt_of_add_lt_add_left step
        have memT : natListGetAt d.partner probeIndex - d.bottomCount
            ∈ throughStrandTops d.bottomCount d.topCount d.partner :=
          memFilterMapGuardComplete (throughTopGuard d.bottomCount d.partner) (List.range d.topCount)
            (natListGetAt d.partner probeIndex - d.bottomCount)
            (memRangeOfLtDispatch _ d.topCount offLtTop) topTrue
        have rt := natIndexOfValueRoundtrip (throughStrandTops d.bottomCount d.topCount d.partner)
          (natListGetAt d.partner probeIndex - d.bottomCount) memT
        have gen := throughArcMatching_general d bottomPos wf
          (natIndexOfValue (throughStrandTops d.bottomCount d.topCount d.partner)
            (natListGetAt d.partner probeIndex - d.bottomCount)) rt.2
        rw [rt.1, keyEq, invPP] at gen
        exact gen
  | inr bcLe =>
      -- TOP port: probeIndex = bc + off
      have probeEq : d.bottomCount + (probeIndex - d.bottomCount) = probeIndex := addSubCancelDispatch _ _ bcLe
      have offLtTop : probeIndex - d.bottomCount < d.topCount := by
        have step : d.bottomCount + (probeIndex - d.bottomCount) < d.bottomCount + d.topCount := by
          rw [probeEq]; exact probeLt
        exact Nat.lt_of_add_lt_add_left step
      have cls := partitionThree_of_involution_top d.bottomCount d.topCount (d.bottomCount + d.topCount) d.partner
        (Nat.le_refl _) wf (probeIndex - d.bottomCount) offLtTop
      dsimp only [onlyOneTrueThree] at cls
      rcases cls with ⟨hCS, _, _⟩ | ⟨_, hCL, _⟩ | ⟨_, _, hTT⟩
      · -- Arm 4: cup-smaller (canonical)
        have memP : probeIndex - d.bottomCount ∈ cupArcTopIndices d.bottomCount d.topCount d.partner :=
          memFilterMapGuardComplete (cupSmallerGuard d.bottomCount d.partner) (List.range d.topCount)
            (probeIndex - d.bottomCount) (memRangeOfLtDispatch _ d.topCount offLtTop) hCS
        have rt := natIndexOfValueRoundtrip (cupArcTopIndices d.bottomCount d.topCount d.partner)
          (probeIndex - d.bottomCount) memP
        have bcLePP : d.bottomCount ≤ natListGetAt d.partner probeIndex := by
          have hle := natLeOfBleDispatch _ _ (boolAndLeftDispatch _ _ hCS)
          rw [probeEq] at hle; exact hle
        have hFst : natListGetAt (cupArcTops d.bottomCount d.topCount d.partner)
            (doublePos (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner)
              (probeIndex - d.bottomCount))) = probeIndex - d.bottomCount :=
          (expandCupTopPairs_getAt_fst d.bottomCount d.partner (cupArcTopIndices d.bottomCount d.topCount d.partner)
            (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner) (probeIndex - d.bottomCount))
            rt.2).trans rt.1
        have hSnd : natListGetAt (cupArcTops d.bottomCount d.topCount d.partner)
            (doublePos (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner)
              (probeIndex - d.bottomCount)) + 1)
            = natListGetAt d.partner probeIndex - d.bottomCount := by
          have base := expandCupTopPairs_getAt_snd d.bottomCount d.partner
            (cupArcTopIndices d.bottomCount d.topCount d.partner)
            (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner) (probeIndex - d.bottomCount)) rt.2
          rw [rt.1, probeEq] at base
          exact base
        have gen := cupArcMatching_general d bottomPos wf
          (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner) (probeIndex - d.bottomCount)) rt.2
        rw [hFst, hSnd, probeEq, addSubCancelDispatch d.bottomCount (natListGetAt d.partner probeIndex) bcLePP] at gen
        exact gen
      · -- Arm 5: cup-larger (FLIP)
        have bcLePP : d.bottomCount ≤ natListGetAt d.partner probeIndex := by
          have hle := natLeOfBleDispatch _ _ (boolAndLeftDispatch _ _ hCL)
          rw [probeEq] at hle; exact hle
        have ppLtProbe : natListGetAt d.partner probeIndex < probeIndex := by
          have hlt := natLtOfBltDispatch _ _ (boolAndRightDispatch _ _ hCL)
          rw [probeEq] at hlt; exact hlt
        have keyEq : d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount)
            = natListGetAt d.partner probeIndex := addSubCancelDispatch _ _ bcLePP
        have smallerTrue : cupSmallerGuard d.bottomCount d.partner
            (natListGetAt d.partner probeIndex - d.bottomCount) = true := by
          show (Nat.ble d.bottomCount (natListGetAt d.partner
              (d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount)))
            && Nat.blt (d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount))
              (natListGetAt d.partner (d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount)))) = true
          rw [keyEq, invPP, natBleOfLeDispatch _ _ bcLe, natBltOfLtDispatch _ _ ppLtProbe]
          rfl
        have ppLtTotal : natListGetAt d.partner probeIndex < d.bottomCount + d.topCount :=
          wf.mapsInRange probeIndex probeLt
        have offLtTop' : natListGetAt d.partner probeIndex - d.bottomCount < d.topCount := by
          have step : d.bottomCount + (natListGetAt d.partner probeIndex - d.bottomCount)
              < d.bottomCount + d.topCount := by rw [keyEq]; exact ppLtTotal
          exact Nat.lt_of_add_lt_add_left step
        have memP : natListGetAt d.partner probeIndex - d.bottomCount
            ∈ cupArcTopIndices d.bottomCount d.topCount d.partner :=
          memFilterMapGuardComplete (cupSmallerGuard d.bottomCount d.partner) (List.range d.topCount)
            (natListGetAt d.partner probeIndex - d.bottomCount) (memRangeOfLtDispatch _ d.topCount offLtTop')
            smallerTrue
        have rt := natIndexOfValueRoundtrip (cupArcTopIndices d.bottomCount d.topCount d.partner)
          (natListGetAt d.partner probeIndex - d.bottomCount) memP
        have hFst : natListGetAt (cupArcTops d.bottomCount d.topCount d.partner)
            (doublePos (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner)
              (natListGetAt d.partner probeIndex - d.bottomCount)))
            = natListGetAt d.partner probeIndex - d.bottomCount :=
          (expandCupTopPairs_getAt_fst d.bottomCount d.partner (cupArcTopIndices d.bottomCount d.topCount d.partner)
            (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner)
              (natListGetAt d.partner probeIndex - d.bottomCount)) rt.2).trans rt.1
        have hSnd : natListGetAt (cupArcTops d.bottomCount d.topCount d.partner)
            (doublePos (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner)
              (natListGetAt d.partner probeIndex - d.bottomCount)) + 1)
            = probeIndex - d.bottomCount := by
          have base := expandCupTopPairs_getAt_snd d.bottomCount d.partner
            (cupArcTopIndices d.bottomCount d.topCount d.partner)
            (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner)
              (natListGetAt d.partner probeIndex - d.bottomCount)) rt.2
          rw [rt.1, keyEq, invPP] at base
          exact base
        have gen := cupArcMatching_general d bottomPos wf
          (natIndexOfValue (cupArcTopIndices d.bottomCount d.topCount d.partner)
            (natListGetAt d.partner probeIndex - d.bottomCount)) rt.2
        rw [hFst, hSnd, keyEq, probeEq] at gen
        exact matchingSameComponent_flipTrue _ _ _ _ gen
      · -- Arm 6: through-top (FLIP)
        have memT : probeIndex - d.bottomCount ∈ throughStrandTops d.bottomCount d.topCount d.partner :=
          memFilterMapGuardComplete (throughTopGuard d.bottomCount d.partner) (List.range d.topCount)
            (probeIndex - d.bottomCount) (memRangeOfLtDispatch _ d.topCount offLtTop) hTT
        have rt := natIndexOfValueRoundtrip (throughStrandTops d.bottomCount d.topCount d.partner)
          (probeIndex - d.bottomCount) memT
        have gen := throughArcMatching_general d bottomPos wf
          (natIndexOfValue (throughStrandTops d.bottomCount d.topCount d.partner)
            (probeIndex - d.bottomCount)) rt.2
        rw [rt.1, probeEq] at gen
        exact matchingSameComponent_flipTrue _ _ _ _ gen

/-! ## Section 3 — the UNCONDITIONAL read-off -/

/-- ★★★ **THE UNCONDITIONAL PARTNER READ-OFF.**  For EVERY well-formed boundary involution `d` (with
`0 < d.bottomCount`) and EVERY in-range boundary port, the extractor's partner map reads exactly `partner probeIndex`
off the corrected six-phase fold — no per-arc `decide`, no per-witness `partnerShares` hypothesis.  The r22 routing
collapse fed the unconditional `partnerShares_general`, with the width `foldOpenWiresWidth_correctedWord` converting
the range premise and `wf.isFixedPointFree` supplying `partnerIndex ≠ probeIndex`. -/
theorem partnerIndexOf_reads_arc_unconditional (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (probeIndex : Nat)
    (probeInRange : probeIndex < d.bottomCount
      + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length) :
    partnerIndexOf
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (matchingBoundaryNodes d.bottomCount
          (processBrauer (brauerSeed d.bottomCount)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))))
        (d.bottomCount + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length)
        probeIndex
      = natListGetAt d.partner probeIndex := by
  have hwidth := foldOpenWiresWidth_correctedWord d wf
  have probeLtTotal : probeIndex < d.bottomCount + d.topCount := by rw [← hwidth]; exact probeInRange
  have partnerLtTotal : natListGetAt d.partner probeIndex < d.bottomCount + d.topCount :=
    wf.mapsInRange probeIndex probeLtTotal
  have partnerInRange : natListGetAt d.partner probeIndex < d.bottomCount
      + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length := by
    rw [hwidth]; exact partnerLtTotal
  exact partnerIndexOf_reads_arc_general d bottomPos wf probeIndex (natListGetAt d.partner probeIndex)
    probeInRange partnerInRange (wf.isFixedPointFree probeIndex probeLtTotal)
    (partnerShares_general d bottomPos wf probeIndex probeLtTotal)

/-! ## Section 4 — the self-attacks: the six-arm dispatch FIRED on the recon hostiles (general, not `decide`) -/

/-- ★★ **partnerShares_general FIRES on the width-12 monster (cap arm 0).**  The general dispatch produces the
per-arc datum on the monster's boundary port `0` (a cap smaller foot) — exercised, not `decide`d. -/
theorem partnerShares_firesMonster_zero :
    matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram)))
      0 (natListGetAt monsterDiagram.partner 0) = true :=
  partnerShares_general monsterDiagram (by decide) monster_isBoundaryInvolution 0 (by decide)

/-- ★★ **partnerShares_general FIRES on the width-12 monster (through arm, bottom port 4).** -/
theorem partnerShares_firesMonster_four :
    matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram)))
      4 (natListGetAt monsterDiagram.partner 4) = true :=
  partnerShares_general monsterDiagram (by decide) monster_isBoundaryInvolution 4 (by decide)

/-- ★★ **partnerShares_general FIRES on the width-12 monster (cup arm, top port 8).** -/
theorem partnerShares_firesMonster_eight :
    matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram)))
      8 (natListGetAt monsterDiagram.partner 8) = true :=
  partnerShares_general monsterDiagram (by decide) monster_isBoundaryInvolution 8 (by decide)

/-- ★★ **partnerShares_general FIRES on the triple-axis adversarial-B (cap `0`, through `1`, cup `3`).** -/
theorem partnerShares_firesAdversarialB :
    (matchingSameComponent 3 (processBrauer (brauerSeed 3)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram)))
      0 (natListGetAt adversarialBDiagram.partner 0) = true)
    ∧ (matchingSameComponent 3 (processBrauer (brauerSeed 3)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram)))
      1 (natListGetAt adversarialBDiagram.partner 1) = true)
    ∧ (matchingSameComponent 3 (processBrauer (brauerSeed 3)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram)))
      3 (natListGetAt adversarialBDiagram.partner 3) = true) :=
  ⟨partnerShares_general adversarialBDiagram (by decide) isBoundaryInvolution_adversarialBDiagram 0 (by decide),
   partnerShares_general adversarialBDiagram (by decide) isBoundaryInvolution_adversarialBDiagram 1 (by decide),
   partnerShares_general adversarialBDiagram (by decide) isBoundaryInvolution_adversarialBDiagram 3 (by decide)⟩

/-- ★★★ **THE UNCONDITIONAL READ-OFF FIRES on the monster (cap port 0), via the general dispatch — no `decide`d
`partnerShares`.**  `partnerIndexOf_reads_arc_unconditional` reads `partner 0` off the width-12 monster fold with the
partnerShares supplied by the general six-arm dispatch. -/
theorem partnerIndexOf_readsArc_unconditional_monster_zero :
    partnerIndexOf
        (processBrauer (brauerSeed 6)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))).links
        (matchingBoundaryNodes 6
          (processBrauer (brauerSeed 6)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))))
        (6 + (processBrauer (brauerSeed 6)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))).openWires.length)
        0
      = natListGetAt monsterDiagram.partner 0 :=
  partnerIndexOf_reads_arc_unconditional monsterDiagram (by decide) monster_isBoundaryInvolution 0 (by decide)

/-! ## Section 5 — the additive flip marker (the wall's content DISCHARGED; the frozen boolean kept) -/

/-- ★★★ **Honesty marker — the UNCONDITIONAL per-arc T-CONNECT is SHIPPED (r29 B2, the six-arm dispatch assembled).**
`partnerShares_general` proves, zero-axiom and structural, that for EVERY well-formed boundary involution and EVERY
boundary port the port and its partner share a component in the corrected six-phase fold — the exact per-arc datum the
r22 routing collapse consumes, discharged UNCONDITIONALLY.  `partnerIndexOf_reads_arc_unconditional` feeds it into the
collapse, reading `partner probeIndex` off the fold for every in-range port with NO per-witness hypothesis.  This
DISCHARGES the semantic content of the wall `fxBrauer_hasTConnectThroughWall` (the general per-arc T-CONNECT PROOF the
r19 fresh-id bridge named as unbuilt): the CAP r24 + CUP r26 + THROUGH r28 generals + the value→rank recovery +
the `matchingSameComponent_symm` flip assemble it in general.  Per the r28 additive-flip precedent, the wall's boolean
`fxBrauer_hasTConnectThroughWall` is KEPT `false` (it anchors the r22/r25/r26/r27/r28 grand-ledger `rfl`s); this NEW
marker carries the `true`.  It flips NO completeness master — #2013 closes only after T-CLOSE(b) (the `loops` field,
B3).  Fired UNCONDITIONALLY on the monster (cap/through/cup) and the adversarial-B.  `= true`. -/
def fxBrauer_hasUnconditionalPartnerShares : Bool := true

end FX1Poly.Polygraph
