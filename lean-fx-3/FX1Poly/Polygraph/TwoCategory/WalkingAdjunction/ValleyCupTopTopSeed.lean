import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupTopTopFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupBottomPartner
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupCapStatePromotion
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorUnlinked

/-! # ValleyCupTopTopSeed — CLOSING the top-top cup-arc partner (Piece II tail, cup case 3)

The two-floor peel induction `topRegionOffsetAgrees_fold` (`ValleyCupTopTopFold`) delivers the top-region
offset-space agreement of the two cup runs at the two floors — but stated over the ARC encoding
(`extractArc ∘ processArcSpine`) and gated on a base-case seed reconciliation.  This file discharges BOTH
remaining sub-nodes and assembles the residual `cupTopTopPartner` (`ValleyCupReconstruct`, cup case 3):

  * the **base-case seed reconciliation** (`seedAgree`) — at the two SEEDS (the folded cap seed and the
    cup-alone from-scratch seed), EVERY top port is a survivor-top (its partner is a BELOW-floor bottom), so
    the top-top tag is FALSE on both runs and the agreement holds vacuously.  The load-bearing fact is
    `pureCapTopPartnerBelow`: a pure-cap block's top-port partner sits below the floor (survivor readoff +
    the whole-valley involution).

  * the **WireState ↔ arc bridge** — both seed and final ARC partner lists are rewritten to the plain
    `matchingOfSpineList` carrier via the shipped `arcDiagram_eq_matching`
    (`(arcStructureOfSpineList bc l).diagram = matchingOfSpineList bc l`), composed over the whole block by
    `processArcSpine_append` / `processSpine_append`.

Assembled, the fold's offset half + the top-top tag hypothesis give the reconstructed cup-top partner value,
closing `cupTopTopPartner` — hence (in `ValleyCupReconstruct`) `cupRestrict_reconstructs` becomes
UNCONDITIONAL, and downstream `valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv` follow.  No
gate flag is flipped; fib-3 also carries the independent Piece-I beam (`MatchingReductsShareSpineTrace`,
#1996), so `convOfMapEq` stays gated regardless.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range / arithmetic plumbing (propext-free copies) -/

private theorem rangeLoopLenLocal : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLenLocal count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLenLocal (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLenLocal count []]
  exact Nat.add_zero count

/-- `base + (extra - base) = extra` for `base ≤ extra` (hand-rolled; `Nat.add_sub_cancel'` leaks `propext`). -/
private theorem addSubCancelLocal : (base extra : Nat) → base ≤ extra → base + (extra - base) = extra
  | 0, extra, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, 0, atMost => absurd atMost (Nat.not_succ_le_zero base)
  | base + 1, extra + 1, atMost => by
      have inner := addSubCancelLocal base extra (Nat.le_of_succ_le_succ atMost)
      rw [Nat.succ_sub_succ, Nat.succ_add, inner]

/-- An in-range positional read is a member (local copy). -/
private theorem getAt_mem_of_lt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## The load-bearing seed fact — a pure-cap block's top port partners below the floor -/

/-- ★ **A pure-cap block's top-port partner is a below-floor bottom.**  For a boundary-chained pure-cap block
run from the canonical seed `⟨range floor, [], floor, 0⟩`, the top port `floor + off` (with `off` an open-wire
position) partners to a bottom port `< floor`.  Every open wire is a SURVIVOR: it sits below the floor
(`processSpine_openWires_below_ofAllCapArity_seed`), is unlinked
(`processSpine_openWires_unlinked_ofAllCapArity_seed`), and distinct
(`processSpine_fromSeed_wireListDistinct`), so the survivor read-off pins the bottom→top partner at
`floor + off`; the whole-valley involution (`matchingOf_partner_isInvolution`) reflects the top port
`floor + off` back to that below-floor survivor bottom. -/
theorem pureCapTopPartnerBelow
    {overallSource overallTarget : adjunctionGraph.Mode} (floor : Nat) (floorPositive : 0 < floor)
    (block : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (blockPure : AllCapArity block)
    (blockChained : SpineBoundaryChained floor block)
    {off : Nat}
    (offLt : off < (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires.length) :
    natListGetAt (matchingOfSpineList floor block).partner (floor + off) < floor := by
  have survivorMem :
      natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off
        ∈ (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires :=
    getAt_mem_of_lt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off offLt
  have survivorBelow :
      natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off < floor :=
    processSpine_openWires_below_ofAllCapArity_seed floor floorPositive block blockPure
      (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off) survivorMem
  have openAllUnlinked : ∀ w ∈ (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires,
      ArcNodeUnlinked (processSpine ⟨List.range floor, [], floor, 0⟩ block).links w :=
    processSpine_openWires_unlinked_ofAllCapArity_seed floor block blockPure blockChained
  have survivorUnlinked :
      ArcNodeUnlinked (processSpine ⟨List.range floor, [], floor, 0⟩ block).links
        (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off) :=
    openAllUnlinked _ survivorMem
  have openDistinct : WireListDistinct (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires :=
    processSpine_fromSeed_wireListDistinct floor floorPositive block
  have readoff :
      partnerIndexOf (processSpine ⟨List.range floor, [], floor, 0⟩ block).links
          (matchingBoundaryNodes floor (processSpine ⟨List.range floor, [], floor, 0⟩ block))
          (floor + (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires.length)
          (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off)
        = floor + off :=
    partnerIndexOf_survivor_eq_rank (processSpine ⟨List.range floor, [], floor, 0⟩ block).links floor
      (processSpine ⟨List.range floor, [], floor, 0⟩ block)
      survivorBelow survivorUnlinked openDistinct openAllUnlinked offLt rfl
  have survInRange :
      natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off
        < floor + (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires.length :=
    Nat.lt_of_lt_of_le survivorBelow
      (Nat.le_add_right floor (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires.length)
  have pEq : natListGetAt (matchingOfSpineList floor block).partner
      (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off) = floor + off := by
    show natListGetAt (extractDiagram floor (processSpine ⟨List.range floor, [], floor, 0⟩ block)).partner
        (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off) = floor + off
    rw [extractDiagram_partner_getAt floor (processSpine ⟨List.range floor, [], floor, 0⟩ block)
      (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off) survInRange]
    exact readoff
  have notFixed : natListGetAt (matchingOfSpineList floor block).partner
      (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off)
        ≠ natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off := by
    rw [pEq]
    intro equal
    exact Nat.lt_irrefl floor
      (Nat.lt_of_le_of_lt (equal ▸ Nat.le_add_right floor off) survivorBelow)
  have invol := matchingOf_partner_isInvolution floor floorPositive block
    (spineHasCupCapAtoms_ofAllCapArity block blockPure) blockChained
    (natListGetAt (processSpine ⟨List.range floor, [], floor, 0⟩ block).openWires off) survInRange notFixed
  rw [pEq] at invol
  rw [invol]
  exact survivorBelow

/-! ## The base-case seed reconciliation and the assembled `cupTopTopPartner` -/

/-- ★ **The top-top cup-arc partner agreement (cup case 3) — CLOSED.**  For a cup-top port
`midWidth + topOffset` (`midWidth = capState.openWires.length`) whose whole-valley top `bc + topOffset` is a
TOP-TOP cup arc (`V.partner[bc + topOffset] ≥ bc`), the cup block's OWN partner equals `cupRestrict`'s
reconstructed value `midWidth + (V.partner[bc + topOffset] − bc)`.

Assembled from the two-floor peel induction `topRegionOffsetAgrees_fold` run at the in-valley cap seed
`capState := processArcSpine (arcInit bc) capBlock` and the cup-alone seed `arcInit midWidth`, with:

  * the SEED agreement (`seedAgree`) discharged vacuously — both seeds' top ports are survivor-tops
    (`pureCapTopPartnerBelow`), so the top-top tag is FALSE, at both floors;
  * both seed and final ARC partner lists bridged to `matchingOfSpineList` via `arcDiagram_eq_matching`
    (composed over the whole block by `processArcSpine_append` / `processSpine_append`);
  * the fold's offset half + `addSubCancelLocal` reassembling the cup-top partner value under the top-top
    tag supplied by the hypothesis.

Takes the valley's structural data (`wholeChained`, `midPositive`) as honest inputs — the eventual caller
(`cupRestrict_reconstructs` and its downstream) supplies them from the genuine valley shape. -/
theorem cupTopTopPartner
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock))
    (midPositive : 0 < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
    {topOffset : Nat}
    (topLt : topOffset < (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock)
        cupBlock).openWires.length)
    (wpAbove : bottomCount ≤ natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
        (bottomCount + topOffset)) :
    natListGetAt (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
        ((processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length + topOffset)
      = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
        + (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
             (bottomCount + topOffset) - bottomCount) := by
  -- The cap prefix is boundary-chained (restriction of the whole valley chaining).
  have capChained : SpineBoundaryChained bottomCount capBlock :=
    spineBoundaryChained_prefix_ofAppend capBlock cupBlock bottomCount wholeChained
  -- The whole valley is a cup/cap spine.
  have wholeArity : SpineHasCupCapAtoms (capBlock ++ cupBlock) :=
    spineHasCupCapAtoms_append capBlock cupBlock
      (spineHasCupCapAtoms_ofAllCapArity capBlock capPure)
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure)
  -- The arc cap seed's open-wire count equals the wire mid-width (bridge top-count).
  have midEqAW :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).openWires.length
        = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length :=
    congrArg DiagramType.topCount
      (arcDiagram_eq_matching bottomCount capBlock
        (spineHasCupCapAtoms_ofAllCapArity capBlock capPure) capChained bottomPositive)
  -- The four per-cup transport preconditions at the in-valley cap seed.
  obtain ⟨freshHi, forestHi, seedBelowHi, censusHi⟩ :=
    arcCapState_stepCupArc_preconditions bottomCount capBlock capChained
  -- Threading data for the fold at floor `midWidth`.
  have chainedLo : SpineBoundaryChained
      (ArcWireState.mk (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
        [] (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length 0 [] []).openWires.length
      cupBlock := by
    show SpineBoundaryChained
      (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length).length cupBlock
    rw [rangeLenLocal]
    exact cupChained
  have chainedHi : SpineBoundaryChained
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).openWires.length
      cupBlock := midEqAW.symm ▸ cupChained
  have openWiresEq :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).openWires.length
        = (ArcWireState.mk (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
            [] (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length 0 [] []).openWires.length := by
    show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).openWires.length
        = (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length).length
    rw [rangeLenLocal]
    exact midEqAW
  -- The base-case seed reconciliation: both seeds' top ports are survivor-tops (tag false), so the agreement is vacuous.
  have seedAgree : topRegionOffsetAgrees bottomCount
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)).diagram.partner
      (extractArc (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
        (ArcWireState.mk (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
          [] (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length 0 [] [])).diagram.partner
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock).openWires.length := by
    let emptyLo : List (SpineAtom adjunctionModeSignature overallSource overallTarget) := []
    have hiSeedEq :
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)).diagram.partner
          = (matchingOfSpineList bottomCount capBlock).partner :=
      congrArg DiagramType.partner
        (arcDiagram_eq_matching bottomCount capBlock
          (spineHasCupCapAtoms_ofAllCapArity capBlock capPure) capChained bottomPositive)
    have loSeedEq :
        (extractArc (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
          (ArcWireState.mk (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
            [] (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length 0 [] [])).diagram.partner
          = (matchingOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
              (emptyLo)).partner := by
      have bridge :
          (arcStructureOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length emptyLo).diagram
            = matchingOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length emptyLo :=
        arcDiagram_eq_matching (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length emptyLo
          (spineHasCupCapAtoms_ofAllCapArity emptyLo AllCapArity.nil)
          (SpineBoundaryChained.nil (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
          midPositive
      exact congrArg DiagramType.partner bridge
    rw [hiSeedEq, loSeedEq]
    intro off offLt
    have offLtMid : off < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length :=
      midEqAW ▸ offLt
    have hiBelow : natListGetAt (matchingOfSpineList bottomCount capBlock).partner (bottomCount + off) < bottomCount :=
      pureCapTopPartnerBelow bottomCount bottomPositive capBlock capPure capChained offLtMid
    have loBelow : natListGetAt
        (matchingOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length emptyLo).partner
        ((processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length + off)
          < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length :=
      pureCapTopPartnerBelow (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
        midPositive emptyLo AllCapArity.nil
        (SpineBoundaryChained.nil (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
        (by
          show off < (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length).length
          rw [rangeLenLocal]
          exact offLtMid)
    exact ⟨⟨fun hiLe => absurd hiLe (Nat.not_le_of_gt hiBelow),
        fun loLe => absurd loLe (Nat.not_le_of_gt loBelow)⟩,
      fun hiLe => absurd hiLe (Nat.not_le_of_gt hiBelow)⟩
  -- Run the fold.
  have foldConcl := topRegionOffsetAgrees_fold bottomCount
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock cupPure
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)
    (ArcWireState.mk (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
      [] (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length 0 [] [])
    freshHi forestHi seedBelowHi censusHi
    (arcStateFresh_initial (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
    isUnionFindForest_nil
    (Nat.le_refl (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
    (arcBoundaryCensus_initial (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
    chainedHi chainedLo openWiresEq seedAgree
  -- Bridge the final HI / LO partner lists to the plain matching carrier.
  have appendArc :
      processArcSpine (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock) cupBlock
        = processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) (capBlock ++ cupBlock) :=
    (processArcSpine_append capBlock cupBlock (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).symm
  have hiFinalEq :
      (extractArc bottomCount
        (processArcSpine (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)
          cupBlock)).diagram.partner
        = (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner := by
    rw [appendArc]
    exact congrArg DiagramType.partner
      (arcDiagram_eq_matching bottomCount (capBlock ++ cupBlock) wholeArity wholeChained bottomPositive)
  have loFinalEq :
      (extractArc (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
        (processArcSpine (ArcWireState.mk (List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length)
          [] (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length 0 [] []) cupBlock)).diagram.partner
        = (matchingOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner :=
    congrArg DiagramType.partner
      (arcDiagram_eq_matching (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock
        (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure) cupChained midPositive)
  -- The final arc top-count equals the wire top-count (so `topLt` feeds the fold).
  have finalMidEq :
      (processArcSpine (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)
        cupBlock).openWires.length
        = (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) cupBlock).openWires.length := by
    have step1 :
        (processArcSpine (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) capBlock)
          cupBlock).openWires.length
          = (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount := by
      rw [appendArc]
      exact congrArg DiagramType.topCount
        (arcDiagram_eq_matching bottomCount (capBlock ++ cupBlock) wholeArity wholeChained bottomPositive)
    have step2 : (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount
        = (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) cupBlock).openWires.length := by
      show (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ (capBlock ++ cupBlock)).openWires.length
          = (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock) cupBlock).openWires.length
      rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
    exact step1.trans step2
  rw [hiFinalEq, loFinalEq, finalMidEq] at foldConcl
  -- Extract the offset half under the top-top tag.
  have midLe : (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
      ≤ natListGetAt (matchingOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
          ((processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length + topOffset) :=
    (foldConcl topOffset topLt).1.mp wpAbove
  have offsetHalf :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner (bottomCount + topOffset) - bottomCount
        = natListGetAt (matchingOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
            ((processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length + topOffset)
          - (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length :=
    (foldConcl topOffset topLt).2 wpAbove
  rw [offsetHalf]
  exact (addSubCancelLocal (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length
    (natListGetAt (matchingOfSpineList (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).partner
      ((processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length + topOffset)) midLe).symm

/-! ## Honesty marker -/

/-- **Honesty marker — the top-top cup-arc partner (cup case 3) is CLOSED; Piece II's cup residual is fully
discharged.**

Landed here, all zero-axiom:

  * `pureCapTopPartnerBelow` — a pure-cap block's top-port partner is a below-floor survivor bottom (survivor
    read-off + whole-valley involution).
  * `cupTopTopPartner` — the top-top cup-arc partner agreement, assembled from the two-floor peel induction
    `topRegionOffsetAgrees_fold` (base-case `seedAgree` discharged vacuously via `pureCapTopPartnerBelow`, both
    seed/final partner lists bridged to `matchingOfSpineList` via `arcDiagram_eq_matching`), the fold offset
    half, and `addSubCancelLocal`.

This was the SOLE un-shipped residual of `cupRestrict_reconstructs` (`ValleyCupReconstruct`, cup case 3).  With
it closed, `cupRestrict_reconstructs` — and hence `valleyAppend_split` /
`valleysWithEqualMatching_spineTraceEquiv` — become UNCONDITIONAL modulo the genuine valley-shape inputs
(`wholeChained`, `midPositive`).  No gate flag is flipped; fib-3 also carries the independent Piece-I beam
(`MatchingReductsShareSpineTrace`, #1996), so `convOfMapEq` stays gated regardless — the flag flip needs BOTH
pieces.  `= true`. -/
def fxMode_hasCupTopTopPartnerClosed : Bool := true

end FX1Poly.Polygraph
