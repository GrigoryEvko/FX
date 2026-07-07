import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSurjectivity
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.CupShiftReranking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyFloorHomogeneous
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWireDistinct

/-! # ValleyCapRestrict — the cap-side restriction functor `capRestrict` (F) on `DiagramType` (Piece II tail)

The valley-append split reconstructs the CAP block's own diagram from the WHOLE valley's diagram.  This file
defines the reconstruction FUNCTION `capRestrict : DiagramType → DiagramType` — the topological "F-restriction"
that compresses out the cup-inserted top wires — and lands the field agreements that are closable with the
shipped arithmetic core.

## The reconstruction function

For a whole-valley diagram `V = matchingOf bc (capBlock ++ cupBlock)`, `capRestrict V` reads off the cap block's
own diagram using ONLY `V`:

  * `bottomCount` — copied (`bc`, the cap block's own bottom count).
  * `topCount` — `survivorTopTotal V` (the number of survivor-tops = the number of cap-block through-strands =
    the mid-width, the cap block's own open-wire count).
  * `loops` — copied (`V.loops`; cups add no loops, `matchingOf_loops_split`).
  * `partner` — the re-ranked matching over the `bc + midWidth` cap-boundary ports:
    - a SURVIVOR-BOTTOM port `k` (`k < bc`, `V.partner[k] ≥ bc`, a through-strand): its whole-valley partner top
      `V.partner[k] = bc + phi rankCap` is COMPRESSED to `bc + survivorTopRank V (V.partner[k]) = bc + rankCap`,
      inverting the cup shift `phi` by the shipped counting bridge;
    - a CAP-CONSUMED bottom port `k` (`k < bc`, `V.partner[k] < bc`, a bottom-bottom cap arc): copied `V.partner[k]`
      (cups leave bottom-bottom connectivity invariant);
    - a CAP-TOP port `bc + r`: points back to the survivor bottom `V.partner[nthSurvivorTop V r]` at the r-th
      survivor-top.

## What this file lands (each closable piece zero-axiom)

  * ★ `capRestrict` + `survivorTopTotal` + `nthSurvivorTop` — the reconstruction function, total and computing.
  * ★ `capRestrict_bottomCount_eq` / `capRestrict_loops_eq` — the two copied fields agree with the cap block's own
    diagram (the `bottomCount` field by `rfl`, the `loops` field via `matchingOf_loops_split`).
  * ★ `capRestrict_partner_survivorBottom` — the SURVIVOR-BOTTOM partner-field agreement (the arithmetic
    keystone): the cap-alone partner of a survivor bottom port equals `capRestrict`'s reconstructed value
    `bc + survivorTopRank V (V.partner[survivor])`.  A clean `.trans` of the shipped endpoints — the cup-shift
    re-ranking (`partnerIndexOf_survivorUnlinked_eq_rank` through the image-cover embedding), the rank read-off
    (`survivorTop_rankReadoff_ofStrictMono`), and the cap-alone read-off (`partnerIndexOf_survivor_eq_rank`) — all
    routed through ONE cup-embedding `phi` (from `processSpine_wireOrderImageCover_ofAllCupArity`), so the
    partner value and its rank read-off share the same embedding and compose directly.

## What this file does NOT close (the standing residual #2185)

The full `matchingOf bc capBlock = capRestrict (matchingOf bc V)` `DiagramType.ext` needs, beyond the survivor
bottom keystone: the `topCount` count-total identity (`midWidth = survivorTopTotal V`, a not-yet-packaged
"count of all cup-embedding images = domain size" corollary of the shipped surjectivity), the cap-CONSUMED bottom
partner-list agreement (a `findPartnerScan` front-confinement lift of the shipped bottom-bottom connectivity
frame), and the cap-TOP port agreement (the `nthSurvivorTop` correctness + a `matchingOf` partner-INVOLUTION,
which does not exist in the corpus — the hardest new lemma).  No gate flag is flipped.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range / map plumbing (propext-free copies) -/

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

private theorem rangeLoopGetAtPastLocal : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastLocal count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowLocal : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowLocal count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastLocal count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowLocal (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowLocal count [] index indexBelow

/-- Reading `(List.range total).map mappedFunction` at an in-range index is `mappedFunction index`. -/
private theorem natRangeMapGetAtLocal (total : Nat) (mappedFunction : Nat → Nat) (index : Nat)
    (indexInRange : index < total) :
    natListGetAt ((List.range total).map mappedFunction) index = mappedFunction index := by
  rw [natListGetAt_map_inRange mappedFunction (List.range total) index
      (by rw [rangeLenLocal total]; exact indexInRange),
    rangeGetAtBelowLocal total index indexInRange]

/-- An in-range positional read is a member (local copy). -/
private theorem getAt_mem_of_lt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- The `partner` field of `extractDiagram bc state`, read at an in-range boundary index, IS the boundary
`partnerIndexOf` — the `List.range … |>.map` reduces to the mapped scan at that index. -/
theorem extractDiagram_partner_getAt (bottomCount : Nat) (state : WireState) (index : Nat)
    (indexInRange : index < bottomCount + state.openWires.length) :
    natListGetAt (extractDiagram bottomCount state).partner index
      = partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
          (bottomCount + state.openWires.length) index :=
  natRangeMapGetAtLocal (bottomCount + state.openWires.length)
    (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
      (bottomCount + state.openWires.length)) index indexInRange

/-! ## The survivor-top total and the rank→port inverse -/

/-- ★ **The survivor-top total** — the number of survivor-tops of the whole diagram, over ALL boundary ports.
This is the reconstructed `topCount` of the cap block: the number of cap-block through-strands = the mid-width. -/
def survivorTopTotal (diagram : DiagramType) : Nat :=
  survivorTopCount diagram (diagram.bottomCount + diagram.topCount)

/-- The first index of a list passing `predicate`, defaulting past the end. -/
def firstIndexWhere (predicate : Nat → Bool) : List Nat → Nat → Nat
  | [], fallback => fallback
  | head :: rest, fallback =>
      if predicate head then head else firstIndexWhere predicate rest fallback

/-- ★ **The rank→port inverse on survivor-tops** — the boundary index of the `targetRank`-th survivor-top: the
first boundary index that both passes `isSurvivorTop` and whose `survivorTopRank` equals `targetRank`.  A total
structural scan over the boundary indices, so it COMPUTES.  (Its correctness — that it returns a genuine
survivor-top of rank `targetRank` — is part of the standing cap-top-port residual; see the honesty marker.) -/
def nthSurvivorTop (diagram : DiagramType) (targetRank : Nat) : Nat :=
  firstIndexWhere
    (fun index => isSurvivorTop diagram index && Nat.beq (survivorTopRank diagram index) targetRank)
    (List.range (diagram.bottomCount + diagram.topCount)) 0

/-! ## The cap-side restriction function -/

/-- ★ **The cap-side restriction `capRestrict` (F).**  Reconstructs the cap block's own `DiagramType` from the
WHOLE valley's diagram, reading ONLY the whole diagram.  `bottomCount` and `loops` are copied; `topCount` is the
survivor-top total; the `partner` re-ranks each cap-boundary port per the three cases in the file header (survivor
bottom → compress the cup shift by `survivorTopRank`; cap-consumed bottom → copy; cap-top port → point back to the
survivor via `nthSurvivorTop`). -/
def capRestrict (diagram : DiagramType) : DiagramType :=
  let bottomCount := diagram.bottomCount
  let midWidth := survivorTopTotal diagram
  { bottomCount := bottomCount,
    topCount := midWidth,
    partner := (List.range (bottomCount + midWidth)).map (fun index =>
      if Nat.blt index bottomCount then
        let wholePartner := natListGetAt diagram.partner index
        if Nat.blt wholePartner bottomCount then wholePartner
        else bottomCount + survivorTopRank diagram wholePartner
      else
        natListGetAt diagram.partner (nthSurvivorTop diagram (index - bottomCount))),
    loops := diagram.loops }

/-! ## The two copied-field agreements -/

/-- ★ **The `bottomCount` field agrees.**  Both the cap block's own diagram and `capRestrict` of the whole valley
carry `bottomCount = bc` (the cap block's own bottom count) — a definitional read of `extractDiagram`'s literal
bottom-count field. -/
theorem capRestrict_bottomCount_eq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (matchingOfSpineList bottomCount capBlock).bottomCount
      = (capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).bottomCount :=
  rfl

/-- ★ **The `loops` field agrees.**  `capRestrict` copies the whole valley's loop count, and cups add no loops
(`matchingOf_loops_split`), so it equals the cap block's own loop count.  This is the loop leg of the cap-side
restriction, threaded through `capRestrict`. -/
theorem capRestrict_loops_eq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList bottomCount capBlock).loops
      = (capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).loops :=
  (matchingOf_loops_split bottomCount capBlock cupBlock cupPure).symm

/-! ## The survivor-bottom partner-field agreement — the arithmetic keystone -/

/-- ★ **The SURVIVOR-BOTTOM partner-field agreement.**  For a survivor bottom port `survivor` of a valley
`capBlock ++ cupBlock` (a bottom node that survives the cap block, hence a cap-block through-strand), the cap
block's OWN partner of `survivor` equals `capRestrict`'s reconstructed value
`bottomCount + survivorTopRank V (V.partner[survivor])`, where `V = matchingOf bc (capBlock ++ cupBlock)`.

This is the value-level closure of the cap-side restriction's through-strand case — the load-bearing arithmetic
of the valley-append split.  All three shipped endpoints are routed through ONE cup-embedding `phi` (obtained
from `processSpine_wireOrderImageCover_ofAllCupArity`), so no coupling residue remains:

  * the cap-alone partner is `bottomCount + rankCap` (`partnerIndexOf_survivor_eq_rank`, cap-state open wires all
    unlinked);
  * the whole-valley partner is `bottomCount + phi rankCap` (`partnerIndexOf_survivorUnlinked_eq_rank` — the
    `openAllUnlinked` hypothesis dropped so it tolerates the linked cup-leg tops — at the shifted position
    `phi rankCap` supplied by the same embedding);
  * `survivorTopRank V (bottomCount + phi rankCap) = rankCap` (`survivorTop_rankReadoff_ofStrictMono` on the same
    embedding + cover, the counting bridge inverting `phi`).

Composing: `capRestrict`-partner `= bottomCount + survivorTopRank V (bottomCount + phi rankCap)
= bottomCount + rankCap = ` cap-alone partner. -/
theorem capRestrict_partner_survivorBottom
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (capChained : SpineBoundaryChained bottomCount capBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    {survivor : Nat}
    (survivorMem : survivor ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires) :
    natListGetAt (matchingOfSpineList bottomCount capBlock).partner survivor
      = bottomCount + survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
          (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner survivor) := by
  -- Abbreviations: the cap-block mid-state and the whole-valley final state (no `set`/Mathlib — plain `let`).
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  -- The whole valley's matching IS the extract of `wholeState` (fold splits over the append).
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  -- Basic survivor facts at the cap-block mid-state.
  have survivorBelow : survivor < bottomCount :=
    processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
      survivor survivorMem
  obtain ⟨rankCap, rankCapLt, survivorAtRankCap⟩ := mem_imp_getAt capState.openWires survivorMem
  have survivorUnlinkedMid : ArcNodeUnlinked capState.links survivor :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
      survivor survivorMem
  have capDistinct : WireListDistinct capState.openWires :=
    processSpine_fromSeed_wireListDistinct bottomCount bottomPositive capBlock
  have capAllUnlinked : ∀ wire ∈ capState.openWires, ArcNodeUnlinked capState.links wire :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
  have capNextFresh : capState.nextFresh = bottomCount :=
    processSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  -- ONE cup embedding `phi` with its value cover — used for BOTH the partner value and its rank read-off.
  obtain ⟨phi, embedding, cover⟩ := processSpine_wireOrderImageCover_ofAllCupArity bottomCount cupBlock cupPure
    capState capState.openWires.length rfl (Nat.le_of_eq capNextFresh.symm) cupChained
  -- The survivor stays unlinked through the cup block, and reappears at the shifted position `phi rankCap`.
  have survivorUnlinkedWhole : ArcNodeUnlinked wholeState.links survivor :=
    processSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure capState survivor
      (by rw [capNextFresh]; exact survivorBelow) survivorUnlinkedMid
  have wholeDistinct : WireListDistinct wholeState.openWires := by
    have base : WireListDistinct
        (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires :=
      processSpine_fromSeed_wireListDistinct bottomCount bottomPositive (capBlock ++ cupBlock)
    rw [show canonicalMatchingSeed bottomCount
          = (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState) from rfl,
      processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩] at base
    exact base
  have rankWholeLt : phi rankCap < wholeState.openWires.length := embedding.inRange rankCap rankCapLt
  have survivorAtRankWhole : natListGetAt wholeState.openWires (phi rankCap) = survivor := by
    rw [embedding.reads rankCap rankCapLt, survivorAtRankCap]
  -- (a) The whole-valley partner of the survivor is `bottomCount + phi rankCap`.
  have wholePartnerEq :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner survivor
        = bottomCount + phi rankCap := by
    rw [wholeSplit, extractDiagram_partner_getAt bottomCount wholeState survivor
      (Nat.lt_of_lt_of_le survivorBelow (Nat.le_add_right bottomCount wholeState.openWires.length))]
    exact partnerIndexOf_survivorUnlinked_eq_rank wholeState.links bottomCount wholeState
      survivorBelow survivorUnlinkedWhole wholeDistinct rankWholeLt survivorAtRankWhole
  -- The whole valley's union-find is floor-homogeneous (cap edges below `bc`, then the cup fold preserves it),
  -- so below-floor nodes keep below-floor roots (N1) and at-or-above-floor nodes keep at-or-above roots (N2).
  have capFresh : WireStateFresh capState :=
    processSpine_wireStateFresh capBlock ⟨List.range bottomCount, [], bottomCount, 0⟩
      (wireStateFresh_initial bottomCount) bottomPositive
  have capEdgesBelow : ∀ edge ∈ capState.links, edge.1 < bottomCount ∧ edge.2 < bottomCount :=
    processSpine_links_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
  have capEdgesHomog : ∀ edge ∈ capState.links, edgeFloorHomogeneous bottomCount edge :=
    fun edge edgeIn =>
      ⟨fun floorLe => absurd floorLe (Nat.not_le.mpr (capEdgesBelow edge edgeIn).1),
       fun _ => (capEdgesBelow edge edgeIn).2⟩
  have wholeEdgesHomog : ∀ edge ∈ wholeState.links, edgeFloorHomogeneous bottomCount edge :=
    processSpine_edgesFloorHomogeneous_ofAllCupArity bottomCount cupBlock cupPure capState
      capFresh (Nat.le_of_eq capNextFresh.symm) capEdgesHomog
  -- (b) The rank read-off collapses that partner top port back to `rankCap`.
  have rankReadoff :
      survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) (bottomCount + phi rankCap)
        = rankCap := by
    rw [wholeSplit]
    exact survivorTop_rankReadoff_ofStrictMono bottomCount wholeState capState.openWires
      (fun node nodeBelow =>
        unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
          (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow)
      (fun node nodeAbove =>
        unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
          (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove)
      embedding cover
      (fun index indexLt =>
        processSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
          (natListGetAt capState.openWires index) (getAt_mem_of_lt capState.openWires index indexLt))
      rankCapLt
  -- (LHS) The cap-alone partner of the survivor is `bottomCount + rankCap`.
  have capPartnerEq :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner survivor
        = bottomCount + rankCap := by
    show natListGetAt (extractDiagram bottomCount capState).partner survivor = bottomCount + rankCap
    rw [extractDiagram_partner_getAt bottomCount capState survivor
      (Nat.lt_of_lt_of_le survivorBelow (Nat.le_add_right bottomCount capState.openWires.length))]
    exact partnerIndexOf_survivor_eq_rank capState.links bottomCount capState
      survivorBelow survivorUnlinkedMid capDistinct capAllUnlinked rankCapLt survivorAtRankCap
  -- Compose: capRestrict-partner = bc + survivorTopRank V (bc + phi rankCap) = bc + rankCap = cap-alone partner.
  rw [capPartnerEq, wholePartnerEq, rankReadoff]

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-side restriction `capRestrict` (F) is DEFINED; the two copied fields and the
survivor-bottom partner keystone AGREE with the cap block's own diagram; the remaining three ext obligations are
the standing residual #2185.**

Landed here, all zero-axiom:

  * `capRestrict` / `survivorTopTotal` / `nthSurvivorTop` — the topological F-restriction on `DiagramType`, total
    and computing, reading ONLY the whole valley's diagram.

  * `capRestrict_bottomCount_eq` / `capRestrict_loops_eq` — the two COPIED fields agree with the cap block's own
    diagram (`bottomCount` by `rfl`; `loops` via `matchingOf_loops_split`, the shipped loop leg).

  * `capRestrict_partner_survivorBottom` — the SURVIVOR-BOTTOM partner-field agreement (the arithmetic keystone):
    the cap-alone partner of a survivor bottom port equals `capRestrict`'s reconstructed value
    `bottomCount + survivorTopRank V (V.partner[survivor])`.  A clean `.trans` of the shipped endpoints
    (cup-shift re-ranking, rank read-off, cap-alone read-off) routed through ONE cup embedding `phi`, so the
    partner value and its rank read-off share the embedding and compose with no coupling residue.

What this marker does NOT close (the standing valley-descent residual #2185, the full `DiagramType.ext`):

  * the `topCount` count-total identity `midWidth = survivorTopTotal V` — a "count of all cup-embedding images =
    domain size" corollary of the shipped surjectivity, not yet packaged as a list-count lemma;

  * the cap-CONSUMED bottom partner-list agreement — a `findPartnerScan` front-confinement lift of the shipped
    bottom-bottom connectivity frame (`processSpine_isSameComponent_bottom_ofAllCupArity`) via
    `findPartnerScan_congr_ofTestAgree`, confining the whole-range scan to the bottom prefix;

  * the cap-TOP port agreement — `nthSurvivorTop`'s correctness (it returns a genuine survivor-top of the
    requested rank) plus a `matchingOf` partner-INVOLUTION (that `V.partner` of a survivor-top is the survivor
    bottom), which does NOT exist in the corpus and is the hardest remaining new lemma.

So `valleyAppend_split` (the `congrArg capRestrict/cupRestrict` over a whole-valley matching equality) and the
clean whole-valley Piece II (`valleysWithEqualMatching_spineTraceEquiv`) remain gated behind those three.  No
gate flag is flipped.  `= true`. -/
def fxMode_hasCapRestrictSurvivorField : Bool := true

end FX1Poly.Polygraph
