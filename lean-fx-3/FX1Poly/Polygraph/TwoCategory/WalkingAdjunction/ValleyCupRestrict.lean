import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyTopCountTotal
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryReads

/-! # ValleyCupRestrict — the cup-side restriction functor `cupRestrict` (G) on `DiagramType` (Piece II tail)

The valley-append split reconstructs the CUP block's own diagram from the WHOLE valley's diagram.  This file
defines the reconstruction FUNCTION `cupRestrict : DiagramType → DiagramType` — the topological "G-restriction"
that keeps the cup arcs and DROPS the bottom-bottom cap arcs — and lands the field agreements that are closable
WITHOUT the two-run seed-relabeling bridge (the genuine cup-specific hard node; see the honesty marker).

## The reconstruction function (the dual of `capRestrict`)

For a whole-valley diagram `V = matchingOf bc (capBlock ++ cupBlock)`, `cupRestrict V` reads off the cup block's
own diagram using ONLY `V`.  Write `midWidth = survivorTopTotal V` (the number of through-strands = the cap block's
own open-wire count) and `bc = V.bottomCount`:

  * `bottomCount` — `midWidth` (the cup block's own bottom count, the mid-boundary width; the DUAL of `capRestrict`'s
    `topCount := midWidth`).
  * `topCount` — copied (`V.topCount`; both runs share the same top boundary, so the cup-alone final open-wire
    count equals the whole valley's).
  * `loops` — `0` (a from-scratch pure-cup run closes NO loops; the DUAL of `capRestrict` COPYING `V.loops`).
  * `partner` — the re-ranked matching over the `midWidth + V.topCount` cup-boundary ports:
    - a CUP-BOTTOM port `s` (`s < midWidth`, a mid-boundary / survivor position): its cup-alone partner is the
      through-top at V-position `phi s = nthSurvivorTop V s - bc`, re-indexed to `midWidth + phi s`;
    - a CUP-TOP port `midWidth + t` (`t = index - midWidth`) whose V top port `bc + t` is a SURVIVOR-TOP
      (`V.partner[bc + t] < bc`, a through-strand): re-indexed to `survivorTopRank V (bc + t)`;
    - a CUP-TOP port whose V top port `bc + t` is a TOP-TOP CUP ARC (`V.partner[bc + t] ≥ bc`): re-indexed to
      `midWidth + (V.partner[bc + t] - bc)`.

## What this file lands (each closable piece zero-axiom)

  * ★ `cupRestrict` — the reconstruction function, total and computing, reading ONLY the whole valley's diagram.
  * ★ `cupRestrict_loops_eq` / `cupRestrict_bottomCount_eq` / `cupRestrict_topCount_eq` — the three fields that
    close WITHOUT the two-run bridge: `loops` (both `0`), `bottomCount` (`midWidth = survivorTopTotal V`, the
    shipped `survivorTopTotal_eq_midWidth`), and `topCount` (both cup runs start from equal-length open-wire
    states and each cup adds exactly two, `processSpine_openWiresLength_congr_ofAllCupArity`).

## What this file does NOT close (the genuine cup asymmetry — NOT a free dual)

The `partner` field — hence the full `cupRestrict_reconstructs` — is gated on a two-run correspondence with NO
cap-side analogue.  The cap block is the valley's PREFIX: `matchingOf bc capBlock = extractDiagram bc capState`
and `capState` IS the intermediate state of the whole run (`wholeState = processSpine capState cupBlock`), so
every cap partner leg is a SAME-SEED comparison.  The cup block is the valley's SUFFIX: its own matching
`matchingOf midWidth cupBlock` runs from the FROM-SCRATCH seed `⟨range midWidth, [], midWidth, 0⟩` (fresh legs
numbered `midWidth + k`, bottoms `0 … midWidth-1`), whereas its action inside `V` runs from `capState` (fresh legs
numbered `bc + k`, bottoms the scattered survivor values, cap links present).  These are DIFFERENT runs with no
`processSpine_append` prefix relation.  Relating them needs a seed-invariance / value-relabeling bridge
(`bc + k ↔ midWidth + k` on legs, survivor values `↔ 0 … midWidth-1`), which the shipped `componentView_ofFreshRename`
(`MatchingRenameSupport`) supplies the BASE correspondence for but whose fold-composition is itself flagged
un-shipped there.  This is bounded work (rename kit + the shipped cup-window scan-transport), NOT the
machine-refuted covariant-monotone reconstruction — but it is not a free port of `capRestrict`.  No gate flag is
flipped.

Raw Lean 4 + Init; structural / `AllCupArity` recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range plumbing (propext-free copy) -/

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

/-! ## The cup-run open-wire length is initial-length-determined -/

/-- ★ **Two pure-cup runs from equal-length open-wire states end at equal open-wire lengths.**  Each cup splices
exactly two fresh legs (`stepCup_openWiresLength` adds `2`), independent of the state's values / links / counter,
so the open-wire length after a pure-cup block depends ONLY on the initial open-wire length.  By induction on the
`AllCupArity` witness.  This is the length-only slice of the two-run cup correspondence — enough to pin the
`topCount` field WITHOUT the full connectivity bridge (the cup-alone run and the whole valley's cup part start
from equal open-wire lengths `midWidth`, hence end equal). -/
theorem processSpine_openWiresLength_congr_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (stateA stateB : WireState) →
    stateA.openWires.length = stateB.openWires.length →
    (processSpine stateA atoms).openWires.length = (processSpine stateB atoms).openWires.length := by
  induction pureCup with
  | nil => intro _ _ lenEq; exact lenEq
  | cons hasCupDomArity hasCupCodArity _restAllCup restCongr =>
      rename_i headAtom rest
      intro stateA stateB lenEq
      show (processSpine (stepAtom stateA headAtom) rest).openWires.length
        = (processSpine (stepAtom stateB headAtom) rest).openWires.length
      rw [stepAtom_ofCupArity stateA headAtom hasCupDomArity hasCupCodArity,
        stepAtom_ofCupArity stateB headAtom hasCupDomArity hasCupCodArity]
      exact restCongr (stepCup stateA headAtom.leftContext.length)
        (stepCup stateB headAtom.leftContext.length)
        (by rw [stepCup_openWiresLength, stepCup_openWiresLength, lenEq])

/-! ## The cup-side restriction function -/

/-- ★ **The cup-side restriction `cupRestrict` (G).**  Reconstructs the cup block's own `DiagramType` from the
WHOLE valley's diagram, reading ONLY the whole diagram.  The DUAL of `capRestrict`: `bottomCount` is the
survivor-top total (`midWidth`), `topCount` is copied (`V.topCount`), `loops` is `0` (a from-scratch cup run closes
no loops), and the `partner` re-ranks each cup-boundary port per the three cases in the file header (cup-bottom →
the through-top via `nthSurvivorTop`; through-top V port → `survivorTopRank`; cup-arc V port → shift into the
mid-width top block). -/
def cupRestrict (diagram : DiagramType) : DiagramType :=
  let bottomCount := diagram.bottomCount
  let midWidth := survivorTopTotal diagram
  { bottomCount := midWidth,
    topCount := diagram.topCount,
    partner := (List.range (midWidth + diagram.topCount)).map (fun index =>
      if Nat.blt index midWidth then
        midWidth + (nthSurvivorTop diagram index - bottomCount)
      else
        let wholeTop := bottomCount + (index - midWidth)
        let wholePartner := natListGetAt diagram.partner wholeTop
        if Nat.blt wholePartner bottomCount then
          survivorTopRank diagram wholeTop
        else
          midWidth + (wholePartner - bottomCount)),
    loops := 0 }

/-! ## The three field agreements that close WITHOUT the two-run bridge -/

/-- ★ **The `loops` field agrees.**  Both sides are `0`: the cup block, run from the from-scratch seed
`⟨range midWidth, [], midWidth, 0⟩`, closes NO loops (`processSpine_loops_ofAllCupArity`, seed loops `0`), and
`cupRestrict` hard-sets `loops := 0` (the DUAL of `capRestrict` COPYING `V.loops`).  This is the loop leg of the
cup-side restriction — a pure-cup run never records a bubble. -/
theorem cupRestrict_loops_eq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).loops
      = (cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).loops :=
  processSpine_loops_ofAllCupArity cupBlock cupPure
    ⟨List.range (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length, [],
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length, 0⟩

/-- ★ **The `bottomCount` field agrees.**  The cup block's own bottom count is `midWidth`
(`= capState.openWires.length`, the mid-boundary width it runs from), and `cupRestrict`'s reconstructed
`bottomCount` is `survivorTopTotal V`, which the shipped `survivorTopTotal_eq_midWidth` proves is exactly
`midWidth`.  This is the DUAL of `capRestrict`'s `topCount` field — the SAME survivor-top total, read on the
cup side as the bottom count rather than the top count. -/
theorem cupRestrict_bottomCount_eq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock) :
    (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).bottomCount
      = (cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).bottomCount :=
  (survivorTopTotal_eq_midWidth bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained).symm

/-- ★ **The `topCount` field agrees.**  The cup block's own top count is its final open-wire count; the
reconstructed `topCount` is `V.topCount = wholeState.openWires.length`.  Both cup runs — the cup-alone run from
`⟨range midWidth, [], midWidth, 0⟩` and the whole valley's cup part from `capState` — start from open-wire states of
EQUAL length `midWidth` (`rangeLenLocal`), and each cup adds exactly two, so they end at equal open-wire lengths
(`processSpine_openWiresLength_congr_ofAllCupArity`).  This is the length-only slice of the two-run correspondence
— no connectivity bridge needed. -/
theorem cupRestrict_topCount_eq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock).topCount
      = (cupRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).topCount := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount (processSpine capState cupBlock) := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount (processSpine capState cupBlock)
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  show (processSpine ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ cupBlock).openWires.length
      = (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount
  rw [wholeSplit]
  show (processSpine ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ cupBlock).openWires.length
      = (processSpine capState cupBlock).openWires.length
  exact processSpine_openWiresLength_congr_ofAllCupArity cupBlock cupPure
    ⟨List.range capState.openWires.length, [], capState.openWires.length, 0⟩ capState
    (rangeLenLocal capState.openWires.length)

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-side restriction `cupRestrict` (G) is DEFINED; the three fields that need NO
two-run bridge AGREE; the `partner` field is the genuine cup asymmetry (NOT a free dual of `capRestrict`).**

Landed here, all zero-axiom:

  * `cupRestrict` — the topological G-restriction on `DiagramType`, total and computing, reading ONLY the whole
    valley's diagram; the DUAL of `capRestrict` (`bottomCount`/`topCount` swapped, `loops := 0`).

  * `cupRestrict_loops_eq` / `cupRestrict_bottomCount_eq` / `cupRestrict_topCount_eq` — the three fields closable
    WITHOUT the two-run bridge: `loops` (both `0`, cups close no loops), `bottomCount` (`survivorTopTotal V =
    midWidth`, the shipped `survivorTopTotal_eq_midWidth`, DUAL of `capRestrict`'s `topCount`), and `topCount`
    (`processSpine_openWiresLength_congr_ofAllCupArity` — both cup runs start equal-length and each cup adds two).

What this marker does NOT close — the `partner` field, hence `cupRestrict_reconstructs`, `valleyAppend_split`, and
`valleysWithEqualMatching_spineTraceEquiv`: the genuine cup-specific asymmetry with NO cap analogue.  The cup block
is the valley's SUFFIX, so `matchingOf midWidth cupBlock` is a SEPARATE `processSpine` run from a from-scratch seed
`⟨range midWidth, [], midWidth, 0⟩`, whereas `capState` (the cap-alone final state) IS the prefix state of the whole
run.  Relating the two runs needs a seed-invariance / floor-relabeling bridge (`bc + k ↔ midWidth + k` on the fresh
legs, survivor values `↔ 0 … midWidth-1`).  The BASE correspondence `componentView_ofFreshRename`
(`MatchingRenameSupport`) is shipped, and the per-cup scan-transport `findPartnerScan_range_cupWindowSplit`
(`MatchingCupWindowScanSplit`) is shipped, but the fold-composition of the rename across the whole cup block is
itself flagged un-shipped by the `MatchingRenameSupport` marker.  This is BOUNDED work (rename fold + scan
transport), and is NOT the machine-refuted covariant-monotone reconstruction map.  No gate flag is flipped.
`= true`. -/
def fxMode_hasCupRestrictDefAndCopiedFields : Bool := true

end FX1Poly.Polygraph
