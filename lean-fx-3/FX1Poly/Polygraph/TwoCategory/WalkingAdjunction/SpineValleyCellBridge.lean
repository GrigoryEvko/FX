import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyTopCountTotal
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyBlockSplit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyChainRestrict
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthTelescope
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence

/-! # SpineValleyCellBridge — the cell-level Piece-II lift (positive branch): equal matching ⇒ trace-equivalent
valley spines (Track B, Brick 3 / Rungs 1+2)

The spine-level whole-valley theorem `valleysWithEqualMatching_spineTraceEquiv` (`ValleyCupAssembly`) is
UNCONDITIONAL, but it consumes the valley already presented as `capBlock ++ cupBlock` together with the two
block-LENGTH equalities `capLengthEq` / `cupLengthEq` and the two positivity facts.  The cell-level bridge
`CellValleyTraceEquiv` (`SpineValleyCellDriver`) instead takes two whole VALLEY cells with equal boundary
`matchingOf` and must PRODUCE the `SpineTraceEquiv` of their raw spines.  This file lands the lift on the
non-degenerate branch — the two genuinely-new wiring rungs the width-telescope honesty marker names, both
zero-axiom:

  * ★ **Rung 1 — `midEq` (mid-region width equality).**  The two cap prefixes' open-wire counts (mid-widths)
    agree: each equals `survivorTopTotal` of the common whole-valley diagram (`survivorTopTotal_eq_midWidth`,
    needs `0 < sourcePath.length`), so `congrArg survivorTopTotal` over the matching equality collapses them.
    This feeds `capLength_eq_of_midWidth_eq` and the mid alignment inside the assembly.

  * ★ **Rung 2 — `finalEq` (terminal-width agreement), COLLAPSED.**  The recon anticipated an unshipped
    `processSpine` terminal-width lemma (final open-wire count `= targetPath.length`).  It is UNNECESSARY: the
    final open-wire width of a valley IS the `topCount` field of its `matchingOf` diagram
    (`extractDiagram … |>.topCount = state.openWires.length`, definitionally), so `finalEq` falls straight out of
    `congrArg DiagramType.topCount` on the matching-equality hypothesis — no terminal-boundary induction, no
    Joyal–Street reconstruction needed.  This feeds `cupLength_eq_of_midWidth_eq_of_finalWidth_eq`.

  * ★ **`cellValleyTraceEquiv_ofPositive`** — the positive-branch cell bridge: two valley cells with equal
    `matchingOf`, positive source width, and positive mid-width (through-strand count
    `survivorTopTotal (matchingOf valleyA)`) are `SpineTraceEquiv`.  Block-splits both spines
    (`spineValley_blockSplit`), restricts the whole chain to the cup suffix
    (`spineBoundaryChained_cupSuffix_ofCapPrefix`), derives `capLengthEq` / `cupLengthEq` from Rungs 1+2 via the
    two width-telescope determinacy corollaries, and invokes the shipped
    `valleysWithEqualMatching_spineTraceEquiv`.

## What this file does NOT close — the Tier-D degenerate residual

The FULL `CellValleyTraceEquiv` also quantifies over the two degenerate valleys the positive branch misses:
`sourcePath.length = 0` (empty source ⇒ empty cap block ⇒ pure cups from an empty seed) and `midWidth = 0`
(the cap block consumes every bottom wire ⇒ the cup blocks run from a width-0 mid-state — closed cup/cap loops).
BOTH reduce to the SAME single unshipped brick: `pureCupSpine_sort` at `bottomCount = 0` (carried in
`ArcCupSortComplete`'s honesty marker as the explicit `0 < bottomCount`, since its transposition atoms need a
positive seed), together with `arcDiagram_eq_matching` at width 0.  That width-0 pure-cup determinacy is a
genuine separate brick, not a wiring rung; it is NOT attempted here.  No gate flag is flipped.

Raw Lean 4 + Init; pure equational assembly over the shipped telescopes / determinacy corollaries, no `omega` /
`simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free `List.range` length (local; the core `List.length_range` leaks propext) -/

/-- The `List.range` accumulator length, structural and propext-free. -/
private theorem rangeLoopLengthBridge : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthBridge count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`, propext-free. -/
private theorem rangeLengthBridge (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthBridge count []]
  exact Nat.add_zero count

/-! ## The positive-branch cell bridge -/

/-- ★ **The positive-branch cell-level Piece-II lift.**  Two valley cells `valleyA`, `valleyB` (same source /
target boundary) with EQUAL boundary `matchingOf`, POSITIVE source width (`0 < sourcePath.length`), and POSITIVE
mid-width (`0 < survivorTopTotal (matchingOf valleyA)`, the through-strand count) have trace-equivalent spines.

The proof block-splits both spines into `capBlock ++ cupBlock`, restricts the whole boundary chain to the cup
suffix, then supplies the two block-length equalities the shipped whole-valley theorem needs — `capLengthEq` from
Rung 1 (`midEq`), `cupLengthEq` from Rungs 1+2 (`midEq` + `finalEq`) — and closes with
`valleysWithEqualMatching_spineTraceEquiv`.  Rung 2's `finalEq` is the `topCount` collapse: the final open-wire
width is the diagram's `topCount`, so equal matchings give it by `congrArg`. -/
theorem cellValleyTraceEquiv_ofPositive
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (isValleyA : isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true)
    (isValleyB : isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true)
    (matchingEq : matchingOf valleyA = matchingOf valleyB)
    (bottomPositive : 0 < sourcePath.length)
    (midPositiveHyp : 0 < survivorTopTotal (matchingOf valleyA)) :
    SpineTraceEquiv adjunctionModeSignature valleyA.spine valleyB.spine := by
  -- Block-split both valley spines into cap-prefix ++ cup-suffix.
  obtain ⟨capA, cupA, splitA, capPureA, cupPureA⟩ := spineValley_blockSplit valleyA.spine isValleyA
  obtain ⟨capB, cupB, splitB, capPureB, cupPureB⟩ := spineValley_blockSplit valleyB.spine isValleyB
  -- The two whole valleys are boundary-chained at the source width.
  have wholeChainedA : SpineBoundaryChained sourcePath.length (capA ++ cupA) := by
    rw [← splitA]; exact valleyA.spineBoundaryChained_spine
  have wholeChainedB : SpineBoundaryChained sourcePath.length (capB ++ cupB) := by
    rw [← splitB]; exact valleyB.spineBoundaryChained_spine
  -- The cup suffixes are boundary-chained at the mid-width (restrict the whole chain over the cap prefix).
  have seedWholeA : SpineBoundaryChained
      (⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ : WireState).openWires.length (capA ++ cupA) := by
    show SpineBoundaryChained (List.range sourcePath.length).length (capA ++ cupA)
    rw [rangeLengthBridge]; exact wholeChainedA
  have seedWholeB : SpineBoundaryChained
      (⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ : WireState).openWires.length (capB ++ cupB) := by
    show SpineBoundaryChained (List.range sourcePath.length).length (capB ++ cupB)
    rw [rangeLengthBridge]; exact wholeChainedB
  have cupChainedA : SpineBoundaryChained
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA).openWires.length cupA :=
    spineBoundaryChained_cupSuffix_ofCapPrefix capA capPureA cupA
      ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ seedWholeA
  have cupChainedB : SpineBoundaryChained
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB).openWires.length cupB :=
    spineBoundaryChained_cupSuffix_ofCapPrefix capB capPureB cupB
      ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ seedWholeB
  -- The cap prefixes are boundary-chained (whole chain restricts to the prefix).
  have capChainedA : SpineBoundaryChained sourcePath.length capA :=
    spineBoundaryChained_prefix_ofAppend capA cupA sourcePath.length wholeChainedA
  have capChainedB : SpineBoundaryChained sourcePath.length capB :=
    spineBoundaryChained_prefix_ofAppend capB cupB sourcePath.length wholeChainedB
  -- Re-read the matching hypothesis at the spine level (matchingOf = matchingOfSpineList sourceLen · spine).
  have wholeEqA : matchingOf valleyA = matchingOfSpineList sourcePath.length (capA ++ cupA) := by
    show matchingOfSpineList sourcePath.length valleyA.spine
      = matchingOfSpineList sourcePath.length (capA ++ cupA)
    rw [splitA]
  have wholeEqB : matchingOf valleyB = matchingOfSpineList sourcePath.length (capB ++ cupB) := by
    show matchingOfSpineList sourcePath.length valleyB.spine
      = matchingOfSpineList sourcePath.length (capB ++ cupB)
    rw [splitB]
  have wholeEq : matchingOfSpineList sourcePath.length (capA ++ cupA)
      = matchingOfSpineList sourcePath.length (capB ++ cupB) :=
    wholeEqA.symm.trans (matchingEq.trans wholeEqB)
  -- ★ Rung 1 — the two mid-widths agree: both equal `survivorTopTotal` of the (equal) whole diagram.
  have midEq :
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA).openWires.length
        = (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB).openWires.length := by
    rw [← survivorTopTotal_eq_midWidth sourcePath.length bottomPositive capA cupA capPureA cupPureA cupChainedA,
      ← survivorTopTotal_eq_midWidth sourcePath.length bottomPositive capB cupB capPureB cupPureB cupChainedB,
      wholeEq]
  -- Mid-positivity for the first valley (rides the through-strand hypothesis through Rung 1's lemma).
  have midPositive : 0 <
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA).openWires.length := by
    rw [← survivorTopTotal_eq_midWidth sourcePath.length bottomPositive capA cupA capPureA cupPureA cupChainedA,
      ← wholeEqA]
    exact midPositiveHyp
  -- ★ Rung 2 — the two whole-valley final open-wire widths agree: each is the diagram's `topCount`, so the
  -- matching equality gives it by `congrArg`.  No terminal-width induction.
  have finalEq :
      (processSpine (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA) cupA).openWires.length
        = (processSpine (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB) cupB).openWires.length := by
    rw [← processSpine_append capA cupA ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩,
      ← processSpine_append capB cupB ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩]
    show (matchingOfSpineList sourcePath.length (capA ++ cupA)).topCount
      = (matchingOfSpineList sourcePath.length (capB ++ cupB)).topCount
    rw [← wholeEqA, ← wholeEqB, matchingEq]
  -- The two block-length equalities from the width telescopes.
  have capLengthEq : capA.length = capB.length :=
    capLength_eq_of_midWidth_eq sourcePath.length capA capB capPureA capPureB capChainedA capChainedB midEq
  have cupLengthEq : cupA.length = cupB.length :=
    cupLength_eq_of_midWidth_eq_of_finalWidth_eq
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capA)
      (processSpine ⟨List.range sourcePath.length, [], sourcePath.length, 0⟩ capB)
      cupA cupB cupPureA cupPureB cupChainedA cupChainedB midEq finalEq
  -- Close with the shipped whole-valley theorem, then transport back through the block splits.
  rw [splitA, splitB]
  exact valleysWithEqualMatching_spineTraceEquiv sourcePath.length bottomPositive
    capA capB cupA cupB capPureA capPureB cupPureA cupPureB
    cupChainedA cupChainedB wholeChainedA wholeChainedB midPositive capLengthEq cupLengthEq wholeEq

/-! ## Tier-D structural fact — an empty source boundary forces an empty cap block -/

/-- ★ **Empty source ⇒ empty cap block** (the Tier-D case-(a) first move).  A pure-cap block boundary-chained at
width `0` is empty: a cap consumes two bottom wires, so its source boundary width is
`leftContext + 2 + rightContext ≥ 2 > 0`, which cannot fire at boundary `0`.  Hence when `sourcePath.length = 0`
the whole valley is its cup suffix (pure cups from the empty seed) — the degenerate branch the positive bridge
punts to the width-0 pure-cup determinacy. -/
theorem capBlockEmpty_ofSourceZero
    {overallSource overallTarget : adjunctionGraph.Mode}
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (chained : SpineBoundaryChained 0 capBlock) :
    capBlock = [] := by
  cases capBlock with
  | nil => rfl
  | cons headAtom rest =>
      cases capPure with
      | cons hasCapDomArity _hasCapCodArity _restAllCap =>
          obtain ⟨headFires, _tailChained⟩ := spineBoundaryChained_tail chained
          have contra : headAtom.leftContext.length + headAtom.rightContext.length + 2 = 0 := by
            have domForm : headAtom.domBoundaryLength
                = headAtom.leftContext.length + headAtom.rightContext.length + 2 := by
              dsimp only [SpineAtom.domBoundaryLength]
              rw [hasCapDomArity,
                Nat.add_right_comm headAtom.leftContext.length 2 headAtom.rightContext.length]
            rw [← domForm]; exact headFires
          exact Nat.noConfusion contra

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-branch cell-level Piece-II lift is SHIPPED, zero-axiom.**
`cellValleyTraceEquiv_ofPositive` lifts the spine-level `valleysWithEqualMatching_spineTraceEquiv` to two whole
VALLEY cells: equal boundary `matchingOf` + positive source width + positive mid-width (through-strand count)
gives `SpineTraceEquiv` of the raw spines.  The two genuinely-new wiring rungs are landed:
Rung 1 (`midEq`) via `survivorTopTotal_eq_midWidth` + `congrArg survivorTopTotal`, and Rung 2 (`finalEq`) via the
`topCount` collapse — the anticipated unshipped `processSpine` terminal-width lemma is UNNECESSARY, since the final
open-wire width is definitionally the matching diagram's `topCount`.

  What this marker does NOT close — the Tier-D degenerate residual: the two valleys the positive branch misses
  (`sourcePath.length = 0`, empty cap block, pure cups from an empty seed; and `midWidth = 0`, all-consuming cap,
  cup blocks from a width-0 mid-state) both reduce to `pureCupSpine_sort` at `bottomCount = 0` +
  `arcDiagram_eq_matching` at width 0 — a genuine unshipped brick (`ArcCupSortComplete` carries the `0 <
  bottomCount` as its explicit residual).  So the FULL `CellValleyTraceEquiv` (and hence Brick 4 R3) stays gated on
  that width-0 pure-cup determinacy.  No gate flag is flipped.  `= true`. -/
def fxMode_hasSpineValleyCellBridge : Bool := true

end FX1Poly.Polygraph
