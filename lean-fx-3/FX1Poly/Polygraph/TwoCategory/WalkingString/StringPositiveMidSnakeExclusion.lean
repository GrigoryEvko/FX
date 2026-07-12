import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidCupSortResidual
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit

/-! # WalkingString/StringPositiveMidSnakeExclusion — the POSITIVE-mid snake exclusion + cup-end split
(FC-3 r43 P2a, the positive-mid LOCATE foundation)

The width-`0` LOCATE recursion (`stringMatchingLocateAux`, `StringWidthZeroPureCupSort`) rests on two
readoff facts about `matchingOfSpineList 0`: two forward chords cannot sit at adjacent windows
(`matchingForwardChordsNotAdjacent`, the snake refutation that rules out the degenerate location) and a
trailing cup grows the processed open-wire count by exactly two (`matchingOpenWiresCupEndSplit`).  The
positive-mid pure-cup determinacy brick `StringPositiveMidPureCupDeterminacy`
(`StringPositiveMidCupSortResidual`) drives its LOCATE off `matchingOfSpineList midWidth` with
`0 < midWidth`, so it needs both facts at the arbitrary `midWidth` bottom boundary — the through-strand
survivor count.  This file ships the two positive-mid siblings.

Both are OFFSET ports (`0 ⤳ midWidth`), NOT genuine re-rankings:

  * ★ `stringMatchingForwardChordsNotAdjacent_mid` — a forward chord at window `windowLow` and another at
    the NEXT window `windowLow + 1` would share the endpoint `midWidth + windowLow + 1`, impossible in the
    involutive boundary matching: the involution sends the shared endpoint back, not forward.  Where the
    width-`0` sibling rides the width-`0` involution `matchingOfSpineListZero_partner_isInvolution` (no
    positivity), this rides the SHIPPED positive-bottom-boundary involution `stringMatchingOf_partner_isInvolution`
    (`StringMatchingPartnerInvolution`), which consumes exactly the brick's `0 < midWidth` witness — the
    survivor strand that makes the perfect matching involutive.  The `SpineHasCupCapAtoms` premise the
    involution needs is delivered from `AllCupArity` by the shipped `spineHasCupCapAtoms_ofAllCupArity`.

  * ★ `stringMatchingOpenWiresCupEndSplit_mid` — folding a trailing cup onto a pure-cup spine grows the
    processed open-wire count by exactly two (the cup's two fresh legs), at the `midWidth` seed.  Verbatim
    token-swap of `matchingOpenWiresCupEndSplit` (`⟨List.range 0, [], 0, 0⟩ ⤳ ⟨List.range midWidth, [],
    midWidth, 0⟩`); the split is seed-agnostic (`stepAtom_ofCupArity` + `natListInsertAt_length`).

Colour-blind throughout: both read only cup arities + boundary indices, never `F`/`G`/`H`.

Raw Lean 4 + Init; no `omega` / `simp`-AC / `WellFounded.fix`.  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin.

What this does NOT close (no gate flag flips): the positive-mid LOCATE
(`stringMatchingLocateAuxMid`), the chord-shift descents (`stringMatchingChordShift_below/above_mid`), the
drop-injectivity (`stringDropLastCup_matching_injective_mid`), and the word-threaded sort assembly that
inhabits `StringPositiveMidPureCupDeterminacy`.  So the masters
`fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
`fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`, and the brick STAYS `def`-open.
The exact next rung is named in the honesty marker. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two-adjacent-forward-chords exclusion at positive mid-width (rides the positive involution) -/

/-- ★ **Two forward chords cannot be adjacent at positive mid-width (positivity USED).**  A forward chord
`(midWidth + windowLow, +1)` and another at the NEXT window `(midWidth + windowLow + 1, +1)` share the
endpoint `midWidth + windowLow + 1`, impossible in the involutive matching: the involution sends
`midWidth + windowLow + 1` back to `midWidth + windowLow`, not forward to `midWidth + windowLow + 2`.  Rules
out the degenerate snake position in both descent directions of the positive-mid location induction.  Rides
the shipped positive-bottom-boundary involution `stringMatchingOf_partner_isInvolution`, consuming the
brick's `0 < midWidth` survivor witness; the `SpineHasCupCapAtoms` premise comes from `AllCupArity` via
`spineHasCupCapAtoms_ofAllCupArity`.  The positive-mid analogue of `matchingForwardChordsNotAdjacent`. -/
theorem stringMatchingForwardChordsNotAdjacent_mid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat) (midPos : 0 < midWidth)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained midWidth spine)
    (pureCup : AllCupArity spine)
    (windowLow : Nat)
    (lowInRange : midWidth + windowLow < midWidth + (matchingOfSpineList midWidth spine).topCount)
    (chordLow : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + windowLow)
      = midWidth + windowLow + 1)
    (chordHigh : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + (windowLow + 1))
      = midWidth + (windowLow + 1) + 1) : False := by
  have notFixed : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + windowLow)
      ≠ midWidth + windowLow := by
    rw [chordLow]; exact Nat.ne_of_gt (Nat.lt_succ_self (midWidth + windowLow))
  have inv := stringMatchingOf_partner_isInvolution midWidth midPos spine
    (spineHasCupCapAtoms_ofAllCupArity spine pureCup) chained (midWidth + windowLow) lowInRange notFixed
  rw [chordLow, Nat.add_assoc midWidth windowLow 1, chordHigh] at inv
  have twoZero : midWidth + windowLow + 2 = midWidth + windowLow := inv
  exact absurd twoZero (Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))

/-! ## The cup-end open-wire split at positive mid-width (seed-agnostic OFFSET) -/

/-- ★ **Folding a trailing cup onto a pure-cup spine grows the processed open-wire count by exactly two, at
the `midWidth` seed** (the cup's two fresh legs).  Verbatim token-swap of `matchingOpenWiresCupEndSplit`
(`⟨List.range 0, …⟩ ⤳ ⟨List.range midWidth, …⟩`); the split reads only the cup's arity through
`stepAtom_ofCupArity` and the insert length `natListInsertAt_length`, both seed-agnostic. -/
theorem stringMatchingOpenWiresCupEndSplit_mid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ (prefixAtoms ++ [lastCup])).openWires.length
      = (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2 := by
  obtain ⟨lastDom, lastCod⟩ := allCupArity_lastCup_arity prefixAtoms lastCup pureCup
  rw [processSpine_append prefixAtoms [lastCup] ⟨List.range midWidth, [], midWidth, 0⟩]
  show (stepAtom (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup).openWires.length
    = (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2
  rw [stepAtom_ofCupArity (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup
    lastDom lastCod]
  exact natListInsertAt_length (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires
    lastCup.leftContext.length
    [(processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh,
      (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh + 1]

/-! ## Concrete truth-probe (anti-vacuity) on the shipped mid-2 fixture -/

/-- ★ **The cup-end split FIRES on the shipped mid-2 cup fixture.**  Folding the shipped window-`0` cup
`stringPositiveMidCupAtZeroOverGH` (`StringPositiveMidCupSortResidual`, the disjoint double-cup's first cup
over the two `G·H` survivors, `midWidth = 2`) onto the empty prefix grows the processed open-wire count by
exactly two — a machine-checked non-vacuous witness that `stringMatchingOpenWiresCupEndSplit_mid` runs on a
genuine POSITIVE-mid-width (`midWidth = 2 > 0`) pure-cup atom, not vacuously. -/
theorem stringPositiveMidCupEndSplit_firesOnMidTwoCup :
    (processSpine ⟨List.range 2, [], 2, 0⟩ [stringPositiveMidCupAtZeroOverGH]).openWires.length
      = (processSpine ⟨List.range 2, [], 2, 0⟩
          ([] : List (SpineAtom adjointTripleModeSignature
            AdjointTripleMode.tip AdjointTripleMode.tip))).openWires.length + 2 :=
  stringMatchingOpenWiresCupEndSplit_mid 2 [] stringPositiveMidCupAtZeroOverGH
    (AllCupArity.cons rfl rfl AllCupArity.nil)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-mid snake exclusion + cup-end split (FC-3 r43 P2a).**
`stringMatchingForwardChordsNotAdjacent_mid` rules out the two adjacent-forward-chord snake position of the
positive-mid location induction, riding the SHIPPED positive-bottom-boundary involution
`stringMatchingOf_partner_isInvolution` (which consumes the brick's `0 < midWidth` survivor witness — the
one place positivity is genuinely used); `stringMatchingOpenWiresCupEndSplit_mid` gives the cup-end
open-wire count at the `midWidth` seed.  Both are OFFSET ports (`0 ⤳ midWidth`), colour-blind, fired on the
shipped mid-`2` cup fixture (`stringPositiveMidCupEndSplit_firesOnMidTwoCup`).

  What this marker does NOT close (no gate flag flips): the positive-mid LOCATE and its enabling chord-shift
  descents.  The EXACT NEXT RUNG is `stringMatchingLastCup_isShortChord_mid` — the positive-mid last-cup
  short-chord readoff `natListGetAt (matchingOfSpineList midWidth (prefix ++ [lastCup])).partner
  (midWidth + lastCup.leftContext.length) = midWidth + lastCup.leftContext.length + 1`, routed through the
  arc-carrier short chord `pureCupSpine_lastCup_isShortChord` (general `bottomCount`, positivity) and the
  signature-generic `arcDiagram_eq_matching` bridge (the same route `stringMatchingOf_partner_isInvolution`
  takes) — followed by the chord-shift descents `stringMatchingChordShift_below/above_mid` (OFFSET via the
  bottomCount-generic splice `diagramPartner_stepCup midWidth`) and the fueled LOCATE
  `stringMatchingLocateAuxMid`.  So `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY
  `false`, and `StringPositiveMidPureCupDeterminacy` stays `def`-open.  `= true`. -/
def fxString_hasPositiveMidSnakeExclusion : Bool := true

end FX1Poly.Polygraph
