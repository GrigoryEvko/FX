import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine

/-! # SpineValleyWidthTelescope — the Piece-I length-determinacy core (Tier C: the width telescopes)

The clean whole-valley theorem `valleysWithEqualMatching_spineTraceEquiv` consumes two side conditions on top of
the arity/chain data: the cap blocks have equal LENGTH (`capLengthEq`) and the cup blocks have equal LENGTH
(`cupLengthEq`).  These are NOT free — they are the genuinely-new content of the cell-level `CellValleyTraceEquiv`
bridge (recon Tier C): they must be DERIVED from the equal boundary matching (which forces the two mid-widths
equal) plus the two boundaries.  This file ships the two width TELESCOPES that make them derivable, plus the two
length-determinacy corollaries.

  * ★ `pureCapBlock_widthTelescope` — over a boundary-chained pure-cap block, each cap drops the open-wire count
    by exactly `2` (`stepAtom_openWires_tracksBoundary`: `codBoundary + 2 = domBoundary`), so the final width plus
    `2 · len` recovers the entry width: `(processSpine state capBlock).openWires.length + 2 * capBlock.length
    = state.openWires.length`.
  * ★ `pureCupBlock_widthTelescope` — DUAL: each cup RAISES the width by `2`, so
    `(processSpine state cupBlock).openWires.length = state.openWires.length + 2 * cupBlock.length`.
  * ★ `capLength_eq_of_midWidth_eq` — the cap length-determinacy: two cap blocks chained from the SAME bottom
    count whose mid-widths agree have equal length (cancel `2 ·` in the telescope).
  * ★ `cupLength_eq_of_midWidth_eq_of_finalWidth_eq` — the cup length-determinacy, parametric in the two whole
    valleys' FINAL widths agreeing (which the assembly supplies from the shared top boundary `targetPath`).

All four are clean structural inductions / Nat cancellations.  No arc readoff, no reconstruction — pure boundary
arithmetic riding the shipped per-atom tracker.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free Nat cancellation (local; the core `Nat.add_left_cancel` leaks propext) -/

/-- Right-cancellation for Nat addition, structural and propext-free (the `+ 0` base is defeq, the
`+ (n+1)` step is `Nat.succ.inj`). -/
private theorem natAddRightCancelLocal : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | cancelled + 1, _, _, sumsEq => natAddRightCancelLocal cancelled (Nat.succ.inj sumsEq)

/-- Left-cancellation for Nat addition, propext-free via `Nat.add_comm` (itself axiom-free) plus the local
right-cancellation. -/
private theorem natAddLeftCancelLocal {sharedLeft leftSum rightSum : Nat}
    (equalSums : sharedLeft + leftSum = sharedLeft + rightSum) : leftSum = rightSum :=
  natAddRightCancelLocal sharedLeft
    ((Nat.add_comm leftSum sharedLeft).trans (equalSums.trans (Nat.add_comm sharedLeft rightSum)))

/-- The `List.range` accumulator length, structural and propext-free (the core `List.length_range` leaks). -/
private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`, propext-free (local copy; the core lemma leaks). -/
private theorem rangeLengthLocal (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The two width telescopes -/

/-- ★ **Cap-block width telescope.**  A boundary-chained pure-cap block drops the open-wire count by exactly `2`
per cap; additively, the final width plus twice the block length is the entry width.  Structural induction: the
head cap fires at the running boundary (`stepAtom_openWires_tracksBoundary`), leaving `codBoundary = domBoundary −
2 = entryWidth − 2`, and the tail is chained at that new boundary. -/
theorem pureCapBlock_widthTelescope
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (capBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    AllCapArity capBlock →
    (state : WireState) →
    SpineBoundaryChained state.openWires.length capBlock →
    (processSpine state capBlock).openWires.length + 2 * capBlock.length = state.openWires.length
  | [], _, state, _ => by
      dsimp only [processSpine, List.foldl, List.length]
      rw [Nat.mul_zero, Nat.add_zero]
  | atom :: rest, capPure, state, chained => by
      cases capPure with
      | cons capDom capCod restCap =>
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have arity : AtomHasCupOrCapArity atom := Or.inr ⟨capDom, capCod⟩
          have stepTracks : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom arity headFires.symm
          -- Each cap: codBoundary + 2 = domBoundary = entry width.
          have hcod : atom.codBoundaryLength = atom.leftContext.length + atom.rightContext.length := by
            dsimp only [SpineAtom.codBoundaryLength]
            rw [capCod, Nat.add_zero]
          have hdom : atom.domBoundaryLength
              = atom.leftContext.length + atom.rightContext.length + 2 := by
            dsimp only [SpineAtom.domBoundaryLength]
            rw [capDom]
            exact Nat.add_right_comm atom.leftContext.length 2 atom.rightContext.length
          have dropTwo : atom.codBoundaryLength + 2 = state.openWires.length := by
            rw [hcod, ← headFires, hdom]
          have tailChainedAtStep :
              SpineBoundaryChained (stepAtom state atom).openWires.length rest := by
            rw [stepTracks]; exact tailChained
          have ih := pureCapBlock_widthTelescope rest restCap (stepAtom state atom) tailChainedAtStep
          -- `processSpine state (atom :: rest) = processSpine (stepAtom state atom) rest`.
          show (processSpine (stepAtom state atom) rest).openWires.length + 2 * (rest.length + 1)
            = state.openWires.length
          rw [Nat.mul_succ, ← Nat.add_assoc, ih, stepTracks, dropTwo]

/-- ★ **Cup-block width telescope.**  DUAL of the cap telescope: a boundary-chained pure-cup block RAISES the
open-wire count by exactly `2` per cup, so the final width is the entry width plus twice the block length. -/
theorem pureCupBlock_widthTelescope
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    AllCupArity cupBlock →
    (state : WireState) →
    SpineBoundaryChained state.openWires.length cupBlock →
    (processSpine state cupBlock).openWires.length = state.openWires.length + 2 * cupBlock.length
  | [], _, state, _ => by
      dsimp only [processSpine, List.foldl, List.length]
      rw [Nat.mul_zero, Nat.add_zero]
  | atom :: rest, cupPure, state, chained => by
      cases cupPure with
      | cons cupDom cupCod restCup =>
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have arity : AtomHasCupOrCapArity atom := Or.inl ⟨cupDom, cupCod⟩
          have stepTracks : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom arity headFires.symm
          -- Each cup: codBoundary = domBoundary + 2 = entry width + 2.
          have hcod : atom.codBoundaryLength
              = atom.leftContext.length + atom.rightContext.length + 2 := by
            dsimp only [SpineAtom.codBoundaryLength]
            rw [cupCod]
            exact Nat.add_right_comm atom.leftContext.length 2 atom.rightContext.length
          have hdom : atom.domBoundaryLength = atom.leftContext.length + atom.rightContext.length := by
            dsimp only [SpineAtom.domBoundaryLength]
            rw [cupDom, Nat.add_zero]
          have raiseTwo : atom.codBoundaryLength = state.openWires.length + 2 := by
            rw [hcod, ← headFires, hdom]
          have tailChainedAtStep :
              SpineBoundaryChained (stepAtom state atom).openWires.length rest := by
            rw [stepTracks]; exact tailChained
          have ih := pureCupBlock_widthTelescope rest restCup (stepAtom state atom) tailChainedAtStep
          show (processSpine (stepAtom state atom) rest).openWires.length
            = state.openWires.length + 2 * (rest.length + 1)
          rw [ih, stepTracks, raiseTwo, Nat.mul_succ, Nat.add_comm (2 * rest.length) 2,
            ← Nat.add_assoc]

/-! ## The length-determinacy corollaries -/

/-- The from-scratch seed for a bottom count: `bottomCount` open wires `0 … bottomCount-1`, no links. -/
private def bottomSeed (bottomCount : Nat) : WireState :=
  ⟨List.range bottomCount, [], bottomCount, 0⟩

/-- The seed's open-wire count is the bottom count. -/
private theorem bottomSeed_openWiresLength (bottomCount : Nat) :
    (bottomSeed bottomCount).openWires.length = bottomCount := by
  dsimp only [bottomSeed]
  exact rangeLengthLocal bottomCount

/-- ★ **Cap length-determinacy.**  Two pure-cap blocks chained from the same bottom count whose mid-widths (the
open-wire counts after processing) agree have equal length: the cap telescope gives `midWidth + 2 · capLength =
bottomCount` for each, so equal mid-widths cancel to equal lengths. -/
theorem capLength_eq_of_midWidth_eq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (capBlockFirst capBlockSecond :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (capChainedFirst : SpineBoundaryChained bottomCount capBlockFirst)
    (capChainedSecond : SpineBoundaryChained bottomCount capBlockSecond)
    (midEq : (processSpine (bottomSeed bottomCount) capBlockFirst).openWires.length
      = (processSpine (bottomSeed bottomCount) capBlockSecond).openWires.length) :
    capBlockFirst.length = capBlockSecond.length := by
  have seedLen := bottomSeed_openWiresLength bottomCount
  have telescopeFirst :
      (processSpine (bottomSeed bottomCount) capBlockFirst).openWires.length
        + 2 * capBlockFirst.length = bottomCount := by
    have chained : SpineBoundaryChained (bottomSeed bottomCount).openWires.length capBlockFirst := by
      rw [seedLen]; exact capChainedFirst
    have telescope :=
      pureCapBlock_widthTelescope capBlockFirst capPureFirst (bottomSeed bottomCount) chained
    rw [seedLen] at telescope
    exact telescope
  have telescopeSecond :
      (processSpine (bottomSeed bottomCount) capBlockSecond).openWires.length
        + 2 * capBlockSecond.length = bottomCount := by
    have chained : SpineBoundaryChained (bottomSeed bottomCount).openWires.length capBlockSecond := by
      rw [seedLen]; exact capChainedSecond
    have telescope :=
      pureCapBlock_widthTelescope capBlockSecond capPureSecond (bottomSeed bottomCount) chained
    rw [seedLen] at telescope
    exact telescope
  -- `midB + 2·lenA = bc = midB + 2·lenB` (after `midEq`), so `2·lenA = 2·lenB`, hence `lenA = lenB`.
  have doubled : 2 * capBlockFirst.length = 2 * capBlockSecond.length := by
    rw [midEq] at telescopeFirst
    refine natAddLeftCancelLocal
      (sharedLeft := (processSpine (bottomSeed bottomCount) capBlockSecond).openWires.length) ?_
    rw [telescopeFirst, telescopeSecond]
  exact Nat.eq_of_mul_eq_mul_left (by decide) doubled

/-- ★ **Cup length-determinacy.**  Two pure-cup blocks chained from their respective mid-widths, with equal
mid-widths AND equal whole-valley FINAL widths, have equal length: the cup telescope gives `finalWidth =
midWidth + 2 · cupLength` for each, so equal mid- and final-widths cancel to equal lengths.  The final-width
equality is supplied by the assembly from the shared top boundary. -/
theorem cupLength_eq_of_midWidth_eq_of_finalWidth_eq
    {overallSource overallTarget : adjunctionGraph.Mode}
    (midStateFirst midStateSecond : WireState)
    (cupBlockFirst cupBlockSecond :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (cupChainedFirst : SpineBoundaryChained midStateFirst.openWires.length cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained midStateSecond.openWires.length cupBlockSecond)
    (midEq : midStateFirst.openWires.length = midStateSecond.openWires.length)
    (finalEq : (processSpine midStateFirst cupBlockFirst).openWires.length
      = (processSpine midStateSecond cupBlockSecond).openWires.length) :
    cupBlockFirst.length = cupBlockSecond.length := by
  have telescopeFirst :
      (processSpine midStateFirst cupBlockFirst).openWires.length
        = midStateFirst.openWires.length + 2 * cupBlockFirst.length :=
    pureCupBlock_widthTelescope cupBlockFirst cupPureFirst midStateFirst cupChainedFirst
  have telescopeSecond :
      (processSpine midStateSecond cupBlockSecond).openWires.length
        = midStateSecond.openWires.length + 2 * cupBlockSecond.length :=
    pureCupBlock_widthTelescope cupBlockSecond cupPureSecond midStateSecond cupChainedSecond
  -- `mid + 2·lenA = finalA = finalB = mid + 2·lenB` (after `midEq`), so `2·lenA = 2·lenB`.
  have doubled : 2 * cupBlockFirst.length = 2 * cupBlockSecond.length := by
    refine natAddLeftCancelLocal (sharedLeft := midStateSecond.openWires.length) ?_
    rw [← midEq, ← telescopeFirst, finalEq, telescopeSecond, midEq]
  exact Nat.eq_of_mul_eq_mul_left (by decide) doubled

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the Piece-I length-determinacy core (Tier C) is SHIPPED, zero-axiom.**  The two width
telescopes (`pureCapBlock_widthTelescope` / `pureCupBlock_widthTelescope`) turn a boundary-chained pure-cap /
pure-cup block into the exact additive width shift (`∓ 2 · length`), riding the shipped per-atom boundary tracker
`stepAtom_openWires_tracksBoundary`.  The two determinacy corollaries
(`capLength_eq_of_midWidth_eq`, `cupLength_eq_of_midWidth_eq_of_finalWidth_eq`) cancel the telescopes to force
`capLengthEq` / `cupLengthEq` from equal mid-widths (and, for cups, equal whole-valley final widths).

  What this marker does NOT itself close: obtaining the mid-width equality from equal boundary matching (rides the
  shipped `survivorTopTotal_eq_midWidth` + `congrArg survivorTopTotal`, needs `0 < bottomCount`), the final-width
  equality (from the shared top boundary), the suffix-chain restriction, and the positivity dispatch for
  degenerate valleys — the remaining rungs of the cell-level `CellValleyTraceEquiv` bridge.  No gate flag is
  flipped.  `= true`. -/
def fxMode_hasSpineValleyWidthTelescope : Bool := true

end FX1Poly.Polygraph
