import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcPairCapWindow
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcSpineChainAlong

/-! # WalkingString/StringArcCapWindowSeedReadoff — the located-cap read-off substrate (FC-3 r22, B3)

The colour-aware cap read-off (`_ofArcEqual`) takes a `StringArcPairCapWindow` certificate over a boundary-chained
spine and emits the located cap as a `WordBubblesToFront` witness whose moved atom is a cap at exactly the window
position on exactly the seed boundary — the head-identification data.  That emission is the string clone of
`WalkingAdjunction/ArcCapWindowSeedReadoff`'s `bubblesToFront_ofArcPairCapWindow`.

★ HONEST BOUNDARY.  The bubble-PRODUCTION half of that read-off runs the WORD descent master (the string clone of
`arcPairSeated_bubblesThroughPrefix`).  Its arc source lives in `ArcPrefixBubbleDescent`, which imports
`DisjointWindowFactorization` and `ArcBubbleToFront` — both keyed on `adjunctionPath_eq_of_length_eq`
(length-rigidity, FALSE at the adjoint triple).  So the descent master is PHANTOM-LOCKED at the source: a
two-token clone would be clean-building but FALSE-backed.  The genuine port must re-plumb the descent onto the WORD
factorizations threading a `SpineBoundaryWordChained` — a from-scratch ~300-line piece, the round's standing
residual (the next round).

This file ships the colour-BLIND substrate the read-off consumes, machine-checked NOW:

  * `stringArcPairCapWindow_splitSeatBound` — from the located certificate and the length boundary chain, the
    split-state seat window sits at least two below the split-state open-wire count (via the shipped arc-fold chain
    advance `stringSpineBoundaryChained_alongArcSpine`, P3).  This is exactly the `seatBound` the descent master
    consumes to seat the located pair adjacent.

Raw Lean 4 + Init; structural / `Nat` positional only.  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range length plumbing (private copy — the seed files' kits are file-private) -/

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

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The split-state seat bound -/

/-- ★ **The located cap's split-state seat bound.**  From a `StringArcPairCapWindow` certificate over a spine
boundary-chained at `bottomCount`, the split at the located cap has, at the split state (the seed folded through
the prefix), open-wire count at least `toucherAtom.leftContext.length + 2` — the window plus its two consumed
strands fit.  The boundary chain advances to the split state through the shipped arc-fold chain advance
(`stringSpineBoundaryChained_alongArcSpine`), and the split head's entry shape plus its cap dom arity give the
bound.  This is the seat bound the (still-open, phantom-locked) word descent master consumes to seat the located
pair adjacent — the colour-blind substrate of the read-off. -/
theorem stringArcPairCapWindow_splitSeatBound (bottomCount : Nat)
    {sourceMode targetMode : adjointTripleGraph.Mode}
    (secondAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {leftIndex rightIndex : Nat}
    (chainedSecond : SpineBoundaryChained bottomCount secondAtoms)
    (located : StringArcPairCapWindow bottomCount leftIndex rightIndex secondAtoms) :
    ∃ (prefixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
      (toucherAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
      (suffixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)),
      secondAtoms = prefixAtoms ++ toucherAtom :: suffixAtoms
        ∧ toucherAtom.generatorDom.length = 2
        ∧ toucherAtom.generatorCod.length = 0
        ∧ toucherAtom.leftContext.length + 2
            ≤ (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                prefixAtoms).openWires.length := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, _isUntouchedBeforeToucher,
    hasCapDomArity, hasCapCodArity, _doesConsumePair⟩ := located
  rw [doesSplitSpine] at chainedSecond
  have chainedAtSeed : SpineBoundaryChained
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires.length
      (prefixAtoms ++ toucherAtom :: suffixAtoms) := by
    show SpineBoundaryChained (List.range bottomCount).length
      (prefixAtoms ++ toucherAtom :: suffixAtoms)
    rw [rangeLength bottomCount]
    exact chainedSecond
  have chainedAtSplit : SpineBoundaryChained
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).openWires.length
      (toucherAtom :: suffixAtoms) :=
    stringSpineBoundaryChained_alongArcSpine prefixAtoms (toucherAtom :: suffixAtoms)
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) chainedAtSeed
  have splitEntryShape : (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      prefixAtoms).openWires.length
      = toucherAtom.leftContext.length + toucherAtom.generatorDom.length
        + toucherAtom.rightContext.length :=
    (spineBoundaryChained_tail chainedAtSplit).1.symm
  refine ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, hasCapDomArity,
    hasCapCodArity, ?_⟩
  rw [splitEntryShape, hasCapDomArity]
  exact Nat.le_add_right (toucherAtom.leftContext.length + 2) toucherAtom.rightContext.length

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the located-cap read-off SEAT-BOUND substrate is machine-checked (FC-3 r22, B3).**
`stringArcPairCapWindow_splitSeatBound` derives, from the `StringArcPairCapWindow` certificate and the length
boundary chain, the split-state seat bound the word descent master consumes — via the shipped P3 arc-fold chain
advance and the split head's cap arity.  Colour-blind `Nat` positional substrate.  `= true`. -/
def fxString_hasCapWindowSeatBound : Bool := true

/-- **OPEN (honest) — the colour-aware bubble EMISSION is NOT shipped; it is gated on the WORD descent master.**
The full read-off `_ofArcEqual` emits the located cap as a `WordBubblesToFront` witness whose moved atom is a cap
at exactly the window position on exactly the seed boundary.  Producing that witness runs the WORD descent master
(the clone of `arcPairSeated_bubblesThroughPrefix`), whose arc source `ArcPrefixBubbleDescent` is PHANTOM-LOCKED
(imports `DisjointWindowFactorization` and `ArcBubbleToFront`, both keyed on the length-rigidity
`adjunctionPath_eq_of_length_eq` that is FALSE at the adjoint triple).  The genuine port re-plumbs the descent
onto the WORD factorizations threading a `SpineBoundaryWordChained` — the round's standing residual, a from-scratch
piece for the next round.  The bubble carrier (`WordBubblesToFront`, both directions, B1), the seat/refute
bookkeeping (P1/P2), the arc-fold chain advance (P3), the pure-cap transport (P4), and this seat bound are all
shipped; only the descent recursion assembling them remains.  `= false`. -/
def fxString_hasCapWindowSeedReadoff : Bool := false

end FX1Poly.Polygraph
