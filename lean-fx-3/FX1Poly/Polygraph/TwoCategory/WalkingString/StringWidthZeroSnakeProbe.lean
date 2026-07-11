import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroSnake
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed

/-! # WalkingString — the width-0 snake exclusion FIRES at the string signature (FC-3 r14, B2 down-payment)

The width-0 LOCATE's snake exclusion `matchingForwardChordsNotAdjacent` (`MatchingWidthZeroSnake`) — the FIRST
consumer of the width-0 partner involution (b#1) — was, like the involution, hardcoded to
`adjunctionModeSignature`.  Riding the r14 involution widen, it is now itself generic over
`{signature : ModeSignature}` (colour-blind: it is pure Nat arithmetic over the widened involution).  This file
is the string-side truth-probe: the snake exclusion is available at `adjointTripleModeSignature`.

  * ★ `stringWidthZeroPureCup_forwardChordsNotAdjacent` — for a width-0 pure-cup string spine, two forward
    chords at adjacent windows `(w, w+1)` and `(w+1, w+2)` are contradictory (they would share the endpoint
    `w+1`, which the involution sends BACK to `w`, not forward to `w+2`).  The widened
    `matchingForwardChordsNotAdjacent` specialised to the three-generator seed — the snake exclusion the string
    LOCATE recursion will ride, now AVAILABLE at the string signature.

## What this does NOT do (the gate flag stays `false`, honestly)

The snake exclusion is one brick of the LOCATE, not the LOCATE and not the sort.  The nested-transposition
MATCHING invariance (the peel `extractDiagram_eq_of_atomicPureCupTraceEquiv`) is NOT yet available at the string
signature — its widen is blocked on the colour-blind `AllCupArity`-preservation-along-`AtomicTraceEquiv`
(eliminating the `capAtomCount → AllCupArity` classifier roundtrip through `allCupArity_ofCapAtomCountZero`'s
`adjunctionSpineAtom_isCupOrCap`), the r15+ classifier-elimination.  So the width-0 SORT
(`StringWidthZeroPureCupDeterminacyShared`) stays open and `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) stays `false`.

Raw Lean 4 + Init; the probe is a one-line instantiation of the widened snake exclusion.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The width-0 snake exclusion, at the string signature.**  For a width-0 pure-cup string spine over
`adjointTripleModeSignature`, two forward chords at adjacent windows `(windowLow, windowLow+1)` and
`(windowLow+1, windowLow+2)` cannot coexist — they share the endpoint `windowLow+1`, and the width-0 partner
involution sends it back to `windowLow`, not forward.  The widened `matchingForwardChordsNotAdjacent` specialised
to the three-generator seed — the LOCATE's snake exclusion, now available at the string signature (riding the
r14 involution widen). -/
theorem stringWidthZeroPureCup_forwardChordsNotAdjacent
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine)
    (windowLow : Nat)
    (lowInRange : 0 + windowLow < 0 + (matchingOfSpineList 0 spine).topCount)
    (chordLow : natListGetAt (matchingOfSpineList 0 spine).partner (0 + windowLow)
      = 0 + windowLow + 1)
    (chordHigh : natListGetAt (matchingOfSpineList 0 spine).partner (0 + (windowLow + 1))
      = 0 + (windowLow + 1) + 1) : False :=
  matchingForwardChordsNotAdjacent spine pureCup windowLow lowInRange chordLow chordHigh

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 snake exclusion fires at the string signature (FC-3 r14, B2 down-payment).**
`stringWidthZeroPureCup_forwardChordsNotAdjacent`: the widened `matchingForwardChordsNotAdjacent` (itself
genericised over `{signature}` riding the r14 involution widen, colour-blind) is available at
`adjointTripleModeSignature` — the LOCATE's snake exclusion, string-ready.

  What this marker does NOT close (no gate flag flips): the nested-transposition MATCHING invariance (the peel
  `extractDiagram_eq_of_atomicPureCupTraceEquiv`) is NOT yet string-ready — its widen is blocked on the
  colour-blind `AllCupArity`-preservation-along-`AtomicTraceEquiv` (the `capAtomCount → AllCupArity` classifier
  roundtrip through `allCupArity_ofCapAtomCountZero`'s `adjunctionSpineAtom_isCupOrCap`), the r15+
  classifier-elimination.  So `StringWidthZeroPureCupDeterminacyShared` stays open and
  `fxString_hasAdjointTripleCompleteness` stays `false`, honestly.  `= true`. -/
def fxString_hasWidthZeroSnakeProbe : Bool := true

end FX1Poly.Polygraph
