import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedSwapChain

/-! # FarCommutation — swaps at distance two or more slide past each other (FREE-7)

The determination zigzag normalization rests on three local moves: inverse cancellation
(shipped — `TaggedSpineAtomSwap.rhsDetermined`/`lhsDetermined`), FAR COMMUTATION (this
file), and the overlapping-swap hexagon (next).  Far commutation is the Mazurkiewicz
independence at distance ≥ 2: a transposition at the head and a move strictly below the
two head positions touch disjoint atoms, so they slide past each other.

  * ★ `TaggedSpineAtomSwap.replaceRest` — THE primitive: the tagged swap constructor is
    parametric in its shared tail, so a head transposition fires over any replacement
    tail (one `cases`, one re-application);
  * `OneTaggedAdjacentSwapChain.exchangeHeadSwapPastDeepChain` /
    `exchangeReversedHeadSwapPastDeepChain` — the packaged square in both head
    directions: given a head transposition and a chain of moves entirely below the two
    head positions, the TAIL-FIRST composite reaches the head-first composite's endpoint
    (the reordering move the zigzag normalizer fires to push head moves together).

HONESTY: there is deliberately NO `OneTaggedAdjacentSwap`-level replaceRest — a
one-swap between `x :: y :: rest` endpoints can also be a `deeper` move whose inner step
lives in the tail, and such a step does not survive tail replacement.  The primitive is
true only at the raw `TaggedSpineAtomSwap` level; the exchange combinators therefore
take the raw swap as the head premise.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The primitive: the swap is parametric in its tail -/

/-- ★ **Tail replacement**: a head transposition never inspects the trace below the two
transposed positions — the same swap fires over any other tail. -/
theorem TaggedSpineAtomSwap.replaceRest {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstHead firstNext secondHead secondNext :
      TaggedSpineAtom signature overallSource overallTarget}
    {sharedRest : List (TaggedSpineAtom signature overallSource overallTarget)}
    (swapStep : TaggedSpineAtomSwap signature
      (firstHead :: firstNext :: sharedRest) (secondHead :: secondNext :: sharedRest))
    (otherRest : List (TaggedSpineAtom signature overallSource overallTarget)) :
    TaggedSpineAtomSwap signature
      (firstHead :: firstNext :: otherRest) (secondHead :: secondNext :: otherRest) := by
  cases swapStep with
  | @swap _swapSourceMode _swapMiddleLeft _swapMiddleRight _swapTargetMode _oneCellFMid
      _oneCellFHigh _oneCellGLow _oneCellGMid generatorLeft generatorRight leftTag
      rightTag leftAcc inertPath rightAcc _rest =>
      exact TaggedSpineAtomSwap.swap generatorLeft generatorRight leftTag rightTag
        leftAcc inertPath rightAcc otherRest

/-! ## The packaged exchange squares -/

/-- **Far commutation, forward head**: a head transposition and a chain of strictly
deeper moves reorder — the tail-first composite (deep moves under both head atoms, then
the tail-replaced head swap) reaches the head-first composite's endpoint. -/
theorem OneTaggedAdjacentSwapChain.exchangeHeadSwapPastDeepChain
    {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstHead firstNext secondHead secondNext :
      TaggedSpineAtom signature overallSource overallTarget}
    {sharedRest otherRest : List (TaggedSpineAtom signature overallSource overallTarget)}
    (headSwap : TaggedSpineAtomSwap signature
      (firstHead :: firstNext :: sharedRest) (secondHead :: secondNext :: sharedRest))
    (tailChain : OneTaggedAdjacentSwapChain signature sharedRest otherRest) :
    OneTaggedAdjacentSwapChain signature
      (firstHead :: firstNext :: sharedRest) (secondHead :: secondNext :: otherRest) :=
  ((tailChain.consCongr firstNext).consCongr firstHead).trans
    (OneTaggedAdjacentSwapChain.single
      (OneTaggedAdjacentSwap.here (headSwap.replaceRest otherRest)))

/-- **Far commutation, reversed head**: the same square when the head move runs against
the constructor direction (`hereReversed`). -/
theorem OneTaggedAdjacentSwapChain.exchangeReversedHeadSwapPastDeepChain
    {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstHead firstNext secondHead secondNext :
      TaggedSpineAtom signature overallSource overallTarget}
    {sharedRest otherRest : List (TaggedSpineAtom signature overallSource overallTarget)}
    (headSwap : TaggedSpineAtomSwap signature
      (secondHead :: secondNext :: sharedRest) (firstHead :: firstNext :: sharedRest))
    (tailChain : OneTaggedAdjacentSwapChain signature sharedRest otherRest) :
    OneTaggedAdjacentSwapChain signature
      (firstHead :: firstNext :: sharedRest) (secondHead :: secondNext :: otherRest) :=
  ((tailChain.consCongr firstNext).consCongr firstHead).trans
    (OneTaggedAdjacentSwapChain.single
      (OneTaggedAdjacentSwap.hereReversed (headSwap.replaceRest otherRest)))

end FX1Poly.Polygraph
