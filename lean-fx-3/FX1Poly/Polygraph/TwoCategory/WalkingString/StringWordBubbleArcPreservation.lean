import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble

/-! # WalkingString/StringWordBubbleArcPreservation — the WORD bubble preserves the extracted arc (FC-3 r5, B4)

The PARTNER LOCATION (recon §3) turns an arc-structure equality (`matchingOf valleyA = matchingOf valleyB`) into a
`WordBubblesToFront` witness, then TRANSFERS arc-preservation along the bubble via the peel
`extractArc_eq_of_stringAtomicTraceEquiv` (`StringArcSwapPeel`, colour-blind, no length-rigidity).  This file ships
the reachable half of that machinery: the arc-preservation TRANSFER along the r4 RIGHT-of word bubble.

  * `extractArc_eq_of_wordBubblesToFront` — ★ a witnessed `WordBubblesToFront` bubble preserves the extracted arc:
    from a fresh, forest-rooted, boundary-tracking start state and the `SpineBoundaryChained` of the un-bubbled
    spine, `extractArc` of the un-bubbled `prefixAtoms ++ target :: suffixAtoms` equals `extractArc` of the
    bubbled `movedTarget :: (movedPrefixAtoms ++ suffixAtoms)`.  It composes the r4 bubble-to-trace-equivalence
    (`atomicTraceEquiv_of_wordBubblesToFront`) into the peel (`extractArc_eq_of_stringAtomicTraceEquiv`) — the
    exact "`extractArc` transfers arc-preservation" step the location design names.

What this file does NOT ship (honest residual, the recon's node-4 remainder — r6 sort-assembly material): the
colour-aware READ-OFF `*_ofArcEqual` that turns arc-structure equality INTO the located atom + window (the
genuinely-new piece, and the only missing one), and its prerequisite `WordBubblesToFront.stepLeftOf` (recorded
residual of B3).  This file ships the arc-preservation TRANSFER that read-off feeds; the read-off itself is gated
on `stepLeftOf` and re-derived colour-aware (a valley cap on `(G,F)` is ε, on `(H,G)` is ε'; a valley cup on
`(F,G)` is η, on `(G,H)` is η').  So `fxString_hasAdjointTripleCompleteness` stays `false`.

Raw Lean 4 + Init; the transfer is one composition of two shipped theorems.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The WORD bubble preserves the extracted arc.**  A witnessed right-of `WordBubblesToFront` carries
`prefixAtoms ++ target :: suffixAtoms` to `movedTarget :: (movedPrefixAtoms ++ suffixAtoms)` inside
`AtomicTraceEquiv` (`atomicTraceEquiv_of_wordBubblesToFront`); the peel
(`extractArc_eq_of_stringAtomicTraceEquiv`) then extracts the SAME arc from both, given a fresh, forest-rooted,
boundary-tracking start state and the `SpineBoundaryChained` of the un-bubbled spine.  This is the
arc-preservation TRANSFER the LOCATION read-off feeds — the reachable half of the partner-location machinery. -/
theorem extractArc_eq_of_wordBubblesToFront
    {overallSource overallTarget : adjointTripleModeSignature.graph.Mode}
    {target movedTarget : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms :
        List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (witness : WordBubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (suffixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (state : ArcWireState) (bottomCount boundaryLength : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (wiresEq : state.openWires.length = boundaryLength)
    (chained : SpineBoundaryChained boundaryLength (prefixAtoms ++ target :: suffixAtoms)) :
    extractArc bottomCount (processArcSpine state (prefixAtoms ++ target :: suffixAtoms))
      = extractArc bottomCount
          (processArcSpine state (movedTarget :: (movedPrefixAtoms ++ suffixAtoms))) :=
  extractArc_eq_of_stringAtomicTraceEquiv
    (atomicTraceEquiv_of_wordBubblesToFront witness suffixAtoms)
    state bottomCount boundaryLength fresh forest nextFreshPos boundaryBelowFresh wiresEq chained

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the WORD bubble preserves the extracted arc (FC-3 r5, B4, arc-preservation transfer).**
`extractArc_eq_of_wordBubblesToFront` composes the r4 bubble-to-trace-equivalence
(`atomicTraceEquiv_of_wordBubblesToFront`) into the colour-blind peel
(`extractArc_eq_of_stringAtomicTraceEquiv`): a witnessed right-of word bubble extracts the SAME arc from the
un-bubbled and bubbled spines, given a valid start state and the un-bubbled `SpineBoundaryChained`.  This is the
arc-preservation TRANSFER step of the partner-location machinery (recon §3).

  What this marker does NOT close (the recon's node-4 residual, r6 sort-assembly material): the colour-aware
  READ-OFF `*_ofArcEqual` that turns arc-structure equality INTO the located atom + window (the genuinely-new
  piece), gated on `WordBubblesToFront.stepLeftOf` (the recorded B3 residual).  Colours are boundary-determined on
  valleys, so the read-off is re-derived label-driven, not length-rigid.  This file ships the transfer that
  read-off feeds; `fxString_hasAdjointTripleCompleteness` stays `false`.  `= true`. -/
def fxString_hasWordBubbleArcPreservation : Bool := true

end FX1Poly.Polygraph
