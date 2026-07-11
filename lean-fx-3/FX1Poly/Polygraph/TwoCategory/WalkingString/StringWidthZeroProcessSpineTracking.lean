import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline

/-! # WalkingString/StringWidthZeroProcessSpineTracking — the width-0 open-wire boundary tracking at the
adjoint-triple seed (FC-3 r15, B3 locate foundation)

The width-0 pure-cup SORT that inhabits `StringWidthZeroPureCupDeterminacyShared`
(`StringValleyDegenerateSplit`) runs a partner-LOCATE recursion mirroring the walking adjunction's
`matchingLocateAux` (`MatchingWidthZeroSort`).  That locate needs to know that folding the prefix of a
boundary-chained pure-cup spine moves the processed open-wire count along the boundary chain, and that
after the prefix the open-wire count is exactly the last cup's dom-boundary width — the two facts the
adjunction ships as `processSpine_openWires_length_ofChainedAppend` /
`processSpine_prefix_openWires_eq_lastDomBoundary`.

Those two adjunction lemmas are NOT signature-generic: their proof reads every prefix atom's cup-or-cap
arity off the TOTAL classifier `adjunctionSpineAtom_hasCupOrCapArity` (a generic `{signature}` has no
such total classification).  The walking adjoint triple, however, HAS a total classification —
`adjointTripleSpineAtom_hasCupOrCapArity` (`StringArcArity`, every three-generator atom is a cup `(0,2)`
or a cap `(2,0)`) — so the two lemmas port to the string seed BYTE-IDENTICALLY, swapping only the
classifier token.  Colour-blind: the boundary tracking reads `AtomHasCupOrCapArity` + boundary lengths,
never the `F`/`G`/`H` labels.  The generic tracking step `stepAtom_openWires_tracksBoundary`
(`SpineArityDiscipline`) is reused verbatim.

  * ★ `stringProcessSpine_openWires_length_ofChainedAppend` — the prefix fold's open-wire count is the
    running boundary, and the suffix stays chained there.
  * ★ `stringProcessSpine_prefix_openWires_eq_lastDomBoundary` — after the prefix, the open-wire count
    equals the last cup's dom-boundary width, bounding its window for the short-chord read-off.

This lands the open-wire tracking the string LOCATE consumes; the read-off engine
(`matchingLastCup_isShortChord`), the chord-shift descents, the drop-injectivity, and the word-threaded
sort assembly (riding the shipped `WordBubblesToFront` + the r11 word pin) are the standing B3 residual —
`fxString_hasAdjointTripleCompleteness` stays `false`, honestly.

Raw Lean 4 + Init; structural recursion on the prefix, the tracking step generic, the arity token the
string total classifier.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing — `List.range` length (per-file copy, `propext`-free) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]; exact Nat.add_zero count

/-! ## The prefix fold's open-wire count tracks the boundary chain (adjoint-triple seed) -/

/-- ★ **The prefix fold's open-wire count is the running boundary, and the suffix stays chained there**
(adjoint-triple seed).  Structural recursion on the prefix: each head atom's cup-or-cap arity is read off
the string total classifier `adjointTripleSpineAtom_hasCupOrCapArity`, feeding the generic tracking step
`stepAtom_openWires_tracksBoundary`; the boundary advances to the head's cod boundary and the tail stays
chained.  The three-generator analogue of the adjunction's
`processSpine_openWires_length_ofChainedAppend`, colour-blind (reads only arity + boundary lengths). -/
theorem stringProcessSpine_openWires_length_ofChainedAppend
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (prefixAtoms suffixAtoms :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength (prefixAtoms ++ suffixAtoms) →
    ∃ midBoundary : Nat,
      (processSpine state prefixAtoms).openWires.length = midBoundary
        ∧ SpineBoundaryChained midBoundary suffixAtoms
  | [], _, _, boundaryLength, tracks, chained => ⟨boundaryLength, tracks, chained⟩
  | headAtom :: restPrefix, suffixAtoms, state, _, tracks, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have headArity := adjointTripleSpineAtom_hasCupOrCapArity headAtom
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      show ∃ midBoundary,
        (processSpine (stepAtom state headAtom) restPrefix).openWires.length = midBoundary
          ∧ SpineBoundaryChained midBoundary suffixAtoms
      exact stringProcessSpine_openWires_length_ofChainedAppend restPrefix suffixAtoms
        (stepAtom state headAtom) headAtom.codBoundaryLength
        (stepAtom_openWires_tracksBoundary state headAtom headArity tracksEntry) tailChained

/-- ★ **After the prefix, the open-wire count equals the last cup's dom-boundary width** (adjoint-triple
seed).  The prefix fold from the width-`bottomCount` seed state lands its open-wire count at the boundary
the trailing `lastCup` fires at (`stringProcessSpine_openWires_length_ofChainedAppend`), which the chain
pins to `lastCup.domBoundaryLength`.  The three-generator analogue of the adjunction's
`processSpine_prefix_openWires_eq_lastDomBoundary`; bounds the last cup's window for the short-chord
read-off. -/
theorem stringProcessSpine_prefix_openWires_eq_lastDomBoundary
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup])) :
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ prefixAtoms).openWires.length
      = lastCup.domBoundaryLength := by
  obtain ⟨midBoundary, lenEq, chainedSuffix⟩ :=
    stringProcessSpine_openWires_length_ofChainedAppend prefixAtoms [lastCup]
      ⟨List.range bottomCount, [], bottomCount, 0⟩ bottomCount (rangeLength bottomCount) chained
  have lastFires : lastCup.domBoundaryLength = midBoundary :=
    (spineBoundaryChained_tail chainedSuffix).1
  rw [lenEq]; exact lastFires.symm

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 open-wire boundary tracking is ported to the adjoint-triple seed (FC-3
r15, B3 locate foundation).**  `stringProcessSpine_openWires_length_ofChainedAppend` /
`stringProcessSpine_prefix_openWires_eq_lastDomBoundary` port the adjunction's boundary-tracking pair
BYTE-IDENTICAL, swapping the total classifier `adjunctionSpineAtom_hasCupOrCapArity →
adjointTripleSpineAtom_hasCupOrCapArity` (the string HAS a total cup-or-cap classification, so no purity
hypothesis is needed) and reusing the generic tracking step `stepAtom_openWires_tracksBoundary`.
Colour-blind: reads arity + boundary lengths, never `F`/`G`/`H`.

  What this marker does NOT close (no gate flag flips): the string width-0 pure-cup SORT inhabiting
  `StringWidthZeroPureCupDeterminacyShared`.  On top of this tracking the locate still needs the string
  read-off engine (the `matchingLastCup_isShortChord` port with its `stepCupMatching_forwardPartner`
  private web), the chord-shift descents (`matchingChordShift_below/above`), the drop-injectivity
  (`dropLastCup_matching_injective`), and the novel word-threaded sort assembly that constructs a
  `WordBubblesToFront` witness (`StringDisjointWordBubble`, already shipped generic) from the located
  partner and pins the dropped cup by the r11 word pin `stringSpineAtom_eq_of_sharedCod_sameWindow`
  (`StringLastCupSharedTopPin`), threading the shared top word through every recursive arm and bottoming
  out at the r13 singleton base `stringWidthZeroPureCupShared_singleton`.  So
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false`, honestly.
  `= true`. -/
def fxString_hasWidthZeroProcessSpineTracking : Bool := true

end FX1Poly.Polygraph
