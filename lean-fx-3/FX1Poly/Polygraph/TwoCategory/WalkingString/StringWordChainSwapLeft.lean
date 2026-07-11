import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordLeftMirror

/-! # WalkingString/StringWordChainSwapLeft — the LEFT swap's WORD-chain preservation (FC-3 r16, B3
word-chain substrate W4)

The shipped right-of swap chain preservation `spineBoundaryWordChained_swappedPair`
(`StringDisjointWordSwap`) threads the boundary-WORD chain across a right-of transposition.  The width-0
sort's LOCATE case (iii) (`spineAtomSwapLeft_of_disjointWordWindows`, consumed through
`AtomicTraceEquiv.symm`) needs the LEFT mirror: after the reversed transposition the moved pair stays
boundary-word-chained at the SAME running boundary word.

This is the fourth word-chain brick W4 the recon flagged as the r17 keystone.  Its arithmetic is the same
`composePath` associativity dance as the right version, driven off the LEFT factorization's `leftFactor` /
`rightFactor` shapes (`spineAtom_contextsFactorLeft_of_disjointWordWindows`):

  * the moved-second atom `{ atomSecond with rightContext := (inertPath · atomFirst.generatorDom) ·
    atomFirst.rightContext }` fires at the original running boundary word (via `leftFactor`);
  * the moved-first atom `{ atomFirst with leftContext := (atomSecond.leftContext ·
    atomSecond.generatorCod) · inertPath }` fires at the moved-second's target word;
  * the tail's chain transports to the moved-first's target word (via `rightFactor`).

Signature-GENERIC, so it fires at the walking adjoint triple.

Raw Lean 4 + Init; three `composePath_assoc` re-associations, one per chain link.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **W4 — the LEFT swap's WORD-chain preservation.**  If `atomFirst :: atomSecond :: rest` is
boundary-word-chained at `boundaryWord` and the two atoms' contexts factor through the inert path via the
LEFT factorization (`leftFactor` / `rightFactor`), then the reversed transposed pair produced by
`spineAtomSwapLeft_of_disjointWordWindows` is boundary-word-chained at the SAME `boundaryWord`.  The LEFT
mirror of `spineBoundaryWordChained_swappedPair`: three `composePath_assoc` re-associations thread the
running boundary word through the moved pair. -/
theorem spineBoundaryWordChained_swappedPairLeft {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    {rest : List (SpineAtom signature overallSource overallTarget)}
    {boundaryWord : ModalityPath signature.graph overallSource overallTarget}
    (pairWordChained : SpineBoundaryWordChained boundaryWord (atomFirst :: atomSecond :: rest))
    (inertPath : ModalityPath signature.graph atomSecond.rightMidMode atomFirst.leftMidMode)
    (leftFactor :
      atomFirst.leftContext
        = composePath (composePath atomSecond.leftContext atomSecond.generatorDom) inertPath)
    (rightFactor :
      atomSecond.rightContext
        = composePath inertPath (composePath atomFirst.generatorCod atomFirst.rightContext)) :
    SpineBoundaryWordChained boundaryWord
      ({ atomSecond with
          rightContext :=
            composePath (composePath inertPath atomFirst.generatorDom) atomFirst.rightContext }
        :: { atomFirst with
              leftContext :=
                composePath (composePath atomSecond.leftContext atomSecond.generatorCod) inertPath }
        :: rest) := by
  obtain ⟨firstFires, tailWordChained⟩ := spineBoundaryWordChained_tail pairWordChained
  obtain ⟨_secondFires, restWordChained⟩ := spineBoundaryWordChained_tail tailWordChained
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at firstFires restWordChained leftFactor rightFactor ⊢
  refine SpineBoundaryWordChained.cons _ ?_ (SpineBoundaryWordChained.cons _ ?_ ?_)
  · rw [firstFires, leftFactor,
        composePath_assoc inertPath generatorDomA rightContextA,
        composePath_assoc (composePath leftContextB generatorDomB) inertPath
          (composePath generatorDomA rightContextA),
        composePath_assoc leftContextB generatorDomB
          (composePath inertPath (composePath generatorDomA rightContextA))]
  · rw [composePath_assoc inertPath generatorDomA rightContextA,
        composePath_assoc (composePath leftContextB generatorCodB) inertPath
          (composePath generatorDomA rightContextA),
        composePath_assoc leftContextB generatorCodB
          (composePath inertPath (composePath generatorDomA rightContextA))]
  · rw [composePath_assoc (composePath leftContextB generatorCodB) inertPath
          (composePath generatorCodA rightContextA),
        composePath_assoc leftContextB generatorCodB
          (composePath inertPath (composePath generatorCodA rightContextA)),
        ← rightFactor]
    exact restWordChained

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the LEFT swap's WORD-chain preservation is machine-checked (FC-3 r16, B3 word-chain
substrate W4).**  `spineBoundaryWordChained_swappedPairLeft` threads the reversed transposed pair back into
`SpineBoundaryWordChained` at the same running boundary WORD — the LEFT mirror of the shipped right-of
`spineBoundaryWordChained_swappedPair`, three `composePath_assoc` re-associations driven off the LEFT
factorization.  Signature-GENERIC.  This closes the fourth word-chain brick the recon named; the full
substrate W1-W4 is now shipped.

  What this marker does NOT close (no gate flag flips): the fueled `stringMatchingLocateAux` threading the
  two parallel chains, the `stringMatchingPureCupSpineSortFueled` assembly, and the inhabitation of
  `StringWidthZeroPureCupDeterminacyShared`.  So `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) stays `false`, honestly.  `= true`. -/
def fxString_hasWordChainSwapLeft : Bool := true

end FX1Poly.Polygraph
