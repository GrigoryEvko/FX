import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWord
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # WalkingString — the SPINE TOP-WORD is INVARIANT under atom transposition (FC-3 r13, N2)

The width-0 pure-cup sort peels the shared last cup and bubbles the located partner to the front through interior
transpositions; the shared-top pin (`stringSpineAtom_eq_of_sharedCod_sameWindow`, `StringLastCupSharedTopPin`) it
feeds needs the SPINE TOP WORD to survive each transposition — the back cup's codomain word must equal the second
list's top word AFTER bubbling.  The recon flags this as the ONE place the "shared top word" story could break, to be
machine-checked BEFORE the locate/sort assembly rests on it (N2).  This file ships it, signature-generic:

  * ★ `spineListTopWord_swapInvariant` — a single adjacent atom transposition (`SpineAtomSwap`) leaves the spine's
    top word fixed.  Both firing orders build the SAME top boundary word `leftAcc · fHigh · inert · gMid · rightAcc`
    over the two-atom window; the equality is three `composePath_assoc` re-associations (the top word of a length-≥2
    list depends only on the SECOND atom's codomain word, and both second atoms carry that same full window cod word).
  * ★★ `spineListTopWord_atomicTraceEquiv` — the top word is invariant under the FULL atomic closure
    (`AtomicTraceEquiv`): reflexivity / symmetry / transitivity thread through, the head-cons congruence shifts the
    accumulator to the head's cod word and applies the induction hypothesis there (so the statement is `∀ bottomWord`,
    generalised for the changing accumulator).  This is the form the sort consumes: any sequence of interior
    transpositions preserves the top boundary word the shared-cod pin reads off.

The `spineListTopWord` extractor discards the bottom word at the first cons, so a length-≥2 list's top word is its LAST
atom's codomain word; a transposition of two adjacent atoms rewrites only the window between them, leaving that last
codomain word — hence the top word — fixed.  Pure `composePath` bookkeeping; no colour read, no length rigidity.

Raw Lean 4 + Init; the swap case is `cases` on the single-constructor `SpineAtomSwap` + `composePath_assoc`
re-associations, the closure is structural induction on `AtomicTraceEquiv`.  `propext`/`Quot.sound`/`Classical`/
`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Invariance under a single adjacent transposition -/

/-- ★ **A single adjacent atom transposition preserves the spine top word.**  For a `SpineAtomSwap`, both firing
orders of the two-atom window build the same top boundary word — the top word of a length-≥2 list is the SECOND
atom's codomain word, and the two second atoms (`generatorRight`-whiskered-left in one order, `generatorLeft`-
whiskered-right in the other) carry the identical full window cod word `leftAcc · fHigh · inert · gMid · rightAcc`
modulo `composePath` associativity. -/
theorem spineListTopWord_swapInvariant {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (bottomWord : ModalityPath signature.graph overallSource overallTarget) :
    spineListTopWord bottomWord firstList = spineListTopWord bottomWord secondList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
      have topEq :
          composePath (composePath (composePath leftAcc oneCellFHigh) inertPath)
              (composePath oneCellGMid rightAcc)
            = composePath leftAcc
                (composePath oneCellFHigh
                  (composePath (composePath inertPath oneCellGMid) rightAcc)) := by
        rw [composePath_assoc (composePath leftAcc oneCellFHigh) inertPath
            (composePath oneCellGMid rightAcc),
          composePath_assoc leftAcc oneCellFHigh
            (composePath inertPath (composePath oneCellGMid rightAcc)),
          composePath_assoc inertPath oneCellGMid rightAcc]
      dsimp only [spineListTopWord]
      rw [topEq]

/-! ## Invariance under the full atomic closure -/

/-- ★★ **The spine top word is invariant under the full atomic trace closure.**  Any `AtomicTraceEquiv` — a sequence
of interior adjacent transpositions closed under reflexivity / symmetry / transitivity / head-cons congruence —
preserves the spine's top boundary word.  Stated `∀ bottomWord` so the head-cons congruence can invoke the induction
hypothesis at the shifted accumulator (the head atom's codomain word).  This is the form the width-0 sort consumes:
bubbling the located partner to the front leaves the shared top word the last-cup pin reads off unchanged. -/
theorem spineListTopWord_atomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    ∀ (bottomWord : ModalityPath signature.graph overallSource overallTarget),
      spineListTopWord bottomWord firstList = spineListTopWord bottomWord secondList := by
  induction atomicEquiv with
  | ofSwap swapStep => intro bottomWord; exact spineListTopWord_swapInvariant swapStep bottomWord
  | refl _ => intro _; rfl
  | symm _ innerInvariance => intro bottomWord; exact (innerInvariance bottomWord).symm
  | trans _ _ firstInvariance secondInvariance =>
      intro bottomWord; exact (firstInvariance bottomWord).trans (secondInvariance bottomWord)
  | consCongr atom _ innerInvariance =>
      intro bottomWord
      dsimp only [spineListTopWord]
      exact innerInvariance _

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the spine TOP-WORD is invariant under atom transposition (FC-3 r13, N2).**
`spineListTopWord_swapInvariant`: a single `SpineAtomSwap` preserves the top word (three `composePath_assoc`
re-associations — the two firing orders build the same window cod word); `spineListTopWord_atomicTraceEquiv`: the full
atomic closure (`AtomicTraceEquiv`) preserves it (structural induction, the head-cons congruence generalised over the
accumulator).  This is the load-bearing "shared top word survives bubbling" fact the recon flagged to verify FIRST —
the back cup's codomain word equals the second list's top word after any sequence of interior transpositions, so the
shared-cod last-cup pin (`stringSpineAtom_eq_of_sharedCod_sameWindow`) can be fed from the strengthened width-0
determinacy Prop's `spineListTopWord` equality.  All UNCONDITIONAL, signature-generic, zero-axiom.

  What this marker does NOT close (no gate flag flips): this is one plumbing lemma for the width-0 sort, not the sort.
  The fueled partner-locate recursion (N1) and the sort assembly (N3) inhabiting
  `StringWidthZeroPureCupDeterminacyShared` are the r14/r15 content.  So `fxString_hasAdjointTripleCompleteness` stays
  `false`, honestly.  `= true`. -/
def fxString_hasSpineTopWordSwapInvariant : Bool := true

end FX1Poly.Polygraph
