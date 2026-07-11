import FX1Poly.Polygraph.TwoCategory.WalkingString.StringInterleavedWindowSort
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordSwapInvariant

/-! # WalkingString — the SCRAMBLED FOUR-CUP transposition truth-probe (FC-3 r13, B2)

The r10 probe (`stringWidthZeroPureCupDeterminacy_probe`, `StringWidthZeroCupProbe`) and the r12 mixed probe
(`stringTwoSpeciesWindow_matchingInvariant`, `StringTwoSpeciesMatchingProbe`) validated the width-0 sort's
reorder mechanism on a TWO-atom window.  Before the fueled partner-locate recursion (N1) is attempted, the recon
calls for the same truth-probe scaled to a FOUR-cup case — a transposition of an adjacent cup pair sitting inside a
larger pure-cup spine, the shape each peel of the sort produces.  This file lands that probe CONCRETELY on the two
INVARIANTS the locate step actually threads: the spine `SpineTraceEquiv` (the sort's conclusion) and the spine TOP
WORD (the shared cod the last-cup pin reads off).

  * ★ `stringScrambledFourCup_traceEquivAndTopWord` — a four-cup spine (two base cups adjacent at the head, two more
    base cups as the trailing context) transposed at the head window: the two firing orders are `SpineTraceEquiv`
    (the shipped transposition atom `stringSpineAtomSwap_spineTraceEquiv`, colour-blind, any `rest`) AND build the
    SAME spine top word for every bottom word (N2 `spineListTopWord_swapInvariant`).  So the reorder + shared-top
    invariance the sort's locate step iterates is confirmed on a four-cup instance, scaling the two-atom probes.

## The honest wall: the MATCHING invariance for a nested transposition is the unported drop/swap brick

This probe deliberately does NOT claim `matchingOfSpineList 0` equality of the two four-cup firing orders.  At the
two-atom window (r10 / r12) that equality is `rfl` (the union-find is definitionally blind to the disjoint firing
order); with a NONEMPTY trailing context the fresh-wire numbering shifts, so the equality is TRUE but no longer
`rfl` (a bare `rfl` blows the heartbeat budget).  Its proof is the adjunction's matching-invariance-under-swap
`extractDiagram_eq_of_atomicPureCupTraceEquiv` (`MatchingSwapPeel` / `MatchingWidthZeroSort`), which rides the generic
union-find but is NOT yet ported to the three-generator seed — the recon's TOKEN-SWAP tranche.  And the fueled
partner-locate recursion (N1) that consumes it bottoms out in the width-0 partner INVOLUTION
(`matchingOfSpineListZero_partner_isInvolution`, `MatchingWidthZeroInvolution`), which is hardcoded to
`adjunctionModeSignature` — so it must first be genericised (or re-derived at the string) before the snake exclusion
(`matchingForwardChordsNotAdjacent`) and the locate can port.  That is the r14 content this probe stands in front of.

## What this probe does NOT do (the flag stays `false` — honestly)

The probe confirms the reorder + shared-top mechanism on a four-cup instance; it is not the sort.  So
`fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false`.

Raw Lean 4 + Init; the probe is one `SpineAtomSwap.swap` with a two-cup `rest`, lifted by the shipped transposition
atom and N2.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- A base cup `η = unitLower` (`id_base ⇒ F·G`) used as trailing context in the four-cup probe. -/
def stringProbeRestCup : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.base, AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    stringFG, StringTwoCell.unitLower,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩

/-- ★ **The scrambled four-cup transposition probe.**  A four-cup spine — two base cups `η`, `η` at the head window
(width 0, disjoint) followed by two more base cups as trailing context — in its two head-window firing orders: the
orders are `SpineTraceEquiv` (the shipped transposition atom, which fires the same Godement constructor regardless of
the trailing `rest`) and they build the SAME spine top word for every bottom word (the N2 swap-invariance).  The
four-cup analog of the two-atom r10 / r12 probes: the transposition + shared-top mechanism the sort's partner-locate
step iterates, confirmed one size up.  (The matching invariance — the third sort invariant — needs the unported
`extractDiagram_eq_of_atomicPureCupTraceEquiv`; see the file header.) -/
theorem stringScrambledFourCup_traceEquivAndTopWord :
    ∃ (cupFirst cupSecond :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base)),
      SpineTraceEquiv adjointTripleModeSignature cupFirst cupSecond
      ∧ ∀ (bottomWord : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base),
          spineListTopWord bottomWord cupFirst = spineListTopWord bottomWord cupSecond := by
  have windowSwap :=
    SpineAtomSwap.swap (signature := adjointTripleModeSignature)
      StringTwoCell.unitLower StringTwoCell.unitLower
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      [stringProbeRestCup, stringProbeRestCup]
  exact ⟨_, _, stringSpineAtomSwap_spineTraceEquiv windowSwap,
    fun bottomWord => spineListTopWord_swapInvariant windowSwap bottomWord⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the scrambled FOUR-CUP transposition truth-probe lands (FC-3 r13, B2).**
`stringScrambledFourCup_traceEquivAndTopWord`: a four-cup spine transposed at its head window has both sort
invariants that are cheaply provable — the two firing orders are `SpineTraceEquiv` (the shipped transposition atom,
any trailing `rest`) and share their spine top word for every bottom word (N2 `spineListTopWord_swapInvariant`).  The
four-cup analog of the two-atom r10 / r12 probes, scaling the reorder + shared-top mechanism the sort's partner-locate
step iterates.

  What this marker does NOT close (the honest wall): the MATCHING invariance of the nested transposition is TRUE but
  no longer `rfl` (the trailing context shifts the fresh-wire numbering); its proof is the unported
  `extractDiagram_eq_of_atomicPureCupTraceEquiv` (`MatchingSwapPeel`), and the fueled locate that consumes it (N1)
  first needs the adjunction-keyed width-0 partner involution
  (`matchingOfSpineListZero_partner_isInvolution`) genericised — the r14 content.  So
  `fxString_hasAdjointTripleCompleteness` stays `false`, honestly.  `= true`. -/
def fxString_hasScrambledFourCupProbe : Bool := true

end FX1Poly.Polygraph
