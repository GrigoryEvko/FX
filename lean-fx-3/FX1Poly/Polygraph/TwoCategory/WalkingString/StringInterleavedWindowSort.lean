import FX1Poly.Polygraph.TwoCategory.WalkingString.StringConvOfMapEqPort
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # WalkingString — the pure-block sort's TRANSPOSITION ATOM, ported to the string (FC-3 r2, B1)

FC-9 (`StringConvOfMapEqPort`) closed the completeness `convOfMapEq` port MODULO the two named sub-producers
(`StringCellDescentStepOracle` × `StringCellValleyTraceEquiv`) and localized the standing crux to the
SAME-boundary interleaved two-colour window.  FC-3 r1 (`StringDisjointFarCommutation`) discharged the DISJOINT
(`|i − j| > 1`) reorderings UNCONDITIONALLY at the CELL level via `stringDisjointWhiskerExchange`
(`TwoCellConvFull.whiskerExchange`), which needs a genuine middle 1-cell between the two whiskers.

This file ports the FIRST genuine brick of the recon's route-(b) pure-block bubble-sort to the string, but at the
SPINE / TRACE level the sort actually runs on — the level `StringCellValleyTraceEquiv` demands (two valleys with
equal matching are `SpineTraceEquiv adjointTripleModeSignature valleyA.spine valleyB.spine`).  The sort reorders one
pure block into any arc-equal pure block by a chain of adjacent sibling transpositions; each transposition is one
`SpineTraceEquiv` step.  That step is the composable ATOM the whole sort iterates.

## Why it ports by INSTANTIATION — the transposition is `{signature}`-GENERIC and colour-BLIND

The adjacent-atom transposition `SpineAtomSwap` (`FreeTwoCell/AtomicSwap`), its inclusion into the block-level
`SpineTraceEquiv` (`AtomicTraceEquiv.toSpineTraceEquiv`, riding `SpineGodementStep`), and `SpineTraceEquiv` itself
(`FreeTwoCell/SpineGodement`) are ALL `{signature : ModeSignature}`-generic.  So the transposition step ports to
`adjointTripleModeSignature` on the nose — it reads NO colour (`F`/`G`/`H`), only the two generators' whisker
columns and the inert middle zone.  Concretely:

  * ★ `stringSpineAtomSwap_spineTraceEquiv` — any adjacent horizontally-independent pair of STRING generators
    transposes as a `SpineTraceEquiv` step (`AtomicTraceEquiv.ofSwap` then `.toSpineTraceEquiv`).  Colour-blind:
    the two generators may be any of the four (`η`/`ε`/`η'`/`ε'`), any colour pattern, and the step fires the SAME
    Godement constructor — no bespoke arms.

## Non-vacuity at the minimal widths, across colour patterns (the crux window, made concrete)

  * ★ `stringTwoColourInterleavedWindow_spineTraceEquiv` — the genuine TWO-COLOUR window: the lower cup `η`
    (colour 1, `id_base ⇒ F·G`) adjacent to the upper cup `η'` (colour 2, `id_tip ⇒ G·H`), separated by the one
    strand `F` the mode structure forces between a `base`-turnback and a `tip`-turnback.  The two firing orders are
    `SpineTraceEquiv` — the same-boundary interleaved two-colour transposition, at the minimal width.
  * ★ `stringSameColourAdjacentWindow_spineTraceEquiv` — the GAP-0 same-colour window: two lower cups `η`, `η`
    directly adjacent (inert zone `nil`), the truly same-boundary case FC-3 r1's `whiskerExchange` (needing a
    middle 1-cell) does NOT reach.  Reorders freely.
  * ★★ `stringPinnedMixedWindow_spineTraceEquiv` — the pinned MIXED cup·cap window `(η, ε')` (lower cup `η` opening
    `F·G` adjacent to upper cap `ε'` closing `H·G`, both `base ⟶ base`), gap-0.  The r6 pin `stringCupCod_ne_capDom`
    proves this window can NEVER STRAIGHTEN (`F·G ≠ H·G`); this theorem proves its two orders nonetheless REORDER
    freely.  Reordering and straightening are DIFFERENT moves: the sort needs only the reorder, which is pin-free,
    so the pin blocks Piece I's straighten arm WITHOUT blocking Piece II's sort.

## What this file does NOT close (the flag stays `false` — honestly)

The transposition atom is one step; the pure-block SORT that closes `StringCellValleyTraceEquiv` needs, ON TOP of
it: the ARC-preservation of each swap (`extractArc_eq_of_atomicTraceEquiv` is `adjunctionModeSignature`-hardcoded via
`arcSwapCorePackage_of_adjunctionSwap`, a colour-blind but un-ported arc dispatch), the bubble-to-front driver
(`bubbleCupToFront`), the locate/tails-cancel crux reconstructing the block arc equality, and the valley-append
`matchingOf`-split feeding per-block `diagram` + length agreement — plus Piece I (`StringCellDescentStepOracle`).
Those are the multi-round content the shipped ledger names; this file lands ONLY the transposition atom, so
`fxString_hasAdjointTripleCompleteness` (in `StringMatchingCompleteness`) is NOT moved and stays `false`.

Raw Lean 4 + Init; the atom is a two-lemma composition of the generic swap machinery, the non-vacuity witnesses are
concrete constructor applications.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The transposition atom — the generic adjacent swap, ported to the string signature -/

/-- ★ **The sort's transposition atom at the walking adjoint triple.**  Any adjacent horizontally-independent pair
of STRING spine atoms (related by `SpineAtomSwap adjointTripleModeSignature`) is a `SpineTraceEquiv` step: embed the
atomic swap (`AtomicTraceEquiv.ofSwap`) and include it into the block-level trace equivalence
(`AtomicTraceEquiv.toSpineTraceEquiv`, which routes the swap through its `SpineGodementStep` at singleton blocks).
Colour-BLIND — the two generators may be any of `η`/`ε`/`η'`/`ε'`, any colour pattern; the step fires the SAME
Godement constructor.  This is the composable atom the pure-block bubble sort (`StringCellValleyTraceEquiv`'s route
b) iterates. -/
theorem stringSpineAtomSwap_spineTraceEquiv
    {overallSource overallTarget : AdjointTripleMode}
    {firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (swapStep : SpineAtomSwap adjointTripleModeSignature firstList secondList) :
    SpineTraceEquiv adjointTripleModeSignature firstList secondList :=
  (AtomicTraceEquiv.ofSwap swapStep).toSpineTraceEquiv

/-! ## Non-vacuity — the crux window at the minimal widths, across the colour patterns -/

/-- ★ **The two-colour interleaved window transposes.**  The lower cup `η = StringTwoCell.unitLower`
(`id_base ⇒ F·G`, colour 1) adjacent to the upper cup `η' = StringTwoCell.unitUpper` (`id_tip ⇒ G·H`, colour 2),
separated by the single strand `F` the mode structure forces between a `base`-turnback and a `tip`-turnback: the two
firing orders are `SpineTraceEquiv`.  The genuine same-boundary interleaved two-colour transposition at the minimal
width — the exact crux configuration FC-9 localized, now discharged as a REORDER (not a straighten) step. -/
theorem stringTwoColourInterleavedWindow_spineTraceEquiv :
    ∃ firstOrder secondOrder :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.tip),
      SpineAtomSwap adjointTripleModeSignature firstOrder secondOrder
        ∧ SpineTraceEquiv adjointTripleModeSignature firstOrder secondOrder := by
  have windowSwap :=
    SpineAtomSwap.swap (signature := adjointTripleModeSignature)
      StringTwoCell.unitLower StringTwoCell.unitUpper
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (singletonModalityPath AdjointTripleModality.left)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
      []
  exact ⟨_, _, windowSwap, stringSpineAtomSwap_spineTraceEquiv windowSwap⟩

/-- ★ **The GAP-0 same-colour adjacent window transposes.**  Two lower cups `η`, `η` directly adjacent — the inert
middle zone is `nil`, so this is the truly same-boundary (`|i − j| = 0`) case the cell-level far-commutation
`stringDisjointWhiskerExchange` (which needs a genuine middle 1-cell) cannot reach.  It reorders freely at the trace
level. -/
theorem stringSameColourAdjacentWindow_spineTraceEquiv :
    ∃ firstOrder secondOrder :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base),
      SpineAtomSwap adjointTripleModeSignature firstOrder secondOrder
        ∧ SpineTraceEquiv adjointTripleModeSignature firstOrder secondOrder := by
  have windowSwap :=
    SpineAtomSwap.swap (signature := adjointTripleModeSignature)
      StringTwoCell.unitLower StringTwoCell.unitLower
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      []
  exact ⟨_, _, windowSwap, stringSpineAtomSwap_spineTraceEquiv windowSwap⟩

/-- ★★ **The pinned MIXED cup·cap window reorders — even though it cannot straighten.**  The lower cup `η`
(`id_base ⇒ F·G`) adjacent to the upper cap `ε' = StringTwoCell.counitUpper` (`H·G ⇒ id_base`), gap-0, both
`base ⟶ base`.  The r6 pin `stringCupCod_ne_capDom` proves this window can NEVER STRAIGHTEN (that would demand
`F·G = H·G`, refuted `stringMixedLowerWindow_cannotStraighten`); THIS theorem proves its two orders nonetheless
transpose as a `SpineTraceEquiv` step.  REORDER and STRAIGHTEN are different moves: the sort (Piece II) needs only
the pin-free reorder, so the pin blocks Piece I's straighten arm without blocking the sort. -/
theorem stringPinnedMixedWindow_spineTraceEquiv :
    ∃ firstOrder secondOrder :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base),
      SpineAtomSwap adjointTripleModeSignature firstOrder secondOrder
        ∧ SpineTraceEquiv adjointTripleModeSignature firstOrder secondOrder := by
  have windowSwap :=
    SpineAtomSwap.swap (signature := adjointTripleModeSignature)
      StringTwoCell.unitLower StringTwoCell.counitUpper
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      []
  exact ⟨_, _, windowSwap, stringSpineAtomSwap_spineTraceEquiv windowSwap⟩

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the pure-block sort's TRANSPOSITION ATOM is ported to the string, colour-blind, at the
minimal widths.**  `stringSpineAtomSwap_spineTraceEquiv` lifts any adjacent horizontally-independent string swap into
`SpineTraceEquiv adjointTripleModeSignature` (the level `StringCellValleyTraceEquiv` runs on), riding the
`{signature}`-generic `SpineAtomSwap` / `AtomicTraceEquiv.toSpineTraceEquiv` / `SpineGodementStep` substrate — no
colour read.  Non-vacuity across the colour patterns: the two-colour window `(η, η')` at the mode-forced minimal
width (`stringTwoColourInterleavedWindow_spineTraceEquiv`), the GAP-0 same-colour window `(η, η)` the cell-level
far-commutation cannot reach (`stringSameColourAdjacentWindow_spineTraceEquiv`), and the pinned MIXED cup·cap window
`(η, ε')` that reorders though it cannot straighten (`stringPinnedMixedWindow_spineTraceEquiv`, the r6 pin governs
STRAIGHTEN not REORDER).  This is the composable atom the recon's route-(b) bubble sort iterates, discharged
generically.  `= true`. -/
def fxString_hasInterleavedWindowTransposition : Bool := true

/-- **OPEN (honest) — the transposition atom is ONE step; the pure-block SORT that closes
`StringCellValleyTraceEquiv` is NOT assembled; NO completeness flip.**  On top of
`stringSpineAtomSwap_spineTraceEquiv` the sort still needs: (1) the ARC-preservation of each swap
(`extractArc_eq_of_atomicTraceEquiv` is `adjunctionModeSignature`-hardcoded through
`arcSwapCorePackage_of_adjunctionSwap` — a colour-blind but un-ported cup/cap-arity arc dispatch); (2) the
bubble-to-front driver (`bubbleCupToFront`) and its termination; (3) the locate / tails-cancel crux reconstructing
the block arc equality from `diagram` + internal counts; (4) the valley-append `matchingOf`-split feeding per-block
`diagram` + length agreement (open even in the walking adjunction — `sameMatchingValleys_spineTraceEquiv` does not
claim it).  Piece I (`StringCellDescentStepOracle`) remains separately open.  These are the multi-round content;
this file lands only the transposition atom, so `fxString_hasAdjointTripleCompleteness` (in
`StringMatchingCompleteness`) is NOT moved and stays `false`, honestly, with the exact remaining sort bricks named.
`= false`. -/
def fxString_hasInterleavedWindowSortAssembly : Bool := false

end FX1Poly.Polygraph
