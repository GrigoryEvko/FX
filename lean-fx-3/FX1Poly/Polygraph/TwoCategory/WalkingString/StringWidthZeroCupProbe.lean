import FX1Poly.Polygraph.TwoCategory.WalkingString.StringInterleavedWindowSort
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # WalkingString — the WIDTH-0 pure-cup determinacy TRUTH-PROBE on the hand-worked disjoint-cup pair
(FC-3 r10, B1)

Before assembling the full width-0 pure-cup sort (`StringWidthZeroPureCupDeterminacy`, the r10 budget defers it),
the recon calls for a truth-probe on a hand-worked disjoint-cup pair: two pure cups in the two firing orders a single
horizontal transposition relates.  This file lands that probe CONCRETELY.

  * ★ `stringWidthZeroPureCupDeterminacy_probe` — the two firing orders of a disjoint same-colour lower-cup pair
    (`η` producing `F·G` at width 0, `η` producing a second `F·G` disjointly) have the SAME width-0 boundary matching
    (`matchingOfSpineList 0`, by `rfl` — the union-find is BLIND to the order two disjoint cups fire) AND are
    `SpineTraceEquiv` (via the shipped transposition atom `stringSpineAtomSwap_spineTraceEquiv`).  So on this
    hand-worked instance the width-0 pure-cup determinacy CONCLUSION holds from its two governing hypotheses (equal
    matching ⟹ trace-equivalent) — a concrete confirmation that the colour-aware sort design is sound before the full
    fueled assembly.

The probe's two spine lists are EXACTLY the two sides of `SpineAtomSwap.swap unitLower unitLower` at the trivial
whisker/inert contexts, so the `SpineTraceEquiv` is one Godement step and the matching equality is a definitional
union-find computation — no colour read, no length rigidity.  The colour-aware SPECIES CONFIRMATION the general sort
performs at each peel (a located partner cup pinned to the head cup on their shared cod word) is discharged by the
keystone `stringSpineAtom_eq_of_wordReadOffs` (`StringSpineAtomWordPin`); this probe exhibits the reorder + matching
invariance the sort iterates the pin over.

## What this probe does NOT do (the flag stays `false` — honestly)

The probe is ONE hand-worked pair.  `StringWidthZeroPureCupDeterminacy` (the ∀-quantified determinacy over all
width-0 pure-cup pairs with equal matching) is NOT inhabited: the general sort still needs the partner-locate-by-chord
port and the matching-injective drop assembled on top of the keystone pin (the r10 budget defers them).  So
`fxString_hasAdjointTripleCompleteness` stays `false`; this file confirms the design on one instance, honestly.

Raw Lean 4 + Init; the probe is one `SpineAtomSwap.swap` plus a `rfl` matching computation.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The width-0 pure-cup determinacy truth-probe on the hand-worked disjoint-cup pair.**  Two lower cups `η`
(each producing `F·G`), fired disjointly in the two orders a single horizontal transposition relates: their width-0
boundary matchings COINCIDE (`matchingOfSpineList 0`, by `rfl` — the union-find is blind to the disjoint firing
order) and the two orders are `SpineTraceEquiv` (the shipped transposition atom).  This witnesses the width-0
determinacy conclusion on a concrete instance: equal matching ⟹ trace-equivalent, exactly as the full sub-producer
`StringWidthZeroPureCupDeterminacy` will assert once the fueled sort is assembled on top of the keystone pin. -/
theorem stringWidthZeroPureCupDeterminacy_probe :
    ∃ (cupFirst cupSecond :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base)),
      matchingOfSpineList 0 cupFirst = matchingOfSpineList 0 cupSecond
        ∧ SpineTraceEquiv adjointTripleModeSignature cupFirst cupSecond := by
  have windowSwap :=
    SpineAtomSwap.swap (signature := adjointTripleModeSignature)
      StringTwoCell.unitLower StringTwoCell.unitLower
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      []
  refine ⟨_, _, ?_, stringSpineAtomSwap_spineTraceEquiv windowSwap⟩
  rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 pure-cup determinacy TRUTH-PROBE lands on the hand-worked pair (FC-3 r10, B1).**
`stringWidthZeroPureCupDeterminacy_probe`: the two firing orders of a disjoint lower-cup pair have equal
`matchingOfSpineList 0` (by `rfl`, the union-find blind to disjoint firing order) and are `SpineTraceEquiv` (the
shipped transposition atom).  The concrete confirmation the recon called for — the colour-aware sort's reorder +
matching-invariance mechanism, exhibited on one instance, with the per-peel species confirmation delegated to the
keystone `stringSpineAtom_eq_of_wordReadOffs`.

  What this marker does NOT close: the ∀-quantified `StringWidthZeroPureCupDeterminacy`
  (`StringValleyDegenerateSplit`) is NOT inhabited — the general fueled sort (partner-locate-by-chord +
  matching-injective drop, on top of the keystone pin) is the r10-deferred content.  So
  `fxString_hasAdjointTripleCompleteness` stays `false`, honestly.  `= true`. -/
def fxString_hasWidthZeroCupDeterminacyProbe : Bool := true

end FX1Poly.Polygraph
