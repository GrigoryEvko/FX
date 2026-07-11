import FX1Poly.Polygraph.TwoCategory.WalkingString.StringInterleavedWindowSort

/-! # WalkingString — the TWO-SPECIES scrambled-pair matching-invariance TRUTH-PROBE (FC-3 r12, B3 gate)

The r10 probe (`stringWidthZeroPureCupDeterminacy_probe`, `StringWidthZeroCupProbe`) validated the width-0 sort's
reorder + matching-invariance mechanism on a SAME-species disjoint pair (two lower cups `η`, `η` at `base`, width 0).
Before the width-0 sort's partner-locate step (`matchingLocateAux` port) is attempted, the recon calls for the same
truth-probe on a TWO-species scrambled pair — the lower cup `η` (`id_base ⇒ F·G`) adjacent to the upper cup `η'`
(`id_tip ⇒ G·H`), the two colours the length-rigidity failure forces apart.  This file lands that probe CONCRETELY.

  * ★ `stringTwoSpeciesWindow_matchingInvariant` — the two firing orders of the mixed-species window `(η, η')`,
    separated by the single `F` strand the mode structure forces between a `base`-turnback and a `tip`-turnback, have
    the SAME boundary matching (`matchingOfSpineList 1`, by `rfl` — the union-find is BLIND to the firing order of two
    disjoint cups, EVEN across colours) AND are `SpineTraceEquiv` (the shipped transposition atom
    `stringSpineAtomSwap_spineTraceEquiv`).  So the mixed-species reorder + matching-invariance the sort's locate step
    relies on is confirmed on a concrete instance.

## The honest finding: two-species pairs are inherently width ≥ 1 (consistent with the B1 forcing adjudication)

The probe fires at width **1**, not 0 — and that is forced, not incidental.  A `SpineAtomSwap` of two DIFFERENT-colour
cups needs an inert middle strand connecting the left cup's `base` end to the right cup's `tip` end (the mode indices
`swapMiddleLeft = base`, `swapMiddleRight = tip`), so the inert path is a nonempty `base ⟶ tip` 1-cell (here `F`) —
never `nil`.  Hence there is NO width-0 two-species DISJOINT pair: at width 0 each endpoint admits exactly one cup
colour (`stringBaseCup_codForced` / `stringTipCup_codForced`, `StringWidthZeroForcingAdjudication`), so two colours
can co-occur in a width-0 valley only NESTED (through whiskering) — which is the width-0 SORT itself.  This probe thus
confirms the adjudication from the reorder side: mixed species reorder freely, but only once they are separated to a
genuine width ≥ 1 window.

## What this probe does NOT do (the flag stays `false` — honestly)

The probe is ONE hand-worked mixed-species pair.  The width-0 SORT's partner-locate recursion (`matchingLocateAux`
re-plumbed onto the shipped WORD-swap kit `spineAtomSwap_of_disjointWordWindows`, threading a `SpineBoundaryWordChained`
and re-establishing the shared top word after each bubble step) and the matching-injective drop
(`dropLastCup_matching_injective` port) are the r13+ content the recon budgets — this round ships the signature
strengthening (`StringWidthZeroPureCupDeterminacyShared`) and the top-word plumbing, not the sort.  So
`fxString_hasAdjointTripleCompleteness` stays `false`; this file confirms the mixed-species design on one instance,
honestly.

Raw Lean 4 + Init; the probe is one `SpineAtomSwap.swap` plus a `rfl` matching computation.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The two-species scrambled-pair matching-invariance truth-probe.**  The lower cup `η = StringTwoCell.unitLower`
(`id_base ⇒ F·G`) adjacent to the upper cup `η' = StringTwoCell.unitUpper` (`id_tip ⇒ G·H`), separated by the single
`F` strand the mode structure forces between the two turnbacks: their two firing orders have EQUAL boundary matching
(`matchingOfSpineList 1`, by `rfl` — the union-find is blind to the disjoint firing order across colours) and are
`SpineTraceEquiv` (the shipped transposition atom).  The mixed-species analog of the r10 same-species width-0 probe:
equal matching ⟹ trace-equivalent, on a concrete two-colour instance, exactly the mechanism the width-0 sort's
partner-locate step iterates once assembled on top of the keystone pin. -/
theorem stringTwoSpeciesWindow_matchingInvariant :
    ∃ (cupFirst cupSecond :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.tip)),
      matchingOfSpineList 1 cupFirst = matchingOfSpineList 1 cupSecond
        ∧ SpineTraceEquiv adjointTripleModeSignature cupFirst cupSecond := by
  have windowSwap :=
    SpineAtomSwap.swap (signature := adjointTripleModeSignature)
      StringTwoCell.unitLower StringTwoCell.unitUpper
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      (singletonModalityPath AdjointTripleModality.left)
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
      []
  refine ⟨_, _, ?_, stringSpineAtomSwap_spineTraceEquiv windowSwap⟩
  rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the TWO-SPECIES scrambled-pair matching-invariance truth-probe lands (FC-3 r12, B3 gate).**
`stringTwoSpeciesWindow_matchingInvariant`: the two firing orders of the mixed-species window `(η, η')` have equal
`matchingOfSpineList 1` (by `rfl`, the union-find blind to the disjoint firing order across colours) and are
`SpineTraceEquiv` (the shipped transposition atom).  The mixed-species analog of the r10 same-species probe — and the
honest finding that two-species pairs are inherently width ≥ 1 (no width-0 two-species disjoint pair exists,
consistent with the B1 forcing adjudication: at width 0 each endpoint admits one cup colour).

  What this marker does NOT close: the width-0 SORT's partner-locate recursion (`matchingLocateAux` re-plumbed onto the
  WORD-swap kit, threading `SpineBoundaryWordChained` + the shared top word) and the matching-injective drop are the
  r13+ content; this round ships the signature strengthening + top-word plumbing, not the sort.  So
  `fxString_hasAdjointTripleCompleteness` stays `false`, honestly.  `= true`. -/
def fxString_hasTwoSpeciesMatchingProbe : Bool := true

end FX1Poly.Polygraph
