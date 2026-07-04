import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain

/-! # ArcChainedExtraction — the chained assembly: seed cell reconstruction reduced to ONE obligation (ARC-3)

`ArcReconstruction` refuted the RAW-list head-extraction residual (`not_arcHeadExtractionMatching` — the
arc fold is right-context blind) and even the general-signature cell form (`not_arcCellReconstruction` —
the arity-`0 ⇒ 0` box leaks); it pinned the genuine residual as the cup/cap-seed cell reconstruction.
The correction the refutations dictate is the CHAIN discipline: cell spines are boundary-chained
(`RawTwoCellExpr.spineBoundaryChained_spine`), and on chained lists the running boundary + the arc
read-offs DETERMINE atoms (ARC-2a, `adjunctionSpineAtom_eq_of_readOffs`).  This brick re-runs the
matching assembly ON the chained fragment:

  * `SpineArcHeadExtractionChained` — the CORRECTED per-head geometric obligation: both lists chained at
    the running boundary, equal arc structures; the head extracts with a realized bubble, a REMAINDER
    CHAINED at the head's target boundary, and the tails arc-equal AT THAT boundary (the boundary moves
    with the peel — the raw-list form's fixed `bottomCount` was part of the over-quantification);
  * `spineTraceMatched_of_chainedHeadExtraction` — the assembly, by structural induction on the first
    list with the boundary generalized: nil closes by nil-inversion, cons peels via the obligation and
    recurses at the head's target boundary;
  * ★ `adjunctionArcCellReconstruction_of_chainedExtraction` — the seed reduction: granted the chained
    extraction at every boundary, `ArcCellReconstruction adjunctionModeSignature` FOLLOWS (cell spines
    are chained at `sourcePath.length`, nil-inversion is the shipped `spineArcNilInversion_adjunction`,
    and the matching assembles into the trace equivalence).

After this brick the ENTIRE remaining reconstruction is the single Prop
`SpineArcHeadExtractionChained adjunctionModeSignature` (at every boundary) — the per-head cup/cap peel,
the genuine Joyal-Street geometric core (upcoming bricks: path splitting, the realized disjoint-window
swap, the peel itself).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The CHAINED per-head geometric extraction obligation** — the correction of the refuted raw-list
`SpineArcHeadExtraction`.  Both lists are boundary-chained at the running boundary `bottomCount` and
arc-equal there; then the head extracts from the second list via a realized `SpineTraceEquiv` bubble,
leaving a remainder that is (i) CHAINED at the head's target boundary and (ii) arc-equal to the tail AT
that target boundary.  The boundary moves with the peel: the raw-list form compared tails at the ORIGINAL
`bottomCount`, which is geometric nonsense once the head has fired — part of the over-quantification the
refutations exposed.  On this chained fragment the arc read-offs determine atoms (ARC-2a), so the
obligation is exactly the faithful per-head Joyal-Street realizability. -/
def SpineArcHeadExtractionChained (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) : Prop :=
  ∀ (headAtom : SpineAtom signature overallSource overallTarget)
    (tailList secondList : List (SpineAtom signature overallSource overallTarget)),
    SpineBoundaryChained bottomCount (headAtom :: tailList) →
    SpineBoundaryChained bottomCount secondList →
    arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList →
    ∃ matchedRemainder,
      SpineTraceEquiv signature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder

/-- ★ **The chained head-extraction matching, assembled.**  Structural induction on the first spine list
with the running boundary GENERALIZED (the peel moves it to the head's target boundary): the empty case
closes by nil-inversion, the cons case peels the head via the chained obligation (a realized bubble, a
chained remainder, tails arc-equal at the new boundary) and recurses there.  The chained analogue of
`spineTraceMatched_of_headExtraction` — the trace algebra is again NOT the obstruction; granted the
per-head chained peel, the full matching is mechanical. -/
theorem spineTraceMatched_of_chainedHeadExtraction {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (chainedExtraction : ∀ (bottomCount : Nat),
      SpineArcHeadExtractionChained signature (overallSource := overallSource)
        (overallTarget := overallTarget) bottomCount)
    (nilInversion : ∀ (bottomCount : Nat),
      SpineArcNilInversion signature (overallSource := overallSource)
        (overallTarget := overallTarget) bottomCount) :
    ∀ {firstList : List (SpineAtom signature overallSource overallTarget)}
      {bottomCount : Nat}
      {secondList : List (SpineAtom signature overallSource overallTarget)},
      SpineBoundaryChained bottomCount firstList →
      SpineBoundaryChained bottomCount secondList →
      arcStructureOfSpineList bottomCount firstList
          = arcStructureOfSpineList bottomCount secondList →
      SpineTraceMatched signature firstList secondList := by
  intro firstList
  induction firstList with
  | nil =>
      intro bottomCount secondList _ _ arcEqual
      rw [nilInversion bottomCount secondList arcEqual]
      exact SpineTraceMatched.nil
  | cons headAtom tailList inductionHypothesis =>
      intro bottomCount secondList firstChained secondChained arcEqual
      obtain ⟨matchedRemainder, headBubble, remainderChained, tailArcEqual⟩ :=
        chainedExtraction bottomCount headAtom tailList secondList firstChained secondChained
          arcEqual
      exact SpineTraceMatched.cons headAtom headBubble
        (inductionHypothesis (spineBoundaryChained_tail firstChained).2 remainderChained
          tailArcEqual)

/-- ★ **The seed reduction: `ArcCellReconstruction adjunctionModeSignature` from the chained peel.**
Granted the chained per-head extraction at every boundary, the cup/cap-seed cell reconstruction follows:
parallel cells' spines are boundary-chained at `sourcePath.length`
(`RawTwoCellExpr.spineBoundaryChained_spine`), the arc structures compare at exactly that boundary
(`arcStructureOf` is definitionally the spine-list fold there), nil-inversion is the shipped
`spineArcNilInversion_adjunction`, and the assembled matching lands the trace equivalence via
`spineTraceEquiv_of_traceMatched`.  The ENTIRE remaining reconstruction is therefore the single chained
obligation — the per-head cup/cap peel. -/
theorem adjunctionArcCellReconstruction_of_chainedExtraction
    (chainedExtraction : ∀ {sourceMode targetMode : adjunctionGraph.Mode} (bottomCount : Nat),
      SpineArcHeadExtractionChained adjunctionModeSignature
        (overallSource := sourceMode) (overallTarget := targetMode) bottomCount) :
    ArcCellReconstruction adjunctionModeSignature :=
  fun firstCell secondCell arcEqual =>
    spineTraceEquiv_of_traceMatched
      (spineTraceMatched_of_chainedHeadExtraction
        (fun bottomCount => chainedExtraction bottomCount)
        (fun bottomCount => spineArcNilInversion_adjunction bottomCount)
        firstCell.spineBoundaryChained_spine
        secondCell.spineBoundaryChained_spine
        arcEqual)

/-! ## Honesty marker -/

/-- **Honesty marker — the CHAINED assembly is SHIPPED (ARC-3), reducing the seed reconstruction to ONE
obligation.**  `spineTraceMatched_of_chainedHeadExtraction` assembles the full head-extraction matching
on the boundary-chained fragment (boundary generalized through the peel), and
`adjunctionArcCellReconstruction_of_chainedExtraction` lands `ArcCellReconstruction
adjunctionModeSignature` from it (spines chained by `RawTwoCellExpr.spineBoundaryChained_spine`,
nil-inversion by `spineArcNilInversion_adjunction`).  The SOLE residual is now
`SpineArcHeadExtractionChained adjunctionModeSignature` at every boundary — the per-head cup/cap peel
(ARC-2b: path splitting + the realized disjoint-window swap + the peel).  NOT claimed: that obligation
itself; `fxMode_hasArcCellReconstruction` stays `false` until it discharges.  `= true`. -/
def fxMode_hasChainedArcExtractionAssembly : Bool := true

end FX1Poly.Polygraph
