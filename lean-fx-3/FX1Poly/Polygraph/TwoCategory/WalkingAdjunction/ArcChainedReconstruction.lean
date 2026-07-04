import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapBoundary
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction

/-! # WalkingAdjunction/ArcChainedReconstruction — the reconstruction reduced to the CHAINED residual

The spine-list head extraction is refuted even at the cup/cap seed by the arc fold's
right-context blindness — raw atom lists carry arbitrary right contexts the fold never reads.
Cells do not: their spines are BOUNDARY-CHAINED (`RawTwoCellExpr.spineBoundaryChained_spine`),
which pins every atom's window inside the running boundary.  This file re-runs the
head-extraction assembly with chainedness threaded through the induction — chainedness of the
bubbled remainder comes from the boundary-chain transfer along the bubble itself — reducing the
genuine residual `ArcCellReconstruction adjunctionModeSignature` to ONE chained per-head
geometric input, `ChainedSpineArcHeadExtraction`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The boundary chain transfers along the Godement-closure trace equivalence — the
`SpineTraceEquiv` face of the shipped `AtomicTraceEquiv` transfer, through the FREE-5 bridge. -/
theorem spineBoundaryChained_iff_of_spineTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : SpineTraceEquiv signature firstList secondList) :
    ∀ boundaryLength : Nat,
      SpineBoundaryChained boundaryLength firstList
        ↔ SpineBoundaryChained boundaryLength secondList :=
  spineBoundaryChained_iff_of_atomicTraceEquiv traceEquiv.toAtomicTraceEquiv

/-- **The CHAINED per-head geometric residual.**  Head extraction restricted to
boundary-chained lists: whenever two chained lists share an arc structure and the first is
nonempty, its head atom bubbles to the front of the second (a realized `SpineTraceEquiv`)
leaving a remainder whose arc structure matches the first's tail.  The chainedness premises are
exactly what closes the right-context blindness that refutes the unrestricted form
(`not_arcHeadExtractionMatching`) — a chained atom's window sits inside the running boundary,
so the arc fold's reads are faithful. -/
def ChainedSpineArcHeadExtraction (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) : Prop :=
  ∀ (boundaryLength : Nat)
    (headAtom : SpineAtom signature overallSource overallTarget)
    (tailList secondList : List (SpineAtom signature overallSource overallTarget)),
    SpineBoundaryChained boundaryLength (headAtom :: tailList) →
    SpineBoundaryChained boundaryLength secondList →
    arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList →
    ∃ matchedRemainder, SpineTraceEquiv signature secondList (headAtom :: matchedRemainder)
      ∧ arcStructureOfSpineList bottomCount tailList
          = arcStructureOfSpineList bottomCount matchedRemainder

/-- ★ **The head-extraction matching, assembled from the CHAINED geometric inputs.**  The same
structural induction as `spineTraceMatched_of_headExtraction`, threading chainedness: the
first list's tail is chained by inversion, and the bubbled remainder is chained because the
bubble is a trace equivalence and the boundary chain transfers along it. -/
theorem spineTraceMatched_of_chainedHeadExtraction {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} {bottomCount : Nat}
    (headExtraction : ChainedSpineArcHeadExtraction signature (overallSource := overallSource)
      (overallTarget := overallTarget) bottomCount)
    (nilInversion : SpineArcNilInversion signature (overallSource := overallSource)
      (overallTarget := overallTarget) bottomCount) :
    ∀ (firstList : List (SpineAtom signature overallSource overallTarget))
      {boundaryLength : Nat}
      (secondList : List (SpineAtom signature overallSource overallTarget)),
      SpineBoundaryChained boundaryLength firstList →
      SpineBoundaryChained boundaryLength secondList →
      arcStructureOfSpineList bottomCount firstList
          = arcStructureOfSpineList bottomCount secondList →
      SpineTraceMatched signature firstList secondList := by
  intro firstList
  induction firstList with
  | nil =>
      intro boundaryLength secondList _ _ arcEqual
      rw [nilInversion secondList arcEqual]
      exact SpineTraceMatched.nil
  | cons headAtom tailList inductionHypothesis =>
      intro boundaryLength secondList chainedFirst chainedSecond arcEqual
      obtain ⟨matchedRemainder, headBubble, tailArcEqual⟩ :=
        headExtraction boundaryLength headAtom tailList secondList
          chainedFirst chainedSecond arcEqual
      obtain ⟨_, tailChained⟩ := spineBoundaryChained_tail chainedFirst
      have chainedBubbled :=
        (spineBoundaryChained_iff_of_spineTraceEquiv headBubble boundaryLength).mp chainedSecond
      obtain ⟨_, remainderChained⟩ := spineBoundaryChained_tail chainedBubbled
      exact SpineTraceMatched.cons headAtom headBubble
        (inductionHypothesis matchedRemainder tailChained remainderChained tailArcEqual)

/-- ★ **The adjunction cell reconstruction, GATED on the chained residual only.**  Cells'
spines are boundary-chained at the source boundary and `arcStructureOf` is definitionally the
spine-list fold at `sourcePath.length`, so the chained assembly plus the seed nil-inversion
land `ArcCellReconstruction adjunctionModeSignature` from `ChainedSpineArcHeadExtraction`
alone. -/
theorem arcCellReconstruction_adjunction_of_chainedExtraction
    (headExtraction : ∀ (sourceMode targetMode : AdjunctionMode) (bottomCount : Nat),
      ChainedSpineArcHeadExtraction adjunctionModeSignature
        (overallSource := sourceMode) (overallTarget := targetMode) bottomCount) :
    ArcCellReconstruction adjunctionModeSignature := by
  intro sourceMode targetMode sourcePath targetPath firstCell secondCell arcEqual
  exact spineTraceEquiv_of_traceMatched
    (spineTraceMatched_of_chainedHeadExtraction
      (headExtraction sourceMode targetMode sourcePath.length)
      (spineArcNilInversion_adjunction sourcePath.length)
      firstCell.spine secondCell.spine
      (RawTwoCellExpr.spineBoundaryChained_spine firstCell)
      (RawTwoCellExpr.spineBoundaryChained_spine secondCell)
      arcEqual)

/-- **Honesty marker — the reconstruction is REDUCED to the chained per-head residual.**
`arcCellReconstruction_adjunction_of_chainedExtraction` gates the genuine completeness residual
`ArcCellReconstruction adjunctionModeSignature` on `ChainedSpineArcHeadExtraction` alone: the
trace algebra, the nil inversion, the cell chainedness, and the chained-remainder threading
(boundary-chain transfer along the bubble) are all discharged.  What this marker does NOT
claim: `ChainedSpineArcHeadExtraction` itself — locating the head atom's arc in the second
chained list and bubbling it to the front through the shipped swap kit
(`extractArc_eq_of_atomicTraceEquiv` guards the remainder's arc match) — and hence the
`fxMode_hasArcCellReconstruction` flip stays pending on that one geometric core.  `= true`. -/
def fxMode_hasChainedArcReconstructionReduction : Bool := true

end FX1Poly.Polygraph
