import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapBoundary
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration

/-! # WalkingAdjunction/ArcChainedReconstruction — boundary-chain transfer along the bubble

CORRECTION NOTE.  This file originally re-derived the chained head-extraction reduction,
duplicating the earlier-shipped `WalkingAdjunction/ArcChainedExtraction.lean` — which is the
CANONICAL reduction: its residual `SpineArcHeadExtractionChained` compares the peeled tails at
the MOVED boundary `headAtom.codBoundaryLength` (the geometrically faithful comparison once the
head has fired), where the duplicate compared them at the original `bottomCount`.  The
duplicated declarations (`ChainedSpineArcHeadExtraction`,
`spineTraceMatched_of_chainedHeadExtraction` — a latent name clash with the canonical file —
`arcCellReconstruction_adjunction_of_chainedExtraction`, and the marker) are retired in favor
of the canonical versions.

What remains is the one lemma with no prior counterpart: the boundary chain transfers along a
`SpineTraceEquiv`.  Whoever proves the canonical residual will realize the head bubble as a
`SpineTraceEquiv` and needs the bubbled list's chainedness to move along it — this is that
transfer, the `SpineTraceEquiv` face of the shipped `AtomicTraceEquiv` transfer through the
FREE-5 bridge.

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

end FX1Poly.Polygraph
