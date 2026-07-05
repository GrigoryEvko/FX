import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcChainedExtraction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadDischarge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # ArcHeadExtractionArityDispatch — the cup/cap arity dispatch closing the chained obligation

Every generator of the walking adjunction is a cup (`0 ⇒ 2`) or a cap (`2 ⇒ 0`)
(`adjunctionSpineAtom_hasCupOrCapArity`), so the single residual
`SpineArcHeadExtractionChained` splits cleanly by the head's arity: the cap branch is the
shipped `spineArcHeadExtractionChained_ofCapArity`, the cup branch is the peel campaign's one
open crux (the orbit-form discharge, #2152).  This brick ships the dispatch — the whole
obligation, and hence `ArcCellReconstruction`, follows from the cup case ALONE.

  * `spineArcHeadExtractionChained_ofArityDispatch` — one `SpineArcHeadExtractionChained` at a
    fixed boundary from the cup case (as a hypothesis) plus the shipped cap case, by casing on
    the head's cup/cap arity;
  * `adjunctionArcCellReconstruction_ofCupExtraction` — the reduction target for the flip:
    `ArcCellReconstruction adjunctionModeSignature` FOLLOWS from the cup-arity head extraction at
    every boundary, feeding the dispatch through `adjunctionArcCellReconstruction_of_chainedExtraction`.

After this brick the ENTIRE walking-adjunction cell reconstruction rests on exactly the cup-head
extraction (`cupHeadExtractionConclusion_ofLocatedBubbleAndCancel` reduces THAT to the located
bubble + the cancel — the orbit).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup/cap arity dispatch for one chained head extraction.**  At a fixed running
boundary, the cup case (supplied as a hypothesis with cup arity `(0, 2)`) plus the shipped cap
case discharge the full `SpineArcHeadExtractionChained`: the head atom is a cup or a cap
(`adjunctionSpineAtom_hasCupOrCapArity`), and each branch hands off to its case. -/
theorem spineArcHeadExtractionChained_ofArityDispatch
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (cupCase :
      ∀ (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget),
        headAtom.generatorDom.length = 0 → headAtom.generatorCod.length = 2 →
        ∀ (tailList secondList :
            List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
          SpineBoundaryChained bottomCount (headAtom :: tailList) →
          SpineBoundaryChained bottomCount secondList →
          arcStructureOfSpineList bottomCount (headAtom :: tailList)
              = arcStructureOfSpineList bottomCount secondList →
          ∃ matchedRemainder,
            SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
              ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
              ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
                  = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder) :
    SpineArcHeadExtractionChained adjunctionModeSignature
      (overallSource := overallSource) (overallTarget := overallTarget) bottomCount := by
  intro headAtom tailList secondList firstChained secondChained arcEqual
  cases adjunctionSpineAtom_hasCupOrCapArity headAtom with
  | inl cupArity =>
      exact cupCase headAtom cupArity.1 cupArity.2 tailList secondList
        firstChained secondChained arcEqual
  | inr capArity =>
      exact spineArcHeadExtractionChained_ofCapArity bottomCount headAtom
        capArity.1 capArity.2 tailList secondList firstChained secondChained arcEqual

/-- ★ **The seed reconstruction from the cup-head extraction alone.**  Granted the cup-arity head
extraction at every boundary, the arity dispatch fills in the cap case (shipped) and
`adjunctionArcCellReconstruction_of_chainedExtraction` lands
`ArcCellReconstruction adjunctionModeSignature`.  This is the flip's reduction target: the whole
walking-adjunction cell reconstruction rests on exactly the cup-head extraction crux. -/
theorem adjunctionArcCellReconstruction_ofCupExtraction
    (cupExtraction :
      ∀ {sourceMode targetMode : adjunctionGraph.Mode} (bottomCount : Nat)
        (headAtom : SpineAtom adjunctionModeSignature sourceMode targetMode),
        headAtom.generatorDom.length = 0 → headAtom.generatorCod.length = 2 →
        ∀ (tailList secondList :
            List (SpineAtom adjunctionModeSignature sourceMode targetMode)),
          SpineBoundaryChained bottomCount (headAtom :: tailList) →
          SpineBoundaryChained bottomCount secondList →
          arcStructureOfSpineList bottomCount (headAtom :: tailList)
              = arcStructureOfSpineList bottomCount secondList →
          ∃ matchedRemainder,
            SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
              ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
              ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
                  = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder) :
    ArcCellReconstruction adjunctionModeSignature :=
  adjunctionArcCellReconstruction_of_chainedExtraction
    (fun bottomCount =>
      spineArcHeadExtractionChained_ofArityDispatch bottomCount (cupExtraction bottomCount))

/-! ## Honesty marker -/

/-- **Honesty marker — the cup/cap arity dispatch is SHIPPED.**
`spineArcHeadExtractionChained_ofArityDispatch` splits the chained head-extraction obligation by
the head's cup/cap arity (`adjunctionSpineAtom_hasCupOrCapArity`), routing the cap branch to the
shipped `spineArcHeadExtractionChained_ofCapArity` and the cup branch to a hypothesis;
`adjunctionArcCellReconstruction_ofCupExtraction` lands `ArcCellReconstruction
adjunctionModeSignature` from the cup-arity extraction alone.  The whole reconstruction now rests
on exactly the cup-head extraction.  What this marker does NOT claim: the cup case itself (the
orbit-form discharge — `cupHeadExtractionConclusion_ofLocatedBubbleAndCancel` reduces it to the
located bubble witness + the cancel, both the orbit's job) nor the flip
`fxMode_hasArcCellReconstruction`.  `= true`. -/
def fxMode_hasArcHeadExtractionArityDispatch : Bool := true

end FX1Poly.Polygraph
