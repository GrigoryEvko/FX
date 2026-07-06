import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomCountTraceInvariance
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcTailsCancelAssembly

/-! # ArcCupTailsCancelCounts — the cup tails-cancel's TOTAL count legs discharge (peel campaign H, count rung P-5d-total)

The cup cancel's five field-agreements (`arcCupTailsCancel_ofDiagramAndCounts`) split into the diagram
leg, the two TOTAL count legs (`cupCount` / `capCount`), and the two per-port INTERNAL count legs.  The
two TOTAL legs are NOT orbit residuals — they follow from the whole-spine arc equality plus the head
being a cup, because the arc structure's total `cupCount` / `capCount` reflect the boundary-independent
cup / cap ATOM counts (`arcStructureOfSpineList_*Count`, re-derived here to keep the discharge chain off
the gate file), and those atom counts are trace-equivalence invariants
(`cupAtomCount_eq_of_atomicTraceEquiv`):

  * ★ `arcCupTailsCancel_countLegs_ofCupHead` — given the whole-spine arc equality at the seed and the
    located bubble's trace equivalence (second spine `~` head cup :: remainder), the tail and the
    remainder carry equal total cup and cap counts.  The head cup contributes `1` to the cup tally on
    both sides (cancelled by `Nat.succ` injectivity) and `0` to the cap tally, so the tails agree on
    both totals.

This leaves the cup cancel owing only the DIAGRAM leg (the parity campaign) and the two per-port
INTERNAL count legs (the leg-de-merge) — the genuine orbit residual.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The arc structure's total `cupCount` reflects the boundary-independent cup-atom count — re-derived
locally (the gate file `ArcReconstruction` owns the shared copy; the discharge chain must not import it,
or flipping the reconstruction marker would cycle). -/
private theorem cupCountReflect {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    (arcStructureOfSpineList bottomCount atoms).cupCount = cupAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).cupEventNodes.length = cupAtomCount atoms
  rw [processArcSpine_cupEventNodes_length]
  exact Nat.zero_add _

/-- The dual: the arc structure's total `capCount` reflects the boundary-independent cap-atom count. -/
private theorem capCountReflect {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    (arcStructureOfSpineList bottomCount atoms).capCount = capAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).capEventNodes.length = capAtomCount atoms
  rw [processArcSpine_capEventNodes_length]
  exact Nat.zero_add _

/-- A cup head contributes exactly one to the cup-atom count of the list it fronts. -/
private theorem cupAtomCount_consCup {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (headAtom : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode))
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2) :
    cupAtomCount (headAtom :: rest) = 1 + cupAtomCount rest := by
  dsimp only [cupAtomCount]
  have guardTrue :
      (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
    rw [hasCupDomArity, hasCupCodArity]
    rfl
  rw [if_pos guardTrue]

/-- A cup head contributes nothing to the cap-atom count of the list it fronts (its domain length is
`0`, not `2`). -/
private theorem capAtomCount_consCup {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (headAtom : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode))
    (hasCupDomArity : headAtom.generatorDom.length = 0) :
    capAtomCount (headAtom :: rest) = capAtomCount rest := by
  dsimp only [capAtomCount]
  have guardFalse :
      ¬ (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
    rw [hasCupDomArity]
    exact Bool.noConfusion
  rw [if_neg guardFalse]
  exact Nat.zero_add _

/-- Left-cancel a common leading `1` on `Nat`, hand-rolled through `add_comm` + `Nat.succ.inj` (the core
`Nat.add_left_cancel` leaks `propext`; `n + 1` is `Nat.succ n` definitionally). -/
private theorem natCancelLeadingOne {leftValue rightValue : Nat}
    (equalOneAdds : 1 + leftValue = 1 + rightValue) : leftValue = rightValue := by
  rw [Nat.add_comm 1 leftValue, Nat.add_comm 1 rightValue] at equalOneAdds
  exact Nat.succ.inj equalOneAdds

/-- ★ **The cup tails-cancel's total count legs discharge.**  For a cup-arity head, the whole-spine arc
equality (at the seed boundary `bottomCount`) plus the located bubble's trace equivalence (the second
spine is `AtomicTraceEquiv` to the head cup fronting the remainder) force the tail and the remainder to
carry equal TOTAL cup and cap counts at any target boundary: both total counts reflect the trace-invariant
atom counts, the head cup adds `1` to the cup tally (cancelled) and `0` to the cap tally. -/
theorem arcCupTailsCancel_countLegs_ofCupHead {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount targetBoundary : Nat)
    (headAtom : SpineAtom signature sourceMode targetMode)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList remainder : List (SpineAtom signature sourceMode targetMode))
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList)
    (atomicEquiv : AtomicTraceEquiv signature secondList (headAtom :: remainder)) :
    (arcStructureOfSpineList targetBoundary tailList).cupCount
        = (arcStructureOfSpineList targetBoundary remainder).cupCount
      ∧ (arcStructureOfSpineList targetBoundary tailList).capCount
          = (arcStructureOfSpineList targetBoundary remainder).capCount := by
  refine ⟨?_, ?_⟩
  · -- cup total: the head cup's shared `1` cancels
    rw [cupCountReflect targetBoundary tailList, cupCountReflect targetBoundary remainder]
    have wholeCupAgree : cupAtomCount (headAtom :: tailList) = cupAtomCount secondList := by
      have reflected := congrArg FullArcStructure.cupCount arcEqual
      rw [cupCountReflect bottomCount (headAtom :: tailList),
        cupCountReflect bottomCount secondList] at reflected
      exact reflected
    have secondCupAgree : cupAtomCount secondList = cupAtomCount (headAtom :: remainder) :=
      cupAtomCount_eq_of_atomicTraceEquiv atomicEquiv
    have tailPlusOne : 1 + cupAtomCount tailList = 1 + cupAtomCount remainder := by
      rw [← cupAtomCount_consCup headAtom tailList hasCupDomArity hasCupCodArity,
        ← cupAtomCount_consCup headAtom remainder hasCupDomArity hasCupCodArity]
      exact wholeCupAgree.trans secondCupAgree
    exact natCancelLeadingOne tailPlusOne
  · -- cap total: the head cup contributes nothing, so the totals agree directly
    rw [capCountReflect targetBoundary tailList, capCountReflect targetBoundary remainder]
    have wholeCapAgree : capAtomCount (headAtom :: tailList) = capAtomCount secondList := by
      have reflected := congrArg FullArcStructure.capCount arcEqual
      rw [capCountReflect bottomCount (headAtom :: tailList),
        capCountReflect bottomCount secondList] at reflected
      exact reflected
    have secondCapAgree : capAtomCount secondList = capAtomCount (headAtom :: remainder) :=
      capAtomCount_eq_of_atomicTraceEquiv atomicEquiv
    rw [← capAtomCount_consCup headAtom tailList hasCupDomArity,
      ← capAtomCount_consCup headAtom remainder hasCupDomArity]
    exact wholeCapAgree.trans secondCapAgree

/-- ★ **The cup tails-cancel reduced to its three CONTENTFUL legs.**  Packages the two orbit-free total
count legs (`arcCupTailsCancel_countLegs_ofCupHead`) into the five-field seam
(`arcCupTailsCancel_ofDiagramAndCounts`): for a cup head with the whole-spine arc equality and the located
bubble's trace equivalence, the full `tailsCancel` (`arc tailList = arc remainder` at `targetBoundary`)
follows from ONLY the diagram agreement and the two per-port internal-count agreements — the two count
totals are supplied internally.  This is the general-located-cup analog of
`pureCupTailsCancel_ofDiagramAndInternalCup`: the orbit-witness builder consumes exactly these three
contentful legs, with the count totals already discharged. -/
theorem arcCupTailsCancel_ofDiagramAndInternal_ofCupHead
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount targetBoundary : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList remainder :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList)
    (atomicEquiv : AtomicTraceEquiv adjunctionModeSignature secondList (headAtom :: remainder))
    (diagramAgree : (arcStructureOfSpineList targetBoundary tailList).diagram
        = (arcStructureOfSpineList targetBoundary remainder).diagram)
    (internalCupCountsAgree : (arcStructureOfSpineList targetBoundary tailList).internalCupCounts
        = (arcStructureOfSpineList targetBoundary remainder).internalCupCounts)
    (internalCapCountsAgree : (arcStructureOfSpineList targetBoundary tailList).internalCapCounts
        = (arcStructureOfSpineList targetBoundary remainder).internalCapCounts) :
    arcStructureOfSpineList targetBoundary tailList
      = arcStructureOfSpineList targetBoundary remainder := by
  obtain ⟨cupCountAgree, capCountAgree⟩ :=
    arcCupTailsCancel_countLegs_ofCupHead bottomCount targetBoundary headAtom
      hasCupDomArity hasCupCodArity tailList secondList remainder arcEqual atomicEquiv
  exact arcCupTailsCancel_ofDiagramAndCounts targetBoundary tailList remainder
    diagramAgree cupCountAgree capCountAgree internalCupCountsAgree internalCapCountsAgree

/-! ## Honesty marker -/

/-- **Honesty marker — the cup tails-cancel's TOTAL count legs are SHIPPED (peel campaign H, count rung
P-5d-total).**  `arcCupTailsCancel_countLegs_ofCupHead`: for a cup head, the whole-spine arc equality plus
the located bubble's trace equivalence force the tail and the remainder to agree on the total cup and cap
counts — the totals reflect the trace-invariant atom counts, the head cup adds `1` to the cup tally
(cancelled) and `0` to the cap tally.  `arcCupTailsCancel_ofDiagramAndInternal_ofCupHead` then packages
those totals into the five-field seam, reducing the full `tailsCancel` to ONLY the diagram leg and the two
per-port INTERNAL count legs (the orbit-witness builder's exact residual).  What this marker does NOT
claim: the DIAGRAM leg (the parity campaign) nor the per-port INTERNAL count legs (`internalCupCounts` /
`internalCapCounts`, the leg-de-merge) — those remain the orbit residual.  `= true`. -/
def fxMode_hasArcCupTailsCancelCounts : Bool := true

end FX1Poly.Polygraph
