import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseOrbitReduction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadDischarge

/-! # ArcCupReselectionOrbit — the orbit witness from the leg-aligned re-selection (tailsCancel is FREE)

The cup-head crux (`ArcCupOrbitWitness`, `ArcCupCaseOrbitReduction.lean:35`) carries FIVE pins; the
shipped locator `arcCupCase_locateAndBubble` supplies THREE (split + `BubblesToFront` + `movedDomPin`),
leaving the two COUPLED pins `windowPin` + `tailsCancel`.  A ~30-file campaign ground `tailsCancel`
down through folded diagram/count legs.  This brick takes the SHORT route the cap discharge already
uses: given the leg-aligned re-selection as an `AtomicTraceEquiv tailList (movedPrefixAtoms ++
suffixAtoms)`, `tailsCancel` is IMMEDIATE — `arcStructureOfSpineList` is DEFINITIONALLY `extractArc` at
the canonical seed (`SpineTraceDecision.lean:175`), and `extractArc_eq_of_atomicTraceEquiv`
(`ArcSwapPeel.lean:29`, the cap discharge's own tool) turns any atomic trace-equivalence into equal arc
structures.  So the whole `ArcCupOrbitWitness` assembles from the three located pins + `windowPin` + the
ONE re-selection `AtomicTraceEquiv` — no folded legs.  This isolates the entire cup crux to producing
that re-selection (the leg-aligned cup, `arcCupReselection_exists`), the genuine planar content.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range length plumbing (private copy — the seed files' kits are file-private) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The orbit witness from the re-selection -/

/-- ★ **The cup orbit witness from the leg-aligned re-selection.**  Given the located split/bubble/dom
pins (from the shipped `arcCupCase_locateAndBubble`), the window pin, and — crucially — the leg-aligned
re-selection as an `AtomicTraceEquiv tailList (movedPrefixAtoms ++ suffixAtoms)`, the full
`ArcCupOrbitWitness` follows: `tailsCancel` is `extractArc_eq_of_atomicTraceEquiv` at the canonical
`headAtom.codBoundaryLength` seed (the arc structure is trace-invariant), no folded legs needed.  This
reduces the whole cup case to producing the re-selection (the leg-aligned cup). -/
theorem arcCupOrbitWitness_ofReselection
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList
      prefixAtoms suffixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (toucherAtom movedTarget :
      SpineAtom adjunctionModeSignature overallSource overallTarget)
    (doesSplitSpine : secondList = prefixAtoms ++ toucherAtom :: suffixAtoms)
    (bubble : BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms)
    (movedDomPin : movedTarget.generatorDom.length = 0)
    (windowPin : movedTarget.leftContext.length = headAtom.leftContext.length)
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (reselection : AtomicTraceEquiv adjunctionModeSignature tailList
      (movedPrefixAtoms ++ suffixAtoms)) :
    ArcCupOrbitWitness headAtom tailList secondList := by
  have hasPositiveWidth : 0 < headAtom.codBoundaryLength := by
    show 0 < headAtom.leftContext.length + headAtom.generatorCod.length
      + headAtom.rightContext.length
    rw [hasCupCodArity]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos (headAtom.leftContext.length + 1))
      (Nat.le_add_right (headAtom.leftContext.length + 2) headAtom.rightContext.length)
  have seedLengthEq :
      (ArcWireState.mk (List.range headAtom.codBoundaryLength) [] headAtom.codBoundaryLength
        0 [] []).openWires.length = headAtom.codBoundaryLength :=
    rangeLength headAtom.codBoundaryLength
  have tailsCancel : arcStructureOfSpineList headAtom.codBoundaryLength tailList
      = arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms) :=
    extractArc_eq_of_atomicTraceEquiv reselection
      (ArcWireState.mk (List.range headAtom.codBoundaryLength) [] headAtom.codBoundaryLength 0 [] [])
      headAtom.codBoundaryLength headAtom.codBoundaryLength
      (arcStateFresh_initial headAtom.codBoundaryLength)
      (isUnionFindForest_initialLinks headAtom.codBoundaryLength) hasPositiveWidth
      (Nat.le_refl headAtom.codBoundaryLength) seedLengthEq tailChained
  exact ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, bubble, movedDomPin, windowPin, tailsCancel⟩

/-- ★ **The front-located cup's orbit witness (the innermost-cup induction shape).**  When the
leg-aligned cup is ALREADY at the front of `secondList` (`secondList = toucherAtom :: suffixAtoms`),
the bubble is `BubblesToFront.nil` — the moved target IS the toucher, untouched — so `windowPin`
reduces to `toucherAtom.leftContext.length = headAtom.leftContext.length` (no bubble shift) and the
re-selection is `AtomicTraceEquiv tailList suffixAtoms`.  This is the shape an innermost cup takes
after bubbling to front (the adjacent-matched-pair the short-chord lemma locates). -/
theorem arcCupOrbitWitness_ofFrontReselection
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList suffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (toucherAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (toucherIsCup : toucherAtom.generatorDom.length = 0)
    (windowPin : toucherAtom.leftContext.length = headAtom.leftContext.length)
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (reselection : AtomicTraceEquiv adjunctionModeSignature tailList suffixAtoms) :
    ArcCupOrbitWitness headAtom tailList (toucherAtom :: suffixAtoms) :=
  arcCupOrbitWitness_ofReselection headAtom hasCupCodArity tailList
    (toucherAtom :: suffixAtoms) [] suffixAtoms [] toucherAtom toucherAtom
    rfl BubblesToFront.nil toucherIsCup windowPin tailChained reselection

/-! ## Honesty marker -/

/-- **Honesty marker — the orbit witness assembles from the re-selection, tailsCancel FREE.**
`arcCupOrbitWitness_ofReselection`: given the three located pins (split/bubble/dom), the window pin, and
the leg-aligned re-selection as an `AtomicTraceEquiv tailList (movedPrefixAtoms ++ suffixAtoms)`, the
full `ArcCupOrbitWitness` follows — `tailsCancel` is `extractArc_eq_of_atomicTraceEquiv` at the
`codBoundaryLength` seed (arc structure is trace-invariant), NO folded diagram/count legs.  What this
marker does NOT claim: producing the re-selection itself (`arcCupReselection_exists` — the leg-aligned
cup, the genuine planar content) nor the window pin from atom rigidity.  `= true`. -/
def fxMode_hasArcCupReselectionOrbit : Bool := true

end FX1Poly.Polygraph
