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

/-! ## The front case: `windowPin` IS head-identity, so the residual is purely the tail re-selection

ANGLE C asked whether the arc-equality FORCES the front cup of the second spine to share the head cup's
window.  It does NOT: unlike a CAP — whose window `bubblesToFront_ofArcPairCapWindow` reads straight off
the two BOTTOM ports it consumes (`natListGetAt (List.range bottomCount) w = w`, the identity below the
seed width), boundary data that survives in `diagram.partner` — a CUP CREATES two FRESH legs (`stepCupArc`,
domain arity `0`) and consumes NO bottom port, so its window has no bottom-boundary anchor.  It manifests
only in the TOP-boundary order, and the whole tail permutes/consumes those legs before the boundary is
read; the surviving flat carrier (`diagram.partner` + `internalCupCounts`) is cup-blind to it, and the
event-node ids do not transfer across arc-equality.  So `windowPin` is genuinely orbit content: the
re-selection must CHOOSE the representative in the trace orbit where the head cup sits at the front at its
window — it is not read off the arc.  These two bricks record what the front case DOES pin, once `windowPin`
is granted. -/

/-- ★ **In the front case, `windowPin` IS full head-identity (seed rigidity).**  Two walking-adjunction
cup atoms firing at the same running boundary `bottomCount` (so their domain-boundary lengths agree) whose
left windows agree ARE the same atom — `adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths` upgrades
the length-only window match to atom equality (the cup codomain arities are `2` on both by the arity
dichotomy, the cap branch dying on `2 = 0`).  So the front-case `windowPin` — the sole orbit-dependent pin
the re-selection supplies — is EQUIVALENT to the front cup BEING the head cup: no residual planar freedom
survives a matched window. -/
theorem frontCupToucher_eq_head_ofWindowPin
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (headAtom toucherAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (headFires : headAtom.domBoundaryLength = bottomCount)
    (toucherFires : toucherAtom.domBoundaryLength = bottomCount)
    (headCupDom : headAtom.generatorDom.length = 0)
    (toucherCupDom : toucherAtom.generatorDom.length = 0)
    (windowPin : toucherAtom.leftContext.length = headAtom.leftContext.length) :
    toucherAtom = headAtom := by
  have headCod : headAtom.generatorCod.length = 2 := by
    cases adjunctionSpineAtom_isCupOrCap headAtom with
    | inl cupArity => exact cupArity.2
    | inr capArity => exact Nat.noConfusion (capArity.1.symm.trans headCupDom)
  have toucherCod : toucherAtom.generatorCod.length = 2 := by
    cases adjunctionSpineAtom_isCupOrCap toucherAtom with
    | inl cupArity => exact cupArity.2
    | inr capArity => exact Nat.noConfusion (capArity.1.symm.trans toucherCupDom)
  exact adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths toucherAtom headAtom
    (toucherFires.trans headFires.symm) windowPin
    (toucherCupDom.trans headCupDom.symm) (toucherCod.trans headCod.symm)

/-- ★ **The front-case orbit witness with the head literally at the front (`windowPin` FREE).**  The
sharpest shape of the cup front case: when the second spine is `headAtom :: suffixAtoms` — the head cup
ALREADY at the front, which by `frontCupToucher_eq_head_ofWindowPin` is exactly what a granted `windowPin`
means — the orbit witness needs ONLY the tail re-selection `AtomicTraceEquiv tailList suffixAtoms`:
`windowPin` collapses to `rfl` and the bubble is `BubblesToFront.nil`.  This isolates the entire front-case
residual to the atomic re-selection that brings the head to the front. -/
theorem arcCupOrbitWitness_ofFrontHead
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList suffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (reselection : AtomicTraceEquiv adjunctionModeSignature tailList suffixAtoms) :
    ArcCupOrbitWitness headAtom tailList (headAtom :: suffixAtoms) :=
  arcCupOrbitWitness_ofFrontReselection headAtom hasCupCodArity tailList suffixAtoms
    headAtom hasCupDomArity rfl tailChained reselection

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
