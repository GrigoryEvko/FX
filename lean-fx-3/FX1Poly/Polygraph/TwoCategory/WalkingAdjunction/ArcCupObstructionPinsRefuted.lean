import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCancelObstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront

/-! # ArcCupObstructionPinsRefuted — the ∀-pins cup reduction is DEAD on the obstruction

`arcCupOrbitWitness_ofWindowPinAndTailsCancel` (ArcCupOrbitPinsReduction) reduces the cup-head
orbit witness to a `pins` hypothesis quantified over EVERY located split of the second spine:
each split's bubbled cup must land at the head's window (`windowPin`) AND cancel the tail's arc
structure at the head's target boundary (`tailsCancel`).  This file machine-checks that this
`pins` premise is FALSE on the canonical cup-cancel obstruction, so that reduction cannot close
the cup case (#2152 / `fxMode_hasArcCellReconstruction`).  The orbit witness must be inhabited by
DIRECTLY re-selecting the leg-aligned cup (`cup@2` swaps through the head), not by discharging
the pins for all splits.

The head cup is the unit cup at window `0` over the length-2 boundary `L·R` (`adjunctionCupAtLeft`'s
spine atom): empty generator domain, `codBoundaryLength = 4`.  The second spine is
`headCup :: rightTail`.  The head-cup composites of the two obstruction tails are EQUAL
(`arcCupObstruction_composite_extract_eq`), so this is a genuine reconstruction case; yet the
FRESH tails differ (`arcCupObstruction_freshTail_extract_ne`).  The FRONT split — empty prefix,
`BubblesToFront.nil`, the head cup itself as toucher — is one of the located splits the `pins`
must cover, and on it `tailsCancel` becomes exactly
`arcStructureOfSpineList 4 leftTail = arcStructureOfSpineList 4 rightTail`, which the fresh
disequality refutes.  The head-cup join forgets the leg split, so the naive front selection is
provably wrong; only the through-the-head re-selection survives.

Raw Lean 4 + Init; the refutation instantiates the pins at the front split and rides the shipped
`decide`-backed obstruction.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The peeled cup head: a unit cup at window `0` over the length-2 boundary `L·R`
(`adjunctionCupAtLeft`'s spine atom).  Empty generator domain, generator cod `L·R`, right context
`L·R`, so `domBoundaryLength = 2` and `codBoundaryLength = 4` — it fires at `bottomCount 2` and
hands the two obstruction tails their fresh boundary `4`. -/
def arcCupObstructionHeadCupAtom :
    SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base :=
  { leftMidMode := AdjunctionMode.base
    rightMidMode := AdjunctionMode.base
    leftContext := ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base
    generatorDom := ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base
    generatorCod := adjunctionLeftThenRight
    generator := AdjunctionTwoCell.unit
    rightContext := adjunctionLeftThenRight }

/-- ★ **The ∀-pins premise is FALSE on the cup-cancel obstruction.**  For the peeled cup head and
the second spine `headCup :: rightTail`, the two orbit pins cannot hold for EVERY located split.
The front split — empty prefix, the head cup itself as toucher, `BubblesToFront.nil` — satisfies
all three antecedents (it IS a split, the nil bubble witnesses it, the cup head has empty domain),
yet forces `tailsCancel` to be
`arcStructureOfSpineList 4 leftTail = arcStructureOfSpineList 4 rightTail`, which
`arcCupObstruction_freshTail_extract_ne` refutes.  Hence
`arcCupOrbitWitness_ofWindowPinAndTailsCancel`'s `pins` hypothesis is unsatisfiable here — the
orbit witness must be produced by re-selecting the leg-aligned cup, not by discharging the pins. -/
theorem arcCupOrbitPins_isFalse_onObstruction :
    ¬ (∀ (prefixAtoms :
          List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base))
        (toucherAtom : SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base)
        (suffixAtoms :
          List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base))
        (movedTarget : SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base)
        (movedPrefixAtoms :
          List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base)),
        arcCupObstructionHeadCupAtom :: arcCupObstructionRightTailAtoms
            = prefixAtoms ++ toucherAtom :: suffixAtoms →
        BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms →
        movedTarget.generatorDom.length = 0 →
        movedTarget.leftContext.length = arcCupObstructionHeadCupAtom.leftContext.length
          ∧ arcStructureOfSpineList arcCupObstructionHeadCupAtom.codBoundaryLength
                arcCupObstructionLeftTailAtoms
              = arcStructureOfSpineList arcCupObstructionHeadCupAtom.codBoundaryLength
                  (movedPrefixAtoms ++ suffixAtoms)) := by
  intro pins
  exact arcCupObstruction_freshTail_extract_ne
    (pins [] arcCupObstructionHeadCupAtom arcCupObstructionRightTailAtoms
      arcCupObstructionHeadCupAtom [] rfl BubblesToFront.nil rfl).2

/-! ## Honesty marker -/

/-- **Honesty marker — the ∀-pins cup reduction is DEAD on the obstruction (peel campaign H).**
`arcCupOrbitPins_isFalse_onObstruction`: the `pins` hypothesis of
`arcCupOrbitWitness_ofWindowPinAndTailsCancel` (quantified over every located split of the second
spine) is unsatisfiable on the canonical obstruction, because the front split forces the refuted
`arc leftTail @ 4 = arc rightTail @ 4`.  What this settles: the ∀-pins REDUCTION is not the closing
route for the cup case — `ArcCupOrbitWitness` must be inhabited by directly re-selecting the
leg-aligned cup (`cup@2` swaps through the head), the through-the-head trace orbit the refuted
unconditional cancel leaves open.  What this marker does NOT claim: that the re-selection succeeds
(the general leg-alignment existence — the deep planar residual of #2152).  `= true`. -/
def fxMode_hasArcCupObstructionPinsRefuted : Bool := true

end FX1Poly.Polygraph
