import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupObstructionPinsRefuted
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseOrbitReduction

/-! # ArcCupObstructionOrbitReselected — the orbit witness HOLDS on the obstruction via re-selection

The companion `ArcCupObstructionPinsRefuted` proves the ∀-pins reduction is DEAD on the canonical
cup-cancel obstruction (the naive FRONT split forces the refuted `arc leftTail@4 = arc rightTail@4`).
This file proves the positive counterpart: `ArcCupOrbitWitness` — the existential the cup case
actually needs — IS inhabited on that same obstruction, by RE-SELECTING the second cup as the
head's realizer.  So the route is SOUND: the obstruction kills only the naive selection, not the
witness.

Second spine `headCup :: rightTail = [headCup@0, cup@2, cap@1]`; tail list `leftTail = [cup@0, cap@1]`.
The re-selected toucher is `cup@2`.  Bubbling it to the front past `headCup` (window-disjoint —
`0 + 2 + 0 = 2` — with an empty inert path at `base`) via `BubblesToFront.stepRightOf`:

  * the moved target re-threads its left context to `nil` — it lands at **window 0** (`windowPin`);
  * the passed `headCup` re-threads its right context to `(L·R)²` — becoming EXACTLY the tail cup
    `cupAtWindowZero`, so the moved prefix is `[cupAtWindowZero]`;
  * the suffix `[cap@1]` is the SAME `connectingCap` atom that closes `leftTail`.

Hence `movedPrefix ++ suffix = [cupAtWindowZero, cap@1] = leftTail` DEFINITIONALLY, so `tailsCancel`
is `rfl`.  All five pins close by `rfl` (the bubble by its constructor).  This is the concrete
witness the through-the-head trace orbit supplies — the shape the general leg-alignment
re-selection must produce for arbitrary spines (the deep residual of #2152).

Raw Lean 4 + Init; the whole witness is one `BubblesToFront.stepRightOf` + `rfl`s.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The re-selected toucher: the second cup, at window `2` over `L·R` — the head cup with its left
context widened to `L·R` (the spine head of `arcCupObstructionRightTailAtoms`). -/
def arcCupObstructionCupTwoAtom :
    SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base :=
  { arcCupObstructionHeadCupAtom with leftContext := adjunctionLeftThenRight }

/-- ★ **The cup orbit witness HOLDS on the obstruction, via `cup@2` re-selection.**  For the peeled
cup head, the tail `leftTail`, and the second spine `headCup :: rightTail`, the located-cup
certificate is inhabited: split at `cup@2` (prefix `[headCup]`, suffix the shared cap), bubble it to
the front past `headCup` (`stepRightOf`, empty inert path at `base`, windows disjoint `0 + 2 + 0 = 2`),
landing at window `0` with dom arity `0`; the moved prefix `[cupAtWindowZero]` and the shared cap
suffix reassemble `leftTail` definitionally, so `tailsCancel` is `rfl`.  The naive front split
(`ArcCupObstructionPinsRefuted`) fails on this very pair — only the re-selection survives. -/
theorem arcCupOrbitWitness_holds_onObstruction :
    ArcCupOrbitWitness arcCupObstructionHeadCupAtom
      arcCupObstructionLeftTailAtoms
      (arcCupObstructionHeadCupAtom :: arcCupObstructionRightTailAtoms) := by
  refine ⟨[arcCupObstructionHeadCupAtom], arcCupObstructionCupTwoAtom,
    arcCupObstructionRightTailAtoms.tail, _, _,
    rfl,
    BubblesToFront.stepRightOf arcCupObstructionHeadCupAtom
      (BubblesToFront.nil : BubblesToFront arcCupObstructionCupTwoAtom []
        arcCupObstructionCupTwoAtom []) rfl
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) rfl,
    ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

/-! ## Honesty marker -/

/-- **Honesty marker — the cup orbit witness holds on the obstruction (peel campaign H).**
`arcCupOrbitWitness_holds_onObstruction`: `ArcCupOrbitWitness` is inhabited on the canonical
obstruction by re-selecting `cup@2` as the head's realizer, so the route survives the refuted
unconditional cancel — the obstruction kills only the naive front selection
(`arcCupOrbitPins_isFalse_onObstruction`), not the existential.  What this marker does NOT claim:
that the re-selection succeeds for ARBITRARY spines (the general leg-alignment existence — the deep
planar residual of #2152); this is a single canonical-case validation, not the general lemma.
`= true`. -/
def fxMode_hasArcCupObstructionOrbitReselected : Bool := true

end FX1Poly.Polygraph
