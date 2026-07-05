import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupInternalCounts

/-! # ArcCupCountLegJoinedAgreement — the leg-joined census agrees under same classification (peel campaign H, count rung P-5d-count)

The cup-head internal-count transport is `arcCupCountTransport = base + (if class then headContribution
else 0)`, where `base` is the LEG-JOINED fresh census (the count in `unionFindJoin freshLinks
windowPosition (windowPosition + 1)`, the two window legs merged) and `class` is whether the shifted
read reaches the merged window strand.  The pointwise transport agreement
(`arcCupHeadFolded_cupCountTransport_pointwise`) gives the two runs' transports equal from the
composite equality; this brick reads off what that gives on the base once the head contribution is
neutralized:

  * ★ `arcCupCountTransport_baseAgrees_ofSameClassification` — when the two runs' classification
    booleans agree (the same-classification precondition — the through-the-head trace orbit's target),
    the `(if class then headContribution else 0)` summand is a common term and cancels, so the two
    LEG-JOINED censuses coincide.

The honest seam this draws: same classification suffices to agree the leg-JOINED census, but NOT the
raw per-leg internal count — the leg-join merges the two window legs, hiding which leg each event
attached to.  So the genuine internal-count residual is precisely the leg-attachment de-merge (which
leg), the count face of the same leg obstruction the partner cancel meets at the two leg positions —
and that de-merge is exactly the orbit's job (a mixed-free, leg-realigned second spine).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Right cancellation on `Nat`, hand-rolled by structural recursion on the cancelled summand (core
`Nat.add_right_cancel` leaks `propext`; `Nat.add` recurses on its second argument, so each step is a
`Nat.succ.inj`). -/
private theorem natAddRightCancel :
    (cancelled leftValue rightValue : Nat) →
    leftValue + cancelled = rightValue + cancelled → leftValue = rightValue
  | 0, _, _, equalSums => equalSums
  | cancelledPred + 1, leftValue, rightValue, equalSums =>
      natAddRightCancel cancelledPred leftValue rightValue (Nat.succ.inj equalSums)

/-- ★ **The leg-joined census agrees under same classification.**  Two cup-head count transports at
one composite index that are equal (the pointwise transport agreement from the composite equality) and
whose classification booleans agree (the same-classification precondition) have equal leg-joined
censuses: the shared `(if class then headContribution else 0)` head contribution cancels.  This isolates
the internal-count residual as the leg-attachment de-merge — the leg-join `unionFindJoin … windowPosition
(windowPosition + 1)` hides which of the two window legs each event attached to, and only the orbit's
leg-realigned second spine recovers it. -/
theorem arcCupCountTransport_baseAgrees_ofSameClassification
    (firstLinks secondLinks : List (Nat × Nat))
    (firstBoundary secondBoundary firstEvents secondEvents : List Nat)
    (windowPosition headContribution compositeIndex : Nat)
    (transportEq :
      arcCupCountTransport firstLinks firstBoundary firstEvents windowPosition headContribution
          compositeIndex
        = arcCupCountTransport secondLinks secondBoundary secondEvents windowPosition headContribution
            compositeIndex)
    (sameClass :
      isSameComponent (unionFindJoin firstLinks windowPosition (windowPosition + 1)) windowPosition
          (natListGetAt firstBoundary (freshShiftAbove windowPosition 2 compositeIndex))
        = isSameComponent (unionFindJoin secondLinks windowPosition (windowPosition + 1)) windowPosition
            (natListGetAt secondBoundary (freshShiftAbove windowPosition 2 compositeIndex))) :
    countEventsInRoot (unionFindJoin firstLinks windowPosition (windowPosition + 1))
        (unionFindRootOf (unionFindJoin firstLinks windowPosition (windowPosition + 1))
          (natListGetAt firstBoundary (freshShiftAbove windowPosition 2 compositeIndex))) firstEvents
      = countEventsInRoot (unionFindJoin secondLinks windowPosition (windowPosition + 1))
          (unionFindRootOf (unionFindJoin secondLinks windowPosition (windowPosition + 1))
            (natListGetAt secondBoundary (freshShiftAbove windowPosition 2 compositeIndex)))
          secondEvents := by
  dsimp only [arcCupCountTransport] at transportEq
  rw [sameClass] at transportEq
  exact natAddRightCancel _ _ _ transportEq

/-! ## Honesty marker -/

/-- **Honesty marker — the leg-joined census agrees under same classification (peel campaign H, count
rung P-5d-count).**  `arcCupCountTransport_baseAgrees_ofSameClassification`: equal cup-head count
transports with agreeing classification booleans have equal leg-joined censuses — the head contribution
`(if class then headContribution else 0)` is a common summand and cancels.  What this marker does NOT
claim: the raw per-leg internal-count agreement — the leg-join merges the two window legs, so agreeing
the leg-joined census leaves the leg-attachment de-merge open; that de-merge is the count face of the
partner cancel's two-leg obstruction, delivered only by the through-the-head trace orbit (a mixed-free,
leg-realigned second spine).  Nor the same-classification precondition itself (the orbit's target).
`= true`. -/
def fxMode_hasArcCupCountLegJoinedAgreement : Bool := true

end FX1Poly.Polygraph
