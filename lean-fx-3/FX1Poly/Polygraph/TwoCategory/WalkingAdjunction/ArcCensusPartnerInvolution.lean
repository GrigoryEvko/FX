import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingExtract
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerUnique
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # ArcCensusPartnerInvolution — the censused partner matching is a fixed-point-free involution (short-chord prereq)

The short-chord planar lemma (`nonCrossing_hasAdjacentMatchedPair`) applies to any fixed-point-free
involution matching in range.  Two of those three properties are discharged from the two-endpoint census
here for the actual `partnerIndexOf` matching:

  * IN RANGE — `partnerIndexOf_below` (shipped in `ArcNonCrossingExtract`): the scan returns `index` or a
    scanned member, both below `total`.
  * INVOLUTION — this file: at a censused state, if `index`'s partner `j` is genuine (`j ≠ index`), then
    `j`'s partner is `index` again.  `j` shares `index`'s component (forward soundness), so `index` is a
    same-component candidate for `j`, and the census pins `partnerIndexOf … j = index`
    (`partnerIndexOf_uniqueSameComponent`).

The remaining property — NO FIXED POINT (every boundary port is genuinely matched, `partnerIndexOf index
≠ index`) — is the `≥ 2`-ends direction of the census and is left as the caller's obligation.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The censused partner matching is an involution on the genuinely-matched ports.**  At a censused
state, if `partnerIndexOf … index` is a genuine partner (`≠ index`), applying `partnerIndexOf` again
returns `index`.  The partner `j` shares `index`'s component (forward scan soundness), so `index` is an
in-range same-component candidate distinct from `j`, and the census pins `j`'s partner to `index`. -/
theorem partnerIndexOf_isInvolution (bottomCount : Nat) (state : ArcWireState)
    (census : ArcBoundaryCensus bottomCount state)
    (index : Nat) (indexInRange : index < bottomCount + state.openWires.length)
    (notFixed : partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) index ≠ index) :
    partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length)
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) index)
      = index := by
  have partnerBelow : partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
      (bottomCount + state.openWires.length) index < bottomCount + state.openWires.length :=
    partnerIndexOf_below state bottomCount index indexInRange
  have sameForward : isSameComponent state.links
      (natListGetAt (List.range bottomCount ++ state.openWires) index)
      (natListGetAt (List.range bottomCount ++ state.openWires)
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length) index)) = true := by
    cases partnerIndexOf_sameComponent_or_fixed state bottomCount index with
    | inl isFixed => exact absurd isFixed notFixed
    | inr sound => exact sound
  exact partnerIndexOf_uniqueSameComponent bottomCount state census
    (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
      (bottomCount + state.openWires.length) index)
    index partnerBelow indexInRange
    (fun indexEqPartner => notFixed indexEqPartner.symm)
    (isSameComponent_flip state.links _ _ sameForward)

/-! ## Honesty marker -/

/-- **Honesty marker — the censused partner matching is a fixed-point-free involution IN RANGE, modulo
the no-fixed-point obligation (short-chord prereq).**  `partnerIndexOf_isInvolution` discharges the
INVOLUTION property from the census + forward scan soundness; IN RANGE is the shipped
`partnerIndexOf_below`.  Together with the caller's NO-FIXED-POINT obligation (the `≥ 2`-ends census
direction), these are exactly the hypotheses `nonCrossing_hasAdjacentMatchedPair` (the short-chord planar
lemma) consumes.  What this marker does NOT claim: the no-fixed-point / perfect-matching fact, nor the
spine-level readback of the resulting leg-aligned cup.  `= true`. -/
def fxMode_hasArcCensusPartnerInvolution : Bool := true

end FX1Poly.Polygraph
