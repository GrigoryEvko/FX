import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingBoundaryInvolution

/-! # NonCrossingShortChord — a non-crossing matching has an adjacent matched pair (cup rung D2, the planar lemma)

The obstruction file (`ArcCupObstructionPinsRefuted`) proves the ∀-pins reduction dead: the cup-head
`ArcCupOrbitWitness` must be inhabited by DIRECTLY re-selecting a LEG-ALIGNED cup, and the "general
leg-alignment existence" is the deep planar residual.  This file discharges that existence at the
matching level: a non-crossing perfect matching over the rectangle boundary always has a SHORT CHORD —
two boundary indices matched to each other whose cyclic positions are CONSECUTIVE (`bp i + 1 =
bp (partner i)`), i.e., an innermost/leg-aligned arc.

## The minimal-gap argument

Order the matched arcs by the gap between their two boundary positions.  Take the arc `(a, b)` with the
smallest positive gap.  If the gap is `1` it IS a short chord.  If the gap is `> 1`, the position
`bp(a) + 1` lies strictly inside `(bp a, bp b)` and — since `boundaryPosition` is a bijection on
`[0, total)` (`NonCrossingBoundaryInvolution`) — is itself some index `k`'s position.  `k` is matched to
some `m`; a case split on `bp m` versus `bp a`, `bp a + 1`, `bp b` either produces an interleaving that
contradicts `IsNonCrossing`, or produces a strictly-smaller-gap arc, contradicting minimality.  Encoded
as structural induction on a decreasing gap budget.

The matching properties (`partner` is a fixed-point-free involution in range) are taken as HYPOTHESES here;
they are discharged from the two-endpoint census at the extract site.

Raw Lean 4 + Init; hand-rolled clean Nat arithmetic and min/max (Init's cancel/comm lemmas leak propext).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean min/max (Init's `min_eq_right`/`max_eq_left` leak propext through comm) -/

/-- `Nat.min a b = b` when `b ≤ a` (`min a b` is defeq `if a ≤ b then a else b`). -/
private theorem natMinRight (firstNat secondNat : Nat) (order : secondNat ≤ firstNat) :
    Nat.min firstNat secondNat = secondNat := by
  show (if firstNat ≤ secondNat then firstNat else secondNat) = secondNat
  cases Nat.decLe firstNat secondNat with
  | isTrue firstLeSecond => rw [if_pos firstLeSecond]; exact Nat.le_antisymm firstLeSecond order
  | isFalse firstNotLeSecond => rw [if_neg firstNotLeSecond]

/-- `Nat.max a b = a` when `b ≤ a` (`max a b` is defeq `if a ≤ b then b else a`). -/
private theorem natMaxLeft (firstNat secondNat : Nat) (order : secondNat ≤ firstNat) :
    Nat.max firstNat secondNat = firstNat := by
  show (if firstNat ≤ secondNat then secondNat else firstNat) = firstNat
  cases Nat.decLe firstNat secondNat with
  | isTrue firstLeSecond => rw [if_pos firstLeSecond]; exact Nat.le_antisymm order firstLeSecond
  | isFalse firstNotLeSecond => rw [if_neg firstNotLeSecond]

/-! ## The arc endpoints as `boundaryPosition` values -/

/-- With the arc's own position the lower one, `arcMinPosition` is the own position. -/
private theorem arcMin_of_le (bottomCount total : Nat) (partner : List Nat) (index : Nat)
    (le : boundaryPosition bottomCount total index
      ≤ boundaryPosition bottomCount total (natListGetAt partner index)) :
    arcMinPosition bottomCount total partner index = boundaryPosition bottomCount total index := by
  unfold arcMinPosition; exact Nat.min_eq_left le

/-- With the arc's own position the lower one, `arcMaxPosition` is the partner position. -/
private theorem arcMax_of_le (bottomCount total : Nat) (partner : List Nat) (index : Nat)
    (le : boundaryPosition bottomCount total index
      ≤ boundaryPosition bottomCount total (natListGetAt partner index)) :
    arcMaxPosition bottomCount total partner index
      = boundaryPosition bottomCount total (natListGetAt partner index) := by
  unfold arcMaxPosition; exact Nat.max_eq_right le

/-- With the partner position the lower one, `arcMinPosition` is the partner position. -/
private theorem arcMin_of_ge (bottomCount total : Nat) (partner : List Nat) (index : Nat)
    (le : boundaryPosition bottomCount total (natListGetAt partner index)
      ≤ boundaryPosition bottomCount total index) :
    arcMinPosition bottomCount total partner index
      = boundaryPosition bottomCount total (natListGetAt partner index) := by
  unfold arcMinPosition; exact natMinRight _ _ le

/-- With the partner position the lower one, `arcMaxPosition` is the own position. -/
private theorem arcMax_of_ge (bottomCount total : Nat) (partner : List Nat) (index : Nat)
    (le : boundaryPosition bottomCount total (natListGetAt partner index)
      ≤ boundaryPosition bottomCount total index) :
    arcMaxPosition bottomCount total partner index = boundaryPosition bottomCount total index := by
  unfold arcMaxPosition; exact natMaxLeft _ _ le

/-! ## The minimal-gap induction -/

/-- ★ **The minimal-gap descent.**  Given a matched arc `(lowIndex, partner lowIndex)` whose upper
position is within `gapBudget` of its lower, a short chord exists — by structural induction on the
budget.  Gap `1` IS the chord; a larger gap forces (via surjectivity of `boundaryPosition` and
`IsNonCrossing`) either a crossing contradiction or a strictly-smaller arc consuming a unit of budget. -/
private theorem shortChordDescent (bottomCount : Nat) (partner : List Nat)
    (isInvolution : ∀ probeIndex, probeIndex < partner.length →
      natListGetAt partner (natListGetAt partner probeIndex) = probeIndex)
    (noFixedPoint : ∀ probeIndex, probeIndex < partner.length →
      natListGetAt partner probeIndex ≠ probeIndex)
    (partnerInRange : ∀ probeIndex, probeIndex < partner.length →
      natListGetAt partner probeIndex < partner.length)
    (nonCrossing : IsNonCrossing bottomCount partner) :
    (gapBudget lowIndex : Nat) → lowIndex < partner.length →
    boundaryPosition bottomCount partner.length lowIndex
      < boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex) →
    boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex)
      ≤ boundaryPosition bottomCount partner.length lowIndex + gapBudget →
    ∃ shortIndex, shortIndex < partner.length ∧
      boundaryPosition bottomCount partner.length shortIndex + 1
        = boundaryPosition bottomCount partner.length (natListGetAt partner shortIndex)
  | 0, lowIndex, _, order, measure => by
      rw [Nat.add_zero] at measure
      exact absurd (Nat.lt_of_lt_of_le order measure) (Nat.lt_irrefl _)
  | gapBudget + 1, lowIndex, lowBelow, order, measure => by
      have partnerInj : ∀ leftProbe rightProbe, leftProbe < partner.length →
          rightProbe < partner.length →
          natListGetAt partner leftProbe = natListGetAt partner rightProbe → leftProbe = rightProbe := by
        intro leftProbe rightProbe leftBelow rightBelow probesEqual
        have congr := congrArg (natListGetAt partner) probesEqual
        rw [isInvolution leftProbe leftBelow, isInvolution rightProbe rightBelow] at congr
        exact congr
      cases Nat.lt_or_ge (boundaryPosition bottomCount partner.length lowIndex + 1)
          (boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex)) with
      | inr gapSmall =>
          exact ⟨lowIndex, lowBelow, Nat.le_antisymm order gapSmall⟩
      | inl gapBig =>
          have highBelow : boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex)
              < partner.length :=
            boundaryPosition_lt bottomCount partner.length (natListGetAt partner lowIndex)
              (partnerInRange lowIndex lowBelow)
          have midPosBelow : boundaryPosition bottomCount partner.length lowIndex + 1 < partner.length :=
            Nat.lt_trans gapBig highBelow
          obtain ⟨midIndex, midBelow, midEq⟩ :=
            boundaryPosition_surjective bottomCount partner.length
              (boundaryPosition bottomCount partner.length lowIndex + 1) midPosBelow
          have midPartnerBelow : natListGetAt partner midIndex < partner.length :=
            partnerInRange midIndex midBelow
          have midPartnerNe : boundaryPosition bottomCount partner.length (natListGetAt partner midIndex)
              ≠ boundaryPosition bottomCount partner.length midIndex := by
            intro contra
            exact noFixedPoint midIndex midBelow
              (boundaryPosition_injective bottomCount partner.length (natListGetAt partner midIndex)
                midIndex midPartnerBelow midBelow contra)
          cases Nat.lt_trichotomy
              (boundaryPosition bottomCount partner.length (natListGetAt partner midIndex))
              (boundaryPosition bottomCount partner.length lowIndex) with
          | inl midPLtLow =>
              -- Case A: bp(midPartner) < bp(low) < bp(mid) < bp(high) — cross (midIndex, lowIndex)
              have leMid : boundaryPosition bottomCount partner.length (natListGetAt partner midIndex)
                  ≤ boundaryPosition bottomCount partner.length midIndex := by
                rw [midEq]; exact Nat.le_of_lt (Nat.lt_succ_of_lt midPLtLow)
              have leLow : boundaryPosition bottomCount partner.length lowIndex
                  ≤ boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex) :=
                Nat.le_of_lt order
              refine absurd ?_ (nonCrossing midIndex midBelow lowIndex lowBelow)
              refine ⟨?_, ?_, ?_⟩
              · rw [arcMin_of_ge bottomCount partner.length partner midIndex leMid,
                  arcMin_of_le bottomCount partner.length partner lowIndex leLow]
                exact midPLtLow
              · rw [arcMin_of_le bottomCount partner.length partner lowIndex leLow,
                  arcMax_of_ge bottomCount partner.length partner midIndex leMid, midEq]
                exact Nat.lt_succ_self _
              · rw [arcMax_of_ge bottomCount partner.length partner midIndex leMid,
                  arcMax_of_le bottomCount partner.length partner lowIndex leLow, midEq]
                exact gapBig
          | inr midPGeLow =>
              cases midPGeLow with
              | inl midPEqLow =>
                  -- bp(midPartner) = bp(low) ⟹ midPartner = low ⟹ partner low = mid ⟹ bp high = bp mid = bp low + 1, contra gapBig
                  have midPEqLowIndex : natListGetAt partner midIndex = lowIndex :=
                    boundaryPosition_injective bottomCount partner.length
                      (natListGetAt partner midIndex) lowIndex midPartnerBelow lowBelow midPEqLow
                  have lowPartnerEqMid : natListGetAt partner lowIndex = midIndex := by
                    have back := isInvolution midIndex midBelow
                    rw [midPEqLowIndex] at back
                    exact back
                  have highEq : boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex)
                      = boundaryPosition bottomCount partner.length lowIndex + 1 := by
                    rw [lowPartnerEqMid]; exact midEq
                  exact absurd (highEq ▸ gapBig) (Nat.lt_irrefl _)
              | inr midPGtLow =>
                  cases Nat.lt_trichotomy
                      (boundaryPosition bottomCount partner.length (natListGetAt partner midIndex))
                      (boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex)) with
                  | inl midPLtHigh =>
                      -- Case B: bp(low) < bp(midPartner) < bp(high) — recurse on midIndex
                      have order' : boundaryPosition bottomCount partner.length midIndex
                          < boundaryPosition bottomCount partner.length (natListGetAt partner midIndex) := by
                        rw [midEq]
                        cases Nat.lt_or_ge
                            (boundaryPosition bottomCount partner.length lowIndex + 1)
                            (boundaryPosition bottomCount partner.length (natListGetAt partner midIndex)) with
                        | inl strict => exact strict
                        | inr small =>
                            exact absurd
                              (midEq ▸ (Nat.le_antisymm small midPGtLow))
                              midPartnerNe
                      have measure' : boundaryPosition bottomCount partner.length (natListGetAt partner midIndex)
                          ≤ boundaryPosition bottomCount partner.length midIndex + gapBudget := by
                        rw [midEq, Nat.add_assoc, Nat.add_comm 1 gapBudget]
                        exact Nat.le_of_lt (Nat.lt_of_lt_of_le midPLtHigh measure)
                      exact shortChordDescent bottomCount partner isInvolution noFixedPoint
                        partnerInRange nonCrossing gapBudget midIndex midBelow order' measure'
                  | inr midPGeHigh =>
                      cases midPGeHigh with
                      | inl midPEqHigh =>
                          -- bp(midPartner) = bp(high) ⟹ midPartner = partner low ⟹ mid = low ⟹ bp low = bp low + 1, contra
                          have midPEqLowPartner : natListGetAt partner midIndex = natListGetAt partner lowIndex :=
                            boundaryPosition_injective bottomCount partner.length
                              (natListGetAt partner midIndex) (natListGetAt partner lowIndex)
                              midPartnerBelow (partnerInRange lowIndex lowBelow) midPEqHigh
                          have midEqLow : midIndex = lowIndex :=
                            partnerInj midIndex lowIndex midBelow lowBelow midPEqLowPartner
                          have selfSucc : boundaryPosition bottomCount partner.length lowIndex
                              = boundaryPosition bottomCount partner.length lowIndex + 1 := by
                            rw [midEqLow] at midEq; exact midEq
                          exact absurd selfSucc (Nat.ne_of_lt (Nat.lt_succ_self _))
                      | inr midPGtHigh =>
                          -- Case D: bp(low) < bp(mid) ≤ bp(high) < bp(midPartner) — cross (lowIndex, midIndex)
                          have geMid : boundaryPosition bottomCount partner.length (natListGetAt partner midIndex)
                              ≥ boundaryPosition bottomCount partner.length midIndex := by
                            rw [midEq]
                            exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_of_lt gapBig) midPGtHigh)
                          have leLow : boundaryPosition bottomCount partner.length lowIndex
                              ≤ boundaryPosition bottomCount partner.length (natListGetAt partner lowIndex) :=
                            Nat.le_of_lt order
                          refine absurd ?_ (nonCrossing lowIndex lowBelow midIndex midBelow)
                          refine ⟨?_, ?_, ?_⟩
                          · rw [arcMin_of_le bottomCount partner.length partner lowIndex leLow,
                              arcMin_of_le bottomCount partner.length partner midIndex geMid, midEq]
                            exact Nat.lt_succ_self _
                          · rw [arcMin_of_le bottomCount partner.length partner midIndex geMid,
                              arcMax_of_le bottomCount partner.length partner lowIndex leLow, midEq]
                            exact gapBig
                          · rw [arcMax_of_le bottomCount partner.length partner lowIndex leLow,
                              arcMax_of_le bottomCount partner.length partner midIndex geMid]
                            exact midPGtHigh

/-! ## The short chord existence -/

/-- ★ **A non-crossing perfect matching has an adjacent matched pair (short chord).**  For a
fixed-point-free involution `partner` on `[0, total)` whose extracted matching is `IsNonCrossing`, some
index sits at a cyclic position exactly one below its partner's — the innermost/leg-aligned arc the
cup-head reconstruction re-selects.  Seeded at index `0` (matched, hence a genuine arc by injectivity of
`boundaryPosition`) and descended by the minimal-gap argument. -/
theorem nonCrossing_hasAdjacentMatchedPair (bottomCount : Nat) (partner : List Nat)
    (isInvolution : ∀ probeIndex, probeIndex < partner.length →
      natListGetAt partner (natListGetAt partner probeIndex) = probeIndex)
    (noFixedPoint : ∀ probeIndex, probeIndex < partner.length →
      natListGetAt partner probeIndex ≠ probeIndex)
    (partnerInRange : ∀ probeIndex, probeIndex < partner.length →
      natListGetAt partner probeIndex < partner.length)
    (nonCrossing : IsNonCrossing bottomCount partner)
    (nonEmpty : 0 < partner.length) :
    ∃ shortIndex, shortIndex < partner.length ∧
      boundaryPosition bottomCount partner.length shortIndex + 1
        = boundaryPosition bottomCount partner.length (natListGetAt partner shortIndex) := by
  have zeroPartnerBelow : natListGetAt partner 0 < partner.length := partnerInRange 0 nonEmpty
  have zeroPosNe : boundaryPosition bottomCount partner.length 0
      ≠ boundaryPosition bottomCount partner.length (natListGetAt partner 0) := by
    intro contra
    exact noFixedPoint 0 nonEmpty
      (boundaryPosition_injective bottomCount partner.length 0 (natListGetAt partner 0)
        nonEmpty zeroPartnerBelow contra).symm
  cases Nat.lt_trichotomy (boundaryPosition bottomCount partner.length 0)
      (boundaryPosition bottomCount partner.length (natListGetAt partner 0)) with
  | inl posLt =>
      exact shortChordDescent bottomCount partner isInvolution noFixedPoint partnerInRange nonCrossing
        (boundaryPosition bottomCount partner.length (natListGetAt partner 0)) 0 nonEmpty posLt
        (Nat.le_add_left _ _)
  | inr rest =>
      cases rest with
      | inl posEq => exact absurd posEq zeroPosNe
      | inr posGt =>
          have inv0 : natListGetAt partner (natListGetAt partner 0) = 0 := isInvolution 0 nonEmpty
          have order : boundaryPosition bottomCount partner.length (natListGetAt partner 0)
              < boundaryPosition bottomCount partner.length (natListGetAt partner (natListGetAt partner 0)) := by
            rw [inv0]; exact posGt
          have measure : boundaryPosition bottomCount partner.length (natListGetAt partner (natListGetAt partner 0))
              ≤ boundaryPosition bottomCount partner.length (natListGetAt partner 0)
                + boundaryPosition bottomCount partner.length 0 := by
            rw [inv0]; exact Nat.le_add_left _ _
          exact shortChordDescent bottomCount partner isInvolution noFixedPoint partnerInRange nonCrossing
            (boundaryPosition bottomCount partner.length 0) (natListGetAt partner 0) zeroPartnerBelow
            order measure

/-! ## Honesty marker -/

/-- **Honesty marker — the SHORT-CHORD planar lemma is SHIPPED (cup rung D2).**
`nonCrossing_hasAdjacentMatchedPair`: a non-crossing fixed-point-free involution matching on `[0, total)`
has an adjacent matched pair (`bp i + 1 = bp (partner i)`), the innermost/leg-aligned arc.  Proved by the
minimal-gap descent (`shortChordDescent`) over the shipped `boundaryPosition` bijection and `IsNonCrossing`
(D2a).  What this marker does NOT claim: the leg-aligned cup SELECTOR that packages this as a decidable
`find` (D1), the bridge from a boundary short chord to the spine-level cup re-selection, or the discharge
of the matching-property hypotheses from the two-endpoint census.  `= true`. -/
def fxMode_hasNonCrossingShortChord : Bool := true

end FX1Poly.Polygraph
