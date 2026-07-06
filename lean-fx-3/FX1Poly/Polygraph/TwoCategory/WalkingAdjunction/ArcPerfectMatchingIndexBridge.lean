import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatching
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingExtract
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingFold

/-! # ArcPerfectMatchingIndexBridge — token-frame perfect matching → range-frame noFixedPoint (noFixedPoint rung, closing)

The token-frame `ArcPerfectMatchingTokens` (stable `ArcEndToken`s) is what the whole-spine fold delivers; the
short-chord planar lemma consumes the RANGE-frame no-fixed-point `partnerIndexOf … index ≠ index`.  This
brick bridges them: the inverse index map `indexOfToken` (of the shipped `tokenOfIndex`) round-trips both ways,
so a token partner becomes a range-index partner with the same node, giving the range-frame
`ArcPerfectMatching`; the shipped `partnerIndexOf_neSelf_ofPerfectMatching` then discharges the no-fixed-point.
The capstone specialises to the extracted state of any chained adjunction spine — the short-chord lemma's
third hypothesis, at the real matching.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean Nat plumbing -/

/-- `(start + amount) - start = amount`, hand-rolled clean. -/
private theorem addSubCancelLeft : (start amount : Nat) → (start + amount) - start = amount
  | 0, amount => by rw [Nat.zero_add, Nat.sub_zero]
  | start + 1, amount => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeft start amount

/-! ## The inverse index map -/

/-- The boundary index of an end token — the inverse of `tokenOfIndex`: a bottom port keeps its value, an
open slot shifts past the seed block. -/
def indexOfToken (bottomCount : Nat) : ArcEndToken → Nat
  | ArcEndToken.bottomPort portValue => portValue
  | ArcEndToken.openSlot slotPosition => bottomCount + slotPosition

/-- Round-trip: the index of the token of an index is the index. -/
theorem indexOfToken_tokenOfIndex (bottomCount index : Nat) :
    indexOfToken bottomCount (tokenOfIndex bottomCount index) = index := by
  unfold tokenOfIndex
  cases Nat.lt_or_ge index bottomCount with
  | inl below => rw [if_pos below]; rfl
  | inr atLeast =>
      rw [if_neg (fun indexLtBottom =>
        Nat.lt_irrefl index (Nat.lt_of_lt_of_le indexLtBottom atLeast))]
      show bottomCount + (index - bottomCount) = index
      obtain ⟨slot, slotEq⟩ := Nat.le.dest atLeast
      rw [← slotEq, addSubCancelLeft bottomCount slot]

/-- Round-trip: the token of the index of a valid token is the token. -/
theorem tokenOfIndex_indexOfToken (bottomCount : Nat) (state : ArcWireState) (token : ArcEndToken)
    (valid : isValidArcEndToken bottomCount state token) :
    tokenOfIndex bottomCount (indexOfToken bottomCount token) = token := by
  cases token with
  | bottomPort portValue =>
      have validLt : portValue < bottomCount := valid
      show tokenOfIndex bottomCount portValue = ArcEndToken.bottomPort portValue
      unfold tokenOfIndex
      rw [if_pos validLt]
  | openSlot slotPosition =>
      show tokenOfIndex bottomCount (bottomCount + slotPosition) = ArcEndToken.openSlot slotPosition
      unfold tokenOfIndex
      rw [if_neg (fun windowLtBottom => Nat.lt_irrefl bottomCount
        (Nat.lt_of_le_of_lt (Nat.le_add_right bottomCount slotPosition) windowLtBottom))]
      show ArcEndToken.openSlot (bottomCount + slotPosition - bottomCount)
        = ArcEndToken.openSlot slotPosition
      rw [addSubCancelLeft bottomCount slotPosition]

/-- A valid token's index is in range. -/
theorem indexOfToken_lt (bottomCount : Nat) (state : ArcWireState) (token : ArcEndToken)
    (valid : isValidArcEndToken bottomCount state token) :
    indexOfToken bottomCount token < bottomCount + state.openWires.length := by
  cases token with
  | bottomPort portValue =>
      exact Nat.lt_of_lt_of_le (valid : portValue < bottomCount)
        (Nat.le_add_right bottomCount state.openWires.length)
  | openSlot slotPosition =>
      exact Nat.add_lt_add_left (valid : slotPosition < state.openWires.length) bottomCount

/-! ## The token → range bridge -/

/-- ★ **The token-frame perfect matching gives the range-frame perfect matching.**  Every in-range boundary
index is the index of a valid token, whose token partner forwards (via `indexOfToken`) to a distinct in-range
same-component index. -/
theorem arcPerfectMatching_ofTokens (bottomCount : Nat) (state : ArcWireState)
    (perfect : ArcPerfectMatchingTokens bottomCount state) :
    ArcPerfectMatching bottomCount state := by
  intro index indexInRange
  have tokValid : isValidArcEndToken bottomCount state (tokenOfIndex bottomCount index) :=
    isValidArcEndToken_tokenOfIndex bottomCount state index indexInRange
  obtain ⟨partnerTok, partnerTokValid, partnerTokNe, sameTok⟩ :=
    perfect (tokenOfIndex bottomCount index) tokValid
  refine ⟨indexOfToken bottomCount partnerTok, ?_, ?_, ?_⟩
  · exact indexOfToken_lt bottomCount state partnerTok partnerTokValid
  · intro partnerIdxEqIndex
    have bothIndicesEq : indexOfToken bottomCount partnerTok
        = indexOfToken bottomCount (tokenOfIndex bottomCount index) :=
      partnerIdxEqIndex.trans (indexOfToken_tokenOfIndex bottomCount index).symm
    have tokensEq : partnerTok = tokenOfIndex bottomCount index := by
      have applied := congrArg (tokenOfIndex bottomCount) bothIndicesEq
      rw [tokenOfIndex_indexOfToken bottomCount state partnerTok partnerTokValid,
        tokenOfIndex_indexOfToken bottomCount state (tokenOfIndex bottomCount index) tokValid]
        at applied
      exact applied
    exact partnerTokNe tokensEq
  · have nodeIndex : natListGetAt (List.range bottomCount ++ state.openWires) index
        = arcEndTokenNode state (tokenOfIndex bottomCount index) :=
      (arcEndTokenNode_tokenOfIndex bottomCount state index).symm
    have nodePartner : natListGetAt (List.range bottomCount ++ state.openWires)
        (indexOfToken bottomCount partnerTok) = arcEndTokenNode state partnerTok := by
      rw [← arcEndTokenNode_tokenOfIndex bottomCount state (indexOfToken bottomCount partnerTok),
        tokenOfIndex_indexOfToken bottomCount state partnerTok partnerTokValid]
    rw [nodeIndex, nodePartner]
    exact sameTok

/-! ## The no-fixed-point capstone at the extracted spine state -/

/-- ★ **No fixed point at the extracted state of any chained adjunction spine.**  Folding a boundary-chained
walking-adjunction spine from the canonical seed lands a state whose `partnerIndexOf` matching has NO fixed
point — every boundary index is genuinely matched to a distinct one.  This is the short-chord planar lemma's
third hypothesis, discharged for the real `extractDiagram` matching. -/
theorem partnerIndexOf_neSelf_ofChainedSpine
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms)
    (index : Nat)
    (indexInRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length) :
    partnerIndexOf
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
        (List.range bottomCount
          ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires)
        (bottomCount
          + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length)
        index
      ≠ index :=
  partnerIndexOf_neSelf_ofPerfectMatching bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)
    (arcPerfectMatching_ofTokens bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)
      (arcPerfectMatchingTokens_ofChainedSpineList bottomCount atoms chained))
    index indexInRange

/-! ## Honesty marker -/

/-- **Honesty marker — the noFixedPoint leg is CLOSED for the real matching (noFixedPoint rung, capstone).**
`indexOfToken` (inverse of `tokenOfIndex`) with its two round-trips + range lemma, `arcPerfectMatching_ofTokens`
(token → range bridge), and `partnerIndexOf_neSelf_ofChainedSpine` (no fixed point at the extracted state of
any chained adjunction spine).  This discharges the THIRD short-chord hypothesis (`noFixedPoint`) for the
`extractDiagram`/`partnerIndexOf` matching — joining the shipped `partnerInRange` and `isInvolution`.  What
this marker does NOT claim: the D3 spine-readback that turns the resulting adjacent-matched pair into a cup
atom satisfying `windowPin` + `tailsCancel` (the `ArcCupOrbitWitness`).  `= true`. -/
def fxMode_hasArcPerfectMatchingNoFixedPoint : Bool := true

end FX1Poly.Polygraph
