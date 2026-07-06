import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatching
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisciplinePreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupRootAtlas

/-! # ArcPerfectMatchingCupPreservation — a CUP step preserves the token-frame perfect matching (noFixedPoint rung, cup half)

A cup fired at an in-range window keeps `ArcPerfectMatchingTokens`: every valid spliced token has a distinct
valid same-component partner.  The classification `arcCupTokenNodeClass` splits each token into an OLD-ZONE
read (node strictly below `nextFresh`) or one of the two fresh cup legs.

  * A LEG token pairs with its sibling leg — the cup joins `nextFresh ~ nextFresh + 1`, so the two legs share
    the component root `nextFresh + 1`.
  * An OLD-ZONE token backmaps to an old token whose old partner (from the old perfect matching) is forwarded
    back to a spliced token via `cupEndTokenForward` — the census cup preservation only ever needed the
    BACKWARD map (it is universal), but perfect matching is EXISTENTIAL, so this file supplies the FORWARD map
    (old valid token → spliced valid token) and its round-trip law `backmap ∘ forward = id`, which gives
    partner-distinctness and (with `isSameComponent_stepCupArc_oldNodes`) same-component transfer.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

/-- `(amount + base) - base = amount`, hand-rolled clean (Init's `Nat.add_sub_cancel` leaks propext). -/
private theorem addSubBaseCancel : (amount base : Nat) → (amount + base) - base = amount
  | amount, 0 => by rw [Nat.add_zero, Nat.sub_zero]
  | amount, base + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact addSubBaseCancel amount base

/-- A read at an in-range index is a member of the list. -/
private theorem natListGetAt_mem_inRange : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- A spliced-state token whose read node stays below `nextFresh` is a syntactic old-zone token: bottom ports
always are, and an open slot cannot be a window slot (those read the fresh legs `nextFresh`/`nextFresh + 1`,
neither below `nextFresh`). -/
private theorem arcCupNodeBelowImpliesZone (state : ArcWireState)
    (position : Nat) (cupInRange : position ≤ state.openWires.length) (token : ArcEndToken)
    (nodeBelow : arcEndTokenNode (stepCupArc state position) token < state.nextFresh) :
    isCupOldZoneToken position token := by
  cases token with
  | bottomPort portValue => exact True.intro
  | openSlot slot =>
      rcases Nat.lt_or_ge slot position with below | atLeast
      · exact Or.inl below
      · rcases Nat.lt_or_ge slot (position + 2) with inWindow | past
        · rcases Nat.lt_or_ge slot (position + 1) with belowSucc | succLe
          · have slotEq : slot = position :=
              Nat.le_antisymm (Nat.le_of_lt_succ belowSucc) atLeast
            rw [slotEq, arcCupLeftLegNode state position cupInRange] at nodeBelow
            exact absurd nodeBelow (Nat.lt_irrefl state.nextFresh)
          · have slotEq : slot = position + 1 :=
              Nat.le_antisymm (Nat.le_of_lt_succ inWindow) succLe
            rw [slotEq, arcCupRightLegNode state position cupInRange] at nodeBelow
            exact (Nat.lt_irrefl (state.nextFresh + 1)
              (Nat.lt_trans nodeBelow (Nat.lt_succ_self state.nextFresh))).elim
        · exact Or.inr past

/-! ## The forward token map (old state → spliced state) -/

/-- Map an old-state boundary end forward to the SPLICED state: bottom ports are untouched; a below-window
slot keeps its position, an at-or-above-window slot shifts up over the two-position splice.  The inverse of
`cupEndTokenBackmap` on the old zone. -/
def cupEndTokenForward (position : Nat) : ArcEndToken → ArcEndToken
  | ArcEndToken.bottomPort portValue => ArcEndToken.bottomPort portValue
  | ArcEndToken.openSlot slotPosition =>
      ArcEndToken.openSlot (if slotPosition < position then slotPosition else slotPosition + 2)

/-- The forward image always lands in the cup's old zone (below-window slots stay below, shifted slots land
at-or-past the far window edge). -/
theorem cupEndTokenForward_isOldZone (position : Nat) (token : ArcEndToken) :
    isCupOldZoneToken position (cupEndTokenForward position token) := by
  cases token with
  | bottomPort _ => exact True.intro
  | openSlot slotPosition =>
      show (if slotPosition < position then slotPosition else slotPosition + 2) < position
          ∨ position + 2 ≤ (if slotPosition < position then slotPosition else slotPosition + 2)
      cases Nat.lt_or_ge slotPosition position with
      | inl below => rw [if_pos below]; exact Or.inl below
      | inr atLeast =>
          rw [if_neg (Nat.not_lt.mpr atLeast)]
          exact Or.inr (Nat.add_le_add_right atLeast 2)

/-- The backmap undoes the forward map on every token — the round-trip law that makes the forward map's image
distinct exactly when its source is. -/
theorem cupEndTokenBackmap_cupEndTokenForward (position : Nat) (token : ArcEndToken) :
    cupEndTokenBackmap position (cupEndTokenForward position token) = token := by
  cases token with
  | bottomPort _ => rfl
  | openSlot slotPosition =>
      cases Nat.lt_or_ge slotPosition position with
      | inl below =>
          show cupEndTokenBackmap position (ArcEndToken.openSlot
              (if slotPosition < position then slotPosition else slotPosition + 2))
            = ArcEndToken.openSlot slotPosition
          rw [if_pos below]
          show ArcEndToken.openSlot (if slotPosition < position then slotPosition else slotPosition - 2)
            = ArcEndToken.openSlot slotPosition
          rw [if_pos below]
      | inr atLeast =>
          have notBelow : ¬ slotPosition < position := Nat.not_lt.mpr atLeast
          have notPast : ¬ slotPosition + 2 < position :=
            fun past => notBelow (Nat.lt_of_le_of_lt (Nat.le_add_right slotPosition 2) past)
          show cupEndTokenBackmap position (ArcEndToken.openSlot
              (if slotPosition < position then slotPosition else slotPosition + 2))
            = ArcEndToken.openSlot slotPosition
          rw [if_neg notBelow]
          show ArcEndToken.openSlot
              (if slotPosition + 2 < position then slotPosition + 2 else slotPosition + 2 - 2)
            = ArcEndToken.openSlot slotPosition
          rw [if_neg notPast]
          exact congrArg ArcEndToken.openSlot (addSubCancelRight slotPosition 2)

/-- The forward map preserves token validity: old valid tokens map to spliced valid tokens. -/
theorem cupEndTokenForward_isValid (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (token : ArcEndToken) (validOld : isValidArcEndToken seedBoundary state token) :
    isValidArcEndToken seedBoundary (stepCupArc state position) (cupEndTokenForward position token) := by
  cases token with
  | bottomPort portValue => exact validOld
  | openSlot slotPosition =>
      show (if slotPosition < position then slotPosition else slotPosition + 2)
        < (stepCupArc state position).openWires.length
      rw [arcCupNewOpenLength]
      cases Nat.lt_or_ge slotPosition position with
      | inl below =>
          rw [if_pos below]
          exact Nat.lt_of_lt_of_le validOld (Nat.le_add_right state.openWires.length 2)
      | inr atLeast =>
          rw [if_neg (Nat.not_lt.mpr atLeast)]
          exact Nat.add_lt_add_right validOld 2

/-- The forward map preserves the read node — derived from `cupEndTokenBackmap_node` (the image is old-zone)
and the round-trip law, so no fresh index bookkeeping is needed. -/
theorem cupEndTokenForward_node (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) (token : ArcEndToken) :
    arcEndTokenNode (stepCupArc state position) (cupEndTokenForward position token)
      = arcEndTokenNode state token := by
  rw [cupEndTokenBackmap_node state position cupInRange (cupEndTokenForward position token)
      (cupEndTokenForward_isOldZone position token),
    cupEndTokenBackmap_cupEndTokenForward position token]

/-! ## Fresh-node bound for valid old tokens -/

/-- Every valid old token reads a node strictly below `nextFresh`: bottom ports sit below the seed boundary
(hence below `nextFresh`), open slots read a current open wire (all fresh-bounded). -/
theorem arcEndTokenNode_below_ofValid (seedBoundary : Nat) (state : ArcWireState)
    (fresh : ArcStateFresh state) (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (token : ArcEndToken) (valid : isValidArcEndToken seedBoundary state token) :
    arcEndTokenNode state token < state.nextFresh := by
  cases token with
  | bottomPort portValue => exact Nat.lt_of_lt_of_le valid seedBelowFresh
  | openSlot slotPosition =>
      exact fresh.1 (natListGetAt state.openWires slotPosition)
        (natListGetAt_mem_inRange state.openWires slotPosition valid)

/-! ## The two cup legs share a component -/

/-- The two fresh cup legs `nextFresh` and `nextFresh + 1` share a component after the step — both root at
`nextFresh + 1`. -/
theorem stepCupArc_legs_sameComponent (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    isSameComponent (stepCupArc state position).links state.nextFresh (state.nextFresh + 1) = true := by
  show (unionFindRootOf (stepCupArc state position).links state.nextFresh
      == unionFindRootOf (stepCupArc state position).links (state.nextFresh + 1)) = true
  rw [stepCupArc_root_leftLeg state position fresh forest,
    stepCupArc_root_rightLeg state position fresh forest]
  exact decide_eq_true rfl

/-! ## The stepCupArc preservation of the token-frame perfect matching -/

/-- ★ **A CUP step preserves the token-frame perfect matching.**  Each valid spliced token is old-zone or a
cup leg; a leg pairs with its sibling (`stepCupArc_legs_sameComponent`), an old-zone token forwards its old
partner (`cupEndTokenForward`) with same-component transfer through the cup's component transparency. -/
theorem arcPerfectMatchingTokens_stepCupArc (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (oldPerfect : ArcPerfectMatchingTokens seedBoundary state) :
    ArcPerfectMatchingTokens seedBoundary (stepCupArc state position) := by
  intro token valid
  rcases arcCupTokenNodeClass seedBoundary state position fresh seedBelowFresh cupInRange token valid with
    nodeBelow | isLeg
  · -- OLD-ZONE: backmap to an old token, forward its old partner
    have zone : isCupOldZoneToken position token :=
      arcCupNodeBelowImpliesZone state position cupInRange token nodeBelow
    have oldValid : isValidArcEndToken seedBoundary state (cupEndTokenBackmap position token) :=
      cupEndTokenBackmap_isValid seedBoundary state position token zone cupInRange valid
    obtain ⟨oldPartner, oldPartnerValid, oldPartnerNe, oldSame⟩ :=
      oldPerfect (cupEndTokenBackmap position token) oldValid
    refine ⟨cupEndTokenForward position oldPartner, ?_, ?_, ?_⟩
    · exact cupEndTokenForward_isValid seedBoundary state position oldPartner oldPartnerValid
    · intro forwardEqToken
      have backEq : cupEndTokenBackmap position (cupEndTokenForward position oldPartner)
          = cupEndTokenBackmap position token :=
        congrArg (cupEndTokenBackmap position) forwardEqToken
      rw [cupEndTokenBackmap_cupEndTokenForward] at backEq
      exact oldPartnerNe backEq
    · have partnerNodeEq : arcEndTokenNode (stepCupArc state position) (cupEndTokenForward position oldPartner)
          = arcEndTokenNode state oldPartner :=
        cupEndTokenForward_node state position cupInRange oldPartner
      have tokenNodeEq : arcEndTokenNode (stepCupArc state position) token
          = arcEndTokenNode state (cupEndTokenBackmap position token) :=
        cupEndTokenBackmap_node state position cupInRange token zone
      have tokenNodeBelow : arcEndTokenNode state (cupEndTokenBackmap position token) < state.nextFresh :=
        arcEndTokenNode_below_ofValid seedBoundary state fresh seedBelowFresh
          (cupEndTokenBackmap position token) oldValid
      have partnerNodeBelow : arcEndTokenNode state oldPartner < state.nextFresh :=
        arcEndTokenNode_below_ofValid seedBoundary state fresh seedBelowFresh oldPartner oldPartnerValid
      rw [partnerNodeEq, tokenNodeEq,
        isSameComponent_stepCupArc_oldNodes state position fresh forest
          (arcEndTokenNode state (cupEndTokenBackmap position token))
          (arcEndTokenNode state oldPartner) tokenNodeBelow partnerNodeBelow]
      exact oldSame
  · -- LEG: pair with the sibling leg
    have positionValid : position < (stepCupArc state position).openWires.length := by
      rw [arcCupNewOpenLength]
      exact Nat.lt_of_le_of_lt cupInRange (Nat.lt_add_of_pos_right (by decide))
    have positionSuccValid : position + 1 < (stepCupArc state position).openWires.length := by
      rw [arcCupNewOpenLength]
      exact Nat.add_lt_add_right (Nat.lt_of_le_of_lt cupInRange (Nat.lt_succ_self _)) 1
    have legsSame : isSameComponent (stepCupArc state position).links state.nextFresh (state.nextFresh + 1)
        = true :=
      stepCupArc_legs_sameComponent state position fresh forest
    cases isLeg with
    | inl tokenIsLeftLeg =>
        refine ⟨ArcEndToken.openSlot (position + 1), positionSuccValid, ?_, ?_⟩
        · intro partnerEqToken
          rw [tokenIsLeftLeg] at partnerEqToken
          injection partnerEqToken with slotEq
          exact Nat.lt_irrefl position
            (Eq.mp (congrArg (position < ·) slotEq) (Nat.lt_succ_self position))
        · rw [tokenIsLeftLeg, arcCupLeftLegNode state position cupInRange,
            arcCupRightLegNode state position cupInRange]
          exact legsSame
    | inr tokenIsRightLeg =>
        refine ⟨ArcEndToken.openSlot position, positionValid, ?_, ?_⟩
        · intro partnerEqToken
          rw [tokenIsRightLeg] at partnerEqToken
          injection partnerEqToken with slotEq
          exact Nat.lt_irrefl position
            (Eq.mp (congrArg (position < ·) slotEq.symm) (Nat.lt_succ_self position))
        · rw [tokenIsRightLeg, arcCupRightLegNode state position cupInRange,
            arcCupLeftLegNode state position cupInRange]
          exact isSameComponent_symm (stepCupArc state position).links state.nextFresh
            (state.nextFresh + 1) ▸ legsSame

/-! ## Honesty marker -/

/-- **Honesty marker — a CUP step preserves the token-frame perfect matching (noFixedPoint rung, cup half).**
`cupEndTokenForward` (the old→spliced token map, inverse of `cupEndTokenBackmap` on the old zone) with its
old-zone / round-trip / validity / node-preservation lemmas, `stepCupArc_legs_sameComponent` (the two fresh
legs share a component), and `arcPerfectMatchingTokens_stepCupArc` (the full preservation for an in-range cup
over a fresh forest).  What this marker does NOT claim: the DUAL stepCapArc preservation (the strand merge),
the whole-spine fold, or the extracted-state token→range bridge to `noFixedPoint`.  `= true`. -/
def fxMode_hasArcPerfectMatchingCupPreservation : Bool := true

end FX1Poly.Polygraph
