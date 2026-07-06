import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatching
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCapPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentPersistence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # ArcPerfectMatchingCapPreservation — a CAP step preserves the token-frame perfect matching (noFixedPoint rung, cap half)

The strand MERGE: a cap removes the two adjacent window wires and joins their components.  Preserving
`ArcPerfectMatchingTokens` splits into two cases for a surviving capped token `token` (backmapped to the old
token `oldToken`, whose old partner is `oldPartner`):

  * **survivor** — `oldPartner` is NOT one of the two removed wires: forward it to a spliced token, same
    component through the cap's join monotonicity.
  * **merge** — `oldPartner` IS a removed wire (`leftWire`/`rightWire`).  Here the census is load-bearing:
    if a THIRD boundary token (`oldToken`) shared the removed wire's component, `{oldToken, leftWire,
    rightWire}` would be three ends of one component when `leftWire ~ rightWire` — a census violation.  So the
    sibling wire's old partner is a genuine SURVIVOR, and `token` reaches it through the capped join
    `leftWire ~ rightWire`.

Consumes the shipped cap backmap kit (`capEndTokenBackmap`, `_node`/`_isValid`/`_missesLeftWindow`/
`_missesRightWindow`) and cap join monotonicity (`isSameComponent_stepCapArc_ofBase`); adds the forward token
map `capEndTokenForward` (defined on survivors) and the two case helpers.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean Nat plumbing -/

/-- `(amount + base) - base = amount`, hand-rolled clean. -/
private theorem addSubBaseCancelCap : (amount base : Nat) → (amount + base) - base = amount
  | amount, 0 => by rw [Nat.add_zero, Nat.sub_zero]
  | amount, base + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact addSubBaseCancelCap amount base

/-- `2 ≤ value → value - 2 + 2 = value`, hand-rolled clean. -/
private theorem subTwoAddTwo (value : Nat) (twoLe : 2 ≤ value) : value - 2 + 2 = value := by
  obtain ⟨remainder, remainderSpec⟩ := Nat.le.dest twoLe
  rw [← remainderSpec, Nat.add_comm 2 remainder, addSubBaseCancelCap remainder 2]

/-- Right-cancellation for `≤`, hand-rolled clean (Init's `Nat.le_of_add_le_add_right` leaks propext). -/
private theorem leOfAddRightLe : (amount base delta : Nat) →
    amount + delta ≤ base + delta → amount ≤ base
  | amount, base, 0, order => by rw [Nat.add_zero, Nat.add_zero] at order; exact order
  | amount, base, delta + 1, order => by
      rw [Nat.add_succ, Nat.add_succ] at order
      exact leOfAddRightLe amount base delta (Nat.le_of_succ_le_succ order)

/-- Right-cancellation for `<`, hand-rolled clean (Init's `Nat.lt_of_add_lt_add_right` leaks propext). -/
private theorem ltOfAddRightLt : (amount base delta : Nat) →
    amount + delta < base + delta → amount < base
  | amount, base, 0, order => by rw [Nat.add_zero, Nat.add_zero] at order; exact order
  | amount, base, delta + 1, order => by
      rw [Nat.add_succ, Nat.add_succ] at order
      exact ltOfAddRightLt amount base delta (Nat.lt_of_succ_lt_succ order)

/-! ## The survivor predicate and the forward token map -/

/-- Is this old token a CAP SURVIVOR — a boundary end that stays after the cap removes the two window wires?
Bottom ports always survive; an open slot survives when it is not one of the two consumed window positions. -/
def isCapSurvivorToken (position : Nat) : ArcEndToken → Prop
  | ArcEndToken.bottomPort _ => True
  | ArcEndToken.openSlot slotPosition => slotPosition < position ∨ position + 2 ≤ slotPosition

/-- Map a surviving old-state boundary end forward to the CAPPED state: bottom ports are untouched; a
below-window slot keeps its position, an above-window slot shifts down over the removed pair.  The inverse of
`capEndTokenBackmap` on the survivors. -/
def capEndTokenForward (position : Nat) : ArcEndToken → ArcEndToken
  | ArcEndToken.bottomPort portValue => ArcEndToken.bottomPort portValue
  | ArcEndToken.openSlot slotPosition =>
      ArcEndToken.openSlot (if slotPosition < position then slotPosition else slotPosition - 2)

/-- The backmap undoes the forward map on survivors — the round-trip law. -/
theorem capEndTokenBackmap_capEndTokenForward (position : Nat) (token : ArcEndToken)
    (survivor : isCapSurvivorToken position token) :
    capEndTokenBackmap position (capEndTokenForward position token) = token := by
  cases token with
  | bottomPort _ => rfl
  | openSlot slotPosition =>
      cases survivor with
      | inl below =>
          show capEndTokenBackmap position (ArcEndToken.openSlot
              (if slotPosition < position then slotPosition else slotPosition - 2))
            = ArcEndToken.openSlot slotPosition
          rw [if_pos below]
          show ArcEndToken.openSlot (freshShiftAbove position 2 slotPosition)
            = ArcEndToken.openSlot slotPosition
          rw [freshShiftAbove_ofNotLe position 2 slotPosition
            (fun windowLeSlot => Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot below))]
      | inr atLeast =>
          have notBelow : ¬ slotPosition < position := fun below =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_add_right position 2) atLeast) below)
          show capEndTokenBackmap position (ArcEndToken.openSlot
              (if slotPosition < position then slotPosition else slotPosition - 2))
            = ArcEndToken.openSlot slotPosition
          rw [if_neg notBelow]
          show ArcEndToken.openSlot (freshShiftAbove position 2 (slotPosition - 2))
            = ArcEndToken.openSlot slotPosition
          have posLeSub : position ≤ slotPosition - 2 := by
            obtain ⟨remainder, remainderSpec⟩ := Nat.le.dest atLeast
            have subEq : slotPosition - 2 = position + remainder := by
              rw [← remainderSpec, Nat.add_right_comm position 2 remainder,
                addSubBaseCancelCap (position + remainder) 2]
            rw [subEq]; exact Nat.le_add_right position remainder
          have twoLe : 2 ≤ slotPosition := Nat.le_trans (Nat.le_add_left 2 position) atLeast
          rw [freshShiftAbove_ofLe position 2 (slotPosition - 2) posLeSub, subTwoAddTwo slotPosition twoLe]

/-- The forward map preserves token validity on survivors. -/
theorem capEndTokenForward_isValid (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length)
    (token : ArcEndToken) (survivor : isCapSurvivorToken position token)
    (validOld : isValidArcEndToken seedBoundary state token) :
    isValidArcEndToken seedBoundary (stepCapArc state position) (capEndTokenForward position token) := by
  cases token with
  | bottomPort portValue => exact validOld
  | openSlot slotPosition =>
      show (if slotPosition < position then slotPosition else slotPosition - 2)
        < (natListRemoveTwoAt state.openWires position).length
      have lengthSplit : (natListRemoveTwoAt state.openWires position).length + 2
          = state.openWires.length := natListRemoveTwoAt_length state.openWires position capInRange
      have posLeNew : position ≤ (natListRemoveTwoAt state.openWires position).length := by
        have shifted : position + 2 ≤ (natListRemoveTwoAt state.openWires position).length + 2 := by
          rw [lengthSplit]; exact capInRange
        exact leOfAddRightLe position (natListRemoveTwoAt state.openWires position).length 2 shifted
      cases survivor with
      | inl below =>
          rw [if_pos below]
          exact Nat.lt_of_lt_of_le below posLeNew
      | inr atLeast =>
          have notBelow : ¬ slotPosition < position := fun below =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_add_right position 2) atLeast) below)
          rw [if_neg notBelow]
          have twoLe : 2 ≤ slotPosition := Nat.le_trans (Nat.le_add_left 2 position) atLeast
          have slotLtNewPlusTwo : slotPosition
              < (natListRemoveTwoAt state.openWires position).length + 2 := by
            rw [lengthSplit]; exact validOld
          have subForm : slotPosition - 2 + 2
              < (natListRemoveTwoAt state.openWires position).length + 2 := by
            rw [subTwoAddTwo slotPosition twoLe]; exact slotLtNewPlusTwo
          exact ltOfAddRightLt (slotPosition - 2)
            (natListRemoveTwoAt state.openWires position).length 2 subForm

/-- The forward map preserves the read node on survivors — derived from `capEndTokenBackmap_node` and the
round-trip law. -/
theorem capEndTokenForward_node (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) (token : ArcEndToken)
    (survivor : isCapSurvivorToken position token) :
    arcEndTokenNode (stepCapArc state position) (capEndTokenForward position token)
      = arcEndTokenNode state token := by
  rw [capEndTokenBackmap_node state position capInRange (capEndTokenForward position token),
    capEndTokenBackmap_capEndTokenForward position token survivor]

/-! ## The two capped wires share a component -/

/-- After a cap, the two removed window wires are in the same component (the cap joins them). -/
theorem stepCapArc_wires_sameComponent (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) :
    isSameComponent (stepCapArc state position).links
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)) = true := by
  show isSameComponent
      (unionFindJoin
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        state.nextFresh (natListGetAt state.openWires position))
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)) = true
  exact isSameComponent_unionFindJoin_ofBase
    (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)))
    (isUnionFindForest_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) forest)
    state.nextFresh (natListGetAt state.openWires position)
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (isSameComponent_unionFindJoin_joined state.links forest
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)))

/-! ## The survivor case -/

/-- **Survivor case**: the old partner is not a removed wire, so forward it. -/
private theorem capPerfectMatchingSurvivorCase (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links)
    (capInRange : position + 2 ≤ state.openWires.length)
    (token oldToken : ArcEndToken)
    (oldTokenIsBackmap : oldToken = capEndTokenBackmap position token)
    (tokenNodeEq : arcEndTokenNode (stepCapArc state position) token = arcEndTokenNode state oldToken)
    (oldPartner : ArcEndToken)
    (oldPartnerValid : isValidArcEndToken seedBoundary state oldPartner)
    (oldPartnerNe : oldPartner ≠ oldToken)
    (oldSame : isSameComponent state.links
      (arcEndTokenNode state oldToken) (arcEndTokenNode state oldPartner) = true)
    (partnerSurvivor : isCapSurvivorToken position oldPartner) :
    ∃ partner, isValidArcEndToken seedBoundary (stepCapArc state position) partner ∧ partner ≠ token ∧
      isSameComponent (stepCapArc state position).links
        (arcEndTokenNode (stepCapArc state position) token)
        (arcEndTokenNode (stepCapArc state position) partner) = true := by
  refine ⟨capEndTokenForward position oldPartner, ?_, ?_, ?_⟩
  · exact capEndTokenForward_isValid seedBoundary state position capInRange oldPartner partnerSurvivor
      oldPartnerValid
  · intro forwardEqToken
    have backEq : capEndTokenBackmap position (capEndTokenForward position oldPartner)
        = capEndTokenBackmap position token := congrArg (capEndTokenBackmap position) forwardEqToken
    rw [capEndTokenBackmap_capEndTokenForward position oldPartner partnerSurvivor] at backEq
    exact oldPartnerNe (backEq.trans oldTokenIsBackmap.symm)
  · rw [capEndTokenForward_node state position capInRange oldPartner partnerSurvivor, tokenNodeEq]
    exact isSameComponent_stepCapArc_ofBase state position forest
      (arcEndTokenNode state oldToken) (arcEndTokenNode state oldPartner) oldSame

/-! ## The merge case -/

/-- **Merge case**: the old partner IS a removed wire.  The census forbids a third boundary token sharing a
capped-together component, so the sibling wire's old partner is a genuine survivor that `token` reaches
through the capped join. -/
private theorem capPerfectMatchingMergeCase (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links)
    (capInRange : position + 2 ≤ state.openWires.length)
    (census : ArcBoundaryCensus seedBoundary state)
    (oldPerfect : ArcPerfectMatchingTokens seedBoundary state)
    (token oldToken : ArcEndToken)
    (oldTokenIsBackmap : oldToken = capEndTokenBackmap position token)
    (oldTokenValid : isValidArcEndToken seedBoundary state oldToken)
    (tokenNodeEq : arcEndTokenNode (stepCapArc state position) token = arcEndTokenNode state oldToken)
    (connectedWire siblingWire : ArcEndToken)
    (connectedValid : isValidArcEndToken seedBoundary state connectedWire)
    (siblingValid : isValidArcEndToken seedBoundary state siblingWire)
    (connectedIsWindow : connectedWire = ArcEndToken.openSlot position
      ∨ connectedWire = ArcEndToken.openSlot (position + 1))
    (siblingIsWindow : siblingWire = ArcEndToken.openSlot position
      ∨ siblingWire = ArcEndToken.openSlot (position + 1))
    (connectedNeSibling : connectedWire ≠ siblingWire)
    (oldTokenNeConnected : oldToken ≠ connectedWire)
    (oldTokenNeSibling : oldToken ≠ siblingWire)
    (oldSameConnected : isSameComponent state.links
      (arcEndTokenNode state oldToken) (arcEndTokenNode state connectedWire) = true)
    (cappedConnectedSibling : isSameComponent (stepCapArc state position).links
      (arcEndTokenNode state connectedWire) (arcEndTokenNode state siblingWire) = true) :
    ∃ partner, isValidArcEndToken seedBoundary (stepCapArc state position) partner ∧ partner ≠ token ∧
      isSameComponent (stepCapArc state position).links
        (arcEndTokenNode (stepCapArc state position) token)
        (arcEndTokenNode (stepCapArc state position) partner) = true := by
  obtain ⟨siblingPartner, siblingPartnerValid, siblingPartnerNe, siblingSame⟩ :=
    oldPerfect siblingWire siblingValid
  -- the census forbids connected ~ sibling in the old state
  have connectedSiblingNotSameOld : isSameComponent state.links
      (arcEndTokenNode state connectedWire) (arcEndTokenNode state siblingWire) = true → False := by
    intro connSibSame
    exact census oldToken connectedWire siblingWire oldTokenValid connectedValid siblingValid
      oldTokenNeConnected oldTokenNeSibling connectedNeSibling oldSameConnected
      (isSameComponent_trans state.links (arcEndTokenNode state oldToken)
        (arcEndTokenNode state connectedWire) (arcEndTokenNode state siblingWire)
        oldSameConnected connSibSame)
  -- the sibling's partner is distinct from the connected wire and from oldToken
  have partnerNeConnected : siblingPartner ≠ connectedWire := fun eq =>
    connectedSiblingNotSameOld
      ((isSameComponent_symm state.links (arcEndTokenNode state siblingWire)
          (arcEndTokenNode state connectedWire)) ▸ (eq ▸ siblingSame))
  have partnerNeOldToken : siblingPartner ≠ oldToken := fun eq =>
    connectedSiblingNotSameOld
      (isSameComponent_trans state.links (arcEndTokenNode state connectedWire)
        (arcEndTokenNode state oldToken) (arcEndTokenNode state siblingWire)
        (isSameComponent_symm state.links (arcEndTokenNode state oldToken)
          (arcEndTokenNode state connectedWire) ▸ oldSameConnected)
        ((isSameComponent_symm state.links (arcEndTokenNode state siblingWire)
            (arcEndTokenNode state oldToken)) ▸ (eq ▸ siblingSame)))
  -- the sibling's partner misses both window slots, so it is a survivor
  have partnerNeLeft : siblingPartner ≠ ArcEndToken.openSlot position := by
    intro eqLeft
    cases connectedIsWindow with
    | inl connIsLeft => exact partnerNeConnected (eqLeft.trans connIsLeft.symm)
    | inr connIsRight =>
        cases siblingIsWindow with
        | inl sibIsLeft => exact siblingPartnerNe (eqLeft.trans sibIsLeft.symm)
        | inr sibIsRight => exact connectedNeSibling (connIsRight.trans sibIsRight.symm)
  have partnerNeRight : siblingPartner ≠ ArcEndToken.openSlot (position + 1) := by
    intro eqRight
    cases connectedIsWindow with
    | inl connIsLeft =>
        cases siblingIsWindow with
        | inl sibIsLeft => exact connectedNeSibling (connIsLeft.trans sibIsLeft.symm)
        | inr sibIsRight => exact siblingPartnerNe (eqRight.trans sibIsRight.symm)
    | inr connIsRight => exact partnerNeConnected (eqRight.trans connIsRight.symm)
  have partnerSurvivor : isCapSurvivorToken position siblingPartner := by
    cases hPartner : siblingPartner with
    | bottomPort _ => exact True.intro
    | openSlot slotPartner =>
        show slotPartner < position ∨ position + 2 ≤ slotPartner
        have slotNePos : slotPartner ≠ position := fun eq =>
          partnerNeLeft (hPartner.trans (congrArg ArcEndToken.openSlot eq))
        have slotNeSucc : slotPartner ≠ position + 1 := fun eq =>
          partnerNeRight (hPartner.trans (congrArg ArcEndToken.openSlot eq))
        rcases Nat.lt_or_ge slotPartner position with below | atLeast
        · exact Or.inl below
        · rcases Nat.lt_or_ge slotPartner (position + 2) with belowTwo | geTwo
          · rcases Nat.lt_or_ge slotPartner (position + 1) with belowOne | geOne
            · exact absurd (Nat.le_antisymm (Nat.le_of_lt_succ belowOne) atLeast) slotNePos
            · exact absurd (Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) geOne) slotNeSucc
          · exact Or.inr geTwo
  -- forward the sibling's partner; token reaches it through the capped join
  refine ⟨capEndTokenForward position siblingPartner, ?_, ?_, ?_⟩
  · exact capEndTokenForward_isValid seedBoundary state position capInRange siblingPartner
      partnerSurvivor siblingPartnerValid
  · intro forwardEqToken
    have backEq : capEndTokenBackmap position (capEndTokenForward position siblingPartner)
        = capEndTokenBackmap position token := congrArg (capEndTokenBackmap position) forwardEqToken
    rw [capEndTokenBackmap_capEndTokenForward position siblingPartner partnerSurvivor] at backEq
    exact partnerNeOldToken (backEq.trans oldTokenIsBackmap.symm)
  · rw [capEndTokenForward_node state position capInRange siblingPartner partnerSurvivor, tokenNodeEq]
    exact isSameComponent_trans (stepCapArc state position).links
      (arcEndTokenNode state oldToken) (arcEndTokenNode state siblingWire)
      (arcEndTokenNode state siblingPartner)
      (isSameComponent_trans (stepCapArc state position).links
        (arcEndTokenNode state oldToken) (arcEndTokenNode state connectedWire)
        (arcEndTokenNode state siblingWire)
        (isSameComponent_stepCapArc_ofBase state position forest
          (arcEndTokenNode state oldToken) (arcEndTokenNode state connectedWire) oldSameConnected)
        cappedConnectedSibling)
      (isSameComponent_stepCapArc_ofBase state position forest
        (arcEndTokenNode state siblingWire) (arcEndTokenNode state siblingPartner) siblingSame)

/-! ## The stepCapArc preservation of the token-frame perfect matching -/

/-- ★ **A CAP step preserves the token-frame perfect matching** (the census is a hypothesis — it forbids the
three-ended component that a naive merge would create). -/
theorem arcPerfectMatchingTokens_stepCapArc (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links)
    (capInRange : position + 2 ≤ state.openWires.length)
    (census : ArcBoundaryCensus seedBoundary state)
    (oldPerfect : ArcPerfectMatchingTokens seedBoundary state) :
    ArcPerfectMatchingTokens seedBoundary (stepCapArc state position) := by
  intro token valid
  have oldValid : isValidArcEndToken seedBoundary state (capEndTokenBackmap position token) :=
    capEndTokenBackmap_isValid seedBoundary state position capInRange token valid
  have tokenNodeEq : arcEndTokenNode (stepCapArc state position) token
      = arcEndTokenNode state (capEndTokenBackmap position token) :=
    capEndTokenBackmap_node state position capInRange token
  have oldTokenNeLeft : capEndTokenBackmap position token ≠ ArcEndToken.openSlot position :=
    capEndTokenBackmap_missesLeftWindow position token
  have oldTokenNeRight : capEndTokenBackmap position token ≠ ArcEndToken.openSlot (position + 1) :=
    capEndTokenBackmap_missesRightWindow position token
  have leftValid : isValidArcEndToken seedBoundary state (ArcEndToken.openSlot position) := by
    show position < state.openWires.length
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) capInRange
  have rightValid : isValidArcEndToken seedBoundary state (ArcEndToken.openSlot (position + 1)) := by
    show position + 1 < state.openWires.length
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) position) capInRange
  have leftNeRight : ArcEndToken.openSlot position ≠ ArcEndToken.openSlot (position + 1) := by
    intro eq
    injection eq with slotEq
    exact Nat.lt_irrefl position
      (Eq.mp (congrArg (position < ·) slotEq.symm) (Nat.lt_succ_self position))
  have cappedWiresSame : isSameComponent (stepCapArc state position).links
      (arcEndTokenNode state (ArcEndToken.openSlot position))
      (arcEndTokenNode state (ArcEndToken.openSlot (position + 1))) = true :=
    stepCapArc_wires_sameComponent state position forest
  obtain ⟨oldPartner, oldPartnerValid, oldPartnerNe, oldSame⟩ :=
    oldPerfect (capEndTokenBackmap position token) oldValid
  cases oldPartner with
  | bottomPort portValue =>
      exact capPerfectMatchingSurvivorCase seedBoundary state position forest capInRange token
        (capEndTokenBackmap position token) rfl tokenNodeEq (ArcEndToken.bottomPort portValue)
        oldPartnerValid oldPartnerNe oldSame True.intro
  | openSlot slotPartner =>
      rcases Nat.lt_or_ge slotPartner position with slotBelow | slotAtLeast
      · exact capPerfectMatchingSurvivorCase seedBoundary state position forest capInRange token
          (capEndTokenBackmap position token) rfl tokenNodeEq (ArcEndToken.openSlot slotPartner)
          oldPartnerValid oldPartnerNe oldSame (Or.inl slotBelow)
      · rcases Nat.lt_or_ge slotPartner (position + 1) with slotBelowOne | slotAtLeastOne
        · -- slotPartner = position: connected = leftWire, sibling = rightWire
          have slotEqPos : slotPartner = position :=
            Nat.le_antisymm (Nat.le_of_lt_succ slotBelowOne) slotAtLeast
          exact capPerfectMatchingMergeCase seedBoundary state position forest capInRange census
            oldPerfect token (capEndTokenBackmap position token) rfl oldValid tokenNodeEq
            (ArcEndToken.openSlot position) (ArcEndToken.openSlot (position + 1)) leftValid rightValid
            (Or.inl rfl) (Or.inr rfl) leftNeRight oldTokenNeLeft oldTokenNeRight
            (slotEqPos ▸ oldSame) cappedWiresSame
        · rcases Nat.lt_or_ge slotPartner (position + 2) with slotBelowTwo | slotAtLeastTwo
          · -- slotPartner = position + 1: connected = rightWire, sibling = leftWire
            have slotEqSucc : slotPartner = position + 1 :=
              Nat.le_antisymm (Nat.le_of_lt_succ slotBelowTwo) slotAtLeastOne
            exact capPerfectMatchingMergeCase seedBoundary state position forest capInRange census
              oldPerfect token (capEndTokenBackmap position token) rfl oldValid tokenNodeEq
              (ArcEndToken.openSlot (position + 1)) (ArcEndToken.openSlot position) rightValid leftValid
              (Or.inr rfl) (Or.inl rfl) (fun eq => leftNeRight eq.symm) oldTokenNeRight oldTokenNeLeft
              (slotEqSucc ▸ oldSame)
              (isSameComponent_symm (stepCapArc state position).links
                (arcEndTokenNode state (ArcEndToken.openSlot position))
                (arcEndTokenNode state (ArcEndToken.openSlot (position + 1))) ▸ cappedWiresSame)
          · -- slotPartner ≥ position + 2: survivor
            exact capPerfectMatchingSurvivorCase seedBoundary state position forest capInRange token
              (capEndTokenBackmap position token) rfl tokenNodeEq (ArcEndToken.openSlot slotPartner)
              oldPartnerValid oldPartnerNe oldSame (Or.inr slotAtLeastTwo)

/-! ## Honesty marker -/

/-- **Honesty marker — a CAP step preserves the token-frame perfect matching (noFixedPoint rung, cap half).**
`capEndTokenForward` (the survivor forward map) with its round-trip / validity / node lemmas,
`stepCapArc_wires_sameComponent` (the two removed wires share a component), and
`arcPerfectMatchingTokens_stepCapArc` (the full CENSUS-COUPLED preservation: survivor case forwards the old
partner, merge case uses the census to forbid a three-ended component and reaches the sibling's partner
through the capped join).  What this marker does NOT claim: the whole-spine fold of
`ArcPerfectMatchingTokens` (cup+cap through `processArcSpine`) or the extracted-state token→range bridge to
`noFixedPoint`.  `= true`. -/
def fxMode_hasArcPerfectMatchingCapPreservation : Bool := true

end FX1Poly.Polygraph
