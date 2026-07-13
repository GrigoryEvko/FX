import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoBlockRootTransposition

/-! # MODE-COMMUTE r27 — the GENERAL disjoint atom-swap arms (cap x cap, cup-cap, cap-cup), full `ArcStepSimCount`

## What this ships

r26 shipped the cap x cap and mixed atom arms only at CONCRETE seeds (fields kernel-decided on a
bounded node support); the general theorems were the named r27 obligation.  This file DELIVERS them,
consuming the r27 two-block engine (`twoBlocksSigma_rootComm`): for every `WellFormedArcState`, at
general `(lowPosition, gap)`, the two firing orders of each disjoint atom pair are related by a full
eight-field `ArcStepSimCount` whose carrier is the width-matched block rotation:

  * `arcDisjointCapCapSwapSimCount_ofWellFormed` — CAP x CAP at `blockRotate nextFresh 1 1`, guarded
    by THREE component disequalities (the machine-sharp guard: the two windows' first reads must not
    share a component with the other window's reads; the second-read/second-read pair `b1 ~ d` is NOT
    excluded — two merges into a shared target commute);
  * `arcDisjointCupCapSwapSimCount_ofWellFormed` — CUP-then-CAP at `blockRotate nextFresh 3 1`,
    UNGUARDED beyond window validity (the cup block is fresh, hence support-disjoint);
  * `arcDisjointCapCupSwapSimCount_ofWellFormed` — CAP-then-CUP at `blockRotate nextFresh 1 3`,
    likewise unguarded.

Together with the shipped cup x cup engine (`twoCupGodement_arcStepSimCount`, r25-consumed), ALL FOUR
ordered atom pairs now have general full-sim swap theorems over the bundle — the complete atom base
the whole-cell double fold (`atomPastCell` -> `cellPastCell`) consumes.

## Position discipline (the r26-confirmed arithmetic, at general parameters)

The left atom fires at `lowPosition` (consuming `domWidth` wires, producing `codWidth`); the right
atom's window starts at `lowPosition + domWidth + gap` in PRE-left coordinates and at
`lowPosition + codWidth + gap` in POST-left coordinates.  Instantiated: cap x cap redex
`low / gap+low`, reduct `gap+2+low / low`; cup-cap redex `low / gap+2+low`, reduct `gap+low / low`;
cap-cup redex `low / gap+low`, reduct `gap+2+low / low`.

## The fires

Each general arm is FIRED on the corresponding r26 concrete seed, upgrading the r26 bounded-support
`decide` fields to the full unbounded `ArcStepSimCount` term (the universal `rootComm` / `cupCorr` /
`capCorr` over ALL of `Nat`).

Raw Lean 4 + Init; structural list recursions for the splice/removal transpositions, engine
composition for the root fields, `countEventsInRoot_rootComm` for the count fields.
Per-declaration `#assert_no_axioms` + independent `#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat micro-helpers (propext-free) -/

/-- `n < k + n` for positive `k` (avoiding the core lemma-name lottery; `Nat.zero_add` is clean). -/
private theorem ltAddOfPosLeft (n k : Nat) (isPositive : 0 < k) : n < k + n := by
  have shifted : 0 + n < k + n := Nat.add_lt_add_right isPositive n
  rw [Nat.zero_add] at shifted
  exact shifted

/-- `n + 1 < k + 2 + n` (the second-read strict bound below a removal two to the right). -/
private theorem succLtAddTwoLeft (n k : Nat) : n + 1 < k + 2 + n := by
  have shifted : 1 + n < (k + 2) + n :=
    Nat.add_lt_add_right (Nat.succ_lt_succ (Nat.succ_pos k)) n
  rw [Nat.add_comm 1 n] at shifted
  exact shifted

/-- `n < n + 2` (explicit, unification-stable). -/
private theorem selfLtAddTwo (n : Nat) : n < n + 2 :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_succ (n + 1))

/-- `n < n + 3` (explicit, unification-stable). -/
private theorem selfLtAddThree (n : Nat) : n < n + 3 :=
  Nat.lt_of_lt_of_le (selfLtAddTwo n) (Nat.le_succ (n + 2))

/-! ## List surgery lemmas — splice/removal transposition and read shifts -/

/-- The cons-successor read-off of the wire read (the `natListRemoveTwoAt_succ` companion). -/
theorem natListGetAt_consSucc (headWire : Nat) (restWires : List Nat) (position : Nat) :
    natListGetAt (headWire :: restWires) (position + 1) = natListGetAt restWires position := by
  cases restWires <;> rfl

/-- ★ **Read shift over a removal below** — reading at `offset + low` after removing two at `low`
reads the original position `offset + low + 2` (window validity `low + 2 <= length`). -/
theorem natListGetAt_removeTwoAt_shift :
    (wires : List Nat) → (lowPosition offset : Nat) → lowPosition + 2 ≤ wires.length →
    natListGetAt (natListRemoveTwoAt wires lowPosition) (offset + lowPosition)
      = natListGetAt wires (offset + lowPosition + 2)
  | [], 0, _, window => absurd window (Nat.not_succ_le_zero 1)
  | [_], 0, _, window => absurd (Nat.le_of_succ_le_succ window) (Nat.not_succ_le_zero 0)
  | headOne :: headTwo :: restWires, 0, offset, _ => by
      have collapseIndex : offset + 0 = offset := rfl
      have splitIndex : offset + 0 + 2 = (offset + 1) + 1 := rfl
      rw [show natListRemoveTwoAt (headOne :: headTwo :: restWires) 0 = restWires from rfl,
        collapseIndex, splitIndex,
        natListGetAt_consSucc headOne (headTwo :: restWires) (offset + 1),
        natListGetAt_consSucc headTwo restWires offset]
  | [], lowPosition + 1, _, window => absurd window (Nat.not_succ_le_zero (lowPosition + 2))
  | headWire :: restWires, lowPosition + 1, offset, window => by
      have stepIndex : offset + (lowPosition + 1) = (offset + lowPosition) + 1 := rfl
      rw [stepIndex, natListRemoveTwoAt_succ headWire restWires lowPosition]
      show natListGetAt (natListRemoveTwoAt restWires lowPosition) (offset + lowPosition)
        = natListGetAt restWires (offset + lowPosition + 2)
      exact natListGetAt_removeTwoAt_shift restWires lowPosition offset
        (Nat.le_of_succ_le_succ window)

/-- ★ **Read stability below a removal above** — reading strictly below the removal position is
untouched.  Unconditional. -/
theorem natListGetAt_removeTwoAt_below :
    (wires : List Nat) → (removalPosition readPosition : Nat) → readPosition < removalPosition →
    natListGetAt (natListRemoveTwoAt wires removalPosition) readPosition
      = natListGetAt wires readPosition
  | _, 0, readPosition, isBelow => absurd isBelow (Nat.not_lt_zero readPosition)
  | [], _ + 1, _, _ => rfl
  | headWire :: restWires, removalPosition + 1, 0, _ => by
      rw [natListRemoveTwoAt_succ headWire restWires removalPosition]
      rfl
  | headWire :: restWires, removalPosition + 1, readPosition + 1, isBelow => by
      rw [natListRemoveTwoAt_succ headWire restWires removalPosition,
        natListGetAt_consSucc headWire (natListRemoveTwoAt restWires removalPosition) readPosition,
        natListGetAt_consSucc headWire restWires readPosition]
      exact natListGetAt_removeTwoAt_below restWires removalPosition readPosition
        (Nat.lt_of_succ_lt_succ isBelow)

/-- The successor-position unfolding of the splice (the `natListRemoveTwoAt_succ` companion). -/
theorem natListInsertAt_succ (headWire : Nat) (restWires : List Nat) (position : Nat)
    (block : List Nat) :
    natListInsertAt (headWire :: restWires) (position + 1) block
      = headWire :: natListInsertAt restWires position block := by
  cases restWires <;> rfl

/-- ★ **Read shift over a two-block splice below** — reading at `offset + pos + 2` after splicing a
two-block at `pos` reads the original `offset + pos` (splice validity `pos <= length`). -/
theorem natListGetAt_insertAt_shift :
    (wires : List Nat) → (insertPosition offset legOne legTwo : Nat) →
    insertPosition ≤ wires.length →
    natListGetAt (natListInsertAt wires insertPosition [legOne, legTwo])
        (offset + insertPosition + 2)
      = natListGetAt wires (offset + insertPosition)
  | wires, 0, offset, legOne, legTwo, _ => by
      have collapseIndex : offset + 0 = offset := rfl
      have splitIndex : offset + 0 + 2 = (offset + 1) + 1 := rfl
      rw [natListInsertAt_zero wires [legOne, legTwo], collapseIndex, splitIndex]
      show natListGetAt (legOne :: legTwo :: wires) ((offset + 1) + 1) = natListGetAt wires offset
      rw [natListGetAt_consSucc legOne (legTwo :: wires) (offset + 1),
        natListGetAt_consSucc legTwo wires offset]
  | [], insertPosition + 1, _, _, _, window =>
      absurd window (Nat.not_succ_le_zero insertPosition)
  | headWire :: restWires, insertPosition + 1, offset, legOne, legTwo, window => by
      have stepIndex : offset + (insertPosition + 1) = (offset + insertPosition) + 1 := rfl
      have stepIndexOuter : offset + insertPosition + 1 + 2 = (offset + insertPosition + 2) + 1 := rfl
      rw [stepIndex, stepIndexOuter, natListInsertAt_succ headWire restWires insertPosition [legOne, legTwo],
        natListGetAt_consSucc headWire (natListInsertAt restWires insertPosition [legOne, legTwo])
          (offset + insertPosition + 2)]
      show natListGetAt (natListInsertAt restWires insertPosition [legOne, legTwo])
          (offset + insertPosition + 2)
        = natListGetAt (headWire :: restWires) ((offset + insertPosition) + 1)
      rw [natListGetAt_consSucc headWire restWires (offset + insertPosition)]
      exact natListGetAt_insertAt_shift restWires insertPosition offset legOne legTwo
        (Nat.le_of_succ_le_succ window)

/-- ★ **Read stability below a splice above** — reading strictly below the splice position is
untouched (splice validity `pos <= length`). -/
theorem natListGetAt_insertAt_below :
    (wires : List Nat) → (insertPosition readPosition : Nat) → (block : List Nat) →
    readPosition < insertPosition → insertPosition ≤ wires.length →
    natListGetAt (natListInsertAt wires insertPosition block) readPosition
      = natListGetAt wires readPosition
  | _, 0, readPosition, _, isBelow, _ => absurd isBelow (Nat.not_lt_zero readPosition)
  | [], insertPosition + 1, _, _, _, window =>
      absurd window (Nat.not_succ_le_zero insertPosition)
  | headWire :: restWires, insertPosition + 1, 0, block, _, _ => by
      rw [natListInsertAt_succ headWire restWires insertPosition block]
      rfl
  | headWire :: restWires, insertPosition + 1, readPosition + 1, block, isBelow, window => by
      rw [natListInsertAt_succ headWire restWires insertPosition block,
        natListGetAt_consSucc headWire (natListInsertAt restWires insertPosition block) readPosition,
        natListGetAt_consSucc headWire restWires readPosition]
      exact natListGetAt_insertAt_below restWires insertPosition readPosition block
        (Nat.lt_of_succ_lt_succ isBelow) (Nat.le_of_succ_le_succ window)

/-! ## The sigma value read-offs at the three arm widths -/

/-- `blockRotate nf 1 1` swaps the two singleton event blocks: `nf ↦ nf+1`. -/
theorem blockRotate_oneOne_base (baseFresh : Nat) :
    blockRotate baseFresh 1 1 baseFresh = baseFresh + 1 :=
  blockRotate_firstBlock baseFresh 1 1 baseFresh (Nat.le_refl _) (Nat.lt_succ_self _)

/-- `blockRotate nf 1 1`: `nf+1 ↦ nf`. -/
theorem blockRotate_oneOne_succ (baseFresh : Nat) :
    blockRotate baseFresh 1 1 (baseFresh + 1) = baseFresh := by
  rw [blockRotate_secondBlock baseFresh 1 1 (baseFresh + 1) (Nat.le_refl _)
    (Nat.lt_succ_self _)]
  exact addSubCancelRight baseFresh 1

/-- `blockRotate nf 3 1` shifts the cup block up by one: `nf+k ↦ nf+k+1` for `k < 3`. -/
theorem blockRotate_threeOne_cup (baseFresh k : Nat) (inBlock : k < 3) :
    blockRotate baseFresh 3 1 (baseFresh + k) = baseFresh + k + 1 :=
  blockRotate_firstBlock baseFresh 3 1 (baseFresh + k) (Nat.le_add_right _ _)
    (Nat.add_lt_add_left inBlock baseFresh)

/-- `blockRotate nf 3 1` drops the trailing cap event to the base: `nf+3 ↦ nf`. -/
theorem blockRotate_threeOne_cap (baseFresh : Nat) :
    blockRotate baseFresh 3 1 (baseFresh + 3) = baseFresh := by
  rw [blockRotate_secondBlock baseFresh 3 1 (baseFresh + 3) (Nat.le_refl _)
    (Nat.lt_succ_self _)]
  exact addSubCancelRight baseFresh 3

/-- `blockRotate nf 1 3` lifts the leading cap event past the cup block: `nf ↦ nf+3`. -/
theorem blockRotate_oneThree_cap (baseFresh : Nat) :
    blockRotate baseFresh 1 3 baseFresh = baseFresh + 3 :=
  blockRotate_firstBlock baseFresh 1 3 baseFresh (Nat.le_refl _) (Nat.lt_succ_self _)

/-- `blockRotate nf 1 3` drops the cup block by one: `nf+k+1 ↦ nf+k` for `k < 3`. -/
theorem blockRotate_oneThree_cup (baseFresh k : Nat) (inBlock : k < 3) :
    blockRotate baseFresh 1 3 (baseFresh + k + 1) = baseFresh + k := by
  have lowerBound : baseFresh + 1 ≤ baseFresh + k + 1 :=
    Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) baseFresh
  have upperBound : baseFresh + k + 1 < baseFresh + 1 + 3 :=
    Nat.add_lt_add_left (Nat.succ_lt_succ inBlock) baseFresh
  rw [blockRotate_secondBlock baseFresh 1 3 (baseFresh + k + 1) lowerBound upperBound]
  exact addSubCancelRight (baseFresh + k) 1

/-! ## ARM 1 — CAP x CAP, general, at `blockRotate nextFresh 1 1` -/

/-- ★★ **The GENERAL disjoint cap x cap swap `ArcStepSimCount` over the bundle** — r26's deferred
full-sim arm, now unconditional on the node support.  Two caps at window-disjoint positions (`low`
and `gap+2+low` in shared coordinates) whose reads satisfy the THREE sharp component disequalities
(first-read vs the other window's two reads, and the second window's first read vs the first
window's second read — `b1 ~ d` sharing is permitted: merges into a shared target commute) are
`ArcStepSimCount`-related by the singleton-block rotation `blockRotate nextFresh 1 1`.  The
`rootComm` field is the r27 engine; the count fields ride `countEventsInRoot_rootComm`; the loop
field is the two-guard transposition through block locality. -/
theorem arcDisjointCapCapSwapSimCount_ofWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state)
    (window : lowPosition + 2 ≤ state.openWires.length)
    (readOneFirstDisjoint :
      isSameComponent state.links (natListGetAt state.openWires lowPosition)
        (natListGetAt state.openWires (gap + 2 + lowPosition)) = false)
    (readOneSecondDisjoint :
      isSameComponent state.links (natListGetAt state.openWires lowPosition)
        (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) = false)
    (readTwoFirstDisjoint :
      isSameComponent state.links (natListGetAt state.openWires (lowPosition + 1))
        (natListGetAt state.openWires (gap + 2 + lowPosition)) = false) :
    ArcStepSimCount (blockRotate state.nextFresh 1 1)
      (stepCapArc (stepCapArc state lowPosition) (gap + lowPosition))
      (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition) := by
  have nfPositive : 0 < state.nextFresh := wellFormed.isNonDegenerate
  have forest : isUnionFindForest state.links := wellFormed.isForest
  have wiresBelow : ∀ wire ∈ state.openWires, wire < state.nextFresh := wellFormed.isFresh.1
  have endpointsBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh :=
    wellFormed.isFresh.2.1
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge he => (endpointsBelow edge he).1
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge he => (endpointsBelow edge he).2
  -- the four reads and their root bounds
  have readRootBelow : ∀ position : Nat,
      unionFindRootOf state.links (natListGetAt state.openWires position) < state.nextFresh :=
    fun position => unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires position wiresBelow)
  have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow state.nextFresh
      (Nat.le_refl _)
  have rootNfSucc : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow (state.nextFresh + 1)
      (Nat.le_add_right _ _)
  -- component disequalities at root level
  have disOneFirst : unionFindRootOf state.links (natListGetAt state.openWires lowPosition)
      ≠ unionFindRootOf state.links (natListGetAt state.openWires (gap + 2 + lowPosition)) :=
    neOfBeqFalse readOneFirstDisjoint
  have disOneSecond : unionFindRootOf state.links (natListGetAt state.openWires lowPosition)
      ≠ unionFindRootOf state.links (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) :=
    neOfBeqFalse readOneSecondDisjoint
  have disTwoFirst : unionFindRootOf state.links (natListGetAt state.openWires (lowPosition + 1))
      ≠ unionFindRootOf state.links (natListGetAt state.openWires (gap + 2 + lowPosition)) :=
    neOfBeqFalse readTwoFirstDisjoint
  -- index bridges
  have indexBridgeFirst : gap + lowPosition + 2 = gap + 2 + lowPosition := by
    rw [Nat.add_right_comm gap lowPosition 2]
  have indexBridgeSecondEntry : gap + lowPosition + 1 = gap + 1 + lowPosition := by
    rw [Nat.add_right_comm gap lowPosition 1]
  have indexBridgeSecondExit : gap + 1 + lowPosition + 2 = gap + 2 + lowPosition + 1 := by
    rw [Nat.add_right_comm (gap + 1) lowPosition 2, Nat.add_right_comm (gap + 2) lowPosition 1]
  -- the redex links in two-block form (reads rewritten to shared coordinates)
  have linksRedex : (stepCapArc (stepCapArc state lowPosition) (gap + lowPosition)).links
      = twoJoinBlock
          (twoJoinBlock state.links (natListGetAt state.openWires lowPosition)
            (natListGetAt state.openWires (lowPosition + 1)) state.nextFresh)
          (natListGetAt state.openWires (gap + 2 + lowPosition))
          (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) (state.nextFresh + 1) := by
    show twoJoinBlock
        (twoJoinBlock state.links (natListGetAt state.openWires lowPosition)
          (natListGetAt state.openWires (lowPosition + 1)) state.nextFresh)
        (natListGetAt (natListRemoveTwoAt state.openWires lowPosition) (gap + lowPosition))
        (natListGetAt (natListRemoveTwoAt state.openWires lowPosition) (gap + lowPosition + 1))
        (state.nextFresh + 1) = _
    rw [natListGetAt_removeTwoAt_shift state.openWires lowPosition gap window, indexBridgeFirst,
      indexBridgeSecondEntry,
      natListGetAt_removeTwoAt_shift state.openWires lowPosition (gap + 1) window,
      indexBridgeSecondExit]
  -- the reduct links in two-block form (reads below the higher removal are stable)
  have lowBelowHigh : lowPosition < gap + 2 + lowPosition :=
    ltAddOfPosLeft lowPosition (gap + 2) (Nat.succ_pos _)
  have lowSuccBelowHigh : lowPosition + 1 < gap + 2 + lowPosition := succLtAddTwoLeft lowPosition gap
  have linksReduct : (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition).links
      = twoJoinBlock
          (twoJoinBlock state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
            (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) state.nextFresh)
          (natListGetAt state.openWires lowPosition)
          (natListGetAt state.openWires (lowPosition + 1)) (state.nextFresh + 1) := by
    show twoJoinBlock
        (twoJoinBlock state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
          (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) state.nextFresh)
        (natListGetAt (natListRemoveTwoAt state.openWires (gap + 2 + lowPosition)) lowPosition)
        (natListGetAt (natListRemoveTwoAt state.openWires (gap + 2 + lowPosition)) (lowPosition + 1))
        (state.nextFresh + 1) = _
    rw [natListGetAt_removeTwoAt_below state.openWires (gap + 2 + lowPosition) lowPosition
        lowBelowHigh,
      natListGetAt_removeTwoAt_below state.openWires (gap + 2 + lowPosition) (lowPosition + 1)
        lowSuccBelowHigh]
  -- the sigma value facts
  have sigmaLowRead : blockRotate state.nextFresh 1 1 (natListGetAt state.openWires lowPosition)
      = natListGetAt state.openWires lowPosition :=
    blockRotate_fixesBelow _ 1 1 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires lowPosition wiresBelow)
  have sigmaLowSecond : blockRotate state.nextFresh 1 1
        (natListGetAt state.openWires (lowPosition + 1))
      = natListGetAt state.openWires (lowPosition + 1) :=
    blockRotate_fixesBelow _ 1 1 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires (lowPosition + 1) wiresBelow)
  have sigmaHighRead : blockRotate state.nextFresh 1 1
        (natListGetAt state.openWires (gap + 2 + lowPosition))
      = natListGetAt state.openWires (gap + 2 + lowPosition) :=
    blockRotate_fixesBelow _ 1 1 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires (gap + 2 + lowPosition) wiresBelow)
  have sigmaHighSecond : blockRotate state.nextFresh 1 1
        (natListGetAt state.openWires (gap + 2 + lowPosition + 1))
      = natListGetAt state.openWires (gap + 2 + lowPosition + 1) :=
    blockRotate_fixesBelow _ 1 1 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires (gap + 2 + lowPosition + 1)
        wiresBelow)
  -- THE ENGINE
  have engineRoot := twoBlocksSigma_rootComm state.links forest state.nextFresh endpointsBelow
    (blockRotate state.nextFresh 1 1) (blockRotate_inj state.nextFresh 1 1)
    (fun node isBelow => blockRotate_fixesBelow state.nextFresh 1 1 node isBelow)
    (fun node isAtOrAbove => blockRotate_preservesAtOrAboveBase state.nextFresh 1 1 node isAtOrAbove)
    (natListGetAt state.openWires lowPosition) (natListGetAt state.openWires (lowPosition + 1))
    state.nextFresh
    (natListGetAt state.openWires (gap + 2 + lowPosition))
    (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) (state.nextFresh + 1)
    (unionFindRootOf state.links (natListGetAt state.openWires lowPosition))
    (unionFindRootOf state.links (natListGetAt state.openWires (lowPosition + 1)))
    (unionFindRootOf state.links (natListGetAt state.openWires (gap + 2 + lowPosition)))
    (unionFindRootOf state.links (natListGetAt state.openWires (gap + 2 + lowPosition + 1)))
    rfl rfl rfl rfl rootNf rootNfSucc
    (Ne.symm (Nat.ne_of_lt (readRootBelow lowPosition)))
    disOneFirst
    (Ne.symm (Nat.ne_of_lt (readRootBelow (gap + 2 + lowPosition))))
    disOneSecond
    (Ne.symm (Nat.ne_of_lt (readRootBelow (gap + 2 + lowPosition + 1))))
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le (readRootBelow lowPosition) (Nat.le_add_right _ _)))
    (Nat.ne_of_lt (Nat.lt_succ_self _))
    (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (readRootBelow (gap + 2 + lowPosition))
      (Nat.le_add_right _ _))))
    (Ne.symm disTwoFirst)
    (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (readRootBelow (lowPosition + 1))
      (Nat.le_add_right _ _))))
  have rootCommWhole : ∀ x,
      unionFindRootOf (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition).links
        (blockRotate state.nextFresh 1 1 x)
      = blockRotate state.nextFresh 1 1
          (unionFindRootOf (stepCapArc (stepCapArc state lowPosition) (gap + lowPosition)).links x) := by
    intro x
    rw [linksRedex, linksReduct]
    have engineAt := engineRoot x
    rw [sigmaHighRead, sigmaHighSecond, blockRotate_oneOne_succ state.nextFresh, sigmaLowRead,
      sigmaLowSecond, blockRotate_oneOne_base state.nextFresh] at engineAt
    exact engineAt
  -- the loop guards transpose through block locality
  have guardRedex : isSameComponent (stepCapArc state lowPosition).links
      (natListGetAt (stepCapArc state lowPosition).openWires (gap + lowPosition))
      (natListGetAt (stepCapArc state lowPosition).openWires (gap + lowPosition + 1))
      = isSameComponent state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
          (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) := by
    show isSameComponent
        (twoJoinBlock state.links (natListGetAt state.openWires lowPosition)
          (natListGetAt state.openWires (lowPosition + 1)) state.nextFresh)
        (natListGetAt (natListRemoveTwoAt state.openWires lowPosition) (gap + lowPosition))
        (natListGetAt (natListRemoveTwoAt state.openWires lowPosition) (gap + lowPosition + 1)) = _
    rw [natListGetAt_removeTwoAt_shift state.openWires lowPosition gap window, indexBridgeFirst,
      indexBridgeSecondEntry,
      natListGetAt_removeTwoAt_shift state.openWires lowPosition (gap + 1) window,
      indexBridgeSecondExit]
    exact isSameComponent_twoJoinBlock_untouched state.links forest _ _ state.nextFresh _ _
      rfl rfl rootNf (Ne.symm (Nat.ne_of_lt (readRootBelow lowPosition)))
      _ _ disOneFirst (Ne.symm (Nat.ne_of_lt (readRootBelow (gap + 2 + lowPosition))))
      disOneSecond (Ne.symm (Nat.ne_of_lt (readRootBelow (gap + 2 + lowPosition + 1))))
  have guardReduct : isSameComponent (stepCapArc state (gap + 2 + lowPosition)).links
      (natListGetAt (stepCapArc state (gap + 2 + lowPosition)).openWires lowPosition)
      (natListGetAt (stepCapArc state (gap + 2 + lowPosition)).openWires (lowPosition + 1))
      = isSameComponent state.links (natListGetAt state.openWires lowPosition)
          (natListGetAt state.openWires (lowPosition + 1)) := by
    show isSameComponent
        (twoJoinBlock state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
          (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) state.nextFresh)
        (natListGetAt (natListRemoveTwoAt state.openWires (gap + 2 + lowPosition)) lowPosition)
        (natListGetAt (natListRemoveTwoAt state.openWires (gap + 2 + lowPosition)) (lowPosition + 1))
        = _
    rw [natListGetAt_removeTwoAt_below state.openWires (gap + 2 + lowPosition) lowPosition
        lowBelowHigh,
      natListGetAt_removeTwoAt_below state.openWires (gap + 2 + lowPosition) (lowPosition + 1)
        lowSuccBelowHigh]
    exact isSameComponent_twoJoinBlock_untouched state.links forest _ _ state.nextFresh _ _
      rfl rfl rootNf (Ne.symm (Nat.ne_of_lt (readRootBelow (gap + 2 + lowPosition))))
      _ _ (Ne.symm disOneFirst)
      (Ne.symm (Nat.ne_of_lt (readRootBelow lowPosition)))
      (Ne.symm disTwoFirst)
      (Ne.symm (Nat.ne_of_lt (readRootBelow (lowPosition + 1))))
  refine
    { openMap := ?_
      nfEq := rfl
      rootComm := rootCommWhole
      loopsEq := ?_
      cupCorr := ?_
      capCorr := ?_
      forestS := isUnionFindForest_stepCapArc _ _ (isUnionFindForest_stepCapArc _ _ forest)
      forestT := isUnionFindForest_stepCapArc _ _ (isUnionFindForest_stepCapArc _ _ forest) }
  · -- openMap : reduct.openWires = redex.openWires.map sigma
    show natListRemoveTwoAt (natListRemoveTwoAt state.openWires (gap + 2 + lowPosition)) lowPosition
      = (natListRemoveTwoAt (natListRemoveTwoAt state.openWires lowPosition) (gap + lowPosition)).map
          (blockRotate state.nextFresh 1 1)
    rw [mapFixedOn (blockRotate state.nextFresh 1 1) _
        (fun wire isMember => blockRotate_fixesBelow state.nextFresh 1 1 wire
          (natListRemoveTwoAt_all_lt state.nextFresh _ (gap + lowPosition)
            (natListRemoveTwoAt_all_lt state.nextFresh state.openWires lowPosition wiresBelow)
            wire isMember))]
    exact natListRemoveTwoAt_removeAbove_commute state.openWires lowPosition gap
  · -- loopsEq : reduct.loops = redex.loops
    show (if isSameComponent (stepCapArc state (gap + 2 + lowPosition)).links
            (natListGetAt (stepCapArc state (gap + 2 + lowPosition)).openWires lowPosition)
            (natListGetAt (stepCapArc state (gap + 2 + lowPosition)).openWires (lowPosition + 1))
          then (stepCapArc state (gap + 2 + lowPosition)).loops + 1
          else (stepCapArc state (gap + 2 + lowPosition)).loops)
        = (if isSameComponent (stepCapArc state lowPosition).links
            (natListGetAt (stepCapArc state lowPosition).openWires (gap + lowPosition))
            (natListGetAt (stepCapArc state lowPosition).openWires (gap + lowPosition + 1))
          then (stepCapArc state lowPosition).loops + 1
          else (stepCapArc state lowPosition).loops)
    rw [guardRedex, guardReduct]
    show (if isSameComponent state.links (natListGetAt state.openWires lowPosition)
            (natListGetAt state.openWires (lowPosition + 1))
          then (if isSameComponent state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
              (natListGetAt state.openWires (gap + 2 + lowPosition + 1))
            then state.loops + 1 else state.loops) + 1
          else (if isSameComponent state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
              (natListGetAt state.openWires (gap + 2 + lowPosition + 1))
            then state.loops + 1 else state.loops))
        = (if isSameComponent state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
            (natListGetAt state.openWires (gap + 2 + lowPosition + 1))
          then (if isSameComponent state.links (natListGetAt state.openWires lowPosition)
              (natListGetAt state.openWires (lowPosition + 1))
            then state.loops + 1 else state.loops) + 1
          else (if isSameComponent state.links (natListGetAt state.openWires lowPosition)
              (natListGetAt state.openWires (lowPosition + 1))
            then state.loops + 1 else state.loops))
    cases isSameComponent state.links (natListGetAt state.openWires lowPosition)
        (natListGetAt state.openWires (lowPosition + 1)) with
    | true =>
        cases isSameComponent state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
            (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) with
        | true => rfl
        | false => rfl
    | false =>
        cases isSameComponent state.links (natListGetAt state.openWires (gap + 2 + lowPosition))
            (natListGetAt state.openWires (gap + 2 + lowPosition + 1)) with
        | true => rfl
        | false => rfl
  · -- cupCorr (cup events untouched by caps)
    intro rootHere
    have transported := countEventsInRoot_rootComm (blockRotate state.nextFresh 1 1)
      (blockRotate_inj state.nextFresh 1 1)
      (stepCapArc (stepCapArc state lowPosition) (gap + lowPosition)).links
      (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition).links
      rootHere rootCommWhole state.cupEventNodes
    rw [mapFixedOn (blockRotate state.nextFresh 1 1) state.cupEventNodes
      (fun node isMember => blockRotate_fixesBelow state.nextFresh 1 1 node
        (wellFormed.isFresh.2.2.1 node isMember))] at transported
    exact transported
  · -- capCorr (both orders cons the same two fresh events; sigma head-swaps them)
    intro rootHere
    have transported := countEventsInRoot_rootComm (blockRotate state.nextFresh 1 1)
      (blockRotate_inj state.nextFresh 1 1)
      (stepCapArc (stepCapArc state lowPosition) (gap + lowPosition)).links
      (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition).links
      rootHere rootCommWhole
      ((state.nextFresh + 1) :: state.nextFresh :: state.capEventNodes)
    have mappedEvents : ((state.nextFresh + 1) :: state.nextFresh :: state.capEventNodes).map
        (blockRotate state.nextFresh 1 1)
        = state.nextFresh :: (state.nextFresh + 1) :: state.capEventNodes := by
      show blockRotate state.nextFresh 1 1 (state.nextFresh + 1)
          :: blockRotate state.nextFresh 1 1 state.nextFresh
          :: state.capEventNodes.map (blockRotate state.nextFresh 1 1)
        = state.nextFresh :: (state.nextFresh + 1) :: state.capEventNodes
      rw [blockRotate_oneOne_succ state.nextFresh, blockRotate_oneOne_base state.nextFresh,
        mapFixedOn (blockRotate state.nextFresh 1 1) state.capEventNodes
          (fun node isMember => blockRotate_fixesBelow state.nextFresh 1 1 node
            (wellFormed.isFresh.2.2.2 node isMember))]
    rw [mappedEvents] at transported
    show countEventsInRoot (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition).links
        (blockRotate state.nextFresh 1 1 rootHere)
        ((state.nextFresh + 1) :: state.nextFresh :: state.capEventNodes)
      = countEventsInRoot (stepCapArc (stepCapArc state lowPosition) (gap + lowPosition)).links
        rootHere ((state.nextFresh + 1) :: state.nextFresh :: state.capEventNodes)
    rw [countEventsInRoot_swap_head
      (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition).links
      (blockRotate state.nextFresh 1 1 rootHere) (state.nextFresh + 1) state.nextFresh
      state.capEventNodes]
    exact transported

/-! ## ARM 2 — CUP then CAP, general, at `blockRotate nextFresh 3 1` (unguarded) -/

/-- ★★ **The GENERAL cup-then-cap swap `ArcStepSimCount` over the bundle** — the cup block is fresh,
so no component guard is needed: window validity alone.  The cup at `lowPosition`, the cap two-plus-gap
to its right. -/
theorem arcDisjointCupCapSwapSimCount_ofWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state)
    (window : gap + lowPosition + 2 ≤ state.openWires.length) :
    ArcStepSimCount (blockRotate state.nextFresh 3 1)
      (stepCapArc (stepCupArc state lowPosition) (gap + 2 + lowPosition))
      (stepCupArc (stepCapArc state (gap + lowPosition)) lowPosition) := by
  have nfPositive : 0 < state.nextFresh := wellFormed.isNonDegenerate
  have forest : isUnionFindForest state.links := wellFormed.isForest
  have wiresBelow : ∀ wire ∈ state.openWires, wire < state.nextFresh := wellFormed.isFresh.1
  have endpointsBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh :=
    wellFormed.isFresh.2.1
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge he => (endpointsBelow edge he).1
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge he => (endpointsBelow edge he).2
  have readRootBelow : ∀ position : Nat,
      unionFindRootOf state.links (natListGetAt state.openWires position) < state.nextFresh :=
    fun position => unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires position wiresBelow)
  have readRootBelowPlus : ∀ position offset : Nat,
      unionFindRootOf state.links (natListGetAt state.openWires position)
        < state.nextFresh + offset :=
    fun position offset =>
      Nat.lt_of_lt_of_le (readRootBelow position) (Nat.le_add_right state.nextFresh offset)
  have rootFreshAt : ∀ offset : Nat,
      unionFindRootOf state.links (state.nextFresh + offset) = state.nextFresh + offset :=
    fun offset => unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow _
      (Nat.le_add_right _ _)
  have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow _ (Nat.le_refl _)
  have windowSplice : lowPosition ≤ state.openWires.length :=
    Nat.le_trans (Nat.le_add_left lowPosition gap)
      (Nat.le_trans (Nat.le_add_right (gap + lowPosition) 2) window)
  -- index bridges
  have indexBridgeFirst : gap + 2 + lowPosition = gap + lowPosition + 2 := by
    rw [Nat.add_right_comm gap lowPosition 2]
  have indexBridgeSecond : gap + 2 + lowPosition + 1 = gap + 1 + lowPosition + 2 := by
    rw [Nat.add_right_comm (gap + 2) lowPosition 1, Nat.add_right_comm (gap + 1) lowPosition 2]
  have indexBridgeSecondRead : gap + 1 + lowPosition = gap + lowPosition + 1 := by
    rw [Nat.add_right_comm gap 1 lowPosition]
  -- the redex links in two-block form
  have linksRedex : (stepCapArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).links
      = twoJoinBlock
          (twoJoinBlock state.links state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2))
          (natListGetAt state.openWires (gap + lowPosition))
          (natListGetAt state.openWires (gap + lowPosition + 1)) (state.nextFresh + 3) := by
    show twoJoinBlock
        (twoJoinBlock state.links state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2))
        (natListGetAt (natListInsertAt state.openWires lowPosition
          [state.nextFresh, state.nextFresh + 1]) (gap + 2 + lowPosition))
        (natListGetAt (natListInsertAt state.openWires lowPosition
          [state.nextFresh, state.nextFresh + 1]) (gap + 2 + lowPosition + 1))
        (state.nextFresh + 3) = _
    rw [indexBridgeSecond,
      natListGetAt_insertAt_shift state.openWires lowPosition (gap + 1) state.nextFresh
        (state.nextFresh + 1) windowSplice,
      indexBridgeSecondRead, indexBridgeFirst,
      natListGetAt_insertAt_shift state.openWires lowPosition gap state.nextFresh
        (state.nextFresh + 1) windowSplice]
  -- the reduct links in two-block form (already in shared coordinates)
  have linksReduct : (stepCupArc (stepCapArc state (gap + lowPosition)) lowPosition).links
      = twoJoinBlock
          (twoJoinBlock state.links (natListGetAt state.openWires (gap + lowPosition))
            (natListGetAt state.openWires (gap + lowPosition + 1)) state.nextFresh)
          (state.nextFresh + 1) (state.nextFresh + 2) (state.nextFresh + 3) := rfl
  -- THE ENGINE (block one = the cup, block two = the cap)
  have engineRoot := twoBlocksSigma_rootComm state.links forest state.nextFresh endpointsBelow
    (blockRotate state.nextFresh 3 1) (blockRotate_inj state.nextFresh 3 1)
    (fun node isBelow => blockRotate_fixesBelow state.nextFresh 3 1 node isBelow)
    (fun node isAtOrAbove => blockRotate_preservesAtOrAboveBase state.nextFresh 3 1 node isAtOrAbove)
    state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2)
    (natListGetAt state.openWires (gap + lowPosition))
    (natListGetAt state.openWires (gap + lowPosition + 1)) (state.nextFresh + 3)
    state.nextFresh (state.nextFresh + 1)
    (unionFindRootOf state.links (natListGetAt state.openWires (gap + lowPosition)))
    (unionFindRootOf state.links (natListGetAt state.openWires (gap + lowPosition + 1)))
    rootNf (rootFreshAt 1) rfl rfl (rootFreshAt 2) (rootFreshAt 3)
    (Nat.ne_of_gt (selfLtAddTwo state.nextFresh))
    (Ne.symm (Nat.ne_of_lt (readRootBelow (gap + lowPosition))))
    (Ne.symm (Nat.ne_of_lt (readRootBelowPlus (gap + lowPosition) 2)))
    (Ne.symm (Nat.ne_of_lt (readRootBelow (gap + lowPosition + 1))))
    (Ne.symm (Nat.ne_of_lt (readRootBelowPlus (gap + lowPosition + 1) 2)))
    (Nat.ne_of_lt (selfLtAddThree state.nextFresh))
    (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : (2 : Nat) < 3) state.nextFresh))
    (Ne.symm (Nat.ne_of_lt (readRootBelowPlus (gap + lowPosition) 3)))
    (Nat.ne_of_lt (readRootBelowPlus (gap + lowPosition) 1))
    (Nat.ne_of_gt (Nat.add_lt_add_left (by decide : (1 : Nat) < 3) state.nextFresh))
  -- rewrite the sigma-imaged reduct parameters to their literal values
  have sigmaCapFirst : blockRotate state.nextFresh 3 1
        (natListGetAt state.openWires (gap + lowPosition))
      = natListGetAt state.openWires (gap + lowPosition) :=
    blockRotate_fixesBelow _ 3 1 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires (gap + lowPosition) wiresBelow)
  have sigmaCapSecond : blockRotate state.nextFresh 3 1
        (natListGetAt state.openWires (gap + lowPosition + 1))
      = natListGetAt state.openWires (gap + lowPosition + 1) :=
    blockRotate_fixesBelow _ 3 1 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires (gap + lowPosition + 1) wiresBelow)
  have rootCommWhole : ∀ x,
      unionFindRootOf (stepCupArc (stepCapArc state (gap + lowPosition)) lowPosition).links
        (blockRotate state.nextFresh 3 1 x)
      = blockRotate state.nextFresh 3 1
          (unionFindRootOf
            (stepCapArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).links x) := by
    intro x
    rw [linksRedex, linksReduct]
    have engineAt := engineRoot x
    rw [sigmaCapFirst, sigmaCapSecond, blockRotate_threeOne_cap state.nextFresh,
      show blockRotate state.nextFresh 3 1 state.nextFresh = state.nextFresh + 1 from
        blockRotate_threeOne_cup state.nextFresh 0 (by decide),
      show blockRotate state.nextFresh 3 1 (state.nextFresh + 1) = state.nextFresh + 2 from
        blockRotate_threeOne_cup state.nextFresh 1 (by decide),
      show blockRotate state.nextFresh 3 1 (state.nextFresh + 2) = state.nextFresh + 3 from
        blockRotate_threeOne_cup state.nextFresh 2 (by decide)] at engineAt
    exact engineAt
  -- the cap's loop guard is block-local on both sides
  have guardRedex : isSameComponent (stepCupArc state lowPosition).links
      (natListGetAt (stepCupArc state lowPosition).openWires (gap + 2 + lowPosition))
      (natListGetAt (stepCupArc state lowPosition).openWires (gap + 2 + lowPosition + 1))
      = isSameComponent state.links (natListGetAt state.openWires (gap + lowPosition))
          (natListGetAt state.openWires (gap + lowPosition + 1)) := by
    show isSameComponent
        (twoJoinBlock state.links state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2))
        (natListGetAt (natListInsertAt state.openWires lowPosition
          [state.nextFresh, state.nextFresh + 1]) (gap + 2 + lowPosition))
        (natListGetAt (natListInsertAt state.openWires lowPosition
          [state.nextFresh, state.nextFresh + 1]) (gap + 2 + lowPosition + 1)) = _
    rw [indexBridgeSecond,
      natListGetAt_insertAt_shift state.openWires lowPosition (gap + 1) state.nextFresh
        (state.nextFresh + 1) windowSplice,
      indexBridgeSecondRead, indexBridgeFirst,
      natListGetAt_insertAt_shift state.openWires lowPosition gap state.nextFresh
        (state.nextFresh + 1) windowSplice]
    exact isSameComponent_twoJoinBlock_untouched state.links forest _ _ (state.nextFresh + 2) _ _
      rootNf (rootFreshAt 1) (rootFreshAt 2)
      (Nat.ne_of_gt (selfLtAddTwo state.nextFresh))
      _ _ (Nat.ne_of_gt (readRootBelow (gap + lowPosition)))
      (Nat.ne_of_gt (readRootBelowPlus (gap + lowPosition) 2))
      (Nat.ne_of_gt (readRootBelow (gap + lowPosition + 1)))
      (Nat.ne_of_gt (readRootBelowPlus (gap + lowPosition + 1) 2))
  refine
    { openMap := ?_
      nfEq := rfl
      rootComm := rootCommWhole
      loopsEq := ?_
      cupCorr := ?_
      capCorr := ?_
      forestS := isUnionFindForest_stepCapArc _ _ (isUnionFindForest_stepCupArc _ _ forest)
      forestT := isUnionFindForest_stepCupArc _ _ (isUnionFindForest_stepCapArc _ _ forest) }
  · -- openMap
    have blockImage : ([state.nextFresh, state.nextFresh + 1].map (blockRotate state.nextFresh 3 1))
        = [state.nextFresh + 1, state.nextFresh + 1 + 1] := by
      show [blockRotate state.nextFresh 3 1 state.nextFresh,
        blockRotate state.nextFresh 3 1 (state.nextFresh + 1)] = _
      rw [show blockRotate state.nextFresh 3 1 state.nextFresh = state.nextFresh + 1 from
          blockRotate_threeOne_cup state.nextFresh 0 (by decide),
        show blockRotate state.nextFresh 3 1 (state.nextFresh + 1) = state.nextFresh + 2 from
          blockRotate_threeOne_cup state.nextFresh 1 (by decide)]
    have lengthCollapse : gap + ([state.nextFresh + 1, state.nextFresh + 1 + 1] : List Nat).length
        + lowPosition = gap + 2 + lowPosition := rfl
    show natListInsertAt (natListRemoveTwoAt state.openWires (gap + lowPosition)) lowPosition
        [state.nextFresh + 1, state.nextFresh + 1 + 1]
      = (natListRemoveTwoAt (natListInsertAt state.openWires lowPosition
          [state.nextFresh, state.nextFresh + 1]) (gap + 2 + lowPosition)).map
          (blockRotate state.nextFresh 3 1)
    rw [natListRemoveTwoAt_map (blockRotate state.nextFresh 3 1),
      natListInsertAt_map (blockRotate state.nextFresh 3 1),
      mapFixedOn (blockRotate state.nextFresh 3 1) state.openWires
        (fun wire isMember => blockRotate_fixesBelow state.nextFresh 3 1 wire
          (wiresBelow wire isMember)),
      blockImage,
      natListInsertAt_removeAbove_commute state.openWires lowPosition gap
        [state.nextFresh + 1, state.nextFresh + 1 + 1] window,
      lengthCollapse]
  · -- loopsEq
    show (if isSameComponent state.links (natListGetAt state.openWires (gap + lowPosition))
            (natListGetAt state.openWires (gap + lowPosition + 1))
          then state.loops + 1 else state.loops)
        = (if isSameComponent (stepCupArc state lowPosition).links
            (natListGetAt (stepCupArc state lowPosition).openWires (gap + 2 + lowPosition))
            (natListGetAt (stepCupArc state lowPosition).openWires (gap + 2 + lowPosition + 1))
          then (stepCupArc state lowPosition).loops + 1 else (stepCupArc state lowPosition).loops)
    rw [guardRedex]
    rfl
  · -- cupCorr : the single cup event maps across
    intro rootHere
    have transported := countEventsInRoot_rootComm (blockRotate state.nextFresh 3 1)
      (blockRotate_inj state.nextFresh 3 1)
      (stepCapArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).links
      (stepCupArc (stepCapArc state (gap + lowPosition)) lowPosition).links
      rootHere rootCommWhole ((state.nextFresh + 2) :: state.cupEventNodes)
    have mappedEvents : ((state.nextFresh + 2) :: state.cupEventNodes).map
        (blockRotate state.nextFresh 3 1)
        = (state.nextFresh + 3) :: state.cupEventNodes := by
      show blockRotate state.nextFresh 3 1 (state.nextFresh + 2)
          :: state.cupEventNodes.map (blockRotate state.nextFresh 3 1)
        = (state.nextFresh + 3) :: state.cupEventNodes
      rw [show blockRotate state.nextFresh 3 1 (state.nextFresh + 2) = state.nextFresh + 3 from
          blockRotate_threeOne_cup state.nextFresh 2 (by decide),
        mapFixedOn (blockRotate state.nextFresh 3 1) state.cupEventNodes
          (fun node isMember => blockRotate_fixesBelow state.nextFresh 3 1 node
            (wellFormed.isFresh.2.2.1 node isMember))]
    rw [mappedEvents] at transported
    exact transported
  · -- capCorr : the single cap event maps across
    intro rootHere
    have transported := countEventsInRoot_rootComm (blockRotate state.nextFresh 3 1)
      (blockRotate_inj state.nextFresh 3 1)
      (stepCapArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).links
      (stepCupArc (stepCapArc state (gap + lowPosition)) lowPosition).links
      rootHere rootCommWhole ((state.nextFresh + 3) :: state.capEventNodes)
    have mappedEvents : ((state.nextFresh + 3) :: state.capEventNodes).map
        (blockRotate state.nextFresh 3 1)
        = state.nextFresh :: state.capEventNodes := by
      show blockRotate state.nextFresh 3 1 (state.nextFresh + 3)
          :: state.capEventNodes.map (blockRotate state.nextFresh 3 1)
        = state.nextFresh :: state.capEventNodes
      rw [blockRotate_threeOne_cap state.nextFresh,
        mapFixedOn (blockRotate state.nextFresh 3 1) state.capEventNodes
          (fun node isMember => blockRotate_fixesBelow state.nextFresh 3 1 node
            (wellFormed.isFresh.2.2.2 node isMember))]
    rw [mappedEvents] at transported
    exact transported

/-! ## ARM 3 — CAP then CUP, general, at `blockRotate nextFresh 1 3` (unguarded) -/

/-- ★★ **The GENERAL cap-then-cup swap `ArcStepSimCount` over the bundle** — the mirror mixed arm:
the cap at `lowPosition`, the cup spliced two-plus-gap to its right.  Unguarded beyond window
validity (the cup block is fresh). -/
theorem arcDisjointCapCupSwapSimCount_ofWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state)
    (window : gap + 2 + lowPosition ≤ state.openWires.length) :
    ArcStepSimCount (blockRotate state.nextFresh 1 3)
      (stepCupArc (stepCapArc state lowPosition) (gap + lowPosition))
      (stepCapArc (stepCupArc state (gap + 2 + lowPosition)) lowPosition) := by
  have nfPositive : 0 < state.nextFresh := wellFormed.isNonDegenerate
  have forest : isUnionFindForest state.links := wellFormed.isForest
  have wiresBelow : ∀ wire ∈ state.openWires, wire < state.nextFresh := wellFormed.isFresh.1
  have endpointsBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh :=
    wellFormed.isFresh.2.1
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge he => (endpointsBelow edge he).1
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge he => (endpointsBelow edge he).2
  have readRootBelow : ∀ position : Nat,
      unionFindRootOf state.links (natListGetAt state.openWires position) < state.nextFresh :=
    fun position => unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires position wiresBelow)
  have readRootBelowPlus : ∀ position offset : Nat,
      unionFindRootOf state.links (natListGetAt state.openWires position)
        < state.nextFresh + offset :=
    fun position offset =>
      Nat.lt_of_lt_of_le (readRootBelow position) (Nat.le_add_right state.nextFresh offset)
  have rootFreshAt : ∀ offset : Nat,
      unionFindRootOf state.links (state.nextFresh + offset) = state.nextFresh + offset :=
    fun offset => unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow _
      (Nat.le_add_right _ _)
  have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow _ (Nat.le_refl _)
  have windowLow : lowPosition + 2 ≤ state.openWires.length := by
    have twoPlusLe : 2 + lowPosition ≤ (gap + 2) + lowPosition :=
      Nat.add_le_add_right (Nat.le_add_left 2 gap) lowPosition
    rw [Nat.add_comm 2 lowPosition] at twoPlusLe
    exact Nat.le_trans twoPlusLe window
  have lowBelowSplice : lowPosition < gap + 2 + lowPosition :=
    ltAddOfPosLeft lowPosition (gap + 2) (Nat.succ_pos _)
  have lowSuccBelowSplice : lowPosition + 1 < gap + 2 + lowPosition := succLtAddTwoLeft lowPosition gap
  have indexBridgeSplice : gap + 2 + lowPosition = gap + lowPosition + 2 := by
    rw [Nat.add_right_comm gap lowPosition 2]
  -- the redex links in two-block form (already in shared coordinates)
  have linksRedex : (stepCupArc (stepCapArc state lowPosition) (gap + lowPosition)).links
      = twoJoinBlock
          (twoJoinBlock state.links (natListGetAt state.openWires lowPosition)
            (natListGetAt state.openWires (lowPosition + 1)) state.nextFresh)
          (state.nextFresh + 1) (state.nextFresh + 2) (state.nextFresh + 3) := rfl
  -- the reduct links in two-block form (cap reads pass below the splice)
  have linksReduct : (stepCapArc (stepCupArc state (gap + 2 + lowPosition)) lowPosition).links
      = twoJoinBlock
          (twoJoinBlock state.links state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2))
          (natListGetAt state.openWires lowPosition)
          (natListGetAt state.openWires (lowPosition + 1)) (state.nextFresh + 3) := by
    show twoJoinBlock
        (twoJoinBlock state.links state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2))
        (natListGetAt (natListInsertAt state.openWires (gap + 2 + lowPosition)
          [state.nextFresh, state.nextFresh + 1]) lowPosition)
        (natListGetAt (natListInsertAt state.openWires (gap + 2 + lowPosition)
          [state.nextFresh, state.nextFresh + 1]) (lowPosition + 1))
        (state.nextFresh + 3) = _
    rw [natListGetAt_insertAt_below state.openWires (gap + 2 + lowPosition) lowPosition
        [state.nextFresh, state.nextFresh + 1] lowBelowSplice window,
      natListGetAt_insertAt_below state.openWires (gap + 2 + lowPosition) (lowPosition + 1)
        [state.nextFresh, state.nextFresh + 1] lowSuccBelowSplice window]
  -- THE ENGINE (block one = the cap, block two = the cup)
  have engineRoot := twoBlocksSigma_rootComm state.links forest state.nextFresh endpointsBelow
    (blockRotate state.nextFresh 1 3) (blockRotate_inj state.nextFresh 1 3)
    (fun node isBelow => blockRotate_fixesBelow state.nextFresh 1 3 node isBelow)
    (fun node isAtOrAbove => blockRotate_preservesAtOrAboveBase state.nextFresh 1 3 node isAtOrAbove)
    (natListGetAt state.openWires lowPosition) (natListGetAt state.openWires (lowPosition + 1))
    state.nextFresh
    (state.nextFresh + 1) (state.nextFresh + 2) (state.nextFresh + 3)
    (unionFindRootOf state.links (natListGetAt state.openWires lowPosition))
    (unionFindRootOf state.links (natListGetAt state.openWires (lowPosition + 1)))
    (state.nextFresh + 1) (state.nextFresh + 2)
    rfl rfl (rootFreshAt 1) (rootFreshAt 2) rootNf (rootFreshAt 3)
    (Ne.symm (Nat.ne_of_lt (readRootBelow lowPosition)))
    (Nat.ne_of_lt (readRootBelowPlus lowPosition 1))
    (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))
    (Nat.ne_of_lt (readRootBelowPlus lowPosition 2))
    (Nat.ne_of_lt (selfLtAddTwo state.nextFresh))
    (Nat.ne_of_lt (readRootBelowPlus lowPosition 3))
    (Nat.ne_of_lt (selfLtAddThree state.nextFresh))
    (Nat.ne_of_gt (Nat.add_lt_add_left (by decide : (1 : Nat) < 3) state.nextFresh))
    (Ne.symm (Nat.ne_of_lt (readRootBelowPlus (lowPosition + 1) 1)))
    (Ne.symm (Nat.ne_of_lt (readRootBelowPlus (lowPosition + 1) 3)))
  have sigmaCapFirst : blockRotate state.nextFresh 1 3 (natListGetAt state.openWires lowPosition)
      = natListGetAt state.openWires lowPosition :=
    blockRotate_fixesBelow _ 1 3 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires lowPosition wiresBelow)
  have sigmaCapSecond : blockRotate state.nextFresh 1 3
        (natListGetAt state.openWires (lowPosition + 1))
      = natListGetAt state.openWires (lowPosition + 1) :=
    blockRotate_fixesBelow _ 1 3 _
      (natListGetAt_lt state.nextFresh nfPositive state.openWires (lowPosition + 1) wiresBelow)
  have rootCommWhole : ∀ x,
      unionFindRootOf (stepCapArc (stepCupArc state (gap + 2 + lowPosition)) lowPosition).links
        (blockRotate state.nextFresh 1 3 x)
      = blockRotate state.nextFresh 1 3
          (unionFindRootOf
            (stepCupArc (stepCapArc state lowPosition) (gap + lowPosition)).links x) := by
    intro x
    rw [linksRedex, linksReduct]
    have engineAt := engineRoot x
    rw [sigmaCapFirst, sigmaCapSecond, blockRotate_oneThree_cap state.nextFresh,
      show blockRotate state.nextFresh 1 3 (state.nextFresh + 1) = state.nextFresh from
        blockRotate_oneThree_cup state.nextFresh 0 (by decide),
      show blockRotate state.nextFresh 1 3 (state.nextFresh + 2) = state.nextFresh + 1 from
        blockRotate_oneThree_cup state.nextFresh 1 (by decide),
      show blockRotate state.nextFresh 1 3 (state.nextFresh + 3) = state.nextFresh + 2 from
        blockRotate_oneThree_cup state.nextFresh 2 (by decide)] at engineAt
    exact engineAt
  -- the reduct cap's loop guard is block-local
  have guardReduct : isSameComponent (stepCupArc state (gap + 2 + lowPosition)).links
      (natListGetAt (stepCupArc state (gap + 2 + lowPosition)).openWires lowPosition)
      (natListGetAt (stepCupArc state (gap + 2 + lowPosition)).openWires (lowPosition + 1))
      = isSameComponent state.links (natListGetAt state.openWires lowPosition)
          (natListGetAt state.openWires (lowPosition + 1)) := by
    show isSameComponent
        (twoJoinBlock state.links state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2))
        (natListGetAt (natListInsertAt state.openWires (gap + 2 + lowPosition)
          [state.nextFresh, state.nextFresh + 1]) lowPosition)
        (natListGetAt (natListInsertAt state.openWires (gap + 2 + lowPosition)
          [state.nextFresh, state.nextFresh + 1]) (lowPosition + 1)) = _
    rw [natListGetAt_insertAt_below state.openWires (gap + 2 + lowPosition) lowPosition
        [state.nextFresh, state.nextFresh + 1] lowBelowSplice window,
      natListGetAt_insertAt_below state.openWires (gap + 2 + lowPosition) (lowPosition + 1)
        [state.nextFresh, state.nextFresh + 1] lowSuccBelowSplice window]
    exact isSameComponent_twoJoinBlock_untouched state.links forest _ _ (state.nextFresh + 2) _ _
      rootNf (rootFreshAt 1) (rootFreshAt 2)
      (Nat.ne_of_gt (selfLtAddTwo state.nextFresh))
      _ _ (Nat.ne_of_gt (readRootBelow lowPosition))
      (Nat.ne_of_gt (readRootBelowPlus lowPosition 2))
      (Nat.ne_of_gt (readRootBelow (lowPosition + 1)))
      (Nat.ne_of_gt (readRootBelowPlus (lowPosition + 1) 2))
  refine
    { openMap := ?_
      nfEq := rfl
      rootComm := rootCommWhole
      loopsEq := ?_
      cupCorr := ?_
      capCorr := ?_
      forestS := isUnionFindForest_stepCupArc _ _ (isUnionFindForest_stepCapArc _ _ forest)
      forestT := isUnionFindForest_stepCapArc _ _ (isUnionFindForest_stepCupArc _ _ forest) }
  · -- openMap
    have blockImage : ([state.nextFresh + 1, state.nextFresh + 1 + 1].map
          (blockRotate state.nextFresh 1 3))
        = [state.nextFresh, state.nextFresh + 1] := by
      show [blockRotate state.nextFresh 1 3 (state.nextFresh + 1),
        blockRotate state.nextFresh 1 3 (state.nextFresh + 2)] = _
      rw [show blockRotate state.nextFresh 1 3 (state.nextFresh + 1) = state.nextFresh from
          blockRotate_oneThree_cup state.nextFresh 0 (by decide),
        show blockRotate state.nextFresh 1 3 (state.nextFresh + 2) = state.nextFresh + 1 from
          blockRotate_oneThree_cup state.nextFresh 1 (by decide)]
    have windowShifted : gap + lowPosition + 2 ≤ state.openWires.length := by
      rw [Nat.add_right_comm gap lowPosition 2]
      exact window
    show natListRemoveTwoAt (natListInsertAt state.openWires (gap + 2 + lowPosition)
        [state.nextFresh, state.nextFresh + 1]) lowPosition
      = (natListInsertAt (natListRemoveTwoAt state.openWires lowPosition) (gap + lowPosition)
          [state.nextFresh + 1, state.nextFresh + 1 + 1]).map (blockRotate state.nextFresh 1 3)
    rw [natListInsertAt_map (blockRotate state.nextFresh 1 3),
      natListRemoveTwoAt_map (blockRotate state.nextFresh 1 3),
      mapFixedOn (blockRotate state.nextFresh 1 3) state.openWires
        (fun wire isMember => blockRotate_fixesBelow state.nextFresh 1 3 wire
          (wiresBelow wire isMember)),
      blockImage]
    exact natListRemoveTwoAt_insertAbove_commute state.openWires lowPosition gap
      [state.nextFresh, state.nextFresh + 1] windowShifted
  · -- loopsEq
    show (if isSameComponent (stepCupArc state (gap + 2 + lowPosition)).links
            (natListGetAt (stepCupArc state (gap + 2 + lowPosition)).openWires lowPosition)
            (natListGetAt (stepCupArc state (gap + 2 + lowPosition)).openWires (lowPosition + 1))
          then (stepCupArc state (gap + 2 + lowPosition)).loops + 1
          else (stepCupArc state (gap + 2 + lowPosition)).loops)
        = (if isSameComponent state.links (natListGetAt state.openWires lowPosition)
            (natListGetAt state.openWires (lowPosition + 1))
          then state.loops + 1 else state.loops)
    rw [guardReduct]
    rfl
  · -- cupCorr
    intro rootHere
    have transported := countEventsInRoot_rootComm (blockRotate state.nextFresh 1 3)
      (blockRotate_inj state.nextFresh 1 3)
      (stepCupArc (stepCapArc state lowPosition) (gap + lowPosition)).links
      (stepCapArc (stepCupArc state (gap + 2 + lowPosition)) lowPosition).links
      rootHere rootCommWhole ((state.nextFresh + 3) :: state.cupEventNodes)
    have mappedEvents : ((state.nextFresh + 3) :: state.cupEventNodes).map
        (blockRotate state.nextFresh 1 3)
        = (state.nextFresh + 2) :: state.cupEventNodes := by
      show blockRotate state.nextFresh 1 3 (state.nextFresh + 3)
          :: state.cupEventNodes.map (blockRotate state.nextFresh 1 3)
        = (state.nextFresh + 2) :: state.cupEventNodes
      rw [show blockRotate state.nextFresh 1 3 (state.nextFresh + 3) = state.nextFresh + 2 from
          blockRotate_oneThree_cup state.nextFresh 2 (by decide),
        mapFixedOn (blockRotate state.nextFresh 1 3) state.cupEventNodes
          (fun node isMember => blockRotate_fixesBelow state.nextFresh 1 3 node
            (wellFormed.isFresh.2.2.1 node isMember))]
    rw [mappedEvents] at transported
    exact transported
  · -- capCorr
    intro rootHere
    have transported := countEventsInRoot_rootComm (blockRotate state.nextFresh 1 3)
      (blockRotate_inj state.nextFresh 1 3)
      (stepCupArc (stepCapArc state lowPosition) (gap + lowPosition)).links
      (stepCapArc (stepCupArc state (gap + 2 + lowPosition)) lowPosition).links
      rootHere rootCommWhole (state.nextFresh :: state.capEventNodes)
    have mappedEvents : (state.nextFresh :: state.capEventNodes).map
        (blockRotate state.nextFresh 1 3)
        = (state.nextFresh + 3) :: state.capEventNodes := by
      show blockRotate state.nextFresh 1 3 state.nextFresh
          :: state.capEventNodes.map (blockRotate state.nextFresh 1 3)
        = (state.nextFresh + 3) :: state.capEventNodes
      rw [blockRotate_oneThree_cap state.nextFresh,
        mapFixedOn (blockRotate state.nextFresh 1 3) state.capEventNodes
          (fun node isMember => blockRotate_fixesBelow state.nextFresh 1 3 node
            (wellFormed.isFresh.2.2.2 node isMember))]
    rw [mappedEvents] at transported
    exact transported

/-! ## The fires — the r26 concrete pairs upgraded to FULL unbounded sims -/

/-- ★ **CAP x CAP fired FULL** — the r26 concrete pair (`capCapDisjointRedex` / `Reduct`), whose
`rootComm`/count fields r26 could only kernel-decide on a bounded support, now carries the complete
unbounded `ArcStepSimCount` via the general arm. -/
theorem capCapDisjointSwap_fullSimCount :
    ArcStepSimCount (blockRotate 56 1 1) capCapDisjointRedex capCapDisjointReduct :=
  arcDisjointCapCapSwapSimCount_ofWellFormed capCapDisjointSeed 0 2
    capCapDisjointSeed_isWellFormed (by decide) (by decide) (by decide) (by decide)

/-- ★ **CUP-then-CAP fired FULL** — the r26 mixed pair (`mixedCupCapRedex` / `Reduct`) upgraded. -/
theorem mixedCupCapSwap_fullSimCount :
    ArcStepSimCount (blockRotate 44 3 1) mixedCupCapRedex mixedCupCapReduct :=
  arcDisjointCupCapSwapSimCount_ofWellFormed mixedCupCapSeed 0 2
    mixedCupCapSeed_isWellFormed (by decide)

/-- ★ **CAP-then-CUP fired FULL** — the fold-oriented geometry (the cup spliced at the cap window's
right edge), on the r26 `mixedCapCupSeed`. -/
theorem mixedCapCupSwap_fullSimCount :
    ArcStepSimCount (blockRotate 64 1 3)
      (stepCupArc (stepCapArc mixedCapCupSeed 0) 0)
      (stepCapArc (stepCupArc mixedCapCupSeed 2) 0) :=
  arcDisjointCapCupSwapSimCount_ofWellFormed mixedCapCupSeed 0 0
    mixedCapCupSeed_isWellFormed (by decide)

/-! ## Honesty marker + pins -/

/-- **Honesty marker — ALL FOUR general disjoint atom-swap arms are SHIPPED over the bundle.**
Cup x cup was the r25-consumed engine (`twoCupGodement_arcStepSimCount`); the cap x cap and both
mixed arms are delivered here at general `(state, lowPosition, gap)` with full unbounded
`ArcStepSimCount` (r26's deferred obligation), each fired on the r26 concrete seeds.  The cap x cap
guard is the machine-sharp THREE-disequality set (second-read/second-read sharing is permitted —
strictly finer than r26's component-disjoint-reads doctrine).  The remaining whole-cell bill is the
double fold `atomPastCell` -> `cellPastCell` alone.  `= true`. -/
def fxMode_hasDisjointAtomSwapGeneralArms : Bool := true

/-- **Honesty pin — the whole-cell disjoint whisker-support target stays OPEN.**  The four atom arms
are the complete BASE; the suffix-fold double induction is the remaining delivery.  `rfl`. -/
theorem arcDisjointAtomSwapGeneralArms_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN.**  `rfl`. -/
theorem arcDisjointAtomSwapGeneralArms_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN.**  `rfl`. -/
theorem arcDisjointAtomSwapGeneralArms_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  `rfl`. -/
theorem arcDisjointAtomSwapGeneralArms_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
