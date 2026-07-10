import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCapNonCrossing
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation

/-! # WalkingString — the two-endpoint BOUNDARY CENSUS over the bare `WireState` (FC-5, P1)

The JOIN branch of `stringNonCrossing_stepCap` (FC-4's residual) is refuted by a PERFECT-MATCHING census: every
union-find component of a cup/cap fold state carries at most TWO boundary ends (an original bottom port and a
currently-open wire end).  This is the load-bearing NEW fold invariant the arc lane shipped as `ArcBoundaryCensus`
over the enriched `ArcWireState`; this file PORTS it to the bare `WireState`.  As of FC-5 P2 the census is CONSUMED:
`stringNonCrossing_stepCap` (in the sibling `StringCapNonCrossingJoin`) is CLOSED, `fxString_hasCapNonCrossingJoinBranch
:= true`.

A boundary END TOKEN (`ArcEndToken`, carrier-free — reused verbatim) is either a `bottomPort v` (an original seed
wire, one per node value below the seed width) or an `openSlot p` (the wire end currently at `openWires` position
`p`).  A straight-through seed wire owns two DISTINCT tokens on the same node — the census counts wire ENDS, not
nodes.  `StringBoundaryCensus seedBoundary state` is the zero-dep pigeonhole rendering of "at most two ends": no
three pairwise-distinct valid tokens hub-share a component.

## What this file ships (each piece zero-axiom)

  * **`stringEndTokenNode` / `isValidStringEndToken` / `StringBoundaryCensus`** — the census statement over `WireState`.
  * **`stringBoundaryCensus_initial`** — the fresh seed satisfies the census (every component a single straight wire).
  * ★ **`stringBoundaryCensus_stepCup`** — a cup step preserves the census (the spliced fresh strand carries exactly
    its two window slots; strictly SIMPLER than the arc's event-node cup — no event node to union in).
  * ★ **`stringBoundaryCensus_stepCap`** — a cap step preserves the census (the merged component loses one open end
    from each side; the arc's `arcBoundaryCensus_stepCapArc` port, with the event-join peel DELETED because
    `stepCap`'s link update is the DIRECT `unionFindJoin` — `stepCap_links_eq_unionFindJoin`).
  * **`stringBoundaryCensus_stepAtom` / `_processSpine` / `_fromSeed`** — the fold transport, so EVERY reachable state
    (from the fresh seed) satisfies the census.

The carrier-free arc infrastructure is REUSED directly (no re-derivation): the token type `ArcEndToken`, the window
backmap `capEndTokenBackmap` + its `_injective` / `_missesLeftWindow` / `_missesRightWindow`, the join membership
dispatch `sameComponent_unionFindJoin_dispatch`, the cup old-zone predicate `isCupOldZoneToken` + `cupEndTokenBackmap`
+ `_injective`, and the generic list/component lemmas.  The one bridge `stringForest_toUnionFindForest` promotes the
byte-identical `stringIsUnionFindForest` to `isUnionFindForest` so the shared join lemmas apply.

Raw Lean 4 + Init; structural list recursion + the shipped forest/freshness kits.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem censusRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := censusRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem censusRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [censusRangeLoopLength count []]; exact Nat.add_zero count

private theorem censusRangeLoopGetPast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := censusRangeLoopGetPast count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem censusRangeLoopGetBelow : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact censusRangeLoopGetBelow count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := censusRangeLoopGetPast count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]; exact pastRead

private theorem censusRangeGetBelow (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  censusRangeLoopGetBelow count [] index indexBelow

/-- `a ≠ b → (a == b) = false`, propext-clean (per-file copy, following the codebase pattern). -/
private theorem censusBeqFalseOfNe (leftNode rightNode : Nat) (notEqual : leftNode ≠ rightNode) :
    (leftNode == rightNode) = false := by
  cases beqCase : leftNode == rightNode with
  | true => exact absurd (of_decide_eq_true beqCase) notEqual
  | false => rfl

/-! ## The forest bridge — `stringIsUnionFindForest` is byte-identical to `isUnionFindForest` -/

/-- ★ **The trivial forest bridge.**  `stringIsUnionFindForest` (re-stated over the bare `WireState` in
`StringFussCatalanForest`) and the shared `isUnionFindForest` have the SAME structural definition, so the string-side
forest fact promotes to the shared one, and the shared join lemmas (`sameComponent_unionFindJoin_dispatch`,
`isSameComponent_unionFindJoin`) apply to string-side `links`. -/
theorem stringForest_toUnionFindForest :
    (links : List (Nat × Nat)) → stringIsUnionFindForest links → isUnionFindForest links
  | [], _ => trivial
  | _ :: rest, forest =>
      ⟨forest.1, forest.2.1, forest.2.2.1, stringForest_toUnionFindForest rest forest.2.2.2⟩

/-! ## The census statement over `WireState` -/

/-- The union-find node a boundary end token reads: a bottom port IS its node value, an open slot reads the wire node
at its position. -/
def stringEndTokenNode (state : WireState) : ArcEndToken → Nat
  | ArcEndToken.bottomPort portValue => portValue
  | ArcEndToken.openSlot slotPosition => natListGetAt state.openWires slotPosition

/-- Is this token a genuine boundary end of the state?  Bottom ports must sit below the seed boundary width; open
slots must index into the current `openWires`. -/
def isValidStringEndToken (seedBoundary : Nat) (state : WireState) : ArcEndToken → Prop
  | ArcEndToken.bottomPort portValue => portValue < seedBoundary
  | ArcEndToken.openSlot slotPosition => slotPosition < state.openWires.length

/-- ★ **The two-endpoint boundary census over `WireState`.**  No three distinct valid boundary end tokens hub-share a
union-find component.  Every component is a path of wires with exactly two ends, so at most two boundary endpoints —
the zero-dep pigeonhole rendering of that bound, and exactly what the cap join-branch consumes (a merged component
carrying three boundary ends is impossible). -/
def StringBoundaryCensus (seedBoundary : Nat) (state : WireState) : Prop :=
  ∀ tokenOne tokenTwo tokenThree : ArcEndToken,
    isValidStringEndToken seedBoundary state tokenOne →
    isValidStringEndToken seedBoundary state tokenTwo →
    isValidStringEndToken seedBoundary state tokenThree →
    tokenOne ≠ tokenTwo →
    tokenOne ≠ tokenThree →
    tokenTwo ≠ tokenThree →
    isSameComponent state.links (stringEndTokenNode state tokenOne)
        (stringEndTokenNode state tokenTwo) = true →
    isSameComponent state.links (stringEndTokenNode state tokenOne)
        (stringEndTokenNode state tokenThree) = true →
    False

/-! ## The census at the fresh seed -/

/-- Over the empty link list, same-component is node equality. -/
private theorem censusSeedNodesEqual_ofSameComponent (leftNode rightNode : Nat)
    (sameComponentHolds : isSameComponent [] leftNode rightNode = true) :
    leftNode = rightNode := by
  have rootsEqualTrue : (unionFindRootOf [] leftNode == unionFindRootOf [] rightNode) = true :=
    sameComponentHolds
  have nodesDecideTrue : decide (leftNode = rightNode) = true := rootsEqualTrue
  exact of_decide_eq_true nodesDecideTrue

/-- At the seed, an in-range open slot reads its own position: the seed `openWires` is the range list. -/
private theorem censusSeedSlotRead (seedBoundary slotPosition : Nat)
    (slotBelowLength : slotPosition < (stringInitialWireState seedBoundary).openWires.length) :
    natListGetAt (stringInitialWireState seedBoundary).openWires slotPosition = slotPosition := by
  have slotBelow : slotPosition < (List.range seedBoundary).length := slotBelowLength
  rw [censusRangeLength seedBoundary] at slotBelow
  show natListGetAt (List.range seedBoundary) slotPosition = slotPosition
  exact censusRangeGetBelow seedBoundary slotPosition slotBelow

/-- ★ The fresh seed state satisfies the census: every component is a single straight wire, whose only boundary ends
are its bottom port and its open slot — any three distinct tokens pairwise on one component would force two tokens of
the same kind with the same payload.  The string port of `arcBoundaryCensus_initial`. -/
theorem stringBoundaryCensus_initial (seedBoundary : Nat) :
    StringBoundaryCensus seedBoundary (stringInitialWireState seedBoundary) := by
  intro tokenOne tokenTwo tokenThree validOne validTwo validThree
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
  show False
  have linksNil : (stringInitialWireState seedBoundary).links = [] := rfl
  rw [linksNil] at sameOneTwo sameOneThree
  cases tokenOne with
  | bottomPort valueOne =>
      cases tokenTwo with
      | bottomPort valueTwo =>
          exact oneNeTwo (congrArg ArcEndToken.bottomPort
            (censusSeedNodesEqual_ofSameComponent valueOne valueTwo sameOneTwo))
      | openSlot slotTwo =>
          cases tokenThree with
          | bottomPort valueThree =>
              exact oneNeThree (congrArg ArcEndToken.bottomPort
                (censusSeedNodesEqual_ofSameComponent valueOne valueThree sameOneThree))
          | openSlot slotThree =>
              have readSlotTwo := censusSeedSlotRead seedBoundary slotTwo validTwo
              have readSlotThree := censusSeedSlotRead seedBoundary slotThree validThree
              have anchorReachesTwo := censusSeedNodesEqual_ofSameComponent valueOne
                (stringEndTokenNode (stringInitialWireState seedBoundary)
                  (ArcEndToken.openSlot slotTwo)) sameOneTwo
              have anchorReachesThree := censusSeedNodesEqual_ofSameComponent valueOne
                (stringEndTokenNode (stringInitialWireState seedBoundary)
                  (ArcEndToken.openSlot slotThree)) sameOneThree
              have slotsEqual : slotTwo = slotThree :=
                readSlotTwo.symm.trans
                  ((anchorReachesTwo.symm.trans anchorReachesThree).trans readSlotThree)
              exact twoNeThree (congrArg ArcEndToken.openSlot slotsEqual)
  | openSlot slotOne =>
      have readSlotOne := censusSeedSlotRead seedBoundary slotOne validOne
      cases tokenTwo with
      | bottomPort valueTwo =>
          cases tokenThree with
          | bottomPort valueThree =>
              have anchorReachesTwo := censusSeedNodesEqual_ofSameComponent
                (stringEndTokenNode (stringInitialWireState seedBoundary)
                  (ArcEndToken.openSlot slotOne)) valueTwo sameOneTwo
              have anchorReachesThree := censusSeedNodesEqual_ofSameComponent
                (stringEndTokenNode (stringInitialWireState seedBoundary)
                  (ArcEndToken.openSlot slotOne)) valueThree sameOneThree
              exact twoNeThree (congrArg ArcEndToken.bottomPort
                (anchorReachesTwo.symm.trans anchorReachesThree))
          | openSlot slotThree =>
              have readSlotThree := censusSeedSlotRead seedBoundary slotThree validThree
              have anchorReachesThree := censusSeedNodesEqual_ofSameComponent
                (stringEndTokenNode (stringInitialWireState seedBoundary)
                  (ArcEndToken.openSlot slotOne))
                (stringEndTokenNode (stringInitialWireState seedBoundary)
                  (ArcEndToken.openSlot slotThree)) sameOneThree
              have slotsEqual : slotOne = slotThree :=
                readSlotOne.symm.trans (anchorReachesThree.trans readSlotThree)
              exact oneNeThree (congrArg ArcEndToken.openSlot slotsEqual)
      | openSlot slotTwo =>
          have readSlotTwo := censusSeedSlotRead seedBoundary slotTwo validTwo
          have anchorReachesTwo := censusSeedNodesEqual_ofSameComponent
            (stringEndTokenNode (stringInitialWireState seedBoundary)
              (ArcEndToken.openSlot slotOne))
            (stringEndTokenNode (stringInitialWireState seedBoundary)
              (ArcEndToken.openSlot slotTwo)) sameOneTwo
          have slotsEqual : slotOne = slotTwo :=
            readSlotOne.symm.trans (anchorReachesTwo.trans readSlotTwo)
          exact oneNeTwo (congrArg ArcEndToken.openSlot slotsEqual)

/-! ## The window backmap on boundary end tokens (CAP), node/validity over `WireState` -/

/-- The backmap (`capEndTokenBackmap`, reused) preserves the read node: the capped state's boundary end sits on the
same union-find node as its old-state preimage.  `stepCap`'s open wires are `natListRemoveTwoAt state.openWires
position` in BOTH branches, so below-window reads are untouched and past-window reads shift by the removed pair. -/
theorem stringCapEndTokenBackmap_node (state : WireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) (token : ArcEndToken) :
    stringEndTokenNode (stepCap state position) token
      = stringEndTokenNode state (capEndTokenBackmap position token) := by
  have owEq : (stepCap state position).openWires = natListRemoveTwoAt state.openWires position := by
    dsimp only [stepCap]; split <;> rfl
  cases token with
  | bottomPort portValue => rfl
  | openSlot slotPosition =>
      show natListGetAt (stepCap state position).openWires slotPosition
        = natListGetAt state.openWires (freshShiftAbove position 2 slotPosition)
      rw [owEq]
      cases Nat.lt_or_ge slotPosition position with
      | inl slotBelowWindow =>
          rw [freshShiftAbove_ofNotLe position 2 slotPosition (fun windowLeSlot =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowWindow))]
          exact natListGetAt_natListRemoveTwoAt_below state.openWires position slotPosition
            slotBelowWindow
      | inr windowLeSlot =>
          rw [freshShiftAbove_ofLe position 2 slotPosition windowLeSlot]
          obtain ⟨offsetAmount, offsetSpec⟩ := Nat.le.dest windowLeSlot
          have pastRead := natListGetAt_natListRemoveTwoAt_pastPair state.openWires position
            offsetAmount capInRange
          rw [offsetSpec] at pastRead
          exact pastRead

/-- The backmap preserves token validity over `WireState`: a genuine boundary end of the capped state comes from a
genuine boundary end of the old state. -/
theorem stringCapEndTokenBackmap_isValid (seedBoundary : Nat) (state : WireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) (token : ArcEndToken)
    (validNew : isValidStringEndToken seedBoundary (stepCap state position) token) :
    isValidStringEndToken seedBoundary state (capEndTokenBackmap position token) := by
  have owEq : (stepCap state position).openWires = natListRemoveTwoAt state.openWires position := by
    dsimp only [stepCap]; split <;> rfl
  cases token with
  | bottomPort portValue => exact validNew
  | openSlot slotPosition =>
      have slotBelowNewLengthStep : slotPosition < (stepCap state position).openWires.length := validNew
      have slotBelowNewLength :
          slotPosition < (natListRemoveTwoAt state.openWires position).length := by
        rw [owEq] at slotBelowNewLengthStep; exact slotBelowNewLengthStep
      have lengthSplit :
          (natListRemoveTwoAt state.openWires position).length + 2 = state.openWires.length :=
        natListRemoveTwoAt_length state.openWires position capInRange
      show freshShiftAbove position 2 slotPosition < state.openWires.length
      cases Nat.lt_or_ge slotPosition position with
      | inl slotBelowWindow =>
          rw [freshShiftAbove_ofNotLe position 2 slotPosition (fun windowLeSlot =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowWindow))]
          exact Nat.lt_of_lt_of_le slotBelowNewLength
            (lengthSplit ▸ Nat.le_add_right (natListRemoveTwoAt state.openWires position).length 2)
      | inr windowLeSlot =>
          rw [freshShiftAbove_ofLe position 2 slotPosition windowLeSlot]
          exact lengthSplit ▸ Nat.add_lt_add_right slotBelowNewLength 2

/-! ## ★ The CAP census preservation -/

/-- ★ **A CAP step preserves the boundary census.**  The string port of `arcBoundaryCensus_stepCapArc`: backmap the
three offending tokens to the old state (nodes and validity preserved, distinctness preserved, the consumed window
slots never hit), and dispatch the wire join.  The event-join peel of the arc version is DELETED — `stepCap`'s link
update is the DIRECT `unionFindJoin` (`stepCap_links_eq_unionFindJoin`, covering BOTH the loop and join branches
uniformly), so the census sits on `unionFindJoin state.links leftWire rightWire` with nothing to peel.  Every dispatch
branch hands the old census a genuine three-token violation — either the backmapped triple itself, or two backmapped
tokens together with a consumed window slot whose component they share. -/
theorem stringBoundaryCensus_stepCap (seedBoundary : Nat) (state : WireState) (position : Nat)
    (forest : stringIsUnionFindForest state.links)
    (capInRange : position + 2 ≤ state.openWires.length)
    (oldCensus : StringBoundaryCensus seedBoundary state) :
    StringBoundaryCensus seedBoundary (stepCap state position) := by
  intro tokenOne tokenTwo tokenThree validOne validTwo validThree
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
  have sharedForest : isUnionFindForest state.links := stringForest_toUnionFindForest state.links forest
  have validOldOne := stringCapEndTokenBackmap_isValid seedBoundary state position capInRange
    tokenOne validOne
  have validOldTwo := stringCapEndTokenBackmap_isValid seedBoundary state position capInRange
    tokenTwo validTwo
  have validOldThree := stringCapEndTokenBackmap_isValid seedBoundary state position capInRange
    tokenThree validThree
  have oldOneNeTwo : capEndTokenBackmap position tokenOne ≠ capEndTokenBackmap position tokenTwo :=
    fun backmapsEqual => oneNeTwo (capEndTokenBackmap_injective position tokenOne tokenTwo
      backmapsEqual)
  have oldOneNeThree :
      capEndTokenBackmap position tokenOne ≠ capEndTokenBackmap position tokenThree :=
    fun backmapsEqual => oneNeThree (capEndTokenBackmap_injective position tokenOne tokenThree
      backmapsEqual)
  have oldTwoNeThree :
      capEndTokenBackmap position tokenTwo ≠ capEndTokenBackmap position tokenThree :=
    fun backmapsEqual => twoNeThree (capEndTokenBackmap_injective position tokenTwo tokenThree
      backmapsEqual)
  have capLeftValid : isValidStringEndToken seedBoundary state (ArcEndToken.openSlot position) :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) capInRange
  have capRightValid :
      isValidStringEndToken seedBoundary state (ArcEndToken.openSlot (position + 1)) :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) position) capInRange
  have joinedOneTwo :
      isSameComponent
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
        (stringEndTokenNode state (capEndTokenBackmap position tokenTwo)) = true := by
    rw [← stringCapEndTokenBackmap_node state position capInRange tokenOne,
      ← stringCapEndTokenBackmap_node state position capInRange tokenTwo,
      ← stepCap_links_eq_unionFindJoin state position]
    exact sameOneTwo
  have joinedOneThree :
      isSameComponent
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
        (stringEndTokenNode state (capEndTokenBackmap position tokenThree)) = true := by
    rw [← stringCapEndTokenBackmap_node state position capInRange tokenOne,
      ← stringCapEndTokenBackmap_node state position capInRange tokenThree,
      ← stepCap_links_eq_unionFindJoin state position]
    exact sameOneThree
  have dispatchOneTwo := sameComponent_unionFindJoin_dispatch state.links sharedForest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
    (stringEndTokenNode state (capEndTokenBackmap position tokenTwo)) joinedOneTwo
  have dispatchOneThree := sameComponent_unionFindJoin_dispatch state.links sharedForest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
    (stringEndTokenNode state (capEndTokenBackmap position tokenThree)) joinedOneThree
  cases dispatchOneTwo with
  | inl baseOneTwo =>
      cases dispatchOneThree with
      | inl baseOneThree =>
          exact oldCensus (capEndTokenBackmap position tokenOne)
            (capEndTokenBackmap position tokenTwo) (capEndTokenBackmap position tokenThree)
            validOldOne validOldTwo validOldThree oldOneNeTwo oldOneNeThree oldTwoNeThree
            baseOneTwo baseOneThree
      | inr crossOneThree =>
          cases crossOneThree with
          | inl legOneThree =>
              obtain ⟨leftReachesOne, _rightReachesThree⟩ := legOneThree
              have leftReachesTwo := isSameComponent_trans state.links
                (natListGetAt state.openWires position)
                (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                (stringEndTokenNode state (capEndTokenBackmap position tokenTwo))
                leftReachesOne baseOneTwo
              exact oldCensus (ArcEndToken.openSlot position)
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenTwo)
                capLeftValid validOldOne validOldTwo
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenTwo))
                oldOneNeTwo leftReachesOne leftReachesTwo
          | inr swapOneThree =>
              obtain ⟨_leftReachesThree, oneReachesRight⟩ := swapOneThree
              have rightReachesOne := isSameComponent_flip state.links
                (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                (natListGetAt state.openWires (position + 1)) oneReachesRight
              have rightReachesTwo := isSameComponent_trans state.links
                (natListGetAt state.openWires (position + 1))
                (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                (stringEndTokenNode state (capEndTokenBackmap position tokenTwo))
                rightReachesOne baseOneTwo
              exact oldCensus (ArcEndToken.openSlot (position + 1))
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenTwo)
                capRightValid validOldOne validOldTwo
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenTwo))
                oldOneNeTwo rightReachesOne rightReachesTwo
  | inr crossOneTwo =>
      cases crossOneTwo with
      | inl legOneTwo =>
          obtain ⟨leftReachesOne, rightReachesTwo⟩ := legOneTwo
          cases dispatchOneThree with
          | inl baseOneThree =>
              have leftReachesThree := isSameComponent_trans state.links
                (natListGetAt state.openWires position)
                (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                (stringEndTokenNode state (capEndTokenBackmap position tokenThree))
                leftReachesOne baseOneThree
              exact oldCensus (ArcEndToken.openSlot position)
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenThree)
                capLeftValid validOldOne validOldThree
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenThree))
                oldOneNeThree leftReachesOne leftReachesThree
          | inr crossOneThree =>
              cases crossOneThree with
              | inl legOneThree =>
                  obtain ⟨_leftReachesOneAgain, rightReachesThree⟩ := legOneThree
                  exact oldCensus (ArcEndToken.openSlot (position + 1))
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    capRightValid validOldTwo validOldThree
                    (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenTwo))
                    (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenThree))
                    oldTwoNeThree rightReachesTwo rightReachesThree
              | inr swapOneThree =>
                  obtain ⟨leftReachesThree, oneReachesRight⟩ := swapOneThree
                  have baseOneTwo := isSameComponent_trans state.links
                    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires (position + 1))
                    (stringEndTokenNode state (capEndTokenBackmap position tokenTwo))
                    oneReachesRight rightReachesTwo
                  have oneReachesLeft := isSameComponent_flip state.links
                    (natListGetAt state.openWires position)
                    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                    leftReachesOne
                  have baseOneThree := isSameComponent_trans state.links
                    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires position)
                    (stringEndTokenNode state (capEndTokenBackmap position tokenThree))
                    oneReachesLeft leftReachesThree
                  exact oldCensus (capEndTokenBackmap position tokenOne)
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    validOldOne validOldTwo validOldThree oldOneNeTwo oldOneNeThree
                    oldTwoNeThree baseOneTwo baseOneThree
      | inr swapOneTwo =>
          obtain ⟨leftReachesTwo, oneReachesRight⟩ := swapOneTwo
          have rightReachesOne := isSameComponent_flip state.links
            (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
            (natListGetAt state.openWires (position + 1)) oneReachesRight
          cases dispatchOneThree with
          | inl baseOneThree =>
              have rightReachesThree := isSameComponent_trans state.links
                (natListGetAt state.openWires (position + 1))
                (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                (stringEndTokenNode state (capEndTokenBackmap position tokenThree))
                rightReachesOne baseOneThree
              exact oldCensus (ArcEndToken.openSlot (position + 1))
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenThree)
                capRightValid validOldOne validOldThree
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenThree))
                oldOneNeThree rightReachesOne rightReachesThree
          | inr crossOneThree =>
              cases crossOneThree with
              | inl legOneThree =>
                  obtain ⟨leftReachesOne, rightReachesThree⟩ := legOneThree
                  have oneReachesLeft := isSameComponent_flip state.links
                    (natListGetAt state.openWires position)
                    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                    leftReachesOne
                  have baseOneTwo := isSameComponent_trans state.links
                    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires position)
                    (stringEndTokenNode state (capEndTokenBackmap position tokenTwo))
                    oneReachesLeft leftReachesTwo
                  have baseOneThree := isSameComponent_trans state.links
                    (stringEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires (position + 1))
                    (stringEndTokenNode state (capEndTokenBackmap position tokenThree))
                    oneReachesRight rightReachesThree
                  exact oldCensus (capEndTokenBackmap position tokenOne)
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    validOldOne validOldTwo validOldThree oldOneNeTwo oldOneNeThree
                    oldTwoNeThree baseOneTwo baseOneThree
              | inr swapOneThreeAgain =>
                  obtain ⟨leftReachesThree, _⟩ := swapOneThreeAgain
                  exact oldCensus (ArcEndToken.openSlot position)
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    capLeftValid validOldTwo validOldThree
                    (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenTwo))
                    (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenThree))
                    oldTwoNeThree leftReachesTwo leftReachesThree

/-! ## The splice backmap on boundary end tokens (CUP), node/validity over `WireState` -/

/-- The splice backmap (`cupEndTokenBackmap`, reused) preserves the read node on the old zone.  `stepCup`'s open
wires are `natListInsertAt state.openWires position [nextFresh, nextFresh+1]`, so below-window reads are untouched and
past-window reads shift over the spliced pair. -/
theorem stringCupEndTokenBackmap_node (state : WireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) (token : ArcEndToken)
    (zone : isCupOldZoneToken position token) :
    stringEndTokenNode (stepCup state position) token
      = stringEndTokenNode state (cupEndTokenBackmap position token) := by
  cases token with
  | bottomPort portValue => rfl
  | openSlot slotPosition =>
      show natListGetAt (natListInsertAt state.openWires position
          [state.nextFresh, state.nextFresh + 1]) slotPosition
        = natListGetAt state.openWires
            (if slotPosition < position then slotPosition else slotPosition - 2)
      cases zone with
      | inl slotBelowWindow =>
          rw [if_pos slotBelowWindow]
          exact natListGetAt_natListInsertAt_below state.openWires position
            [state.nextFresh, state.nextFresh + 1] slotPosition slotBelowWindow
            (Nat.lt_of_lt_of_le slotBelowWindow cupInRange)
      | inr windowPastSlot =>
          obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastSlot
          have slotSpec : slotPosition = position + gapAmount + 2 :=
            gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
          have positionLeSlot : position ≤ slotPosition :=
            Nat.le_trans (Nat.le_add_right position 2) windowPastSlot
          have backmapValue : slotPosition - 2 = position + gapAmount := by
            rw [slotSpec]; exact rfl
          have pastRead : natListGetAt (natListInsertAt state.openWires position
              [state.nextFresh, state.nextFresh + 1]) (position + gapAmount + 2)
              = natListGetAt state.openWires (position + gapAmount) :=
            natListGetAt_natListInsertAt_pastBlock state.openWires position
              [state.nextFresh, state.nextFresh + 1] gapAmount cupInRange
          rw [if_neg (fun slotBelowWindow =>
              Nat.lt_irrefl position (Nat.lt_of_le_of_lt positionLeSlot slotBelowWindow)),
            backmapValue, slotSpec]
          exact pastRead

/-- The splice backmap preserves token validity on the old zone over `WireState`. -/
theorem stringCupEndTokenBackmap_isValid (seedBoundary : Nat) (state : WireState) (position : Nat)
    (token : ArcEndToken) (zone : isCupOldZoneToken position token)
    (cupInRange : position ≤ state.openWires.length)
    (validNew : isValidStringEndToken seedBoundary (stepCup state position) token) :
    isValidStringEndToken seedBoundary state (cupEndTokenBackmap position token) := by
  cases token with
  | bottomPort portValue => exact validNew
  | openSlot slotPosition =>
      show (if slotPosition < position then slotPosition else slotPosition - 2)
        < state.openWires.length
      cases zone with
      | inl slotBelowWindow =>
          rw [if_pos slotBelowWindow]
          exact Nat.lt_of_lt_of_le slotBelowWindow cupInRange
      | inr windowPastSlot =>
          obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastSlot
          have slotSpec : slotPosition = position + gapAmount + 2 :=
            gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
          have positionLeSlot : position ≤ slotPosition :=
            Nat.le_trans (Nat.le_add_right position 2) windowPastSlot
          have backmapValue : slotPosition - 2 = position + gapAmount := by
            rw [slotSpec]; exact rfl
          have slotBelowNewLength : slotPosition < (natListInsertAt state.openWires position
              [state.nextFresh, state.nextFresh + 1]).length := validNew
          rw [natListInsertAt_length state.openWires position
            [state.nextFresh, state.nextFresh + 1]] at slotBelowNewLength
          rw [slotSpec] at slotBelowNewLength
          rw [if_neg (fun slotBelowWindow =>
              Nat.lt_irrefl position (Nat.lt_of_le_of_lt positionLeSlot slotBelowWindow)),
            backmapValue]
          exact Nat.lt_of_add_lt_add_right slotBelowNewLength

/-! ## The cup's link update is a fresh-edge cons + the old/leg separation -/

/-- ★ **A cup's link update is a fresh-edge prepend.**  Given freshness, the two spliced legs `nextFresh`,
`nextFresh+1` are each nobody's child (roots), so `unionFindJoin state.links nextFresh (nextFresh+1)` prepends exactly
`(nextFresh, nextFresh+1)`.  This puts `(stepCup state position).links` into the `freshChild :: links` shape the shipped
`stringIsSameComponent_cons_freshAbove_forest` and freshness kits consume. -/
theorem stringStepCup_links_cons (state : WireState) (position : Nat)
    (fresh : StringWireStateFresh state) :
    (stepCup state position).links = (state.nextFresh, state.nextFresh + 1) :: state.links := by
  show unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
    = (state.nextFresh, state.nextFresh + 1) :: state.links
  have leftNotChild : ∀ edge ∈ state.links, edge.1 ≠ state.nextFresh :=
    fun edge memEdge => Nat.ne_of_lt (fresh.linksBelow edge memEdge).1
  have rightNotChild : ∀ edge ∈ state.links, edge.1 ≠ state.nextFresh + 1 :=
    fun edge memEdge =>
      Nat.ne_of_lt (Nat.lt_trans (fresh.linksBelow edge memEdge).1 (Nat.lt_succ_self state.nextFresh))
  have leftRoot : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_notChild state.links state.nextFresh leftNotChild
  have rightRoot : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_notChild state.links (state.nextFresh + 1) rightNotChild
  have distinct : (state.nextFresh == state.nextFresh + 1) = false :=
    censusBeqFalseOfNe state.nextFresh (state.nextFresh + 1) (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))
  exact unionFindJoin_freshPair state.links state.nextFresh (state.nextFresh + 1) leftRoot rightRoot distinct

/-- Same-component is `false` when the two nodes have distinct roots. -/
theorem stringNotSame_of_rootsNe (links : List (Nat × Nat)) (leftNode rightNode : Nat)
    (rootsNe : unionFindRootOf links leftNode ≠ unionFindRootOf links rightNode) :
    isSameComponent links leftNode rightNode = false := by
  cases sameTest : isSameComponent links leftNode rightNode with
  | false => rfl
  | true => exact absurd (of_decide_eq_true sameTest) rootsNe

/-- ★ **The cup leg SEPARATION.**  An OLD wire (`oldNode < nextFresh`) never shares a component with a fresh LEG
(`nextFresh ≤ legNode`) after the cup's fresh join.  The join only relates `nextFresh ↔ nextFresh+1` (both ≥
`nextFresh`); on the forest the old node's root stays below `nextFresh` (`unionFindRootOf_lt`) while every leg root is
`≥ nextFresh` (`unionFindRootOf_of_notChild`), so the flat-disjunction characterization collapses to `false`.  This is
the string port of the arc's `isSameComponent_stepCupArc_oldFreshProbes`, without an event node. -/
theorem stringCupLegSeparation (state : WireState) (position : Nat)
    (fresh : StringWireStateFresh state) (forest : stringIsUnionFindForest state.links)
    (oldNode legNode : Nat) (oldBelow : oldNode < state.nextFresh)
    (legAtLeast : state.nextFresh ≤ legNode) :
    isSameComponent (stepCup state position).links oldNode legNode = false := by
  have sharedForest : isUnionFindForest state.links := stringForest_toUnionFindForest state.links forest
  have edgesSndBounded : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge memEdge => (fresh.linksBelow edge memEdge).2
  have rootOldBelow : unionFindRootOf state.links oldNode < state.nextFresh :=
    unionFindRootOf_lt state.nextFresh state.links edgesSndBounded oldNode oldBelow
  have legNotChild : ∀ edge ∈ state.links, edge.1 ≠ legNode :=
    fun edge memEdge => Nat.ne_of_lt (Nat.lt_of_lt_of_le (fresh.linksBelow edge memEdge).1 legAtLeast)
  have rootLegSelf : unionFindRootOf state.links legNode = legNode :=
    unionFindRootOf_of_notChild state.links legNode legNotChild
  have freshNotChild : ∀ edge ∈ state.links, edge.1 ≠ state.nextFresh :=
    fun edge memEdge => Nat.ne_of_lt (fresh.linksBelow edge memEdge).1
  have rootFreshSelf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_notChild state.links state.nextFresh freshNotChild
  have freshSuccNotChild : ∀ edge ∈ state.links, edge.1 ≠ state.nextFresh + 1 :=
    fun edge memEdge =>
      Nat.ne_of_lt (Nat.lt_trans (fresh.linksBelow edge memEdge).1 (Nat.lt_succ_self state.nextFresh))
  have rootFreshSuccSelf : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_notChild state.links (state.nextFresh + 1) freshSuccNotChild
  have disjOldLeg : isSameComponent state.links oldNode legNode = false := by
    apply stringNotSame_of_rootsNe
    rw [rootLegSelf]
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le rootOldBelow legAtLeast)
  have disjFreshOld : isSameComponent state.links state.nextFresh oldNode = false := by
    apply stringNotSame_of_rootsNe
    rw [rootFreshSelf]
    exact (Nat.ne_of_lt rootOldBelow).symm
  have disjOldFreshSucc : isSameComponent state.links oldNode (state.nextFresh + 1) = false := by
    apply stringNotSame_of_rootsNe
    rw [rootFreshSuccSelf]
    exact Nat.ne_of_lt (Nat.lt_trans rootOldBelow (Nat.lt_succ_self state.nextFresh))
  have expand := isSameComponent_unionFindJoin state.links sharedForest
    state.nextFresh (state.nextFresh + 1) oldNode legNode
  show isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) oldNode legNode
    = false
  rw [expand, disjOldLeg, disjFreshOld, disjOldFreshSucc]
  cases isSameComponent state.links (state.nextFresh + 1) legNode <;>
    cases isSameComponent state.links state.nextFresh legNode <;> rfl

/-! ## ★ The CUP census preservation -/

/-- ★ **A CUP step preserves the boundary census.**  The string port of `arcBoundaryCensus_stepCupArc`, over the bare
`WireState`.  Classify the three offending tokens by node zone (below `nextFresh` = old, else one of the two spliced
legs): any old/leg mixture contradicts the leg SEPARATION (`stringCupLegSeparation`), three leg tokens pigeonhole into
the two window slots against their distinctness, and three old-zone tokens transport onto the old census through the
fresh-edge invisibility (`stringIsSameComponent_cons_freshAbove_forest`) via the splice backmap.  STRICTLY simpler than
the arc's cup: no event node — the fresh join is a direct `(nextFresh, nextFresh+1)` prepend
(`stringStepCup_links_cons`). -/
theorem stringBoundaryCensus_stepCup (seedBoundary : Nat) (state : WireState) (position : Nat)
    (fresh : StringWireStateFresh state) (forest : stringIsUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (oldCensus : StringBoundaryCensus seedBoundary state) :
    StringBoundaryCensus seedBoundary (stepCup state position) := by
  intro tokenOne tokenTwo tokenThree validOne validTwo validThree
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
  have parentsBounded : ∀ parent ∈ state.links.map Prod.snd, parent < state.nextFresh :=
    StringWireStateFresh_parentsBelow fresh
  have linksCons : (stepCup state position).links = (state.nextFresh, state.nextFresh + 1) :: state.links :=
    stringStepCup_links_cons state position fresh
  have wireReadBelowFresh : ∀ index : Nat, index < state.openWires.length →
      natListGetAt state.openWires index < state.nextFresh := by
    intro index indexBelowLength
    have boundPositive : 0 < state.nextFresh := by
      cases wiresShape : state.openWires with
      | nil =>
          rw [wiresShape] at indexBelowLength
          exact absurd indexBelowLength (Nat.not_lt_zero index)
      | cons headWire restWires =>
          have headInOpen : headWire ∈ state.openWires := by
            rw [wiresShape]; exact List.Mem.head _
          exact Nat.lt_of_le_of_lt (Nat.zero_le headWire) (fresh.openBelow headWire headInOpen)
    exact natListGetAt_lt state.nextFresh boundPositive state.openWires index fresh.openBelow
  have legReadLeft : natListGetAt (natListInsertAt state.openWires position
      [state.nextFresh, state.nextFresh + 1]) position = state.nextFresh := by
    have insideRead := natListGetAt_natListInsertAt_inside state.openWires position
      [state.nextFresh, state.nextFresh + 1] 0 (Nat.zero_lt_succ 1) cupInRange
    rw [Nat.add_zero] at insideRead
    exact insideRead
  have legReadRight : natListGetAt (natListInsertAt state.openWires position
      [state.nextFresh, state.nextFresh + 1]) (position + 1) = state.nextFresh + 1 :=
    natListGetAt_natListInsertAt_inside state.openWires position
      [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) cupInRange
  have classify : ∀ token : ArcEndToken,
      isValidStringEndToken seedBoundary (stepCup state position) token →
      (isCupOldZoneToken position token
          ∧ stringEndTokenNode (stepCup state position) token < state.nextFresh)
        ∨ (token = ArcEndToken.openSlot position
            ∧ stringEndTokenNode (stepCup state position) token = state.nextFresh)
        ∨ (token = ArcEndToken.openSlot (position + 1)
            ∧ stringEndTokenNode (stepCup state position) token = state.nextFresh + 1) := by
    intro token tokenValid
    cases token with
    | bottomPort portValue =>
        exact Or.inl ⟨True.intro, Nat.lt_of_lt_of_le tokenValid seedBelowFresh⟩
    | openSlot slotPosition =>
        cases Nat.lt_or_ge slotPosition position with
        | inl slotBelowWindow =>
            refine Or.inl ⟨Or.inl slotBelowWindow, ?_⟩
            show natListGetAt (natListInsertAt state.openWires position
                [state.nextFresh, state.nextFresh + 1]) slotPosition < state.nextFresh
            rw [natListGetAt_natListInsertAt_below state.openWires position
              [state.nextFresh, state.nextFresh + 1] slotPosition slotBelowWindow
              (Nat.lt_of_lt_of_le slotBelowWindow cupInRange)]
            exact wireReadBelowFresh slotPosition
              (Nat.lt_of_lt_of_le slotBelowWindow cupInRange)
        | inr windowLeSlot =>
            cases Nat.lt_or_ge slotPosition (position + 2) with
            | inl slotInWindow =>
                cases Nat.lt_or_ge slotPosition (position + 1) with
                | inl slotBelowSucc =>
                    have slotEqualsWindow : slotPosition = position :=
                      Nat.le_antisymm (Nat.le_of_lt_succ slotBelowSucc) windowLeSlot
                    refine Or.inr (Or.inl
                      ⟨congrArg ArcEndToken.openSlot slotEqualsWindow, ?_⟩)
                    show natListGetAt (natListInsertAt state.openWires position
                        [state.nextFresh, state.nextFresh + 1]) slotPosition = state.nextFresh
                    rw [slotEqualsWindow]; exact legReadLeft
                | inr succLeSlot =>
                    have slotEqualsSucc : slotPosition = position + 1 :=
                      Nat.le_antisymm (Nat.le_of_lt_succ slotInWindow) succLeSlot
                    refine Or.inr (Or.inr
                      ⟨congrArg ArcEndToken.openSlot slotEqualsSucc, ?_⟩)
                    show natListGetAt (natListInsertAt state.openWires position
                        [state.nextFresh, state.nextFresh + 1]) slotPosition = state.nextFresh + 1
                    rw [slotEqualsSucc]; exact legReadRight
            | inr windowPastSlot =>
                refine Or.inl ⟨Or.inr windowPastSlot, ?_⟩
                obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastSlot
                have slotSpec : slotPosition = position + gapAmount + 2 :=
                  gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
                have pastRead : natListGetAt (natListInsertAt state.openWires position
                    [state.nextFresh, state.nextFresh + 1]) (position + gapAmount + 2)
                    = natListGetAt state.openWires (position + gapAmount) :=
                  natListGetAt_natListInsertAt_pastBlock state.openWires position
                    [state.nextFresh, state.nextFresh + 1] gapAmount cupInRange
                have slotBelowNewLength : slotPosition < (natListInsertAt state.openWires
                    position [state.nextFresh, state.nextFresh + 1]).length := tokenValid
                rw [natListInsertAt_length state.openWires position
                    [state.nextFresh, state.nextFresh + 1], slotSpec] at slotBelowNewLength
                show natListGetAt (natListInsertAt state.openWires position
                    [state.nextFresh, state.nextFresh + 1]) slotPosition < state.nextFresh
                rw [slotSpec, pastRead]
                exact wireReadBelowFresh (position + gapAmount)
                  (Nat.lt_of_add_lt_add_right slotBelowNewLength)
  have refuteOldLeg : ∀ oldNode legNode : Nat, oldNode < state.nextFresh →
      state.nextFresh ≤ legNode →
      isSameComponent (stepCup state position).links oldNode legNode = true → False := by
    intro oldNode legNode oldBelow legAtLeast sameHolds
    rw [stringCupLegSeparation state position fresh forest oldNode legNode oldBelow legAtLeast] at sameHolds
    exact Bool.noConfusion sameHolds
  have refuteLegOld : ∀ legNode oldNode : Nat, state.nextFresh ≤ legNode →
      oldNode < state.nextFresh →
      isSameComponent (stepCup state position).links legNode oldNode = true → False := by
    intro legNode oldNode legAtLeast oldBelow sameHolds
    have flipped := isSameComponent_flip (stepCup state position).links legNode oldNode sameHolds
    rw [stringCupLegSeparation state position fresh forest oldNode legNode oldBelow legAtLeast] at flipped
    exact Bool.noConfusion flipped
  have legNodeAtLeast : ∀ token : ArcEndToken,
      (token = ArcEndToken.openSlot position
          ∧ stringEndTokenNode (stepCup state position) token = state.nextFresh)
        ∨ (token = ArcEndToken.openSlot (position + 1)
            ∧ stringEndTokenNode (stepCup state position) token = state.nextFresh + 1) →
      state.nextFresh ≤ stringEndTokenNode (stepCup state position) token := by
    intro token legFact
    cases legFact with
    | inl leftLeg => exact Nat.le_of_eq leftLeg.2.symm
    | inr rightLeg =>
        exact Nat.le_trans (Nat.le_succ state.nextFresh) (Nat.le_of_eq rightLeg.2.symm)
  cases classify tokenOne validOne with
  | inl oldOne =>
      obtain ⟨zoneOne, nodeOneBelow⟩ := oldOne
      cases classify tokenTwo validTwo with
      | inl oldTwo =>
          obtain ⟨zoneTwo, nodeTwoBelow⟩ := oldTwo
          cases classify tokenThree validThree with
          | inl oldThree =>
              obtain ⟨zoneThree, nodeThreeBelow⟩ := oldThree
              have backmapNodeOne := stringCupEndTokenBackmap_node state position cupInRange tokenOne zoneOne
              have backmapNodeTwo := stringCupEndTokenBackmap_node state position cupInRange tokenTwo zoneTwo
              have backmapNodeThree :=
                stringCupEndTokenBackmap_node state position cupInRange tokenThree zoneThree
              have oldBelowOne : stringEndTokenNode state (cupEndTokenBackmap position tokenOne)
                  < state.nextFresh := backmapNodeOne ▸ nodeOneBelow
              have oldBelowTwo : stringEndTokenNode state (cupEndTokenBackmap position tokenTwo)
                  < state.nextFresh := backmapNodeTwo ▸ nodeTwoBelow
              have oldBelowThree : stringEndTokenNode state (cupEndTokenBackmap position tokenThree)
                  < state.nextFresh := backmapNodeThree ▸ nodeThreeBelow
              have oldSameOneTwo : isSameComponent state.links
                  (stringEndTokenNode state (cupEndTokenBackmap position tokenOne))
                  (stringEndTokenNode state (cupEndTokenBackmap position tokenTwo)) = true := by
                have transported := sameOneTwo
                rw [backmapNodeOne, backmapNodeTwo, linksCons,
                  stringIsSameComponent_cons_freshAbove_forest state.nextFresh (state.nextFresh + 1)
                    state.nextFresh state.links parentsBounded (Nat.le_refl state.nextFresh) forest
                    (stringEndTokenNode state (cupEndTokenBackmap position tokenOne))
                    (stringEndTokenNode state (cupEndTokenBackmap position tokenTwo))
                    oldBelowOne oldBelowTwo] at transported
                exact transported
              have oldSameOneThree : isSameComponent state.links
                  (stringEndTokenNode state (cupEndTokenBackmap position tokenOne))
                  (stringEndTokenNode state (cupEndTokenBackmap position tokenThree)) = true := by
                have transported := sameOneThree
                rw [backmapNodeOne, backmapNodeThree, linksCons,
                  stringIsSameComponent_cons_freshAbove_forest state.nextFresh (state.nextFresh + 1)
                    state.nextFresh state.links parentsBounded (Nat.le_refl state.nextFresh) forest
                    (stringEndTokenNode state (cupEndTokenBackmap position tokenOne))
                    (stringEndTokenNode state (cupEndTokenBackmap position tokenThree))
                    oldBelowOne oldBelowThree] at transported
                exact transported
              exact oldCensus (cupEndTokenBackmap position tokenOne)
                (cupEndTokenBackmap position tokenTwo) (cupEndTokenBackmap position tokenThree)
                (stringCupEndTokenBackmap_isValid seedBoundary state position tokenOne zoneOne
                  cupInRange validOne)
                (stringCupEndTokenBackmap_isValid seedBoundary state position tokenTwo zoneTwo
                  cupInRange validTwo)
                (stringCupEndTokenBackmap_isValid seedBoundary state position tokenThree zoneThree
                  cupInRange validThree)
                (fun backmapsEqual => oneNeTwo (cupEndTokenBackmap_injective position tokenOne
                  tokenTwo zoneOne zoneTwo backmapsEqual))
                (fun backmapsEqual => oneNeThree (cupEndTokenBackmap_injective position tokenOne
                  tokenThree zoneOne zoneThree backmapsEqual))
                (fun backmapsEqual => twoNeThree (cupEndTokenBackmap_injective position tokenTwo
                  tokenThree zoneTwo zoneThree backmapsEqual))
                oldSameOneTwo oldSameOneThree
          | inr legThree =>
              exact refuteOldLeg (stringEndTokenNode (stepCup state position) tokenOne)
                (stringEndTokenNode (stepCup state position) tokenThree) nodeOneBelow
                (legNodeAtLeast tokenThree legThree) sameOneThree
      | inr legTwo =>
          exact refuteOldLeg (stringEndTokenNode (stepCup state position) tokenOne)
            (stringEndTokenNode (stepCup state position) tokenTwo) nodeOneBelow
            (legNodeAtLeast tokenTwo legTwo) sameOneTwo
  | inr legOne =>
      cases classify tokenTwo validTwo with
      | inl oldTwo =>
          exact refuteLegOld (stringEndTokenNode (stepCup state position) tokenOne)
            (stringEndTokenNode (stepCup state position) tokenTwo)
            (legNodeAtLeast tokenOne legOne) oldTwo.2 sameOneTwo
      | inr legTwo =>
          cases classify tokenThree validThree with
          | inl oldThree =>
              exact refuteLegOld (stringEndTokenNode (stepCup state position) tokenOne)
                (stringEndTokenNode (stepCup state position) tokenThree)
                (legNodeAtLeast tokenOne legOne) oldThree.2 sameOneThree
          | inr legThree =>
              cases legOne with
              | inl oneIsLeft =>
                  cases legTwo with
                  | inl twoIsLeft => exact oneNeTwo (oneIsLeft.1.trans twoIsLeft.1.symm)
                  | inr twoIsRight =>
                      cases legThree with
                      | inl threeIsLeft =>
                          exact oneNeThree (oneIsLeft.1.trans threeIsLeft.1.symm)
                      | inr threeIsRight =>
                          exact twoNeThree (twoIsRight.1.trans threeIsRight.1.symm)
              | inr oneIsRight =>
                  cases legTwo with
                  | inl twoIsLeft =>
                      cases legThree with
                      | inl threeIsLeft =>
                          exact twoNeThree (twoIsLeft.1.trans threeIsLeft.1.symm)
                      | inr threeIsRight =>
                          exact oneNeThree (oneIsRight.1.trans threeIsRight.1.symm)
                  | inr twoIsRight => exact oneNeTwo (oneIsRight.1.trans twoIsRight.1.symm)

/-! ## ★ The census FOLD TRANSPORT — every reachable state (from a cup/cap cell) satisfies the census -/

/-- Freshness is preserved by one cup/cap atom: dispatch on the arity (`stepAtom_ofCupArity` / `_ofCapArity`) and
apply the shipped cup / cap freshness legs.  The cap leg needs the window in range, supplied by the boundary
tracking. -/
theorem StringWireStateFresh_stepAtom {sourceMode targetMode : AdjointTripleMode}
    (state : WireState) (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom) (fresh : StringWireStateFresh state)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength) :
    StringWireStateFresh (stepAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length := tracksEntry
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity state atom cupArity.1 cupArity.2]
      exact StringWireStateFresh_stepCup state atom.leftContext.length fresh
  | inr capArity =>
      obtain ⟨hasCapDom, hasCapCod⟩ := capArity
      have windowInRange : atom.leftContext.length + 1 < state.openWires.length := by
        rw [entryShape, hasCapDom]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1))
          (Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length)
      rw [stepAtom_ofCapArity state atom hasCapDom hasCapCod]
      exact StringWireStateFresh_stepCap state atom.leftContext.length windowInRange fresh

/-- ★ **One cup/cap atom preserves the boundary census** — dispatch on the arity, computing the window range from the
boundary tracking (`domBoundaryLength`), and apply the cup / cap step preservation. -/
theorem stringBoundaryCensus_stepAtom {sourceMode targetMode : AdjointTripleMode}
    (seedBoundary : Nat) (state : WireState)
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom) (fresh : StringWireStateFresh state)
    (forest : stringIsUnionFindForest state.links) (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (oldCensus : StringBoundaryCensus seedBoundary state) :
    StringBoundaryCensus seedBoundary (stepAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length := tracksEntry
  cases arity with
  | inl cupArity =>
      obtain ⟨hasCupDom, hasCupCod⟩ := cupArity
      have cupInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape, hasCupDom, Nat.add_zero]
        exact Nat.le_add_right atom.leftContext.length atom.rightContext.length
      rw [stepAtom_ofCupArity state atom hasCupDom hasCupCod]
      exact stringBoundaryCensus_stepCup seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldCensus
  | inr capArity =>
      obtain ⟨hasCapDom, hasCapCod⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDom]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepAtom_ofCapArity state atom hasCapDom hasCapCod]
      exact stringBoundaryCensus_stepCap seedBoundary state atom.leftContext.length
        forest capInRange oldCensus

/-- ★ **A cup/cap-disciplined boundary-chained spine fold preserves the census end-to-end** — the freshness / forest /
boundary-tracking / seed-bound / arity companions thread through the fold, and each atom's step preserves the census
by the per-atom dispatch.  The string port of `arcBoundaryCensus_processArcSpine_ofChained`. -/
theorem stringBoundaryCensus_processSpine_ofChained {sourceMode targetMode : AdjointTripleMode} :
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    (state : WireState) → (boundaryLength seedBoundary : Nat) →
    StringWireStateFresh state → stringIsUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    SpineHasCupCapAtoms atoms →
    seedBoundary ≤ state.nextFresh →
    StringBoundaryCensus seedBoundary state →
    StringBoundaryCensus seedBoundary (processSpine state atoms)
  | [], _, _, _, _, _, _, _, _, _, census => census
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained, arityAll,
      seedBelowFresh, census => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      obtain ⟨headArity, tailArity⟩ := spineHasCupCapAtoms_tail arityAll
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      show StringBoundaryCensus seedBoundary (processSpine (stepAtom state headAtom) restAtoms)
      exact stringBoundaryCensus_processSpine_ofChained restAtoms (stepAtom state headAtom)
        headAtom.codBoundaryLength seedBoundary
        (StringWireStateFresh_stepAtom state headAtom headArity fresh tracksEntry)
        (stringUnionFindForest_stepAtom state headAtom forest)
        (stepAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained tailArity
        (Nat.le_trans seedBelowFresh (stepAtom_nextFresh_le state headAtom))
        (stringBoundaryCensus_stepAtom seedBoundary state headAtom headArity fresh forest
          seedBelowFresh tracksEntry census)

/-- ★★ **The census capstone at the canonical seed** — every cup/cap-generated adjoint-triple cell folds from the
fresh initial state to a state whose every union-find component touches at most TWO boundary endpoints (bottom ports
and surviving open slots).  This is the load-bearing perfect-matching structure the JOIN-branch cap non-crossing
consumes. -/
theorem stringBoundaryCensus_fromCell {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (cellCupCap : CellHasCupCapGenerators cell) :
    StringBoundaryCensus sourcePath.length
      (processSpine (stringInitialWireState sourcePath.length) cell.spine) :=
  stringBoundaryCensus_processSpine_ofChained cell.spine
    (stringInitialWireState sourcePath.length) sourcePath.length sourcePath.length
    (stringInitialWireState_fresh sourcePath.length)
    (stringInitialWireState_isUnionFindForest sourcePath.length)
    (censusRangeLength sourcePath.length)
    (RawTwoCellExpr.spineBoundaryChained_spine cell)
    (RawTwoCellExpr.spineHasCupCapAtoms_spine cell cellCupCap)
    (Nat.le_refl sourcePath.length)
    (stringBoundaryCensus_initial sourcePath.length)

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the two-endpoint BOUNDARY CENSUS over the bare `WireState`, seed + cup + cap + FOLD (FC-5, P1).**
The full perfect-matching census fold invariant is SHIPPED zero-axiom, the string port of the arc lane's
`ArcBoundaryCensus` apparatus:

  * the STATEMENT layer (`stringEndTokenNode` / `isValidStringEndToken` / `StringBoundaryCensus`, reusing the
    carrier-free `ArcEndToken`) + the trivial forest bridge (`stringForest_toUnionFindForest`);
  * the SEED (`stringBoundaryCensus_initial`);
  * the CUP step preservation (`stringBoundaryCensus_stepCup`) — the spliced fresh strand carries exactly its two
    window slots; the cup leg SEPARATION (`stringCupLegSeparation`) proves an old wire never shares a component with a
    fresh leg (strictly simpler than the arc's event-node cup);
  * the CAP step preservation (`stringBoundaryCensus_stepCap`) — the merged component loses one open end from each
    side; the arc's event-join peel is DELETED because `stepCap`'s link update is the DIRECT `unionFindJoin`
    (`stepCap_links_eq_unionFindJoin`);
  * the FOLD transport (`stringBoundaryCensus_stepAtom` / `_processSpine_ofChained`) threading freshness / forest /
    boundary-tracking / seed-bound / cup-cap arity, and the SEED capstone (`stringBoundaryCensus_fromCell`): every
    cup/cap-generated adjoint-triple cell folds to a state whose every union-find component touches at most TWO
    boundary endpoints.

This is the load-bearing perfect-matching structure the JOIN-branch cap non-crossing (`fxString_hasCapNonCrossingJoinBranch`)
consumes — a genuine NEW fold invariant, now available.  `= true`. -/
def fxString_hasBoundaryCensus : Bool := true

/-- **OPEN (honest, LOCALIZED) — the census UNLOCKS `preserves.orient`(cap join), NOT `capPin`.**  The census fold
(above) is the exact perfect-matching fact the JOIN-branch cap non-crossing survivor analysis
(`fxString_hasCapNonCrossingJoinBranch`, in `StringFussCatalanCapNonCrossing`) needs to refute the "two survivors reach
the same window end" combos.  As of FC-5 P2 it is CONSUMED — the 5-survivor + 4-census combo table (the string port of
`ArcNonCrossingCapMain`) is SHIPPED as `stringNonCrossing_stepCap` in the sibling `StringCapNonCrossingJoin`, so
`fxString_hasCapNonCrossingJoinBranch := true`.  That consumer feeds ONLY the cap case of the FC-1 `preserves`
obligation (`StringOrientationDiscipline` fold invariance).

It does NOT unlock the FC-1 `capPin` obligation.  `capPin` (a cap window reads its `generatorDom` cap word) is NOT a
census consequence and NOT derivable from `StringOrientationDiscipline` alone: `orient` constrains SAME-component open
pairs, saying nothing about which labels a 2->0 atom's window reads, so a disciplined state admits a cap firing on a
cup-word window.  Discharging `capPin` requires strengthening the fold invariant to carry label-boundary-tracking
(`labels = pathLabels` of the intermediate 1-cell — the string port of `ArcBoundaryTracking` / a `StringJointInvariant`
field), from which capPin is a projection (both walking-adjoint-triple cap words `(G,F)`, `(H,G)` fail
`isCupWordOrdered`, `stringBothCapWords_notCupWord`).  So `fxString_hasNoLoopsTheorem` (in `StringFussCatalan`) stays
`false`, HONESTLY: the census is shipped, the join-branch non-crossing + the capPin label-tracking are the two exact
remaining residuals — and only the FIRST is a census consequence.  `= false`. -/
def fxString_hasBoundaryCensusUnlocksBothResiduals : Bool := false

end FX1Poly.Polygraph
