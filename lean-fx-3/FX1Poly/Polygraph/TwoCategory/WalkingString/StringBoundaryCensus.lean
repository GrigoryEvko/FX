import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCapNonCrossing
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation

/-! # WalkingString — the two-endpoint BOUNDARY CENSUS over the bare `WireState` (FC-5, P1)

The JOIN branch of `stringNonCrossing_stepCap` (FC-4's residual, `fxString_hasCapNonCrossingJoinBranch := false`) is
refuted by a PERFECT-MATCHING census: every union-find component of a cup/cap fold state carries at most TWO boundary
ends (an original bottom port and a currently-open wire end).  This is the load-bearing NEW fold invariant the arc
lane shipped as `ArcBoundaryCensus` over the enriched `ArcWireState`; this file PORTS it to the bare `WireState`.

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

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the boundary-census STATEMENT layer + the SEED leg (FC-5, P1a).**  The census over the bare
`WireState` (`stringEndTokenNode` / `isValidStringEndToken` / `StringBoundaryCensus`, reusing the carrier-free
`ArcEndToken`), the trivial forest bridge (`stringForest_toUnionFindForest`), and its truth at the fresh seed
(`stringBoundaryCensus_initial`, the string port of `arcBoundaryCensus_initial`).  What this marker does NOT yet
claim: the cup / cap step PRESERVATION and the fold transport (P1b–d below).  `= true`. -/
def fxString_hasBoundaryCensusSeed : Bool := true

end FX1Poly.Polygraph
