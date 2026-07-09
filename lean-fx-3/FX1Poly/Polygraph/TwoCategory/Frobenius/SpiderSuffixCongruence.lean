import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderConvTable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewStability
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescComponentSim
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReachable

/-! # WP-FROB r6 (FROB-6) — the FORWARD `stepWiring` view-functoriality brick + the uniform SUFFIX congruence

The FROB-5 ledger (`SpiderConvTable.lean`, `fxFrob_hasSpiderSuffixCongruence = false`) named the standing residual:
the UNIFORM suffix congruence `SpiderConv n a b → SpiderConv n (a ++ suffix) (b ++ suffix)` for all (disciplined)
suffixes, whose one missing ingredient is the FORWARD view-functoriality — view-equal inputs to a `stepWiring` fold
give view-equal outputs.  This is NOT a second application of the r4 keystone
`processBrauer_forgetView_eq_ofCanonicalViewParts` (that keystone fixes ONE mid-state and varies the WORD, under a
single `relativeWireMap` rename; the suffix leg fixes ONE word and varies the MID-STATE — two different renames), so
it is a genuinely new brick.

## The new brick — a boundary-view-only forward congruence (no global rename)

The right/left pads and the Godement kit all transport connectivity through a GLOBAL `sigma`-relabeling
(`stepWiringArcs_componentView` needs `sigma : Nat → Nat` with `sigma 0 = 0`).  Here the two states `stateS`,
`stateT` agree ONLY on the boundary partition VIEW — there is no functional rename between their node values.  So the
brick is built from scratch, generalizing the cap/cup view-stability arms (`matchingViewAgrees_stepCap` /
`matchingViewAgrees_stepCup`, single-arc) to the whole generic `stepWiring` arc fold, via a `StepNodeCorr`
correspondence invariant carried through the fold:

  * `StepNodeCorr` — corresponding nodes: a boundary read at the SAME in-range index in both states, or a fresh
    leg at the SAME offset above each state's own `nextFresh`.
  * `stepNodeCorr_baseSameComp` — the boundary view + the fresh-separation kit give, for corresponding pairs, equal
    same-component booleans at the two INITIAL link tables (four zones: boundary/boundary via the view, the mixed
    zones `false`, fresh/fresh the offset equality).
  * `stepWiringArcs_viewInvariant` — the same-component-of-corresponding-pairs invariant is PRESERVED by the whole
    generic arc fold: the branch test agrees by the invariant, and each `unionFindJoin` step's post-join view is a
    boolean combination of PRE-join views of corresponding pairs (`isSameComponent_unionFindJoin`).
  * `stepWiring_boundaryRead_stepNodeCorr` — every post-step boundary read is a `StepNodeCorr` descriptor (the
    generic four-zone classifier: below the window an old read, inside the fresh block a fresh leg, past the block a
    shifted old read).
  * `stepWiring_viewCongruence` — assembles the three into the single-atom forward congruence; `processBrauer_viewCongruence` folds it over an in-range suffix.

## The reconstruction + assembly

`spiderConv_stateViewEq` reconstructs the boundary view of the two seed-processed states from a `SpiderConv`
derivation (the decided per-row seed views + the interchange/whisker view facts — loops never enter, so the special
row `μδ = 1` is carried).  `spiderConv_suffixCongruence` chains it with the forward brick and the empty-prefix
`whisker` into the uniform suffix congruence.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private Nat / list primitives (public duplicates are file-private elsewhere) -/

private theorem rangeLoopLengthLocal : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthLocal count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthLocalCopy (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthLocal count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastLocal : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastLocal count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowLocal : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowLocal count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastLocal count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowLocal (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowLocal count [] index indexBelow

/-- `natListGetAt` of a `(range count).map (· + base)` at an in-range index is `index + base`. -/
private theorem natListGetAtRangeMapAddLocal (base count index : Nat) (indexBelow : index < count) :
    natListGetAt ((List.range count).map (· + base)) index = index + base := by
  rw [natListGetAt_map_inRange (· + base) (List.range count) index
      (by rw [rangeLengthLocalCopy]; exact indexBelow),
    rangeGetAtBelowLocal count index indexBelow]

/-- `natListGetAt` of a slice reads the original at the shifted position (in range). -/
private theorem natListGetAtSliceLocal :
    (wires : List Nat) → (position count tag : Nat) → tag < count →
    natListGetAt (natListSliceAt wires position count) tag = natListGetAt wires (position + tag)
  | _, _, 0, tag, tagBelow => absurd tagBelow (Nat.not_lt_zero tag)
  | [], _, _ + 1, _, _ => rfl
  | headWire :: rest, 0, count + 1, tag, tagBelow => by
      show natListGetAt (headWire :: natListSliceAt rest 0 count) tag = natListGetAt (headWire :: rest) (0 + tag)
      cases tag with
      | zero => rfl
      | succ innerTag =>
          show natListGetAt (natListSliceAt rest 0 count) innerTag = natListGetAt rest (0 + innerTag)
          rw [natListGetAtSliceLocal rest 0 count innerTag (Nat.lt_of_succ_lt_succ tagBelow)]
  | headWire :: rest, position + 1, count + 1, tag, tagBelow => by
      show natListGetAt (natListSliceAt rest position (count + 1)) tag
        = natListGetAt (headWire :: rest) (position + 1 + tag)
      rw [natListGetAtSliceLocal rest position (count + 1) tag tagBelow, Nat.succ_add]
      rfl

/-- `(a + base == b + base) = (a == b)` on `Nat`, propext-free (induction on `base`; the `succ` step cases on
`Nat.decEq` — core `Nat.add_right_cancel` leaks propext). -/
private theorem natAddBeqCancelRightLocal (a b : Nat) : (base : Nat) → ((a + base == b + base) = (a == b))
  | 0 => rfl
  | base + 1 => by
      have inner := natAddBeqCancelRightLocal a b base
      show (a + base + 1 == b + base + 1) = (a == b)
      rw [show ((a + base + 1 == b + base + 1) = (a + base == b + base)) from by
          cases Nat.decEq (a + base) (b + base) with
          | isTrue areEqual => rw [areEqual]; exact (decide_eq_true rfl).trans (decide_eq_true rfl).symm
          | isFalse notEqual =>
              exact (decide_eq_false (fun succEq => notEqual (Nat.succ.inj succEq))).trans
                (decide_eq_false notEqual).symm]
      exact inner

/-! ## The node correspondence between two boundary-view-agreeing states -/

/-- ★ **Corresponding nodes of two states agreeing on the boundary view.**  Either a boundary read at the SAME
in-range index in both states, or a fresh leg at the SAME offset above each state's own `nextFresh`.  These are the
only nodes the generic `stepWiring` arc fold reads (input tags decode to in-window boundary reads, output tags to
fresh legs) and the only nodes the post-step boundary view queries. -/
inductive StepNodeCorr (bottomCount : Nat) (stateS stateT : WireState) : Nat → Nat → Prop where
  /-- A boundary read at the same in-range index. -/
  | boundary (index : Nat) (inRange : index < bottomCount + stateS.openWires.length) :
      StepNodeCorr bottomCount stateS stateT
        (natListGetAt (matchingBoundaryNodes bottomCount stateS) index)
        (natListGetAt (matchingBoundaryNodes bottomCount stateT) index)
  /-- A fresh leg at the same offset above each state's fresh counter. -/
  | fresh (offset : Nat) :
      StepNodeCorr bottomCount stateS stateT (offset + stateS.nextFresh) (offset + stateT.nextFresh)

/-- ★ **The base same-component fact.**  For two corresponding node pairs, the same-component booleans at the two
INITIAL link tables agree: boundary/boundary by the boundary view, the mixed boundary/fresh zones are `false` on
both sides (a boundary read's root is below the fresh counter, a fresh leg is its own root above it), and fresh/fresh
is the offset equality on both sides. -/
theorem stepNodeCorr_baseSameComp (bottomCount : Nat) (stateS stateT : WireState)
    (conditionsS : MatchingSwapStateConditions bottomCount stateS)
    (conditionsT : MatchingSwapStateConditions bottomCount stateT)
    (viewAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + stateS.openWires.length →
        secondIndex < bottomCount + stateS.openWires.length →
        matchingSameComponent bottomCount stateS firstIndex secondIndex
          = matchingSameComponent bottomCount stateT firstIndex secondIndex)
    (firstNodeS firstNodeT secondNodeS secondNodeT : Nat)
    (firstCorr : StepNodeCorr bottomCount stateS stateT firstNodeS firstNodeT)
    (secondCorr : StepNodeCorr bottomCount stateS stateT secondNodeS secondNodeT) :
    isSameComponent stateS.links firstNodeS secondNodeS
      = isSameComponent stateT.links firstNodeT secondNodeT := by
  cases firstCorr with
  | boundary firstIndex firstInRange =>
      cases secondCorr with
      | boundary secondIndex secondInRange =>
          exact viewAgrees firstIndex secondIndex firstInRange secondInRange
      | fresh secondOffset =>
          rw [isSameComponent_boundaryRead_fresh_eq_false bottomCount stateS conditionsS firstIndex
              (secondOffset + stateS.nextFresh) (Nat.le_add_left stateS.nextFresh secondOffset),
            isSameComponent_boundaryRead_fresh_eq_false bottomCount stateT conditionsT firstIndex
              (secondOffset + stateT.nextFresh) (Nat.le_add_left stateT.nextFresh secondOffset)]
  | fresh firstOffset =>
      cases secondCorr with
      | boundary secondIndex secondInRange =>
          rw [isSameComponent_fresh_boundaryRead_eq_false bottomCount stateS conditionsS secondIndex
              (firstOffset + stateS.nextFresh) (Nat.le_add_left stateS.nextFresh firstOffset),
            isSameComponent_fresh_boundaryRead_eq_false bottomCount stateT conditionsT secondIndex
              (firstOffset + stateT.nextFresh) (Nat.le_add_left stateT.nextFresh firstOffset)]
      | fresh secondOffset =>
          show (unionFindRootOf stateS.links (firstOffset + stateS.nextFresh)
              == unionFindRootOf stateS.links (secondOffset + stateS.nextFresh))
            = (unionFindRootOf stateT.links (firstOffset + stateT.nextFresh)
              == unionFindRootOf stateT.links (secondOffset + stateT.nextFresh))
          rw [unionFindRootOf_eq_self_ofFresh stateS.nextFresh stateS.links
              (fun edge edgeIn => (conditionsS.fresh.2 edge edgeIn).1)
              (firstOffset + stateS.nextFresh) (Nat.le_add_left stateS.nextFresh firstOffset),
            unionFindRootOf_eq_self_ofFresh stateS.nextFresh stateS.links
              (fun edge edgeIn => (conditionsS.fresh.2 edge edgeIn).1)
              (secondOffset + stateS.nextFresh) (Nat.le_add_left stateS.nextFresh secondOffset),
            unionFindRootOf_eq_self_ofFresh stateT.nextFresh stateT.links
              (fun edge edgeIn => (conditionsT.fresh.2 edge edgeIn).1)
              (firstOffset + stateT.nextFresh) (Nat.le_add_left stateT.nextFresh firstOffset),
            unionFindRootOf_eq_self_ofFresh stateT.nextFresh stateT.links
              (fun edge edgeIn => (conditionsT.fresh.2 edge edgeIn).1)
              (secondOffset + stateT.nextFresh) (Nat.le_add_left stateT.nextFresh secondOffset),
            natAddBeqCancelRightLocal firstOffset secondOffset stateS.nextFresh,
            natAddBeqCancelRightLocal firstOffset secondOffset stateT.nextFresh]

/-! ## The generic arc fold preserves the correspondence view -/

/-- The invariant carried through the arc fold: corresponding node pairs have equal same-component booleans on the
two fold-links tables. -/
def StepFoldViewInvariant (bottomCount : Nat) (stateS stateT : WireState)
    (linksS linksT : List (Nat × Nat)) : Prop :=
  ∀ firstNodeS firstNodeT secondNodeS secondNodeT,
    StepNodeCorr bottomCount stateS stateT firstNodeS firstNodeT →
    StepNodeCorr bottomCount stateS stateT secondNodeS secondNodeT →
    isSameComponent linksS firstNodeS secondNodeS = isSameComponent linksT firstNodeT secondNodeT

/-- ★ **The generic arc fold preserves the correspondence view.**  Given that decoding each in-range endpoint tag
yields a corresponding node pair, the same-component-of-corresponding-pairs invariant survives the whole
`stepWiringArcs` fold over the two states: the loop-vs-join branch test agrees by the invariant (both endpoints
corresponding), and each join step's post-join view is the flat-disjunction boolean of PRE-join views of
corresponding pairs (`isSameComponent_unionFindJoin`), all of which agree by the incoming invariant. -/
theorem stepWiringArcs_viewInvariant (bottomCount : Nat) (stateS stateT : WireState)
    (inputNodesS outputNodesS inputNodesT outputNodesT : List Nat) (inputCount portBound : Nat)
    (endpointCorr : ∀ tag, tag < portBound →
      StepNodeCorr bottomCount stateS stateT
        (wiringEndpointNode inputNodesS outputNodesS inputCount tag)
        (wiringEndpointNode inputNodesT outputNodesT inputCount tag)) :
    (arcs : List (Nat × Nat)) → (loopsS loopsT : Nat) → (linksS linksT : List (Nat × Nat)) →
    isUnionFindForest linksS → isUnionFindForest linksT →
    (∀ arc ∈ arcs, arc.1 < portBound ∧ arc.2 < portBound) →
    StepFoldViewInvariant bottomCount stateS stateT linksS linksT →
    StepFoldViewInvariant bottomCount stateS stateT
      (stepWiringArcs inputNodesS outputNodesS inputCount arcs loopsS linksS).fst
      (stepWiringArcs inputNodesT outputNodesT inputCount arcs loopsT linksT).fst
  | [], _, _, _, _, _, _, _, invariant => invariant
  | (firstTag, secondTag) :: rest, loopsS, loopsT, linksS, linksT, forestS, forestT, tagsInRange,
      invariant => by
    have headTags := tagsInRange (firstTag, secondTag) (List.Mem.head rest)
    have restTags : ∀ arc ∈ rest, arc.1 < portBound ∧ arc.2 < portBound :=
      fun arc arcMem => tagsInRange arc (List.Mem.tail (firstTag, secondTag) arcMem)
    have firstCorr := endpointCorr firstTag headTags.1
    have secondCorr := endpointCorr secondTag headTags.2
    have testEq :
        isSameComponent linksS (wiringEndpointNode inputNodesS outputNodesS inputCount firstTag)
            (wiringEndpointNode inputNodesS outputNodesS inputCount secondTag)
          = isSameComponent linksT (wiringEndpointNode inputNodesT outputNodesT inputCount firstTag)
            (wiringEndpointNode inputNodesT outputNodesT inputCount secondTag) :=
      invariant _ _ _ _ firstCorr secondCorr
    show StepFoldViewInvariant bottomCount stateS stateT
        (stepWiringArcs inputNodesS outputNodesS inputCount ((firstTag, secondTag) :: rest) loopsS linksS).fst
        (stepWiringArcs inputNodesT outputNodesT inputCount ((firstTag, secondTag) :: rest) loopsT linksT).fst
    dsimp only [stepWiringArcs]
    cases hbranch :
        isSameComponent linksS (wiringEndpointNode inputNodesS outputNodesS inputCount firstTag)
          (wiringEndpointNode inputNodesS outputNodesS inputCount secondTag) with
    | true =>
        rw [testEq] at hbranch
        rw [hbranch]
        exact stepWiringArcs_viewInvariant bottomCount stateS stateT inputNodesS outputNodesS
          inputNodesT outputNodesT inputCount portBound endpointCorr rest (loopsS + 1) (loopsT + 1)
          linksS linksT forestS forestT restTags invariant
    | false =>
        rw [testEq] at hbranch
        rw [hbranch]
        refine stepWiringArcs_viewInvariant bottomCount stateS stateT inputNodesS outputNodesS
          inputNodesT outputNodesT inputCount portBound endpointCorr rest loopsS loopsT
          (unionFindJoin linksS (wiringEndpointNode inputNodesS outputNodesS inputCount firstTag)
            (wiringEndpointNode inputNodesS outputNodesS inputCount secondTag))
          (unionFindJoin linksT (wiringEndpointNode inputNodesT outputNodesT inputCount firstTag)
            (wiringEndpointNode inputNodesT outputNodesT inputCount secondTag))
          (isUnionFindForest_unionFindJoin linksS _ _ forestS)
          (isUnionFindForest_unionFindJoin linksT _ _ forestT) restTags ?_
        intro probeFirstS probeFirstT probeSecondS probeSecondT probeFirstCorr probeSecondCorr
        rw [isSameComponent_unionFindJoin linksS forestS _ _ probeFirstS probeSecondS,
          isSameComponent_unionFindJoin linksT forestT _ _ probeFirstT probeSecondT,
          invariant _ _ _ _ probeFirstCorr probeSecondCorr,
          invariant _ _ _ _ firstCorr probeFirstCorr,
          invariant _ _ _ _ secondCorr probeSecondCorr,
          invariant _ _ _ _ firstCorr probeSecondCorr,
          invariant _ _ _ _ probeFirstCorr secondCorr]

/-! ## The generic four-zone post-step boundary-read classifier -/

/-- The below-window post-step open-wire read is the untouched original read. -/
private theorem stepWiringOpenRead_below (state : WireState) (position rightLen wireOffset : Nat)
    (desc : WiringDesc) (fits : state.openWires.length = position + desc.inputCount + rightLen)
    (below : wireOffset < position) :
    natListGetAt (stepWiring state position desc).openWires wireOffset
      = natListGetAt state.openWires wireOffset := by
  have removeLen : (natListRemoveManyAt state.openWires position desc.inputCount).length = position + rightLen :=
    natListRemoveManyAt_length_fits state.openWires position desc.inputCount rightLen fits
  show natListGetAt (natListInsertAt (natListRemoveManyAt state.openWires position desc.inputCount) position
      ((List.range desc.outputCount).map (· + state.nextFresh))) wireOffset
    = natListGetAt state.openWires wireOffset
  rw [natListGetAt_natListInsertAt_below (natListRemoveManyAt state.openWires position desc.inputCount)
      position ((List.range desc.outputCount).map (· + state.nextFresh)) wireOffset below
      (by rw [removeLen]; exact Nat.lt_of_lt_of_le below (Nat.le_add_right position rightLen)),
    natListGetAt_removeManyAt_below state.openWires position desc.inputCount wireOffset below]

/-- The in-fresh-block post-step open-wire read is the fresh leg at that offset. -/
private theorem stepWiringOpenRead_fresh (state : WireState) (position rightLen offset : Nat)
    (desc : WiringDesc) (fits : state.openWires.length = position + desc.inputCount + rightLen)
    (offsetLt : offset < desc.outputCount) :
    natListGetAt (stepWiring state position desc).openWires (position + offset)
      = offset + state.nextFresh := by
  have removeLen : (natListRemoveManyAt state.openWires position desc.inputCount).length = position + rightLen :=
    natListRemoveManyAt_length_fits state.openWires position desc.inputCount rightLen fits
  have blockLen : ((List.range desc.outputCount).map (· + state.nextFresh)).length = desc.outputCount := by
    rw [mapLength, rangeLengthLocalCopy]
  show natListGetAt (natListInsertAt (natListRemoveManyAt state.openWires position desc.inputCount) position
      ((List.range desc.outputCount).map (· + state.nextFresh))) (position + offset)
    = offset + state.nextFresh
  rw [natListGetAt_natListInsertAt_inside (natListRemoveManyAt state.openWires position desc.inputCount)
      position ((List.range desc.outputCount).map (· + state.nextFresh)) offset
      (by rw [blockLen]; exact offsetLt) (by rw [removeLen]; exact Nat.le_add_right position rightLen),
    natListGetAtRangeMapAddLocal state.nextFresh desc.outputCount offset offsetLt]

/-- The past-block post-step open-wire read is the original read shifted by the net width `outputCount - inputCount`. -/
private theorem stepWiringOpenRead_past (state : WireState) (position rightLen offset : Nat)
    (desc : WiringDesc) (fits : state.openWires.length = position + desc.inputCount + rightLen)
    (offsetLt : offset < rightLen) :
    natListGetAt (stepWiring state position desc).openWires (position + desc.outputCount + offset)
      = natListGetAt state.openWires (position + desc.inputCount + offset) := by
  have removeLen : (natListRemoveManyAt state.openWires position desc.inputCount).length = position + rightLen :=
    natListRemoveManyAt_length_fits state.openWires position desc.inputCount rightLen fits
  have blockLen : ((List.range desc.outputCount).map (· + state.nextFresh)).length = desc.outputCount := by
    rw [mapLength, rangeLengthLocalCopy]
  show natListGetAt (natListInsertAt (natListRemoveManyAt state.openWires position desc.inputCount) position
      ((List.range desc.outputCount).map (· + state.nextFresh))) (position + desc.outputCount + offset)
    = natListGetAt state.openWires (position + desc.inputCount + offset)
  rw [Nat.add_right_comm position desc.outputCount offset,
    show position + offset + desc.outputCount
        = position + offset + ((List.range desc.outputCount).map (· + state.nextFresh)).length from by rw [blockLen],
    natListGetAt_natListInsertAt_pastBlock (natListRemoveManyAt state.openWires position desc.inputCount)
      position ((List.range desc.outputCount).map (· + state.nextFresh)) offset
      (by rw [removeLen]; exact Nat.le_add_right position rightLen),
    natListGetAt_removeManyAt_atOrAbove state.openWires position desc.inputCount (position + offset)
      (Nat.le_add_right position offset) ⟨rightLen, fits⟩
      (by rw [removeLen]; exact Nat.add_lt_add_left offsetLt position),
    Nat.add_right_comm position offset desc.inputCount]

/-- ★ **The generic four-zone post-step boundary classifier.**  Every in-range post-step boundary read is a
`StepNodeCorr` descriptor: below the bottom count it is the index itself; below the window it is the untouched
original read at the same index; inside the fresh block it is a fresh leg at the same offset; past the block it is
the original read shifted by the net width — every case a corresponding pair in both states. -/
theorem stepWiring_boundaryRead_stepNodeCorr (bottomCount : Nat) (stateS stateT : WireState)
    (position rightLen : Nat) (desc : WiringDesc)
    (fitsS : stateS.openWires.length = position + desc.inputCount + rightLen)
    (fitsT : stateT.openWires.length = position + desc.inputCount + rightLen)
    (index : Nat)
    (indexInRange : index < bottomCount + (stepWiring stateS position desc).openWires.length) :
    StepNodeCorr bottomCount stateS stateT
      (natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateS position desc)) index)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateT position desc)) index) := by
  have stepLenS : (stepWiring stateS position desc).openWires.length = position + desc.outputCount + rightLen :=
    stepWiring_openWires_length_fits stateS position rightLen desc fitsS
  cases Nat.lt_or_ge index bottomCount with
  | inl belowBottom =>
      have readSEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateS position desc)) index
          = natListGetAt (matchingBoundaryNodes bottomCount stateS) index := by
        rw [matchingBoundaryNodes_getAt_bottom bottomCount (stepWiring stateS position desc) index belowBottom,
          matchingBoundaryNodes_getAt_bottom bottomCount stateS index belowBottom]
      have readTEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateT position desc)) index
          = natListGetAt (matchingBoundaryNodes bottomCount stateT) index := by
        rw [matchingBoundaryNodes_getAt_bottom bottomCount (stepWiring stateT position desc) index belowBottom,
          matchingBoundaryNodes_getAt_bottom bottomCount stateT index belowBottom]
      rw [readSEq, readTEq]
      exact StepNodeCorr.boundary index
        (Nat.lt_of_lt_of_le belowBottom (Nat.le_add_right bottomCount stateS.openWires.length))
  | inr atLeastBottom =>
      obtain ⟨wireOffset, wireOffsetEq⟩ := Nat.le.dest atLeastBottom
      subst wireOffsetEq
      have wireOffsetLt : wireOffset < (stepWiring stateS position desc).openWires.length :=
        Nat.lt_of_add_lt_add_left indexInRange
      cases Nat.lt_or_ge wireOffset position with
      | inl belowWindow =>
          have wireLtLen : wireOffset < stateS.openWires.length := by
            rw [fitsS]
            exact Nat.lt_of_lt_of_le belowWindow
              (Nat.le_trans (Nat.le_add_right position desc.inputCount)
                (Nat.le_add_right (position + desc.inputCount) rightLen))
          have readSEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateS position desc))
                (bottomCount + wireOffset)
              = natListGetAt (matchingBoundaryNodes bottomCount stateS) (bottomCount + wireOffset) := by
            rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring stateS position desc) wireOffset,
              matchingBoundaryNodes_getAt_top bottomCount stateS wireOffset,
              stepWiringOpenRead_below stateS position rightLen wireOffset desc fitsS belowWindow]
          have readTEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateT position desc))
                (bottomCount + wireOffset)
              = natListGetAt (matchingBoundaryNodes bottomCount stateT) (bottomCount + wireOffset) := by
            rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring stateT position desc) wireOffset,
              matchingBoundaryNodes_getAt_top bottomCount stateT wireOffset,
              stepWiringOpenRead_below stateT position rightLen wireOffset desc fitsT belowWindow]
          rw [readSEq, readTEq]
          exact StepNodeCorr.boundary (bottomCount + wireOffset)
            (Nat.add_lt_add_left wireLtLen bottomCount)
      | inr atLeastWindow =>
          obtain ⟨blockOffset, blockOffsetEq⟩ := Nat.le.dest atLeastWindow
          subst blockOffsetEq
          cases Nat.lt_or_ge blockOffset desc.outputCount with
          | inl inFreshBlock =>
              have readSEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateS position desc))
                    (bottomCount + (position + blockOffset))
                  = blockOffset + stateS.nextFresh := by
                rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring stateS position desc)
                    (position + blockOffset),
                  stepWiringOpenRead_fresh stateS position rightLen blockOffset desc fitsS inFreshBlock]
              have readTEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateT position desc))
                    (bottomCount + (position + blockOffset))
                  = blockOffset + stateT.nextFresh := by
                rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring stateT position desc)
                    (position + blockOffset),
                  stepWiringOpenRead_fresh stateT position rightLen blockOffset desc fitsT inFreshBlock]
              rw [readSEq, readTEq]
              exact StepNodeCorr.fresh blockOffset
          | inr pastBlock =>
              obtain ⟨pastOffset, pastOffsetEq⟩ := Nat.le.dest pastBlock
              subst pastOffsetEq
              have pastOffsetLt : pastOffset < rightLen := by
                have expanded : position + (desc.outputCount + pastOffset)
                    < position + desc.outputCount + rightLen := by
                  rw [← stepLenS]; exact wireOffsetLt
                rw [← Nat.add_assoc position desc.outputCount pastOffset] at expanded
                exact Nat.lt_of_add_lt_add_left expanded
              have reassoc : position + (desc.outputCount + pastOffset) = position + desc.outputCount + pastOffset :=
                (Nat.add_assoc position desc.outputCount pastOffset).symm
              have idxBound : bottomCount + (position + desc.inputCount + pastOffset)
                  < bottomCount + stateS.openWires.length := by
                rw [fitsS]
                exact Nat.add_lt_add_left (Nat.add_lt_add_left pastOffsetLt (position + desc.inputCount)) bottomCount
              have readSEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateS position desc))
                    (bottomCount + (position + (desc.outputCount + pastOffset)))
                  = natListGetAt (matchingBoundaryNodes bottomCount stateS)
                    (bottomCount + (position + desc.inputCount + pastOffset)) := by
                rw [matchingBoundaryNodes_getAt_top bottomCount stateS (position + desc.inputCount + pastOffset),
                  matchingBoundaryNodes_getAt_top bottomCount (stepWiring stateS position desc)
                    (position + (desc.outputCount + pastOffset)),
                  reassoc, stepWiringOpenRead_past stateS position rightLen pastOffset desc fitsS pastOffsetLt]
              have readTEq : natListGetAt (matchingBoundaryNodes bottomCount (stepWiring stateT position desc))
                    (bottomCount + (position + (desc.outputCount + pastOffset)))
                  = natListGetAt (matchingBoundaryNodes bottomCount stateT)
                    (bottomCount + (position + desc.inputCount + pastOffset)) := by
                rw [matchingBoundaryNodes_getAt_top bottomCount stateT (position + desc.inputCount + pastOffset),
                  matchingBoundaryNodes_getAt_top bottomCount (stepWiring stateT position desc)
                    (position + (desc.outputCount + pastOffset)),
                  reassoc, stepWiringOpenRead_past stateT position rightLen pastOffset desc fitsT pastOffsetLt]
              rw [readSEq, readTEq]
              exact StepNodeCorr.boundary (bottomCount + (position + desc.inputCount + pastOffset)) idxBound

/-! ## The single-atom forward view congruence -/

/-- `(n + m) - m = n`, structural on `m` (Init's `Nat.add_sub_cancel` leaks propext). -/
private theorem addSubCancelRightLocalCopy : (n m : Nat) → (n + m) - m = n
  | _, 0 => rfl
  | value, count + 1 => by
      show (value + (count + 1)) - (count + 1) = value
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact addSubCancelRightLocalCopy value count

/-- One `stepWiring` step preserves the reachable-state conditions bundle. -/
private theorem matchingSwapStateConditions_stepWiring (bottomCount : Nat) (state : WireState)
    (position : Nat) (desc : WiringDesc) (conditions : MatchingSwapStateConditions bottomCount state) :
    MatchingSwapStateConditions bottomCount (stepWiring state position desc) where
  bottomLe := by
    rw [stepWiring_nextFresh]
    exact Nat.le_trans conditions.bottomLe (Nat.le_add_right state.nextFresh desc.outputCount)
  forest := stepWiring_links_isUnionFindForest state position desc conditions.forest
  nfPos := by
    rw [stepWiring_nextFresh]
    exact Nat.lt_of_lt_of_le conditions.nfPos (Nat.le_add_right state.nextFresh desc.outputCount)
  fresh := wiringDescStateFresh_stepWiring state position desc conditions.fresh conditions.nfPos

/-- Convert the Brauer reachable-state conditions to the swap-conditions bundle (same fields). -/
private theorem matchingSwapStateConditions_ofBrauer (bottomCount : Nat) (state : WireState)
    (conditions : BrauerStateConditions bottomCount state) :
    MatchingSwapStateConditions bottomCount state where
  bottomLe := conditions.bottomLe
  forest := conditions.forest
  nfPos := conditions.nfPos
  fresh := conditions.fresh

/-- ★ **Each in-range decoded arc endpoint is a corresponding node pair.**  An input tag reads the sliced open
wires — a boundary read at the same in-window index in both states; an output tag reads the fresh block — a fresh
leg at the same offset in both states. -/
theorem stepWiring_endpointCorr (bottomCount : Nat) (stateS stateT : WireState)
    (position rightLen : Nat) (desc : WiringDesc)
    (fitsS : stateS.openWires.length = position + desc.inputCount + rightLen)
    (tag : Nat) (tagInRange : tag < desc.inputCount + desc.outputCount) :
    StepNodeCorr bottomCount stateS stateT
      (wiringEndpointNode (natListSliceAt stateS.openWires position desc.inputCount)
        ((List.range desc.outputCount).map (· + stateS.nextFresh)) desc.inputCount tag)
      (wiringEndpointNode (natListSliceAt stateT.openWires position desc.inputCount)
        ((List.range desc.outputCount).map (· + stateT.nextFresh)) desc.inputCount tag) := by
  by_cases tagBelow : tag < desc.inputCount
  · have windowBound : position + tag < stateS.openWires.length := by
        rw [fitsS]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left tagBelow position)
          (Nat.le_add_right (position + desc.inputCount) rightLen)
    have decodeS : wiringEndpointNode (natListSliceAt stateS.openWires position desc.inputCount)
          ((List.range desc.outputCount).map (· + stateS.nextFresh)) desc.inputCount tag
        = natListGetAt (matchingBoundaryNodes bottomCount stateS) (bottomCount + (position + tag)) := by
      rw [matchingBoundaryNodes_getAt_top bottomCount stateS (position + tag)]
      show (if tag < desc.inputCount then natListGetAt (natListSliceAt stateS.openWires position desc.inputCount) tag
          else natListGetAt ((List.range desc.outputCount).map (· + stateS.nextFresh)) (tag - desc.inputCount))
        = natListGetAt stateS.openWires (position + tag)
      rw [if_pos tagBelow, natListGetAtSliceLocal stateS.openWires position desc.inputCount tag tagBelow]
    have decodeT : wiringEndpointNode (natListSliceAt stateT.openWires position desc.inputCount)
          ((List.range desc.outputCount).map (· + stateT.nextFresh)) desc.inputCount tag
        = natListGetAt (matchingBoundaryNodes bottomCount stateT) (bottomCount + (position + tag)) := by
      rw [matchingBoundaryNodes_getAt_top bottomCount stateT (position + tag)]
      show (if tag < desc.inputCount then natListGetAt (natListSliceAt stateT.openWires position desc.inputCount) tag
          else natListGetAt ((List.range desc.outputCount).map (· + stateT.nextFresh)) (tag - desc.inputCount))
        = natListGetAt stateT.openWires (position + tag)
      rw [if_pos tagBelow, natListGetAtSliceLocal stateT.openWires position desc.inputCount tag tagBelow]
    rw [decodeS, decodeT]
    exact StepNodeCorr.boundary (bottomCount + (position + tag)) (Nat.add_lt_add_left windowBound bottomCount)
  · have inputLe : desc.inputCount ≤ tag := Nat.le_of_not_lt tagBelow
    obtain ⟨offset, tagEq⟩ := Nat.le.dest inputLe
    have offsetLt : offset < desc.outputCount := by
      rw [← tagEq] at tagInRange
      exact Nat.lt_of_add_lt_add_left tagInRange
    have subEq : tag - desc.inputCount = offset := by
      rw [← tagEq, Nat.add_comm desc.inputCount offset, addSubCancelRightLocalCopy offset desc.inputCount]
    have decodeS : wiringEndpointNode (natListSliceAt stateS.openWires position desc.inputCount)
          ((List.range desc.outputCount).map (· + stateS.nextFresh)) desc.inputCount tag
        = offset + stateS.nextFresh := by
      show (if tag < desc.inputCount then natListGetAt (natListSliceAt stateS.openWires position desc.inputCount) tag
          else natListGetAt ((List.range desc.outputCount).map (· + stateS.nextFresh)) (tag - desc.inputCount))
        = offset + stateS.nextFresh
      rw [if_neg tagBelow, subEq, natListGetAtRangeMapAddLocal stateS.nextFresh desc.outputCount offset offsetLt]
    have decodeT : wiringEndpointNode (natListSliceAt stateT.openWires position desc.inputCount)
          ((List.range desc.outputCount).map (· + stateT.nextFresh)) desc.inputCount tag
        = offset + stateT.nextFresh := by
      show (if tag < desc.inputCount then natListGetAt (natListSliceAt stateT.openWires position desc.inputCount) tag
          else natListGetAt ((List.range desc.outputCount).map (· + stateT.nextFresh)) (tag - desc.inputCount))
        = offset + stateT.nextFresh
      rw [if_neg tagBelow, subEq, natListGetAtRangeMapAddLocal stateT.nextFresh desc.outputCount offset offsetLt]
    rw [decodeS, decodeT]
    exact StepNodeCorr.fresh offset

/-- ★ **The FORWARD single-atom view congruence.**  Two conditioned states agreeing on the boundary partition view
keep agreeing after firing the SAME `WiringDesc` at the SAME position: the arc fold's post-step links preserve the
`StepNodeCorr` view invariant (`stepWiringArcs_viewInvariant` from the base view + the fresh-separation kit), and
every post-step boundary read is a `StepNodeCorr` descriptor (`stepWiring_boundaryRead_stepNodeCorr`).  The generic
generalization of `matchingViewAgrees_stepCap` / `matchingViewAgrees_stepCup` to any generator. -/
theorem stepWiring_viewCongruence (bottomCount : Nat) (stateS stateT : WireState)
    (position rightLen : Nat) (desc : WiringDesc) (tagsInRange : WiringDescTagsInRange desc)
    (fitsS : stateS.openWires.length = position + desc.inputCount + rightLen)
    (fitsT : stateT.openWires.length = position + desc.inputCount + rightLen)
    (conditionsS : MatchingSwapStateConditions bottomCount stateS)
    (conditionsT : MatchingSwapStateConditions bottomCount stateT)
    (viewAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + stateS.openWires.length →
        secondIndex < bottomCount + stateS.openWires.length →
        matchingSameComponent bottomCount stateS firstIndex secondIndex
          = matchingSameComponent bottomCount stateT firstIndex secondIndex)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < bottomCount + (stepWiring stateS position desc).openWires.length)
    (secondInRange : secondIndex < bottomCount + (stepWiring stateS position desc).openWires.length) :
    matchingSameComponent bottomCount (stepWiring stateS position desc) firstIndex secondIndex
      = matchingSameComponent bottomCount (stepWiring stateT position desc) firstIndex secondIndex := by
  have baseInv : StepFoldViewInvariant bottomCount stateS stateT stateS.links stateT.links :=
    fun firstNodeS firstNodeT secondNodeS secondNodeT firstCorr secondCorr =>
      stepNodeCorr_baseSameComp bottomCount stateS stateT conditionsS conditionsT viewAgrees
        firstNodeS firstNodeT secondNodeS secondNodeT firstCorr secondCorr
  have foldInv := stepWiringArcs_viewInvariant bottomCount stateS stateT
    (natListSliceAt stateS.openWires position desc.inputCount)
    ((List.range desc.outputCount).map (· + stateS.nextFresh))
    (natListSliceAt stateT.openWires position desc.inputCount)
    ((List.range desc.outputCount).map (· + stateT.nextFresh))
    desc.inputCount (desc.inputCount + desc.outputCount)
    (fun tag tagLt => stepWiring_endpointCorr bottomCount stateS stateT position rightLen desc fitsS tag tagLt)
    desc.arcs 0 0 stateS.links stateT.links conditionsS.forest conditionsT.forest tagsInRange baseInv
  have firstCorr := stepWiring_boundaryRead_stepNodeCorr bottomCount stateS stateT position rightLen desc
    fitsS fitsT firstIndex firstInRange
  have secondCorr := stepWiring_boundaryRead_stepNodeCorr bottomCount stateS stateT position rightLen desc
    fitsS fitsT secondIndex secondInRange
  exact foldInv _ _ _ _ firstCorr secondCorr

/-! ## The suffix fold: the forward congruence over a whole in-range suffix -/

/-- ★ **The FORWARD view congruence folds over an in-range suffix.**  Two conditioned states agreeing on the
boundary partition view keep agreeing (length + view) after processing the SAME in-range Brauer suffix — the
uniform `stepWiring` view-functoriality, structural on the suffix, threading the conditions
(`matchingSwapStateConditions_stepWiring`), the length equality, and the view via `stepWiring_viewCongruence`. -/
theorem processBrauer_viewCongruence (bottomCount : Nat) :
    (atoms : List BrauerAtom) → (stateS stateT : WireState) →
    MatchingSwapStateConditions bottomCount stateS → MatchingSwapStateConditions bottomCount stateT →
    BrauerWordInRange stateS.openWires.length atoms →
    stateT.openWires.length = stateS.openWires.length →
    (∀ firstIndex secondIndex,
        firstIndex < bottomCount + stateS.openWires.length →
        secondIndex < bottomCount + stateS.openWires.length →
        matchingSameComponent bottomCount stateS firstIndex secondIndex
          = matchingSameComponent bottomCount stateT firstIndex secondIndex) →
    (processBrauer stateT atoms).openWires.length = (processBrauer stateS atoms).openWires.length
      ∧ (∀ firstIndex secondIndex,
          firstIndex < bottomCount + (processBrauer stateS atoms).openWires.length →
          secondIndex < bottomCount + (processBrauer stateS atoms).openWires.length →
          matchingSameComponent bottomCount (processBrauer stateS atoms) firstIndex secondIndex
            = matchingSameComponent bottomCount (processBrauer stateT atoms) firstIndex secondIndex)
  | [], stateS, stateT, _, _, _, lengthEq, viewAgrees => ⟨lengthEq, viewAgrees⟩
  | atom :: rest, stateS, stateT, conditionsS, conditionsT, inRange, lengthEq, viewAgrees => by
      obtain ⟨rightLen, fitsS, tagsInRange, tailInRange⟩ := brauerWordInRange_tail inRange
      have fitsT : stateT.openWires.length = atom.position + atom.wiring.inputCount + rightLen :=
        lengthEq.trans fitsS
      have stepLenS : (stepWiring stateS atom.position atom.wiring).openWires.length
          = atom.position + atom.wiring.outputCount + rightLen :=
        stepWiring_openWires_length_fits stateS atom.position rightLen atom.wiring fitsS
      have stepLenT : (stepWiring stateT atom.position atom.wiring).openWires.length
          = atom.position + atom.wiring.outputCount + rightLen :=
        stepWiring_openWires_length_fits stateT atom.position rightLen atom.wiring fitsT
      have stepLengthEq : (stepWiring stateT atom.position atom.wiring).openWires.length
          = (stepWiring stateS atom.position atom.wiring).openWires.length := stepLenT.trans stepLenS.symm
      have stepViewAgrees : ∀ firstIndex secondIndex,
          firstIndex < bottomCount + (stepWiring stateS atom.position atom.wiring).openWires.length →
          secondIndex < bottomCount + (stepWiring stateS atom.position atom.wiring).openWires.length →
          matchingSameComponent bottomCount (stepWiring stateS atom.position atom.wiring) firstIndex secondIndex
            = matchingSameComponent bottomCount (stepWiring stateT atom.position atom.wiring)
              firstIndex secondIndex :=
        fun firstIndex secondIndex firstBound secondBound =>
          stepWiring_viewCongruence bottomCount stateS stateT atom.position rightLen atom.wiring tagsInRange
            fitsS fitsT conditionsS conditionsT viewAgrees firstIndex secondIndex firstBound secondBound
      have tailInRangeS : BrauerWordInRange (stepWiring stateS atom.position atom.wiring).openWires.length rest := by
        rw [stepLenS]; exact tailInRange
      exact processBrauer_viewCongruence bottomCount rest
        (stepWiring stateS atom.position atom.wiring) (stepWiring stateT atom.position atom.wiring)
        (matchingSwapStateConditions_stepWiring bottomCount stateS atom.position atom.wiring conditionsS)
        (matchingSwapStateConditions_stepWiring bottomCount stateT atom.position atom.wiring conditionsT)
        tailInRangeS stepLengthEq stepViewAgrees

/-! ## Reconstruction — a `SpiderConv` derivation reaches boundary-view-equal seed states -/

/-- ★ **Convertible words reach boundary-view-equal seed states.**  From a `SpiderConv` derivation, the two
seed-processed states agree on open-wire length and the boundary `matchingSameComponent` view (loops-free, so the
special row `μδ = 1` is carried).  By induction: the equivalence closure by symmetry / transitivity of the view, the
thirteen rows by their decided seed views (`frobXSeedView_ordered`) + parallel length (`frobX_parallel`), the
interchange move by `matchingConnectivityViewSim_ofExtractEq` of the reachable-interchange extract equality, and the
whisker move directly by its premise (after `processBrauer_append`).  This is the loops-free strengthening of
`spiderConv_partitionSound` — the reconstruction leg the suffix congruence consumes. -/
theorem spiderConv_stateViewEq {bottomCount : Nat} {leftWord rightWord : List BrauerAtom}
    (conv : SpiderConv bottomCount leftWord rightWord) :
    (processBrauer (brauerSeed bottomCount) rightWord).openWires.length
        = (processBrauer (brauerSeed bottomCount) leftWord).openWires.length
      ∧ (∀ firstIndex secondIndex,
          firstIndex < bottomCount + (processBrauer (brauerSeed bottomCount) leftWord).openWires.length →
          secondIndex < bottomCount + (processBrauer (brauerSeed bottomCount) leftWord).openWires.length →
          matchingSameComponent bottomCount (processBrauer (brauerSeed bottomCount) leftWord) firstIndex secondIndex
            = matchingSameComponent bottomCount (processBrauer (brauerSeed bottomCount) rightWord)
              firstIndex secondIndex) := by
  induction conv with
  | refl _ _ => exact ⟨rfl, fun _ _ _ _ => rfl⟩
  | symm _ ih =>
      refine ⟨ih.1.symm, fun firstIndex secondIndex firstBound secondBound => ?_⟩
      exact (ih.2 firstIndex secondIndex (ih.1 ▸ firstBound) (ih.1 ▸ secondBound)).symm
  | trans _ _ ihLeft ihRight =>
      refine ⟨ihRight.1.trans ihLeft.1, fun firstIndex secondIndex firstBound secondBound => ?_⟩
      exact (ihLeft.2 firstIndex secondIndex firstBound secondBound).trans
        (ihRight.2 firstIndex secondIndex (ihLeft.1 ▸ firstBound) (ihLeft.1 ▸ secondBound))
  | frobAssoc => exact ⟨frobAssoc_parallel.symm, fun i j hi hj => frobAssocSeedView_ordered i hi j hj⟩
  | frobUnitLeft => exact ⟨frobUnitLeft_parallel.symm, fun i j hi hj => frobUnitLeftSeedView_ordered i hi j hj⟩
  | frobUnitRight => exact ⟨frobUnitRight_parallel.symm, fun i j hi hj => frobUnitRightSeedView_ordered i hi j hj⟩
  | frobCoassoc => exact ⟨frobCoassoc_parallel.symm, fun i j hi hj => frobCoassocSeedView_ordered i hi j hj⟩
  | frobCounitLeft => exact ⟨frobCounitLeft_parallel.symm, fun i j hi hj => frobCounitLeftSeedView_ordered i hi j hj⟩
  | frobCounitRight => exact ⟨frobCounitRight_parallel.symm, fun i j hi hj => frobCounitRightSeedView_ordered i hi j hj⟩
  | frobLeft => exact ⟨frobLeft_parallel.symm, fun i j hi hj => frobLeftSeedView_ordered i hi j hj⟩
  | frobRight => exact ⟨frobRight_parallel.symm, fun i j hi hj => frobRightSeedView_ordered i hi j hj⟩
  | frobCommMult => exact ⟨frobCommMult_parallel.symm, fun i j hi hj => frobCommMultSeedView_ordered i hi j hj⟩
  | frobCommComult => exact ⟨frobCommComult_parallel.symm, fun i j hi hj => frobCommComultSeedView_ordered i hi j hj⟩
  | frobCrossingInvolution =>
      exact ⟨frobCrossingInvolution_parallel.symm,
        fun i j hi hj => frobCrossingInvolutionSeedView_ordered i hi j hj⟩
  | frobYangBaxter => exact ⟨frobYangBaxter_parallel.symm, fun i j hi hj => frobYangBaxterSeedView_ordered i hi j hj⟩
  | frobSpecial => exact ⟨frobSpecial_parallel.symm, fun i j hi hj => frobSpecialSeedView_ordered i hi j hj⟩
  | interchange bottomCount prefixAtoms positionA positionB descA descB bottomPos disjoint windowB =>
      have brauerEq : extractDiagram bottomCount
            (processBrauer (brauerSeed bottomCount)
              (prefixAtoms ++ [⟨positionA, descA⟩,
                ⟨positionB - descA.inputCount + descA.outputCount, descB⟩]))
          = extractDiagram bottomCount
            (processBrauer (brauerSeed bottomCount)
              (prefixAtoms ++ [⟨positionB, descB⟩, ⟨positionA, descA⟩])) := by
        rw [processBrauer_append prefixAtoms (brauerSeed bottomCount)
              [⟨positionA, descA⟩, ⟨positionB - descA.inputCount + descA.outputCount, descB⟩],
          processBrauer_append prefixAtoms (brauerSeed bottomCount)
              [⟨positionB, descB⟩, ⟨positionA, descA⟩]]
        exact brauer_reachable_interchange bottomCount bottomPos prefixAtoms positionA positionB descA descB
          disjoint windowB
      have view := matchingConnectivityViewSim_ofExtractEq bottomCount
        (processBrauer (brauerSeed bottomCount)
          (prefixAtoms ++ [⟨positionA, descA⟩, ⟨positionB - descA.inputCount + descA.outputCount, descB⟩]))
        (processBrauer (brauerSeed bottomCount) (prefixAtoms ++ [⟨positionB, descB⟩, ⟨positionA, descA⟩]))
        brauerEq
      exact ⟨view.lengthEq.symm, fun firstIndex secondIndex firstBound secondBound =>
        view.viewAgrees firstIndex secondIndex (view.lengthEq ▸ firstBound) (view.lengthEq ▸ secondBound)⟩
  | whisker bottomCount prefixAtoms wordLeft wordRight lengthsAgree relationAgrees =>
      rw [processBrauer_append prefixAtoms (brauerSeed bottomCount) wordLeft,
        processBrauer_append prefixAtoms (brauerSeed bottomCount) wordRight]
      exact ⟨lengthsAgree.symm, relationAgrees⟩

/-! ## The uniform two-sided SUFFIX congruence -/

/-- ★ **The UNIFORM suffix congruence.**  If two words are `SpiderConv`-convertible over `bottomCount > 0` bottom
wires, then whiskering ANY in-range Brauer suffix on the right keeps them convertible.  The reconstruction
(`spiderConv_stateViewEq`) supplies the boundary view of the two seed states; the forward brick
(`processBrauer_viewCongruence`) transports it through the common suffix; the empty-prefix `whisker` re-packages it
as a `SpiderConv`.  Uniform over all in-range suffixes — no per-suffix semantic gate. -/
theorem spiderConv_suffixCongruence {bottomCount : Nat} {leftWord rightWord suffix : List BrauerAtom}
    (bottomPos : 0 < bottomCount) (conv : SpiderConv bottomCount leftWord rightWord)
    (suffixInRange :
      BrauerWordInRange (processBrauer (brauerSeed bottomCount) leftWord).openWires.length suffix) :
    SpiderConv bottomCount (leftWord ++ suffix) (rightWord ++ suffix) := by
  obtain ⟨viewLengthEq, viewAgrees⟩ := spiderConv_stateViewEq conv
  have condS := matchingSwapStateConditions_ofBrauer bottomCount
    (processBrauer (brauerSeed bottomCount) leftWord) (brauerReachable_conditions bottomCount bottomPos leftWord)
  have condT := matchingSwapStateConditions_ofBrauer bottomCount
    (processBrauer (brauerSeed bottomCount) rightWord) (brauerReachable_conditions bottomCount bottomPos rightWord)
  obtain ⟨foldLengthEq, foldViewAgrees⟩ := processBrauer_viewCongruence bottomCount suffix
    (processBrauer (brauerSeed bottomCount) leftWord) (processBrauer (brauerSeed bottomCount) rightWord)
    condS condT suffixInRange viewLengthEq viewAgrees
  rw [← processBrauer_append leftWord (brauerSeed bottomCount) suffix,
    ← processBrauer_append rightWord (brauerSeed bottomCount) suffix] at foldLengthEq foldViewAgrees
  exact SpiderConv.whisker bottomCount [] (leftWord ++ suffix) (rightWord ++ suffix)
    foldLengthEq.symm foldViewAgrees

/-- ★ **`SpiderConvTable` whiskered by an in-range suffix is a `SpiderConv`** — the table-level uniform suffix
congruence, routed through the r5 table→`SpiderConv` bridge then `spiderConv_suffixCongruence`. -/
theorem spiderConvTable_suffixCongruence {bottomCount : Nat} {leftWord rightWord suffix : List BrauerAtom}
    (bottomPos : 0 < bottomCount) (conv : SpiderConvTable bottomCount leftWord rightWord)
    (suffixInRange :
      BrauerWordInRange (processBrauer (brauerSeed bottomCount) leftWord).openWires.length suffix) :
    SpiderConv bottomCount (leftWord ++ suffix) (rightWord ++ suffix) :=
  spiderConv_suffixCongruence bottomPos (spiderConvTable_toSpiderConv conv) suffixInRange

/-! ## Non-vacuity — the SAME lemma whiskering distinct suffixes on the special row -/

/-- The comultiplication suffix `δ` is in range on the produced strand of `μδ` (boundary `1`). -/
private theorem inRange_special_comult :
    BrauerWordInRange (processBrauer (brauerSeed 1) frobSpecial.lhs).openWires.length [comultAt 0] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)

/-- The counit suffix `ε` is in range on the produced strand of `μδ` (boundary `1`). -/
private theorem inRange_special_counit :
    BrauerWordInRange (processBrauer (brauerSeed 1) frobSpecial.lhs).openWires.length [counitAt 0] :=
  BrauerWordInRange.cons (counitAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 0)

/-- ★ **The special law `μδ = 1` whiskered by a suffix comultiplication, through the UNIFORM lemma.**
`spiderConv_suffixCongruence` applied to `SpiderConv.frobSpecial` with the suffix `[comultAt 0]` — genuinely
whiskering a suffix onto a convertibility (not the seed relation), supplied by the ONE lemma. -/
theorem spiderConv_special_suffixComult :
    SpiderConv 1 (frobSpecial.lhs ++ [comultAt 0]) (frobSpecial.rhs ++ [comultAt 0]) :=
  spiderConv_suffixCongruence (by decide) SpiderConv.frobSpecial inRange_special_comult

/-- ★ **The special law `μδ = 1` whiskered by a DIFFERENT suffix (a counit), through the SAME UNIFORM lemma.**
Demonstrates the congruence is uniform over the suffix — one lemma, two distinct suffixes. -/
theorem spiderConv_special_suffixCounit :
    SpiderConv 1 (frobSpecial.lhs ++ [counitAt 0]) (frobSpecial.rhs ++ [counitAt 0]) :=
  spiderConv_suffixCongruence (by decide) SpiderConv.frobSpecial inRange_special_counit

/-- The comult-suffixed special witness genuinely relates DISTINCT words. -/
theorem spiderConv_special_suffixComult_distinct :
    (frobSpecial.lhs ++ [comultAt 0]) ≠ (frobSpecial.rhs ++ [comultAt 0])
      ∧ SpiderConv 1 (frobSpecial.lhs ++ [comultAt 0]) (frobSpecial.rhs ++ [comultAt 0]) :=
  ⟨by decide, spiderConv_special_suffixComult⟩

/-- ★ **The suffix identification is partition-real** — `μδ` and `1` each post-composed with `δ` induce the SAME
boundary partition, via `spiderConv_partitionSound`. -/
theorem spiderConv_special_suffixComult_partitionAgrees :
    extraSpiderDiagramOf 1 (frobSpecial.lhs ++ [comultAt 0])
      = extraSpiderDiagramOf 1 (frobSpecial.rhs ++ [comultAt 0]) :=
  spiderConv_partitionSound spiderConv_special_suffixComult

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the UNIFORM two-sided SUFFIX congruence is SHIPPED (r6, flag flipped `false → true`).**
The FROB-5 ledger named the one missing ingredient: the FORWARD `stepWiring` view-functoriality (view-equal inputs
give view-equal outputs), which is NOT the r4 keystone (that varies the WORD from a fixed mid-state under a single
rename; the suffix leg varies the MID-STATE under two renames).  It is now built from scratch — no global rename,
only the boundary view — via the `StepNodeCorr` correspondence invariant carried through the whole generic
`stepWiring` arc fold (`stepWiringArcs_viewInvariant`), the fresh-separation base fact (`stepNodeCorr_baseSameComp`),
and the four-zone post-step classifier (`stepWiring_boundaryRead_stepNodeCorr`), assembled into
`stepWiring_viewCongruence` and folded over an in-range suffix (`processBrauer_viewCongruence`).  The reconstruction
`spiderConv_stateViewEq` (loops-free, carries the special row) supplies the two seed states' view; the empty-prefix
`whisker` re-packages, giving `spiderConv_suffixCongruence : SpiderConv n a b → (in-range suffix) → SpiderConv n
(a ++ suffix) (b ++ suffix)` (and the table-level `spiderConvTable_suffixCongruence`).  Uniform over ALL in-range
suffixes — no per-suffix semantic gate (the `BrauerWordInRange` datum is bookkeeping, exactly the gate-free discipline
of the r5 table).  NON-VACUOUS: the ONE lemma whiskers TWO distinct suffixes onto `μδ = 1`
(`spiderConv_special_suffixComult`, `spiderConv_special_suffixCounit`), relates distinct words
(`spiderConv_special_suffixComult_distinct`), and is partition-real
(`spiderConv_special_suffixComult_partitionAgrees`).  `= true`. -/
def fxFrob_hasSpiderSuffixCongruenceShipped : Bool := true

end FX1Poly.Polygraph
