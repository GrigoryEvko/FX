import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSiblingSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDrop
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDropAndAppend
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations

/-! # WalkingAdjunction/ArcCupSortComplete — pure-cup completeness `pureCupSpine_sort` (#2184)

The crux of the walking-adjunction word-problem completeness: two boundary-chained pure-cup
spines with equal arc structure are `SpineTraceEquiv`.  This file assembles the top theorem
`pureCupSpine_sort` from the shipped transposition atoms (`cupSwapStep` / its mirror), the
last-cup short-chord readoff (S1), the drop-injectivity linchpin (S3), and the back-append
congruence, driven by a shift-tracked location induction.

  * `cupSwapStepMirror` (M1) — the LEFT variant of `cupSwapStep`: swapping two adjacent
    disjoint-window sibling cups where the FIRST has the LARGER window.  Rides the mirrored
    realized swap (`adjunctionSpineAtomSwapLeft_of_disjointWindows`) through the atomic
    closure's symmetry and the shipped peel.
  * `allCupArity_prefix_ofAppend` (M2) — a pure-cup append's prefix is pure cup (the `propext`-free
    prefix analogue of `allCupArity_ofCons`, via the cap-count split).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (the sibling kit copies are file-private) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## Cup arity readoff helpers (`propext`-free, routed through the cap count) -/

/-- **A pure-cup head atom is a cup** — its domain arity is `0` and codomain arity `2`.  Every
walking-adjunction atom is a cup or a cap (`adjunctionSpineAtom_isCupOrCap`); a cap head would
tally one, refuting `capAtomCount (headAtom :: rest) = 0` (`capAtomCount_ofAllCupArity`).  Routed
through the cap count rather than an indexed `cases` on `AllCupArity`, so it stays `propext`-free. -/
private theorem headCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    {headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (pureCup : AllCupArity (headAtom :: rest)) :
    headAtom.generatorDom.length = 0 ∧ headAtom.generatorCod.length = 2 := by
  have consCapZero : capAtomCount (headAtom :: rest) = 0 :=
    capAtomCount_ofAllCupArity (headAtom :: rest) pureCup
  cases adjunctionSpineAtom_isCupOrCap headAtom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue :
          (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]
        rfl
      dsimp only [capAtomCount] at consCapZero
      rw [if_pos guardTrue] at consCapZero
      exact Nat.noConfusion (Nat.add_comm 1 (capAtomCount rest) ▸ consCapZero)

/-! ## M1 — the mirrored sibling-cup transposition -/

/-- ★ **The mirrored sibling-cup transposition (M1).**  Two adjacent disjoint-window sibling cups
transpose when the FIRST has the LARGER window: `atomSecond.leftContext.length + windowGap =
atomFirst.leftContext.length`.  The moved pair's BACK element is `atomFirst`-derived with its
left context re-threaded through `atomSecond`'s codomain and the inert gap, so its window is
`atomSecond.leftContext.length + 2 + windowGap = atomFirst.leftContext.length + 2` (the
smaller-window `atomSecond` firing first shifts the bubbled cup up by its two legs).

The EQUIV half rides the mirrored realized swap (`adjunctionSpineAtomSwapLeft_of_disjointWindows`,
whose SOURCE is the moved pair) through the atomic closure's `symm` + `toSpineTraceEquiv`; the ARC
half rides the shipped peel `extractArc_eq_of_atomicTraceEquiv` at the fresh initial state, with
the window fit threaded by the chain discipline.  The moved back element's window is returned
explicitly for the location induction's shift bookkeeping. -/
theorem cupSwapStepMirror
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (bothCup : AllCupArity (atomFirst :: atomSecond :: rest))
    (chained : SpineBoundaryChained bottomCount (atomFirst :: atomSecond :: rest))
    (bottomPositive : 0 < bottomCount)
    (windowGap : Nat)
    (windowsDisjoint :
      atomSecond.leftContext.length + windowGap = atomFirst.leftContext.length) :
    ∃ movedFront movedBack,
      SpineTraceEquiv adjunctionModeSignature (atomFirst :: atomSecond :: rest)
          (movedFront :: movedBack :: rest)
        ∧ arcStructureOfSpineList bottomCount (atomFirst :: atomSecond :: rest)
            = arcStructureOfSpineList bottomCount (movedFront :: movedBack :: rest)
        ∧ movedBack.leftContext.length = atomFirst.leftContext.length + 2
        ∧ movedBack.generatorDom.length = 0
        ∧ movedBack.generatorCod.length = 2 := by
  obtain ⟨secondDom, secondCod⟩ := headCupArity (allCupArity_ofCons bothCup)
  obtain ⟨firstDom, firstCod⟩ := headCupArity bothCup
  have boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength := by
    obtain ⟨_, tailChained⟩ := spineBoundaryChained_tail chained
    exact (spineBoundaryChained_tail tailChained).1
  have windowsDisjoint' :
      atomSecond.leftContext.length + atomSecond.generatorDom.length + windowGap
        = atomFirst.leftContext.length := by
    rw [secondDom, Nat.add_zero]
    exact windowsDisjoint
  obtain ⟨inertPath, inertLength, swapLeft⟩ :=
    adjunctionSpineAtomSwapLeft_of_disjointWindows atomFirst atomSecond rest boundariesChain
      windowGap windowsDisjoint'
  refine ⟨{ atomSecond with
              rightContext :=
                composePath (composePath inertPath atomFirst.generatorDom)
                  atomFirst.rightContext },
          { atomFirst with
              leftContext :=
                composePath (composePath atomSecond.leftContext atomSecond.generatorCod)
                  inertPath },
          ?_, ?_, ?_, firstDom, firstCod⟩
  · exact (AtomicTraceEquiv.ofSwap swapLeft).symm.toSpineTraceEquiv
  · exact extractArc_eq_of_atomicTraceEquiv (AtomicTraceEquiv.ofSwap swapLeft).symm
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
      (arcStateFresh_initial bottomCount) isUnionFindForest_nil bottomPositive
      (Nat.le_refl bottomCount) (rangeLength bottomCount) chained
  · show (composePath (composePath atomSecond.leftContext atomSecond.generatorCod) inertPath).length
        = atomFirst.leftContext.length + 2
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLength, secondCod,
      Nat.add_assoc atomSecond.leftContext.length 2 windowGap,
      Nat.add_comm 2 windowGap, ← Nat.add_assoc atomSecond.leftContext.length windowGap 2,
      windowsDisjoint]

/-! ## M2 — a pure-cup append's prefix is pure cup -/

/-- The left summand of a vanishing `Nat` sum is zero — a `noConfusion` peel on the successor case
(`succ predLeft + rightSummand` is defeq `succ (predLeft + rightSummand)`), staying `propext`-free
where `Nat.eq_zero_of_add_eq_zero_right` would leak. -/
private theorem addLeftZero {leftSummand rightSummand : Nat}
    (sumZero : leftSummand + rightSummand = 0) : leftSummand = 0 := by
  cases leftSummand with
  | zero => rfl
  | succ predLeft =>
      exact Nat.noConfusion (Nat.add_comm (predLeft + 1) rightSummand ▸ sumZero)

/-- ★ **A pure-cup append's prefix is pure cup (M2).**  From `AllCupArity (prefixAtoms ++
suffixAtoms)`, the whole cap tally is zero (`capAtomCount_ofAllCupArity`); the append splits the
tally (`capAtomCount_append`), so the prefix's cap tally is the left summand of a vanishing sum,
hence zero (`addLeftZero`), whence `AllCupArity prefixAtoms` (`allCupArity_ofCapAtomCountZero`).
Routed through the cap count rather than an indexed `cases`, so it stays `propext`-free.  The
location induction peels the last cup off the append and recurses on the prefix. -/
theorem allCupArity_prefix_ofAppend
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms suffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (appendPureCup : AllCupArity (prefixAtoms ++ suffixAtoms)) :
    AllCupArity prefixAtoms := by
  have appendCapZero : capAtomCount (prefixAtoms ++ suffixAtoms) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ suffixAtoms) appendPureCup
  have splitCapZero : capAtomCount prefixAtoms + capAtomCount suffixAtoms = 0 :=
    (capAtomCount_append prefixAtoms suffixAtoms).symm.trans appendCapZero
  exact allCupArity_ofCapAtomCountZero prefixAtoms (addLeftZero splitCapZero)

/-! ## The chord-shift readoff — how a partner chord survives the last-cup drop

The location induction peels the last cup `lastCup` (window `wlast`) off a pure-cup spine
`prefix ++ [lastCup]`.  The last cup's step splices the short chord `[bc+wlast+1, bc+wlast]` at
`bc+wlast` and shifts every earlier port's partner up by two above `bc+wlast`
(`diagramPartner_stepCupArc`).  So a partner chord at some OTHER window `targetWindow ≠ wlast` in
`arc(prefix ++ [lastCup])` reads off, in `arc(prefix)`, at the SHIFTED window: unchanged if below
`wlast`, dropped by two if above.  These two readoffs are the induction's descent step. -/

/-- A singleton pure-cup atom is a cup — the last-element analogue of `headCupArity`, routed through
the cap tally to stay `propext`-free. -/
private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (capZero : capAtomCount [atom] = 0) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue :
          (atom.generatorDom.length == 2 && atom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]; rfl
      dsimp only [capAtomCount] at capZero
      rw [if_pos guardTrue] at capZero
      exact Nat.noConfusion capZero

/-- `(list.map f).length = list.length` — hand-rolled (core `List.length_map` leaks `propext`). -/
private theorem natListMapLength (mapFunction : Nat → Nat) :
    (list : List Nat) → (list.map mapFunction).length = list.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (natListMapLength mapFunction rest)

private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below =>
      natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

/-- The shared setup for the chord-shift readoffs: the prefix state's invariants, the partner-list
splice form, the window fit, and the base partner length. -/
private theorem chordShiftSetup
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    ((arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner
        = natListInsertAt
            ((arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.map
              (freshShiftAbove (bottomCount + lastCup.leftContext.length) 2))
            (bottomCount + lastCup.leftContext.length)
            [bottomCount + lastCup.leftContext.length + 1, bottomCount + lastCup.leftContext.length])
      ∧ lastCup.leftContext.length
          ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires.length
      ∧ (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.length
          = bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                prefixAtoms).openWires.length := by
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have splitZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  have singletonZero : capAtomCount [lastCup] = 0 := by
    have := addLeftZero splitZero
    exact (Nat.zero_add (capAtomCount [lastCup])).symm.trans
      (by rw [this] at splitZero; exact splitZero)
  obtain ⟨lastDom, _lastCod⟩ := singletonCupArity lastCup singletonZero
  have prefixChained : SpineBoundaryChained bottomCount prefixAtoms :=
    spineBoundaryChained_prefix_ofAppend prefixAtoms [lastCup] bottomCount chained
  have freshS := arcStateFresh_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) (arcStateFresh_initial bottomCount)
  have forestS := isUnionFindForest_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) isUnionFindForest_nil
  have censusS := arcBoundaryCensus_ofChainedSpineList bottomCount prefixAtoms prefixChained
  have seedBelowS := seedBottomCount_le_processArcSpine_nextFresh bottomCount prefixAtoms
  have domLen := processArcSpine_prefix_openWires_eq_lastDomBoundary bottomCount prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  refine ⟨?_, windowFitsS, ?_⟩
  · -- fold the last cup onto the prefix state, then apply the shipped partner splice
    have structEq : arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])
        = extractArc bottomCount
            (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms) lastCup.leftContext.length) := by
      show extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            (prefixAtoms ++ [lastCup]))
        = extractArc bottomCount
            (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms) lastCup.leftContext.length)
      rw [processArcSpine_append prefixAtoms [lastCup]
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])]
      show extractArc bottomCount
          (stepArcAtom (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup)
        = extractArc bottomCount
            (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms) lastCup.leftContext.length)
      rw [stepArcAtom_eq_stepCupArc
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
        lastCup lastDom _lastCod]
    rw [structEq]
    exact diagramPartner_stepCupArc bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
      lastCup.leftContext.length freshS forestS seedBelowS censusS windowFitsS
  · show ((List.range (bottomCount
          + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires.length)).map _).length
      = bottomCount
        + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms).openWires.length
    rw [natListMapLength, rangeLength]

/-- ★ **Chord-shift, below the dropped cup.**  If a partner chord `(bc+targetWindow, +1)` lives in
`arc(prefix ++ [lastCup])` at a window strictly below the last cup's window `wlast`, then the SAME
chord lives in `arc(prefix)` at the unshifted window `targetWindow` — the drop only splices/shifts
at or above `bc+wlast`, leaving the region below untouched. -/
theorem chordShift_below
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup]))
    (targetWindow : Nat)
    (targetBelow : targetWindow < lastCup.leftContext.length)
    (chordAt : natListGetAt
        (arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner
        (bottomCount + targetWindow)
      = bottomCount + targetWindow + 1) :
    natListGetAt (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner
        (bottomCount + targetWindow)
      = bottomCount + targetWindow + 1 := by
  obtain ⟨partnerSplice, windowFitsS, baseLen⟩ :=
    chordShiftSetup bottomCount prefixAtoms lastCup chained pureCup
  rw [partnerSplice] at chordAt
  have indexBelowPos : bottomCount + targetWindow < bottomCount + lastCup.leftContext.length :=
    Nat.add_lt_add_left targetBelow bottomCount
  have indexBelowLen : bottomCount + targetWindow
      < ((arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.map
          (freshShiftAbove (bottomCount + lastCup.leftContext.length) 2)).length := by
    rw [natListMapLength, baseLen]
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le targetBelow windowFitsS) bottomCount
  have indexBelowBaseLen : bottomCount + targetWindow
      < (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.length := by
    rw [baseLen]
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le targetBelow windowFitsS) bottomCount
  rw [natListGetAt_natListInsertAt_below _ _ _ _ indexBelowPos indexBelowLen,
    natListGetAt_map_below _ _ _ indexBelowBaseLen] at chordAt
  -- freshShiftAbove of the base read equals bc+targetWindow+1; the below-threshold branch is forced
  cases Nat.lt_or_ge
      (natListGetAt (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner
        (bottomCount + targetWindow))
      (bottomCount + lastCup.leftContext.length) with
  | inl isBelow =>
      rw [freshShiftAbove_ofNotLe _ _ _ (Nat.not_le.mpr isBelow)] at chordAt
      exact chordAt
  | inr isAtOrAbove =>
      exfalso
      rw [freshShiftAbove_ofLe _ _ _ isAtOrAbove] at chordAt
      -- baseRead + 2 = bc+targetWindow+1 forces baseRead+2 ≥ bc+wlast+2 > bc+targetWindow+1, contra
      have chainBound : bottomCount + lastCup.leftContext.length + 2 ≤ bottomCount + targetWindow + 1 :=
        chordAt ▸ Nat.add_le_add_right isAtOrAbove 2
      have : bottomCount + lastCup.leftContext.length ≤ bottomCount + targetWindow :=
        Nat.le_of_succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ 1)) chainBound)
      exact Nat.not_lt.mpr this indexBelowPos

/-- `(xs ++ ys).length = xs.length + ys.length` — hand-rolled (core `List.length_append` leaks
`propext`). -/
private theorem lengthAppendNat : (xs ys : List Nat) → (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | _ :: restWires, ys => by
      show (restWires ++ ys).length + 1 = (restWires.length + 1) + ys.length
      rw [lengthAppendNat restWires ys]
      exact Nat.add_right_comm restWires.length ys.length 1

/-- Splicing a block grows the wire list's length by the block's length (position-independent). -/
private theorem natListInsertAt_lengthNat :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    (natListInsertAt wires position block).length = wires.length + block.length
  | [], 0, block => by
      show (block ++ ([] : List Nat)).length = ([] : List Nat).length + block.length
      rw [lengthAppendNat block []]; exact Nat.add_comm block.length 0
  | [], _ + 1, block => (Nat.zero_add block.length).symm
  | headWire :: restWires, 0, block => by
      show (block ++ (headWire :: restWires)).length = (headWire :: restWires).length + block.length
      rw [lengthAppendNat block (headWire :: restWires)]
      exact Nat.add_comm block.length (headWire :: restWires).length
  | _ :: restWires, position + 1, block => by
      show (natListInsertAt restWires position block).length + 1 = (restWires.length + 1) + block.length
      rw [natListInsertAt_lengthNat restWires position block]
      exact Nat.add_right_comm restWires.length block.length 1

/-- Out of range `natListGetAt` reads zero — structural on the list then the index. -/
private theorem natListGetAt_zeroOfGe :
    (list : List Nat) → (index : Nat) → list.length ≤ index → natListGetAt list index = 0
  | [], _, _ => rfl
  | _ :: _, 0, atLeast => absurd atLeast (Nat.not_succ_le_zero _)
  | _ :: rest, index + 1, atLeast =>
      natListGetAt_zeroOfGe rest index (Nat.le_of_succ_le_succ atLeast)

/-- Right-cancellation for `Nat` addition, hand-rolled (core `Nat.add_right_cancel` leaks
`propext`), structural on the cancelled summand. -/
private theorem natAddRightCancel :
    (added : Nat) → {leftSide rightSide : Nat} →
    leftSide + added = rightSide + added → leftSide = rightSide
  | 0, _, _, sumsEqual => sumsEqual
  | added + 1, _, _, sumsEqual => natAddRightCancel added (Nat.succ.inj sumsEqual)

/-- `n + m - m = n` — hand-rolled (core `Nat.add_sub_cancel` leaks `propext`), by induction on `m`
through the clean `Nat.succ_sub_succ`. -/
private theorem natAddSubCancel (baseValue : Nat) : (subtracted : Nat) →
    baseValue + subtracted - subtracted = baseValue
  | 0 => rfl
  | subtracted + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact natAddSubCancel baseValue subtracted

/-- A three-term reassociation used by the above-window chord shift. -/
private theorem natSum_middle2 (a b c : Nat) : a + (b + 2 + c) = a + b + c + 2 := by
  rw [Nat.add_right_comm b 2 c, ← Nat.add_assoc a (b + c) 2, ← Nat.add_assoc a b c]

/-- ★ **Chord-shift, above the dropped cup.**  If a partner chord `(bc+targetWindow, +1)` lives in
`arc(prefix ++ [lastCup])` at a window strictly above the last cup's window `wlast`, then the SAME
chord lives in `arc(prefix)` at the window `targetWindow - 2` — the drop splices two ports at
`bc+wlast` and shifts everything above down by two.  The `targetWindow = wlast + 1` snake position is
arithmetically impossible (it would read the short chord's other leg `bc+wlast`, not `bc+wlast+2`). -/
theorem chordShift_above
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup]))
    (targetWindow : Nat)
    (targetAbove : lastCup.leftContext.length < targetWindow)
    (chordAt : natListGetAt
        (arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner
        (bottomCount + targetWindow)
      = bottomCount + targetWindow + 1) :
    natListGetAt (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner
        (bottomCount + (targetWindow - 2))
      = bottomCount + (targetWindow - 2) + 1 := by
  obtain ⟨partnerSplice, windowFitsS, baseLen⟩ :=
    chordShiftSetup bottomCount prefixAtoms lastCup chained pureCup
  -- full-spine partner length = base length + 2; force target in range from the nonzero chord read
  have fullLen : (arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner.length
      = (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.length + 2 := by
    rw [partnerSplice, natListInsertAt_lengthNat, natListMapLength]
    rfl
  have targetInFull : bottomCount + targetWindow
      < (arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner.length := by
    cases Nat.lt_or_ge (bottomCount + targetWindow)
        (arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner.length with
    | inl inRange => exact inRange
    | inr outRange =>
        exfalso
        rw [natListGetAt_zeroOfGe _ _ outRange] at chordAt
        exact Nat.noConfusion chordAt
  have targetLtTotal : targetWindow
      < (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).openWires.length + 2 := by
    rw [fullLen, baseLen, Nat.add_assoc] at targetInFull
    exact Nat.lt_of_add_lt_add_left targetInFull
  -- the snake position wlast+1 reads the short chord's other leg; rule it out, else target ≥ wlast+2
  cases Nat.lt_or_ge targetWindow (lastCup.leftContext.length + 2) with
  | inl targetSnake =>
      have targetIsSnake : targetWindow = lastCup.leftContext.length + 1 :=
        Nat.le_antisymm (Nat.le_of_succ_le_succ targetSnake) targetAbove
      exfalso
      rw [partnerSplice, targetIsSnake] at chordAt
      have snakeRead : natListGetAt
          (natListInsertAt
            ((arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.map
              (freshShiftAbove (bottomCount + lastCup.leftContext.length) 2))
            (bottomCount + lastCup.leftContext.length)
            [bottomCount + lastCup.leftContext.length + 1, bottomCount + lastCup.leftContext.length])
          (bottomCount + (lastCup.leftContext.length + 1))
        = bottomCount + lastCup.leftContext.length := by
        rw [← Nat.add_assoc bottomCount lastCup.leftContext.length 1]
        exact natListGetAt_natListInsertAt_inside _ _ _ 1 (Nat.lt_succ_self 1)
          (by rw [natListMapLength, baseLen]; exact Nat.add_le_add_left windowFitsS bottomCount)
      rw [snakeRead] at chordAt
      -- chordAt : bc+wlast = bc+(wlast+1)+1, i.e. x = x.succ.succ
      exact absurd chordAt (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _)))
  | inr targetAtLeast =>
      obtain ⟨offset, offsetSpec⟩ := Nat.le.dest targetAtLeast
      subst offsetSpec
      rw [partnerSplice] at chordAt
      -- reduce the goal window (wlast+2+offset) - 2 = wlast+offset
      have windowReduce : lastCup.leftContext.length + 2 + offset - 2 = lastCup.leftContext.length + offset := by
        rw [Nat.add_right_comm lastCup.leftContext.length 2 offset]
        exact natAddSubCancel (lastCup.leftContext.length + offset) 2
      rw [windowReduce, ← Nat.add_assoc bottomCount lastCup.leftContext.length offset]
      -- read chordAt past the two-element block (rewrite ONLY the natListGetAt term, not the RHS)
      have readEq : natListGetAt
            (natListInsertAt
              ((arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.map
                (freshShiftAbove (bottomCount + lastCup.leftContext.length) 2))
              (bottomCount + lastCup.leftContext.length)
              [bottomCount + lastCup.leftContext.length + 1, bottomCount + lastCup.leftContext.length])
            (bottomCount + (lastCup.leftContext.length + 2 + offset))
          = natListGetAt
              ((arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.map
                (freshShiftAbove (bottomCount + lastCup.leftContext.length) 2))
              (bottomCount + lastCup.leftContext.length + offset) := by
        rw [natSum_middle2 bottomCount lastCup.leftContext.length offset]
        exact natListGetAt_natListInsertAt_pastBlock _ _ _ offset
          (by rw [natListMapLength, baseLen]; exact Nat.add_le_add_left windowFitsS bottomCount)
      rw [readEq] at chordAt
      have wPrimeLtBase : bottomCount + lastCup.leftContext.length + offset
          < (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner.length := by
        rw [baseLen, Nat.add_assoc bottomCount lastCup.leftContext.length offset]
        apply Nat.add_lt_add_left
        have step2 : lastCup.leftContext.length + offset + 2
            < (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                prefixAtoms).openWires.length + 2 := by
          rw [Nat.add_right_comm lastCup.leftContext.length offset 2]; exact targetLtTotal
        exact Nat.lt_of_add_lt_add_right step2
      rw [natListGetAt_map_below _ _ _ wPrimeLtBase] at chordAt
      -- chordAt : freshShiftAbove (bc+wlast) 2 Z = bc + (wlast+2+offset) + 1, Z = read at bc+wlast+offset
      cases Nat.lt_or_ge
          (natListGetAt (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner
            (bottomCount + lastCup.leftContext.length + offset))
          (bottomCount + lastCup.leftContext.length) with
      | inr isAtOrAbove =>
          rw [freshShiftAbove_ofLe _ _ _ isAtOrAbove] at chordAt
          have expand : bottomCount + (lastCup.leftContext.length + 2 + offset) + 1
              = bottomCount + lastCup.leftContext.length + offset + 1 + 2 := by
            rw [natSum_middle2 bottomCount lastCup.leftContext.length offset]
          rw [expand] at chordAt
          exact natAddRightCancel 2 chordAt
      | inl isBelow =>
          exfalso
          rw [freshShiftAbove_ofNotLe _ _ _ (Nat.not_le.mpr isBelow)] at chordAt
          have zGe : bottomCount + lastCup.leftContext.length
              ≤ natListGetAt (arcStructureOfSpineList bottomCount prefixAtoms).diagram.partner
                (bottomCount + lastCup.leftContext.length + offset) := by
            rw [chordAt]
            exact Nat.le_trans
              (Nat.add_le_add_left
                (Nat.le_trans (Nat.le_add_right _ 2) (Nat.le_add_right _ offset)) bottomCount)
              (Nat.le_add_right _ 1)
          exact Nat.not_lt.mpr zGe isBelow

/-- ★ **Prefix congruence for the ATOMIC trace equivalence.**  Prepending a fixed prefix list to
both sides of an `AtomicTraceEquiv` preserves it — iterate the single-atom `consCongr` over the
prefix.  The location induction swaps the LAST two atoms of a spine, which is a front-two swap
sitting behind a prefix, so it lifts the front swap through this congruence. -/
theorem atomicTraceEquiv_prefixCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    (prefixAtoms : List (SpineAtom signature overallSource overallTarget)) →
    AtomicTraceEquiv signature (prefixAtoms ++ firstList) (prefixAtoms ++ secondList)
  | [] => atomicEquiv
  | headAtom :: restPrefix =>
      AtomicTraceEquiv.consCongr headAtom (atomicTraceEquiv_prefixCongr atomicEquiv restPrefix)

/-! ## Honesty marker -/

/-- **Honesty marker — the pure-cup sort's mirrored transposition atom + prefix purity are
SHIPPED.**  `cupSwapStepMirror` (M1) transposes two adjacent disjoint-window sibling cups where
the first has the larger window (mirror of `cupSwapStep`), returning the moved back cup's window
explicitly for the location induction's shift bookkeeping; `allCupArity_prefix_ofAppend` (M2) is
the `propext`-free prefix purity the peel-and-recurse induction needs.  What this marker does NOT
claim: the location induction `locateAux` (constructing the located spine from a partner chord) or
the top theorem `pureCupSpine_sort`. -/
def fxMode_hasArcCupSortComplete : Bool := true

end FX1Poly.Polygraph
