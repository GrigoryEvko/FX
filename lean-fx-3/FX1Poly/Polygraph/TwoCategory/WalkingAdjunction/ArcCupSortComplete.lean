import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSiblingSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDrop
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDropAndAppend
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerUnique
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingExtract

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

/-- ★ **A pure-cup append's prefix is pure cup (M2).**  Structural recursion on `prefixAtoms`:
each cons peels the head cup witness by a DIRECT `cases` on `AllCupArity (headAtom :: (restPrefix
++ suffixAtoms))` and recurses on the tail, rebuilding `AllCupArity (headAtom :: restPrefix)`.
Machine-checked axiom-clean (Route B — the `cases`-on-`AllCupArity` pattern carries no `propext`,
`scratchpad/probe.lean`), signature-generic, superseding the cap-count detour: the walking-
adjunction classifier is gone.  The location induction peels the last cup off the append and
recurses on the prefix. -/
theorem allCupArity_prefix_ofAppend {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    (prefixAtoms suffixAtoms :
      List (SpineAtom signature overallSource overallTarget)) →
    AllCupArity (prefixAtoms ++ suffixAtoms) → AllCupArity prefixAtoms
  | [], _, _ => AllCupArity.nil
  | headAtom :: restPrefix, suffixAtoms, appendPureCup => by
      cases appendPureCup with
      | cons hasCupDomArity hasCupCodArity restAppendPureCup =>
          exact AllCupArity.cons hasCupDomArity hasCupCodArity
            (allCupArity_prefix_ofAppend restPrefix suffixAtoms restAppendPureCup)

/-- ★ **The last cup of a pure-cup append carries cup arity `(0, 2)`, classifier-free.**  Structural
recursion on `prefixAtoms`: at `[]` the append is the singleton `[lastCup]`, whose sole cup witness a
DIRECT `cases` reads as `lastCup`'s dom/cod arity; each cons peels the head and recurses on the shorter
append.  Route B (the `cases`-on-`AllCupArity` pattern is `propext`-free, `scratchpad/probe.lean`),
signature-generic — the string-usable replacement for the cap-count/`adjunctionSpineAtom_isCupOrCap`
`singletonCupArity`, so the last-cup arity read-off no longer routes through the walking-adjunction
classifier. -/
theorem allCupArity_lastCup_arity {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    (prefixAtoms : List (SpineAtom signature overallSource overallTarget)) →
    (lastCup : SpineAtom signature overallSource overallTarget) →
    AllCupArity (prefixAtoms ++ [lastCup]) →
    lastCup.generatorDom.length = 0 ∧ lastCup.generatorCod.length = 2
  | [], lastCup, appendPureCup => by
      cases appendPureCup with
      | cons hasCupDomArity hasCupCodArity _ => exact ⟨hasCupDomArity, hasCupCodArity⟩
  | headAtom :: restPrefix, lastCup, appendPureCup => by
      cases appendPureCup with
      | cons _ _ restAppendPureCup =>
          exact allCupArity_lastCup_arity restPrefix lastCup restAppendPureCup

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

/-! ## The location induction `locateAux` and the top theorem `pureCupSpine_sort`

The peel-and-recurse location induction bubbles the target cup (identified by its chord window) to
the tail of a pure-cup spine, keeping the trace equivalence (atomic granularity), the arc structure,
the pure-cup regime, and the chain discipline.  It descends by chord-shift (below/above the last
cup) and re-ascends by a single disjoint-window transposition per level. -/

/-! ### Range-index read-off plumbing (the sibling copies are file-private) -/

private theorem rangeLoopGetAtPast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPast count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelow : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelow count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPast count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelow (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelow count [] index indexBelow

private theorem natListGetAtMapRange (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  have inRangeList : index < (List.range total).length := by rw [rangeLength]; exact inRange
  rw [natListGetAt_map_below mapFunction (List.range total) index inRangeList,
    rangeGetAtBelow total index inRange]

/-! ### The diagram-partner read-off and its involution -/

/-- The arc structure's `diagram.partner` reads off, at an in-range index, as the canonical
`partnerIndexOf` on the processed state's boundary — `.diagram.partner` IS `(List.range total).map
(partnerIndexOf ...)` by construction, so the read is a `map`-of-range read-off. -/
private theorem diagramPartnerReadAt
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (index : Nat)
    (inRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length) :
    natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index
      = partnerIndexOf
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).links
          (List.range bottomCount
            ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires)
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)
          index := by
  have partnerListEq :
      (arcStructureOfSpineList bottomCount spine).diagram.partner
        = (List.range (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)).map
            (partnerIndexOf
              (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).links
              (List.range bottomCount
                ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    spine).openWires)
              (bottomCount
                + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    spine).openWires.length)) := rfl
  rw [partnerListEq]
  exact natListGetAtMapRange _ _ index inRange

/-- The censused boundary matching is an involution IN the arc structure: a non-fixed partner read
maps back to the source.  Bridges the raw `partnerIndexOf_isInvolution` through the diagram read-off
at both the source index and its (in-range) partner. -/
private theorem diagramPartnerInvolutionAt
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount spine)
    (index : Nat)
    (inRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length)
    (notFixed : natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index
      ≠ index) :
    natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
        (natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index)
      = index := by
  have census := arcBoundaryCensus_ofChainedSpineList bottomCount spine chained
  have readIndex := diagramPartnerReadAt bottomCount spine index inRange
  have partnerBelow := partnerIndexOf_below
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) spine)
    bottomCount index inRange
  have notFixed' :
      partnerIndexOf
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).links
          (List.range bottomCount
            ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires)
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)
          index
        ≠ index := fun partnerEqIndex => notFixed (readIndex.trans partnerEqIndex)
  rw [readIndex,
    diagramPartnerReadAt bottomCount spine _ partnerBelow]
  exact partnerIndexOf_isInvolution bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) spine)
    census index inRange notFixed'

/-- The arc structure's partner list has length `bottomCount + openWires.length` — it is a mapped
range over exactly that many boundary indices. -/
private theorem partnerLengthReflect
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount spine).diagram.partner.length
      = bottomCount
        + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).openWires.length := by
  show ((List.range (bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length)).map _).length
    = bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length
  rw [natListMapLength, rangeLength]

/-- Folding a trailing cup onto a pure-cup spine grows the processed open-wire count by exactly two
(the cup's two fresh legs). -/
private theorem openWiresCupEndSplit
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        (prefixAtoms ++ [lastCup])).openWires.length
      = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).openWires.length + 2 := by
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have splitZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  have singletonZero : capAtomCount [lastCup] = 0 := by
    have leftZero := addLeftZero splitZero
    rw [leftZero, Nat.zero_add] at splitZero
    exact splitZero
  obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup singletonZero
  rw [processArcSpine_append prefixAtoms [lastCup]
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])]
  show (stepArcAtom (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      prefixAtoms) lastCup).openWires.length
    = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).openWires.length + 2
  rw [stepArcAtom_eq_stepCupArc
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
    lastCup lastDom lastCod]
  exact natListInsertAt_length
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      prefixAtoms).openWires lastCup.leftContext.length
    [(processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).nextFresh,
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).nextFresh + 1]

/-! ### The atomic smaller-window transposition, detailed -/

/-- ★ **The smaller-window sibling-cup transposition, ATOMIC and detailed.**  The companion of
`cupSwapStep` for the case where the FIRST cup has the SMALLER window: it returns the moved pair
SPLIT (front / back), at the ATOMIC granularity the location induction threads, with the moved back
cup's window explicit (it keeps `atomFirst`'s window and arities — the record update touches only its
right context). -/
theorem cupSwapStepSmallerDetail
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (bothCup : AllCupArity (atomFirst :: atomSecond :: rest))
    (chained : SpineBoundaryChained bottomCount (atomFirst :: atomSecond :: rest))
    (bottomPositive : 0 < bottomCount)
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + 2 + windowGap = atomSecond.leftContext.length) :
    ∃ movedFront movedBack,
      AtomicTraceEquiv adjunctionModeSignature (atomFirst :: atomSecond :: rest)
          (movedFront :: movedBack :: rest)
        ∧ arcStructureOfSpineList bottomCount (atomFirst :: atomSecond :: rest)
            = arcStructureOfSpineList bottomCount (movedFront :: movedBack :: rest)
        ∧ movedBack.leftContext.length = atomFirst.leftContext.length
        ∧ movedBack.generatorDom.length = 0
        ∧ movedBack.generatorCod.length = 2 := by
  obtain ⟨firstDom, firstCod⟩ := headCupArity bothCup
  have boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength := by
    obtain ⟨_, tailChained⟩ := spineBoundaryChained_tail chained
    exact (spineBoundaryChained_tail tailChained).1
  have windowsDisjoint' :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length := by
    rw [firstCod]; exact windowsDisjoint
  obtain ⟨inertPath, _, swapStep⟩ :=
    adjunctionSpineAtomSwap_of_disjointWindows atomFirst atomSecond rest boundariesChain
      windowGap windowsDisjoint'
  refine ⟨{ atomSecond with
              leftContext :=
                composePath (composePath atomFirst.leftContext atomFirst.generatorDom) inertPath },
          { atomFirst with
              rightContext :=
                composePath (composePath inertPath atomSecond.generatorCod)
                  atomSecond.rightContext },
          AtomicTraceEquiv.ofSwap swapStep, ?_, rfl, firstDom, firstCod⟩
  exact extractArc_eq_of_atomicTraceEquiv (AtomicTraceEquiv.ofSwap swapStep)
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil bottomPositive
    (Nat.le_refl bottomCount) (rangeLength bottomCount) chained

/-! ### The empty spine has no forward chord (the induction's vacuous floor) -/

/-- An empty pure-cup spine has no forward chord `(bc+targetWindow, bc+targetWindow+1)` — its
matching is the identity that pairs each top boundary index down to its bottom origin, never
forward.  Below the seed width the read pins to `targetWindow` (via the uniqueness finisher); at or
above it the read is out of range (zero).  Either way it cannot equal `bc+targetWindow+1`. -/
private theorem emptyArcNoForwardChord
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount) (targetWindow : Nat)
    (chordAt : natListGetAt
        (arcStructureOfSpineList bottomCount
          ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).diagram.partner
        (bottomCount + targetWindow)
      = bottomCount + targetWindow + 1) : False := by
  have openLen :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires.length
        = bottomCount := rangeLength bottomCount
  cases Nat.lt_or_ge targetWindow bottomCount with
  | inr atLeast =>
      have lenLe : (arcStructureOfSpineList bottomCount
          ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).diagram.partner.length
          ≤ bottomCount + targetWindow := by
        rw [partnerLengthReflect, openLen]
        exact Nat.add_le_add_left atLeast bottomCount
      rw [natListGetAt_zeroOfGe _ _ lenLe] at chordAt
      exact Nat.noConfusion chordAt
  | inl below =>
      have inRange : bottomCount + targetWindow
          < bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires.length := by
        rw [openLen]; exact Nat.add_lt_add_left below bottomCount
      have census := arcBoundaryCensus_ofChainedSpineList bottomCount
        ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
        (SpineBoundaryChained.nil bottomCount)
      have excludeRead :
          natListGetAt (List.range bottomCount
              ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires)
              (bottomCount + targetWindow)
            = targetWindow := by
        show natListGetAt (List.range bottomCount ++ List.range bottomCount) (bottomCount + targetWindow)
          = targetWindow
        have idxEq : bottomCount + targetWindow = targetWindow + (List.range bottomCount).length := by
          rw [rangeLength]; exact Nat.add_comm bottomCount targetWindow
        rw [idxEq,
          natListGetAt_append_pastBlock (List.range bottomCount) (List.range bottomCount) targetWindow]
        exact rangeGetAtBelow bottomCount targetWindow below
      have candidateRead :
          natListGetAt (List.range bottomCount
              ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires)
              targetWindow
            = targetWindow := by
        show natListGetAt (List.range bottomCount ++ List.range bottomCount) targetWindow = targetWindow
        exact natListGetAt_rangeAppend_below bottomCount (List.range bottomCount) targetWindow below
      have candidateNeExclude : targetWindow ≠ bottomCount + targetWindow := by
        have targetLt : targetWindow < bottomCount + targetWindow := by
          rw [Nat.add_comm bottomCount targetWindow]
          exact Nat.lt_add_of_pos_right bottomPositive
        exact Nat.ne_of_lt targetLt
      have sameReads : isSameComponent
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).links
          (natListGetAt (List.range bottomCount
              ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires)
              (bottomCount + targetWindow))
          (natListGetAt (List.range bottomCount
              ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires)
              targetWindow) = true := by
        rw [excludeRead, candidateRead]
        exact isSameComponent_self _ targetWindow
      have pinned := partnerIndexOf_uniqueSameComponent bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget)))
        census (bottomCount + targetWindow) targetWindow inRange
        (by rw [openLen]; exact Nat.lt_of_lt_of_le below (Nat.le_add_right bottomCount bottomCount))
        candidateNeExclude sameReads
      have readEq := diagramPartnerReadAt bottomCount
        ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
        (bottomCount + targetWindow) inRange
      rw [readEq, pinned] at chordAt
      have targetLt : targetWindow < bottomCount + targetWindow + 1 :=
        Nat.lt_succ_of_lt (by
          rw [Nat.add_comm bottomCount targetWindow]; exact Nat.lt_add_of_pos_right bottomPositive)
      exact Nat.ne_of_lt targetLt chordAt

/-! ### The nil-or-snoc list view (zero-axiom, avoiding the `propext`-tainted `List.reverse`) -/

/-- Every list is empty or a prefix with a distinguished last element — proved structurally, so the
location induction's unsnoc stays `propext`-free (`List.reverse_reverse` leaks `propext`). -/
private theorem listNilOrSnoc {carrier : Type _} :
    (list : List carrier) → list = [] ∨ ∃ prefixAtoms lastAtom, list = prefixAtoms ++ [lastAtom]
  | [] => Or.inl rfl
  | headAtom :: restAtoms =>
      match listNilOrSnoc restAtoms with
      | Or.inl restNil => Or.inr ⟨[], headAtom, by subst restNil; rfl⟩
      | Or.inr ⟨prefixAtoms, lastAtom, restSnoc⟩ =>
          Or.inr ⟨headAtom :: prefixAtoms, lastAtom, by subst restSnoc; rfl⟩

/-- `(prefixAtoms ++ [lastAtom]).length = prefixAtoms.length + 1` — structural, general carrier. -/
private theorem lengthSnoc {carrier : Type _} :
    (prefixAtoms : List carrier) → (lastAtom : carrier) →
    (prefixAtoms ++ [lastAtom]).length = prefixAtoms.length + 1
  | [], _ => rfl
  | _ :: restAtoms, lastAtom => congrArg Nat.succ (lengthSnoc restAtoms lastAtom)

/-- Re-grouping a double snoc: `(xs ++ [a]) ++ [b] = xs ++ [a, b]` — structural on `xs`, general
carrier (`List.append_assoc` leaks `propext`).  The location induction produces the swapped pair
back-appended as `(pre ++ [a]) ++ [b]`; this re-groups it into the two-atom front `pre ++ [a, b]` the
transposition acts on, and back again. -/
private theorem snocSnocRegroup {carrier : Type _} :
    (xs : List carrier) → (firstAtom secondAtom : carrier) →
    (xs ++ [firstAtom]) ++ [secondAtom] = xs ++ [firstAtom, secondAtom]
  | [], _, _ => rfl
  | headAtom :: restAtoms, firstAtom, secondAtom =>
      congrArg (headAtom :: ·) (snocSnocRegroup restAtoms firstAtom secondAtom)

/-- ★ **Two forward chords cannot be adjacent.**  A forward chord `(bc+w, bc+w+1)` and another at the
NEXT window `(bc+w+1, bc+w+2)` would share the endpoint `bc+w+1`, impossible in the involutive
matching: the involution sends `bc+w+1` back to `bc+w`, not forward to `bc+w+2`.  This rules out the
degenerate snake position in both descent directions of the location induction. -/
private theorem forwardChordsNotAdjacent
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount spine)
    (windowLow : Nat)
    (lowInRange : bottomCount + windowLow
      < bottomCount
        + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).openWires.length)
    (chordLow : natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
        (bottomCount + windowLow)
      = bottomCount + windowLow + 1)
    (chordHigh : natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
        (bottomCount + (windowLow + 1))
      = bottomCount + (windowLow + 1) + 1) : False := by
  have notFixed : natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
      (bottomCount + windowLow) ≠ bottomCount + windowLow := by
    rw [chordLow]; exact Nat.ne_of_gt (Nat.lt_succ_self (bottomCount + windowLow))
  have inv := diagramPartnerInvolutionAt bottomCount spine chained (bottomCount + windowLow)
    lowInRange notFixed
  rw [chordLow, Nat.add_assoc bottomCount windowLow 1, chordHigh] at inv
  have twoZero : bottomCount + windowLow + 2 = bottomCount + windowLow := inv
  exact absurd twoZero (Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))

/-- The last atom of a pure-cup append is a cup (arities `0 ⇒ 2`) — the last-element analogue of
`headCupArity`, routed through the cap tally to stay `propext`-free. -/
private theorem lastCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    lastCup.generatorDom.length = 0 ∧ lastCup.generatorCod.length = 2 := by
  have capZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have splitZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans capZero
  have singletonZero : capAtomCount [lastCup] = 0 := by
    have leftZero := addLeftZero splitZero
    rw [leftZero, Nat.zero_add] at splitZero
    exact splitZero
  exact singletonCupArity lastCup singletonZero

/-! ### `locateAux` — bubble the target cup (by chord window) to the spine's tail -/

/-- Fuel-driven core of the location induction (structural on `fuel ≥ spine.length`, so `propext`-free
where a `List.reverse` well-founded recursion would leak).  Peels the last cup `Clast` off the pure-cup
spine `t ++ [Clast]`; if the target window IS the last cup's it is done, else it chord-shifts the target
into `arc(t)`, recurses, back-appends `Clast`, and transposes the located cup past `Clast` (a single
disjoint-window swap — smaller-first below, larger-first/mirror above), keeping the atomic trace
equivalence, the arc structure, the pure-cup regime, and the chain discipline. -/
private theorem locateAuxFueled
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat) :
    (fuel : Nat) →
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    spine.length ≤ fuel →
    SpineBoundaryChained bottomCount spine →
    AllCupArity spine →
    0 < bottomCount →
    (targetWindow : Nat) →
    natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
        (bottomCount + targetWindow)
      = bottomCount + targetWindow + 1 →
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjunctionModeSignature spine (movedPrefix ++ [backCup])
        ∧ arcStructureOfSpineList bottomCount spine
            = arcStructureOfSpineList bottomCount (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained bottomCount (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow
  | 0, spine, lengthBound, _, _, bottomPositive, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (emptyArcNoForwardChord bottomCount bottomPositive targetWindow chordAt).elim
      | inr snocWit =>
          obtain ⟨t, Clast, spineSnoc⟩ := snocWit
          subst spineSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, spine, lengthBound, chained, pureCup, bottomPositive, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (emptyArcNoForwardChord bottomCount bottomPositive targetWindow chordAt).elim
      | inr snocWit =>
      obtain ⟨t, Clast, spineSnoc⟩ := snocWit
      subst spineSnoc
      have tLenBound : t.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChained : SpineBoundaryChained bottomCount t :=
        spineBoundaryChained_prefix_ofAppend t [Clast] bottomCount chained
      have tPure : AllCupArity t := allCupArity_prefix_ofAppend t [Clast] pureCup
      have clastChord := pureCupSpine_lastCup_isShortChord bottomCount t Clast chained bottomPositive pureCup
      obtain ⟨clastDom, clastCod⟩ := lastCupArity t Clast pureCup
      have owSplit := openWiresCupEndSplit bottomCount t Clast pureCup
      have windowFits : Clast.leftContext.length
          ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              t).openWires.length := by
        rw [processArcSpine_prefix_openWires_eq_lastDomBoundary bottomCount t Clast chained]
        show Clast.leftContext.length
          ≤ Clast.leftContext.length + Clast.generatorDom.length + Clast.rightContext.length
        exact Nat.le_trans (Nat.le_add_right Clast.leftContext.length Clast.generatorDom.length)
          (Nat.le_add_right (Clast.leftContext.length + Clast.generatorDom.length)
            Clast.rightContext.length)
      rcases Nat.lt_trichotomy targetWindow Clast.leftContext.length with below | middle | aboveW
      · -- (ii) targetWindow < wlast : chord-shift below, recurse, transpose the SMALLER cup past Clast
        have wlastGe : targetWindow + 2 ≤ Clast.leftContext.length := by
          rcases Nat.lt_or_ge (targetWindow + 1) Clast.leftContext.length with hlt | hge
          · exact hlt
          · exfalso
            have snakeEq : targetWindow + 1 = Clast.leftContext.length := Nat.le_antisymm below hge
            have lowInRange : bottomCount + targetWindow
                < bottomCount
                  + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                      (t ++ [Clast])).openWires.length := by
              rw [owSplit]
              exact Nat.add_lt_add_left
                (Nat.lt_of_lt_of_le below (Nat.le_trans windowFits (Nat.le_add_right _ 2))) bottomCount
            have chordHigh : natListGetAt
                (arcStructureOfSpineList bottomCount (t ++ [Clast])).diagram.partner
                (bottomCount + (targetWindow + 1))
              = bottomCount + (targetWindow + 1) + 1 := by rw [snakeEq]; exact clastChord
            exact forwardChordsNotAdjacent bottomCount (t ++ [Clast]) chained targetWindow
              lowInRange chordAt chordHigh
        have chordInT := chordShift_below bottomCount t Clast chained pureCup targetWindow below chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _arcEqT, pureT', _chainedT', sigWindow⟩ :=
          locateAuxFueled bottomCount fuel t tLenBound prefixChained tPure bottomPositive
            targetWindow chordInT
        obtain ⟨_sigDom, sigCod⟩ := lastCupArity pre' Csigma pureT'
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest wlastGe
        have e1' : AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have chainedFull := (spineBoundaryChained_iff_of_atomicTraceEquiv e1' bottomCount).mp chained
        obtain ⟨_, _, suffixChained⟩ := processArcSpine_openWires_length_ofChainedAppend pre'
          [Csigma, Clast] (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          bottomCount (rangeLength bottomCount) chainedFull
        obtain ⟨_, clastTail⟩ := spineBoundaryChained_tail suffixChained
        have boundariesChain : Clast.domBoundaryLength = Csigma.codBoundaryLength :=
          (spineBoundaryChained_tail clastTail).1
        have windowsDisjoint :
            Csigma.leftContext.length + Csigma.generatorCod.length + windowGap
              = Clast.leftContext.length := by rw [sigWindow, sigCod]; exact gapSpec
        obtain ⟨inertPath, _inertLen, swapStep⟩ :=
          adjunctionSpineAtomSwap_of_disjointWindows Csigma Clast [] boundariesChain windowGap
            windowsDisjoint
        have swapEquiv : AtomicTraceEquiv adjunctionModeSignature [Csigma, Clast]
            [{ Clast with
                leftContext :=
                  composePath (composePath Csigma.leftContext Csigma.generatorDom) inertPath },
             { Csigma with
                rightContext :=
                  composePath (composePath inertPath Clast.generatorCod) Clast.rightContext }] :=
          AtomicTraceEquiv.ofSwap swapStep
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    leftContext :=
                      composePath (composePath Csigma.leftContext Csigma.generatorDom) inertPath }])
                ++ [{ Csigma with
                      rightContext :=
                        composePath (composePath inertPath Clast.generatorCod) Clast.rightContext }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, sigWindow⟩
        · exact extractArc_eq_of_atomicTraceEquiv fullEquivCasted
            (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
            (arcStateFresh_initial bottomCount) isUnionFindForest_nil bottomPositive
            (Nat.le_refl bottomCount) (rangeLength bottomCount) chained
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted bottomCount).mp chained
      · -- (i) targetWindow = wlast : Clast IS the target
        exact ⟨t, Clast, AtomicTraceEquiv.refl (t ++ [Clast]), rfl, pureCup, chained, middle.symm⟩
      · -- (iii) targetWindow > wlast : chord-shift above, recurse, transpose the LARGER cup past Clast
        have targetGe : Clast.leftContext.length + 2 ≤ targetWindow := by
          rcases Nat.lt_or_ge (Clast.leftContext.length + 1) targetWindow with hlt | hge
          · exact hlt
          · exfalso
            have snakeEq : Clast.leftContext.length + 1 = targetWindow := Nat.le_antisymm aboveW hge
            have lowInRange : bottomCount + Clast.leftContext.length
                < bottomCount
                  + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                      (t ++ [Clast])).openWires.length := by
              rw [owSplit]
              exact Nat.add_lt_add_left
                (Nat.lt_of_le_of_lt windowFits (Nat.lt_add_of_pos_right (by decide : 0 < 2))) bottomCount
            have chordHigh : natListGetAt
                (arcStructureOfSpineList bottomCount (t ++ [Clast])).diagram.partner
                (bottomCount + (Clast.leftContext.length + 1))
              = bottomCount + (Clast.leftContext.length + 1) + 1 := by rw [snakeEq]; exact chordAt
            exact forwardChordsNotAdjacent bottomCount (t ++ [Clast]) chained Clast.leftContext.length
              lowInRange clastChord chordHigh
        have chordInT := chordShift_above bottomCount t Clast chained pureCup targetWindow aboveW chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _arcEqT, pureT', _chainedT', sigWindow⟩ :=
          locateAuxFueled bottomCount fuel t tLenBound prefixChained tPure bottomPositive
            (targetWindow - 2) chordInT
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest targetGe
        have e1' : AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have chainedFull := (spineBoundaryChained_iff_of_atomicTraceEquiv e1' bottomCount).mp chained
        obtain ⟨_, _, suffixChained⟩ := processArcSpine_openWires_length_ofChainedAppend pre'
          [Csigma, Clast] (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          bottomCount (rangeLength bottomCount) chainedFull
        obtain ⟨_, clastTail⟩ := spineBoundaryChained_tail suffixChained
        have boundariesChain : Clast.domBoundaryLength = Csigma.codBoundaryLength :=
          (spineBoundaryChained_tail clastTail).1
        have windowsDisjoint :
            Clast.leftContext.length + Clast.generatorDom.length + windowGap
              = Csigma.leftContext.length := by
          rw [clastDom, Nat.add_zero, sigWindow, ← gapSpec,
            Nat.add_right_comm Clast.leftContext.length 2 windowGap]
          exact (natAddSubCancel (Clast.leftContext.length + windowGap) 2).symm
        obtain ⟨inertPath, inertLen, swapLeft⟩ :=
          adjunctionSpineAtomSwapLeft_of_disjointWindows Csigma Clast [] boundariesChain windowGap
            windowsDisjoint
        have swapEquiv : AtomicTraceEquiv adjunctionModeSignature [Csigma, Clast]
            [{ Clast with
                rightContext :=
                  composePath (composePath inertPath Csigma.generatorDom) Csigma.rightContext },
             { Csigma with
                leftContext :=
                  composePath (composePath Clast.leftContext Clast.generatorCod) inertPath }] :=
          (AtomicTraceEquiv.ofSwap swapLeft).symm
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    rightContext :=
                      composePath (composePath inertPath Csigma.generatorDom) Csigma.rightContext }])
                ++ [{ Csigma with
                      leftContext :=
                        composePath (composePath Clast.leftContext Clast.generatorCod) inertPath }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, ?_⟩
        · exact extractArc_eq_of_atomicTraceEquiv fullEquivCasted
            (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
            (arcStateFresh_initial bottomCount) isUnionFindForest_nil bottomPositive
            (Nat.le_refl bottomCount) (rangeLength bottomCount) chained
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted bottomCount).mp chained
        · show (composePath (composePath Clast.leftContext Clast.generatorCod) inertPath).length
            = targetWindow
          rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLen, clastCod]
          exact gapSpec

/-- ★ **The location step.**  In a boundary-chained pure-cup spine, the cup whose short chord sits at
`targetWindow` bubbles to the tail: the spine is atomic-trace-equivalent to `movedPrefix ++ [backCup]`
with `backCup` a cup of window exactly `targetWindow`, preserving the arc structure, the pure-cup
regime, and the chain discipline.  Fuel-instantiated at `spine.length`. -/
theorem locateAux
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount spine)
    (pureCup : AllCupArity spine)
    (bottomPositive : 0 < bottomCount)
    (targetWindow : Nat)
    (chordAt : natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
        (bottomCount + targetWindow)
      = bottomCount + targetWindow + 1) :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjunctionModeSignature spine (movedPrefix ++ [backCup])
        ∧ arcStructureOfSpineList bottomCount spine
            = arcStructureOfSpineList bottomCount (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained bottomCount (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow :=
  locateAuxFueled bottomCount spine.length spine (Nat.le_refl spine.length) chained pureCup
    bottomPositive targetWindow chordAt

/-! ## `pureCupSpine_sort` — the pure-cup completeness theorem -/

/-- Left-cancellation for `Nat` addition, hand-rolled (core `Nat.add_left_cancel` leaks `propext`),
structural on the cancelled summand. -/
private theorem natAddLeftCancel :
    (base : Nat) → {leftSide rightSide : Nat} →
    base + leftSide = base + rightSide → leftSide = rightSide
  | 0, _, _, sumsEqual => by rw [Nat.zero_add, Nat.zero_add] at sumsEqual; exact sumsEqual
  | base + 1, _, _, sumsEqual =>
      natAddLeftCancel base (Nat.succ.inj (by rw [Nat.succ_add, Nat.succ_add] at sumsEqual; exact sumsEqual))

/-- Fuel-driven core of the pure-cup sort (structural on `fuel ≥ firstList.length`).  Peels the last
cup `C1` off `firstList = t1 ++ [C1]`, LOCATES the matching cup in `secondList` (bubbling it to the
tail via `locateAux` at `C1`'s chord window), pins it to `C1` by boundary-length rigidity, drops both
last cups by arc-injectivity (`dropLastCup_arc_injective`), recurses on the shortened prefixes, and
re-appends `C1`. -/
private theorem pureCupSpineSortFueled
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat) :
    (fuel : Nat) →
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    firstList.length ≤ fuel →
    SpineBoundaryChained bottomCount firstList →
    SpineBoundaryChained bottomCount secondList →
    AllCupArity firstList →
    AllCupArity secondList →
    0 < bottomCount →
    arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList →
    SpineTraceEquiv adjunctionModeSignature firstList secondList
  | 0, firstList, secondList, lengthBound, _, _, _, secondPureCup, _, arcEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact pureCupSpine_sort_nil bottomCount secondList secondPureCup arcEqual
      | inr snocWit =>
          obtain ⟨t1, C1, firstSnoc⟩ := snocWit
          subst firstSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, firstList, secondList, lengthBound, chainedFirst, chainedSecond, firstPureCup,
      secondPureCup, bottomPositive, arcEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact pureCupSpine_sort_nil bottomCount secondList secondPureCup arcEqual
      | inr snocWit =>
      obtain ⟨t1, C1, firstSnoc⟩ := snocWit
      subst firstSnoc
      have t1LenBound : t1.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChainedFirst : SpineBoundaryChained bottomCount t1 :=
        spineBoundaryChained_prefix_ofAppend t1 [C1] bottomCount chainedFirst
      have t1Pure : AllCupArity t1 := allCupArity_prefix_ofAppend t1 [C1] firstPureCup
      obtain ⟨c1Dom, c1Cod⟩ := lastCupArity t1 C1 firstPureCup
      have c1Chord := pureCupSpine_lastCup_isShortChord bottomCount t1 C1 chainedFirst bottomPositive
        firstPureCup
      have chordSecond : natListGetAt
          (arcStructureOfSpineList bottomCount secondList).diagram.partner
          (bottomCount + C1.leftContext.length)
        = bottomCount + C1.leftContext.length + 1 := by rw [← arcEqual]; exact c1Chord
      obtain ⟨pre2, backCup, locEquiv, locArc, locPure, locChained, backWindow⟩ :=
        locateAux bottomCount secondList chainedSecond secondPureCup bottomPositive
          C1.leftContext.length chordSecond
      obtain ⟨backDom, backCod⟩ := lastCupArity pre2 backCup locPure
      have appendedEqual := arcEqual.trans locArc
      -- the two prefixes fold to equal open-wire counts (arc-equal, both cup-ended)
      have owEqual :
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              t1).openWires.length
            = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                pre2).openWires.length := by
        have partnerLenEq :
            (arcStructureOfSpineList bottomCount (t1 ++ [C1])).diagram.partner.length
              = (arcStructureOfSpineList bottomCount (pre2 ++ [backCup])).diagram.partner.length :=
          congrArg (fun arcData => arcData.diagram.partner.length) appendedEqual
        rw [partnerLengthReflect, partnerLengthReflect] at partnerLenEq
        have owFullEq :
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                (t1 ++ [C1])).openWires.length
              = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  (pre2 ++ [backCup])).openWires.length :=
          natAddLeftCancel bottomCount partnerLenEq
        rw [openWiresCupEndSplit bottomCount t1 C1 firstPureCup,
          openWiresCupEndSplit bottomCount pre2 backCup locPure] at owFullEq
        exact natAddRightCancel 2 owFullEq
      have boundaryEqual : backCup.domBoundaryLength = C1.domBoundaryLength := by
        have domBackEq : backCup.domBoundaryLength
            = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                pre2).openWires.length :=
          (processArcSpine_prefix_openWires_eq_lastDomBoundary bottomCount pre2 backCup locChained).symm
        have domC1Eq : C1.domBoundaryLength
            = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                t1).openWires.length :=
          (processArcSpine_prefix_openWires_eq_lastDomBoundary bottomCount t1 C1 chainedFirst).symm
        exact domBackEq.trans (owEqual.symm.trans domC1Eq.symm)
      have backEqC1 : backCup = C1 :=
        adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths backCup C1 boundaryEqual backWindow
          (backDom.trans c1Dom.symm) (backCod.trans c1Cod.symm)
      subst backCup
      have arcPrefixEqual : arcStructureOfSpineList bottomCount t1
          = arcStructureOfSpineList bottomCount pre2 :=
        dropLastCup_arc_injective bottomCount t1 pre2 C1 chainedFirst locChained firstPureCup locPure
          appendedEqual
      have prefixTrace : SpineTraceEquiv adjunctionModeSignature t1 pre2 :=
        pureCupSpineSortFueled bottomCount fuel t1 pre2 t1LenBound prefixChainedFirst
          (spineBoundaryChained_prefix_ofAppend pre2 [C1] bottomCount locChained) t1Pure
          (allCupArity_prefix_ofAppend pre2 [C1] locPure) bottomPositive arcPrefixEqual
      exact (spineTraceEquiv_backAppendCongr prefixTrace C1).trans locEquiv.toSpineTraceEquiv.symm

/-- ★ **Pure-cup completeness (#2184).**  Two boundary-chained pure-cup spines over a positive bottom
boundary with EQUAL arc structure are trace-equivalent.  The walking-adjunction word problem restricted
to pure cups is thus DECIDED by the arc structure: equal planar-arc data forces a chain of
disjoint-window transpositions between the two spines.  Proved by peeling the last cup of one spine,
locating and pinning its partner in the other (`locateAux` + boundary-length rigidity), dropping both
by arc-injectivity, and recursing. -/
theorem pureCupSpine_sort
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chainedFirst : SpineBoundaryChained bottomCount firstList)
    (chainedSecond : SpineBoundaryChained bottomCount secondList)
    (firstPureCup : AllCupArity firstList)
    (secondPureCup : AllCupArity secondList)
    (bottomPositive : 0 < bottomCount)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    SpineTraceEquiv adjunctionModeSignature firstList secondList :=
  pureCupSpineSortFueled bottomCount firstList.length firstList secondList (Nat.le_refl firstList.length)
    chainedFirst chainedSecond firstPureCup secondPureCup bottomPositive arcEqual

/-! ## Honesty marker -/

/-- **Honesty marker — pure-cup completeness `pureCupSpine_sort` is SHIPPED (#2184).**  The full
assembly is landed, zero-axiom: the transposition atoms (`cupSwapStepMirror` / `cupSwapStepSmallerDetail`),
the prefix purity (`allCupArity_prefix_ofAppend`), the chord-shift descent (`chordShift_below` /
`chordShift_above`), the prefix congruence (`atomicTraceEquiv_prefixCongr`), the diagram-partner
involution + empty-arc floor (`diagramPartnerInvolutionAt` / `emptyArcNoForwardChord`), the location
induction `locateAux` (bubble the target cup to the tail by its chord window, via a fuel-driven
`propext`-free unsnoc + `forwardChordsNotAdjacent` snake exclusion), and the top theorem
`pureCupSpine_sort`: two boundary-chained pure-cup spines over a positive bottom boundary with equal
arc structure are `SpineTraceEquiv`.  What this marker does NOT claim: the `bottomCount = 0` case
(carried as the hypothesis `0 < bottomCount`, since the transpositions need a positive seed — a
separate residual for any consumer that needs it), nor the cup/cap-mixed word problem (this is the
pure-cup restriction). -/
def fxMode_hasArcCupSortComplete : Bool := true

end FX1Poly.Polygraph
