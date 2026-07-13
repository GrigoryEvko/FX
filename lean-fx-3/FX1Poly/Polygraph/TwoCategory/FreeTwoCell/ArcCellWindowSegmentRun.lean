import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGenPastGenCellSwapSimCount

/-! # MODE-COMMUTE r28 — the whole-cell SEGMENT-RUN engine: window decomposition + the component-disjointness invariant

## What this ships (Brick 1 of the whole-cell fold)

The r27 residual named the double induction `atomPastCell -> cellPastCell` as the sole remaining
delivery, with the CRUX being GUARD RE-ESTABLISHMENT: after each intra-cell atom fires, the forest
changes, and component-disjointness against the other window must persist.  This file ships the
master engine both fold layers consume — ONE structural induction over the cell giving, for every
turnback-only cell (every generator `0 => 2` or `2 => 0`) run inside a window of the open-wire list:

  * **the segment action** — running the cell rewrites ONLY the window segment: the openWires
    decomposition `prefix ++ (domSegment ++ suffix)` with `|prefix| = |leftWhisker|` and
    `|domSegment| = |cellDom|` becomes `prefix ++ (codSegment ++ suffix)` with
    `|codSegment| = |cellCod|` — the prefix and suffix ride along BYTE-INTACT (the horizontal
    position discipline, delivered as an equation, not a bound);
  * **probe root stability** — any probe node whose component is disjoint from every window read
    keeps its exact union-find root through the whole run;
  * **the fold invariant (THE CRUX)** — the probe stays component-disjoint from EVERY wire of the
    evolving window segment: cups splice in fresh legs (roots at-or-above the fresh frontier, never
    the probe's), caps merge two window components into a window component (`rootOf_twoJoinBlock`
    redirects roots only onto the second carrier's root — another guarded window root);
  * **general disjointness transport** — the probe stays component-disjoint from ANY node it was
    disjoint from before (window or not): every root redirect lands on a window root or a fresh id.

Also ships `RawTwoCellExpr.isTurnbackOnly` (the decidable cup/cap-only cell class — the box atom's
`2*numConsumed` removal semantics is outside the segment discipline, honestly excluded) and the
monomorphic `List Nat` append kit the decomposition algebra needs (hand-rolled cons-only, keeping
the file propext-free; the corpus' `List.append` stdlib-lemma trap is documented).

## What this does NOT ship

No swap simulation yet: this file never runs two orders.  The pins stay `false`.  Bricks 2/3
(`ArcAtomPastCellSwapSimCount` / `ArcCellPastCellSwapSimCount`) consume this engine.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` + independent
`#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The monomorphic `List Nat` append kit (cons-only, propext-free) -/

/-- Append is associative — hand-rolled for `List Nat` (the stdlib lemma routes through `simp`). -/
theorem natListAppendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: restFront, middle, back =>
      congrArg (headWire :: ·) (natListAppendAssoc restFront middle back)

/-- Reading strictly inside the front of an append reads the front. -/
theorem natListGetAt_appendBelow : (front back : List Nat) → (position : Nat) →
    position < front.length →
    natListGetAt (front ++ back) position = natListGetAt front position
  | [], _, position, isBelow => absurd isBelow (Nat.not_lt_zero position)
  | _ :: _, _, 0, _ => rfl
  | headWire :: restFront, back, position + 1, isBelow => by
      show natListGetAt (restFront ++ back) position = natListGetAt restFront position
      exact natListGetAt_appendBelow restFront back position (Nat.lt_of_succ_lt_succ isBelow)

/-- Reading at the front's length plus an offset reads the back at the offset. -/
theorem natListGetAt_appendAtLength : (front back : List Nat) → (offset : Nat) →
    natListGetAt (front ++ back) (front.length + offset) = natListGetAt back offset
  | [], back, offset => by
      show natListGetAt back (0 + offset) = natListGetAt back offset
      rw [Nat.zero_add]
  | headWire :: restFront, back, offset => by
      show natListGetAt (headWire :: (restFront ++ back)) (restFront.length + 1 + offset)
        = natListGetAt back offset
      rw [Nat.add_right_comm restFront.length 1 offset]
      exact (natListGetAt_consSucc headWire (restFront ++ back) (restFront.length + offset)).trans
        (natListGetAt_appendAtLength restFront back offset)

/-- Membership in the front injects into the append. -/
theorem natListMem_appendOfLeft {wire : Nat} : (front back : List Nat) →
    wire ∈ front → wire ∈ front ++ back
  | [], _, memberHyp => nomatch memberHyp
  | _ :: restFront, back, List.Mem.head _ => List.Mem.head (restFront ++ back)
  | headWire :: restFront, back, List.Mem.tail _ memberRest =>
      List.Mem.tail headWire (natListMem_appendOfLeft restFront back memberRest)

/-- Membership in the back injects into the append. -/
theorem natListMem_appendOfRight {wire : Nat} : (front back : List Nat) →
    wire ∈ back → wire ∈ front ++ back
  | [], _, memberHyp => memberHyp
  | headWire :: restFront, back, memberHyp =>
      List.Mem.tail headWire (natListMem_appendOfRight restFront back memberHyp)

/-- Membership in an append splits into front or back membership. -/
theorem natListMem_appendElim {wire : Nat} : (front back : List Nat) →
    wire ∈ front ++ back → wire ∈ front ∨ wire ∈ back
  | [], _, memberHyp => Or.inr memberHyp
  | headWire :: restFront, back, memberHyp => by
      cases memberHyp with
      | head => exact Or.inl (List.Mem.head restFront)
      | tail _ memberRest =>
          cases natListMem_appendElim restFront back memberRest with
          | inl memberFront => exact Or.inl (List.Mem.tail headWire memberFront)
          | inr memberBack => exact Or.inr memberBack

/-- A zero-length wire list is empty. -/
theorem natListEqNilOfLengthZero : (wires : List Nat) → wires.length = 0 → wires = []
  | [], _ => rfl
  | _ :: _, lengthZero => Nat.noConfusion lengthZero

/-- A two-length wire list is a literal pair. -/
theorem natListEqPairOfLengthTwo : (wires : List Nat) → wires.length = 2 →
    ∃ firstWire secondWire, wires = [firstWire, secondWire]
  | [], lengthTwo => Nat.noConfusion lengthTwo
  | [_], lengthTwo => Nat.noConfusion (Nat.succ.inj lengthTwo)
  | [firstWire, secondWire], _ => ⟨firstWire, secondWire, rfl⟩
  | _ :: _ :: _ :: _, lengthTwo => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj lengthTwo))

/-- Split a wire list at a prescribed front length. -/
theorem natListSplitAtLength : (wires : List Nat) → (frontLength : Nat) →
    frontLength ≤ wires.length →
    ∃ frontWires backWires, wires = frontWires ++ backWires ∧ frontWires.length = frontLength
  | wires, 0, _ => ⟨[], wires, rfl, rfl⟩
  | [], frontLength + 1, isWithin => absurd isWithin (Nat.not_succ_le_zero frontLength)
  | headWire :: restWires, frontLength + 1, isWithin => by
      obtain ⟨frontWires, backWires, splitEq, frontLen⟩ :=
        natListSplitAtLength restWires frontLength (Nat.le_of_succ_le_succ isWithin)
      exact ⟨headWire :: frontWires, backWires, congrArg (headWire :: ·) splitEq,
        congrArg (· + 1) frontLen⟩

/-- Right-cancellation of `Nat` addition — hand-rolled structural recursion on the shared summand
(the core `Nat.add_left_cancel` depends on `propext`; this suffixed twin is axiom-free and
collision-free against the monad-lane `natAddLeftCancel`). -/
theorem natAddRightCancelSeg : (first second shared : Nat) →
    first + shared = second + shared → first = second
  | _, _, 0, sumsEqual => sumsEqual
  | first, second, shared + 1, sumsEqual =>
      natAddRightCancelSeg first second shared (Nat.succ.inj sumsEqual)

/-- Left-cancellation of `Nat` addition via commutativity and the right-cancel twin. -/
theorem natAddLeftCancelSeg (shared first second : Nat)
    (sumsEqual : shared + first = shared + second) : first = second :=
  natAddRightCancelSeg first second shared
    (by rw [Nat.add_comm first shared, Nat.add_comm second shared]; exact sumsEqual)

/-! ## Bool split helpers (full-enumeration, propext-free) -/

/-- A true conjunction has two true legs. -/
theorem boolBothTrueOfAndTrue : {firstFlag secondFlag : Bool} →
    (firstFlag && secondFlag) = true → firstFlag = true ∧ secondFlag = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, evidence => Bool.noConfusion evidence
  | false, true, evidence => Bool.noConfusion evidence
  | false, false, evidence => Bool.noConfusion evidence

/-- A true disjunction has a true leg. -/
theorem boolEitherTrueOfOrTrue : {firstFlag secondFlag : Bool} →
    (firstFlag || secondFlag) = true → firstFlag = true ∨ secondFlag = true
  | true, _, _ => Or.inl rfl
  | false, true, _ => Or.inr rfl
  | false, false, evidence => Bool.noConfusion evidence

/-! ## The turnback-only cell class -/

/-- Whether every generator of the cell is a turnback — a cup (`0 => 2`) or a cap (`2 => 0`).
The box atom's removal semantics (`2 * numConsumed` wires dropped) sits outside the window segment
discipline, so the whole-cell fold honestly restricts to this decidable class (which covers the
walking-adjunction / Brauer lane in full: unit and counit are the only generators). -/
def RawTwoCellExpr.isTurnbackOnly {signature : ModeSignature} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    RawTwoCellExpr signature localDom localCod → Bool
  | _, _, localDom, localCod, .gen _ =>
      ((localDom.length == 0) && (localCod.length == 2))
        || ((localDom.length == 2) && (localCod.length == 0))
  | _, _, _, _, .id _ => true
  | _, _, _, _, .vcomp cellLower cellUpper =>
      cellLower.isTurnbackOnly && cellUpper.isTurnbackOnly
  | _, _, _, _, .whiskerLeft _ body => body.isTurnbackOnly
  | _, _, _, _, .whiskerRight _ body => body.isTurnbackOnly

/-! ## The component-disjointness guard -/

/-- The probe node is component-disjoint from every wire of the segment — the r26-doctrine guard
(three decidable `isSameComponent = false` reads per cap pair are instances of this), stated at
segment granularity so it can be threaded as a fold invariant. -/
def arcProbeDisjointFromSegment (links : List (Nat × Nat)) (probe : Nat)
    (segment : List Nat) : Prop :=
  ∀ wire ∈ segment, isSameComponent links probe wire = false

/-! ## The master engine — segment action + probe transport, one structural induction -/

/-- ★★ **The whole-cell segment-run engine.**  A turnback-only cell run at a left whisker whose
length matches the window start rewrites ONLY its window: the openWires decomposition transports
`domSegment -> codSegment` with the prefix and suffix byte-intact, and every probe whose component
is disjoint from the window keeps (a) its exact root, (b) disjointness from the evolving window,
and (c) disjointness from every node it was already disjoint from.  This is the r27-named CRUX —
guard re-establishment through intra-cell joins — proved once, for both fold layers:

  * cup leaf: the block `twoJoinBlock links nf (nf+1) (nf+2)` touches only fresh ids, so old roots
    are byte-stable and the two spliced legs root at `nf+1 >` every guarded root;
  * cap leaf: the block `twoJoinBlock links c d nf` redirects roots ONLY onto `rootOf d` — another
    guarded window root — so the probe's disequalities survive (`rootOf_twoJoinBlock`);
  * vcomp: thread the transported guard through the pipe segment (the literal invariant step);
  * whiskers: re-associate the decomposition, the untouched flank rides via transport (c).  -/
theorem arcCellSegmentRun_ofWellFormed {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (innerLeft : ModalityPath signature.graph overallSource localSource) →
    (innerRight : ModalityPath signature.graph localTarget overallTarget) →
    (state : ArcWireState) → (prefixWires domSegment suffixWires : List Nat) →
    WellFormedArcState state →
    cell.isTurnbackOnly = true →
    state.openWires = prefixWires ++ (domSegment ++ suffixWires) →
    prefixWires.length = innerLeft.length →
    domSegment.length = localDom.length →
    ∃ codSegment,
      (runArcCell state innerLeft innerRight cell).openWires
          = prefixWires ++ (codSegment ++ suffixWires)
      ∧ codSegment.length = localCod.length
      ∧ (∀ probe,
          unionFindRootOf state.links probe < state.nextFresh →
          arcProbeDisjointFromSegment state.links probe domSegment →
          unionFindRootOf (runArcCell state innerLeft innerRight cell).links probe
              = unionFindRootOf state.links probe
            ∧ arcProbeDisjointFromSegment (runArcCell state innerLeft innerRight cell).links
                probe codSegment
            ∧ (∀ otherNode, isSameComponent state.links probe otherNode = false →
                isSameComponent (runArcCell state innerLeft innerRight cell).links probe otherNode
                  = false))
  | _, _, _, _, .id _, innerLeft, innerRight, state, prefixWires, domSegment, suffixWires,
      _, _, decomp, _, segLen =>
    ⟨domSegment, decomp, segLen,
      fun _ _ probeGuard => ⟨rfl, probeGuard, fun _ disjointBefore => disjointBefore⟩⟩
  | _, _, localDom, localCod, .gen generator, innerLeft, innerRight, state, prefixWires,
      domSegment, suffixWires, wellFormed, isTurnback, decomp, prefixLen, segLen => by
    have nfPositive : 0 < state.nextFresh := wellFormed.isNonDegenerate
    have forest : isUnionFindForest state.links := wellFormed.isForest
    have wiresBelow : ∀ wire ∈ state.openWires, wire < state.nextFresh := wellFormed.isFresh.1
    have endpointsBelow : ∀ edge ∈ state.links,
        edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh := wellFormed.isFresh.2.1
    have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
      fun edge edgeMem => (endpointsBelow edge edgeMem).1
    have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
      fun edge edgeMem => (endpointsBelow edge edgeMem).2
    have rootFreshAt : ∀ offset : Nat,
        unionFindRootOf state.links (state.nextFresh + offset) = state.nextFresh + offset :=
      fun offset => unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow _
        (Nat.le_add_right _ _)
    have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
      unionFindRootOf_of_unmentioned state.links state.nextFresh childrenBelow _ (Nat.le_refl _)
    cases boolEitherTrueOfOrTrue isTurnback with
    | inl isCup =>
        obtain ⟨domZeroBeq, codTwoBeq⟩ := boolBothTrueOfAndTrue isCup
        have domZero : localDom.length = 0 := of_decide_eq_true domZeroBeq
        have codTwo : localCod.length = 2 := of_decide_eq_true codTwoBeq
        have segNil : domSegment = [] := natListEqNilOfLengthZero domSegment (segLen.trans domZero)
        subst segNil
        have decompFlat : state.openWires = prefixWires ++ suffixWires := decomp
        have runsAsCup : runArcCell state innerLeft innerRight (RawTwoCellExpr.gen generator)
            = stepCupArc state innerLeft.length :=
          stepArcAtom_eq_stepCupArc state
            (SpineAtom.mk _ _ innerLeft localDom localCod generator innerRight) domZero codTwo
        have openWiresEq : (stepCupArc state innerLeft.length).openWires
            = prefixWires ++ ([state.nextFresh, state.nextFresh + 1] ++ suffixWires) := by
          show natListInsertAt state.openWires innerLeft.length
              [state.nextFresh, state.nextFresh + 1]
            = prefixWires ++ ([state.nextFresh, state.nextFresh + 1] ++ suffixWires)
          rw [decompFlat, ← prefixLen]
          show natListInsertAt (prefixWires ++ suffixWires) (prefixWires.length + 0)
              [state.nextFresh, state.nextFresh + 1]
            = prefixWires ++ ([state.nextFresh, state.nextFresh + 1] ++ suffixWires)
          rw [natListInsertAt_appendPrefix prefixWires suffixWires 0
              [state.nextFresh, state.nextFresh + 1],
            natListInsertAt_zero suffixWires [state.nextFresh, state.nextFresh + 1]]
        have linksEq : (stepCupArc state innerLeft.length).links
            = twoJoinBlock state.links state.nextFresh (state.nextFresh + 1)
                (state.nextFresh + 2) :=
          stepCupArc_links_twoJoinBlock state innerLeft.length
        have eventNeFirstRoot : state.nextFresh + 2 ≠ state.nextFresh :=
          Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _))
        refine ⟨[state.nextFresh, state.nextFresh + 1], ?_, ?_, ?_⟩
        · rw [runsAsCup]; exact openWiresEq
        · show 2 = localCod.length
          exact codTwo.symm
        · intro probe probeRootBelow _
          have probeUntouched : unionFindRootOf (stepCupArc state innerLeft.length).links probe
              = unionFindRootOf state.links probe := by
            rw [linksEq]
            exact rootOf_twoJoinBlock_untouched state.links forest state.nextFresh
              (state.nextFresh + 1) (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1)
              rootNf (rootFreshAt 1) (rootFreshAt 2) eventNeFirstRoot probe
              (Nat.ne_of_gt probeRootBelow)
              (Nat.ne_of_gt (Nat.lt_of_lt_of_le probeRootBelow (Nat.le_add_right _ 2)))
          have rootLegLeft : unionFindRootOf (stepCupArc state innerLeft.length).links
              state.nextFresh = state.nextFresh + 1 := by
            rw [linksEq,
              rootOf_twoJoinBlock state.links forest state.nextFresh (state.nextFresh + 1)
                (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1) rootNf (rootFreshAt 1)
                (rootFreshAt 2) eventNeFirstRoot state.nextFresh,
              rootNf, natBeqSelf]
            rfl
          have rootLegRight : unionFindRootOf (stepCupArc state innerLeft.length).links
              (state.nextFresh + 1) = state.nextFresh + 1 := by
            rw [linksEq,
              rootOf_twoJoinBlock state.links forest state.nextFresh (state.nextFresh + 1)
                (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1) rootNf (rootFreshAt 1)
                (rootFreshAt 2) eventNeFirstRoot (state.nextFresh + 1),
              rootFreshAt 1,
              natBeqFalseOfNe (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh)),
              natBeqFalseOfNe (Nat.ne_of_gt (Nat.lt_succ_self (state.nextFresh + 1)))]
            rfl
          have probeNeLegRoot : unionFindRootOf state.links probe ≠ state.nextFresh + 1 :=
            Nat.ne_of_lt (Nat.lt_of_lt_of_le probeRootBelow (Nat.le_succ _))
          rw [runsAsCup]
          refine ⟨probeUntouched, ?_, ?_⟩
          · intro wire wireMem
            show (unionFindRootOf (stepCupArc state innerLeft.length).links probe
                == unionFindRootOf (stepCupArc state innerLeft.length).links wire) = false
            cases wireMem with
            | head =>
                rw [probeUntouched, rootLegLeft]
                exact natBeqFalseOfNe probeNeLegRoot
            | tail _ wireMemTail =>
                cases wireMemTail with
                | head =>
                    rw [probeUntouched, rootLegRight]
                    exact natBeqFalseOfNe probeNeLegRoot
                | tail _ impossibleMem => cases impossibleMem
          · intro otherNode disjointBefore
            show (unionFindRootOf (stepCupArc state innerLeft.length).links probe
                == unionFindRootOf (stepCupArc state innerLeft.length).links otherNode) = false
            rw [probeUntouched, linksEq,
              rootOf_twoJoinBlock state.links forest state.nextFresh (state.nextFresh + 1)
                (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1) rootNf (rootFreshAt 1)
                (rootFreshAt 2) eventNeFirstRoot otherNode]
            cases redirectGuard : (state.nextFresh == unionFindRootOf state.links otherNode
                || state.nextFresh + 2 == unionFindRootOf state.links otherNode) with
            | true =>
                show (unionFindRootOf state.links probe == state.nextFresh + 1) = false
                exact natBeqFalseOfNe probeNeLegRoot
            | false => exact disjointBefore
    | inr isCap =>
        obtain ⟨domTwoBeq, codZeroBeq⟩ := boolBothTrueOfAndTrue isCap
        have domTwo : localDom.length = 2 := of_decide_eq_true domTwoBeq
        have codZero : localCod.length = 0 := of_decide_eq_true codZeroBeq
        obtain ⟨readLeftWire, readRightWire, segPair⟩ :=
          natListEqPairOfLengthTwo domSegment (segLen.trans domTwo)
        subst segPair
        have runsAsCap : runArcCell state innerLeft innerRight (RawTwoCellExpr.gen generator)
            = stepCapArc state innerLeft.length :=
          stepArcAtom_eq_stepCapArc state
            (SpineAtom.mk _ _ innerLeft localDom localCod generator innerRight) domTwo codZero
        have readLeftEq : natListGetAt state.openWires innerLeft.length = readLeftWire := by
          rw [decomp, ← prefixLen]
          show natListGetAt (prefixWires ++ ([readLeftWire, readRightWire] ++ suffixWires))
              (prefixWires.length + 0) = readLeftWire
          exact natListGetAt_appendAtLength prefixWires
            ([readLeftWire, readRightWire] ++ suffixWires) 0
        have readRightEq : natListGetAt state.openWires (innerLeft.length + 1) = readRightWire := by
          rw [decomp, ← prefixLen]
          exact natListGetAt_appendAtLength prefixWires
            ([readLeftWire, readRightWire] ++ suffixWires) 1
        have openWiresEq : (stepCapArc state innerLeft.length).openWires
            = prefixWires ++ ([] ++ suffixWires) := by
          show natListRemoveTwoAt state.openWires innerLeft.length
            = prefixWires ++ ([] ++ suffixWires)
          rw [decomp, ← prefixLen]
          show natListRemoveTwoAt (prefixWires ++ ([readLeftWire, readRightWire] ++ suffixWires))
              (prefixWires.length + 0) = prefixWires ++ suffixWires
          rw [natListRemoveTwoAt_appendPrefix prefixWires
              ([readLeftWire, readRightWire] ++ suffixWires) 0]
          rfl
        have linksEq : (stepCapArc state innerLeft.length).links
            = twoJoinBlock state.links readLeftWire readRightWire state.nextFresh := by
          rw [stepCapArc_links_twoJoinBlock state innerLeft.length, readLeftEq, readRightEq]
        have readLeftMem : readLeftWire ∈ state.openWires := by
          rw [decomp]
          exact natListMem_appendOfRight prefixWires _
            (natListMem_appendOfLeft _ suffixWires (List.Mem.head _))
        have readRightMem : readRightWire ∈ state.openWires := by
          rw [decomp]
          exact natListMem_appendOfRight prefixWires _
            (natListMem_appendOfLeft _ suffixWires (List.Mem.tail _ (List.Mem.head _)))
        have readLeftRootBelow : unionFindRootOf state.links readLeftWire < state.nextFresh :=
          unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow readLeftWire
            (wiresBelow readLeftWire readLeftMem)
        refine ⟨[], ?_, codZero.symm, ?_⟩
        · rw [runsAsCap]; exact openWiresEq
        · intro probe probeRootBelow probeGuard
          have guardLeft : isSameComponent state.links probe readLeftWire = false :=
            probeGuard readLeftWire (List.Mem.head _)
          have guardRight : isSameComponent state.links probe readRightWire = false :=
            probeGuard readRightWire (List.Mem.tail _ (List.Mem.head _))
          have probeNeLeftRoot : unionFindRootOf state.links probe
              ≠ unionFindRootOf state.links readLeftWire := neOfBeqFalse guardLeft
          have probeNeRightRoot : unionFindRootOf state.links probe
              ≠ unionFindRootOf state.links readRightWire := neOfBeqFalse guardRight
          have probeUntouched : unionFindRootOf (stepCapArc state innerLeft.length).links probe
              = unionFindRootOf state.links probe := by
            rw [linksEq]
            exact rootOf_twoJoinBlock_untouched state.links forest readLeftWire readRightWire
              state.nextFresh (unionFindRootOf state.links readLeftWire)
              (unionFindRootOf state.links readRightWire) rfl rfl rootNf
              (Nat.ne_of_gt readLeftRootBelow) probe (Ne.symm probeNeLeftRoot)
              (Nat.ne_of_gt probeRootBelow)
          rw [runsAsCap]
          refine ⟨probeUntouched, ?_, ?_⟩
          · intro wire wireMem
            cases wireMem
          intro otherNode disjointBefore
          show (unionFindRootOf (stepCapArc state innerLeft.length).links probe
              == unionFindRootOf (stepCapArc state innerLeft.length).links otherNode) = false
          rw [probeUntouched, linksEq,
            rootOf_twoJoinBlock state.links forest readLeftWire readRightWire state.nextFresh
              (unionFindRootOf state.links readLeftWire)
              (unionFindRootOf state.links readRightWire) rfl rfl rootNf
              (Nat.ne_of_gt readLeftRootBelow) otherNode]
          cases redirectGuard : (unionFindRootOf state.links readLeftWire
              == unionFindRootOf state.links otherNode
              || state.nextFresh == unionFindRootOf state.links otherNode) with
          | true =>
              show (unionFindRootOf state.links probe
                  == unionFindRootOf state.links readRightWire) = false
              exact natBeqFalseOfNe probeNeRightRoot
          | false => exact disjointBefore
  | _, _, _, _, .vcomp cellLower cellUpper, innerLeft, innerRight, state, prefixWires,
      domSegment, suffixWires, wellFormed, isTurnback, decomp, prefixLen, segLen => by
    obtain ⟨lowerTurnback, upperTurnback⟩ := boolBothTrueOfAndTrue isTurnback
    obtain ⟨pipeSegment, decompPipe, pipeLen, probeFactsLower⟩ :=
      arcCellSegmentRun_ofWellFormed cellLower innerLeft innerRight state prefixWires domSegment
        suffixWires wellFormed lowerTurnback decomp prefixLen segLen
    have wellFormedMid : WellFormedArcState (runArcCell state innerLeft innerRight cellLower) :=
      wellFormedArcState_runArcCell state innerLeft innerRight cellLower wellFormed
    obtain ⟨codSegment, decompCod, codLen, probeFactsUpper⟩ :=
      arcCellSegmentRun_ofWellFormed cellUpper innerLeft innerRight
        (runArcCell state innerLeft innerRight cellLower) prefixWires pipeSegment suffixWires
        wellFormedMid upperTurnback decompPipe prefixLen pipeLen
    refine ⟨codSegment, ?_, codLen, ?_⟩
    · rw [runArcCell_vcomp]; exact decompCod
    · intro probe probeRootBelow probeGuard
      obtain ⟨rootStableLower, disjointPipe, transportLower⟩ :=
        probeFactsLower probe probeRootBelow probeGuard
      have probeRootBelowMid :
          unionFindRootOf (runArcCell state innerLeft innerRight cellLower).links probe
            < (runArcCell state innerLeft innerRight cellLower).nextFresh := by
        rw [rootStableLower]
        exact Nat.lt_of_lt_of_le probeRootBelow
          (runArcCell_nextFresh_le state innerLeft innerRight cellLower)
      obtain ⟨rootStableUpper, disjointCod, transportUpper⟩ :=
        probeFactsUpper probe probeRootBelowMid disjointPipe
      refine ⟨?_, ?_, ?_⟩
      · rw [runArcCell_vcomp]; exact rootStableUpper.trans rootStableLower
      · rw [runArcCell_vcomp]; exact disjointCod
      · intro otherNode disjointBefore
        rw [runArcCell_vcomp]
        exact transportUpper otherNode (transportLower otherNode disjointBefore)
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodyDom bodyCod body, innerLeft,
      innerRight, state, prefixWires, domSegment, suffixWires, wellFormed, isTurnback, decomp,
      prefixLen, segLen => by
    have domLenSplit : domSegment.length = oneCell.length + bodyDom.length := by
      rw [segLen]
      exact ModalityPath.length_composePath oneCell bodyDom
    obtain ⟨oneSegment, bodyDomSegment, segSplit, oneSegLen⟩ :=
      natListSplitAtLength domSegment oneCell.length
        (by rw [domLenSplit]; exact Nat.le_add_right _ _)
    have bodyDomSegLen : bodyDomSegment.length = bodyDom.length := by
      have totalLen : oneSegment.length + bodyDomSegment.length
          = oneCell.length + bodyDom.length := by
        rw [← lengthAppend oneSegment bodyDomSegment, ← segSplit]
        exact domLenSplit
      rw [oneSegLen] at totalLen
      exact natAddLeftCancelSeg oneCell.length _ _ totalLen
    have decompShifted : state.openWires
        = (prefixWires ++ oneSegment) ++ (bodyDomSegment ++ suffixWires) := by
      rw [decomp, segSplit, natListAppendAssoc oneSegment bodyDomSegment suffixWires,
        ← natListAppendAssoc prefixWires oneSegment (bodyDomSegment ++ suffixWires)]
    have prefixLenShifted : (prefixWires ++ oneSegment).length
        = (composePath innerLeft oneCell).length := by
      rw [lengthAppend prefixWires oneSegment,
        ModalityPath.length_composePath innerLeft oneCell, prefixLen, oneSegLen]
    obtain ⟨codSegmentBody, decompCodBody, codBodyLen, probeFactsBody⟩ :=
      arcCellSegmentRun_ofWellFormed body (composePath innerLeft oneCell) innerRight state
        (prefixWires ++ oneSegment) bodyDomSegment suffixWires wellFormed isTurnback
        decompShifted prefixLenShifted bodyDomSegLen
    refine ⟨oneSegment ++ codSegmentBody, ?_, ?_, ?_⟩
    · show (runArcCell state (composePath innerLeft oneCell) innerRight body).openWires
        = prefixWires ++ ((oneSegment ++ codSegmentBody) ++ suffixWires)
      rw [decompCodBody, natListAppendAssoc prefixWires oneSegment
          (codSegmentBody ++ suffixWires),
        ← natListAppendAssoc oneSegment codSegmentBody suffixWires]
    · show (oneSegment ++ codSegmentBody).length = (composePath oneCell bodyCod).length
      rw [lengthAppend oneSegment codSegmentBody,
        ModalityPath.length_composePath oneCell bodyCod, oneSegLen, codBodyLen]
    · intro probe probeRootBelow probeGuard
      have probeGuardBody : arcProbeDisjointFromSegment state.links probe bodyDomSegment :=
        fun wire wireMem => probeGuard wire
          (by rw [segSplit]; exact natListMem_appendOfRight oneSegment bodyDomSegment wireMem)
      obtain ⟨rootStable, disjointCodBody, transport⟩ :=
        probeFactsBody probe probeRootBelow probeGuardBody
      refine ⟨rootStable, ?_, transport⟩
      intro wire wireMem
      cases natListMem_appendElim oneSegment codSegmentBody wireMem with
      | inl memberOne =>
          exact transport wire (probeGuard wire
            (by rw [segSplit]; exact natListMem_appendOfLeft oneSegment bodyDomSegment memberOne))
      | inr memberCod => exact disjointCodBody wire memberCod
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ bodyDom bodyCod oneCell body, innerLeft,
      innerRight, state, prefixWires, domSegment, suffixWires, wellFormed, isTurnback, decomp,
      prefixLen, segLen => by
    have domLenSplit : domSegment.length = bodyDom.length + oneCell.length := by
      rw [segLen]
      exact ModalityPath.length_composePath bodyDom oneCell
    obtain ⟨bodyDomSegment, oneSegment, segSplit, bodySegLen⟩ :=
      natListSplitAtLength domSegment bodyDom.length
        (by rw [domLenSplit]; exact Nat.le_add_right _ _)
    have oneSegLen : oneSegment.length = oneCell.length := by
      have totalLen : bodyDomSegment.length + oneSegment.length
          = bodyDom.length + oneCell.length := by
        rw [← lengthAppend bodyDomSegment oneSegment, ← segSplit]
        exact domLenSplit
      rw [bodySegLen] at totalLen
      exact natAddLeftCancelSeg bodyDom.length _ _ totalLen
    have decompShifted : state.openWires
        = prefixWires ++ (bodyDomSegment ++ (oneSegment ++ suffixWires)) := by
      rw [decomp, segSplit, natListAppendAssoc bodyDomSegment oneSegment suffixWires]
    obtain ⟨codSegmentBody, decompCodBody, codBodyLen, probeFactsBody⟩ :=
      arcCellSegmentRun_ofWellFormed body innerLeft (composePath oneCell innerRight) state
        prefixWires bodyDomSegment (oneSegment ++ suffixWires) wellFormed isTurnback
        decompShifted prefixLen bodySegLen
    refine ⟨codSegmentBody ++ oneSegment, ?_, ?_, ?_⟩
    · show (runArcCell state innerLeft (composePath oneCell innerRight) body).openWires
        = prefixWires ++ ((codSegmentBody ++ oneSegment) ++ suffixWires)
      rw [decompCodBody, ← natListAppendAssoc codSegmentBody oneSegment suffixWires]
    · show (codSegmentBody ++ oneSegment).length = (composePath bodyCod oneCell).length
      rw [lengthAppend codSegmentBody oneSegment,
        ModalityPath.length_composePath bodyCod oneCell, oneSegLen, codBodyLen]
    · intro probe probeRootBelow probeGuard
      have probeGuardBody : arcProbeDisjointFromSegment state.links probe bodyDomSegment :=
        fun wire wireMem => probeGuard wire
          (by rw [segSplit]; exact natListMem_appendOfLeft bodyDomSegment oneSegment wireMem)
      obtain ⟨rootStable, disjointCodBody, transport⟩ :=
        probeFactsBody probe probeRootBelow probeGuardBody
      refine ⟨rootStable, ?_, transport⟩
      intro wire wireMem
      cases natListMem_appendElim codSegmentBody oneSegment wireMem with
      | inl memberCod => exact disjointCodBody wire memberCod
      | inr memberOne =>
          exact transport wire (probeGuard wire
            (by rw [segSplit]; exact natListMem_appendOfRight bodyDomSegment oneSegment memberOne))

/-! ## Firing fixtures — a three-atom turnback cell at the walking adjunction -/

/-- The single-modality path `[left] : base -> tip`. -/
def leftOnlyPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip :=
  ModalityPath.cons AdjunctionModality.left
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)

/-- The single-modality path `[right] : tip -> base`. -/
def rightOnlyPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base :=
  ModalityPath.cons AdjunctionModality.right
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)

/-- The middle cup of the fixture: the unit whisker-shifted right by `leftThenRight` — a cup at
window-relative position `2` (`[l,r] => [l,r,l,r]`). -/
def whiskerShiftedUnitCell : RawTwoCellExpr adjunctionModeSignature adjunctionLeftThenRight
    (composePath adjunctionLeftThenRight adjunctionLeftThenRight) :=
  (RawTwoCellExpr.whiskerLeft adjunctionLeftThenRight
      (RawTwoCellExpr.gen AdjunctionTwoCell.unit : RawTwoCellExpr adjunctionModeSignature
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight)
    : RawTwoCellExpr adjunctionModeSignature
        (composePath adjunctionLeftThenRight
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
        (composePath adjunctionLeftThenRight adjunctionLeftThenRight))

/-- The closing cap of the fixture: the counit sandwiched between `[left]` and `[right]` — a cap
at window-relative position `1` (`[l,r,l,r] => [l,r]`). -/
def whiskerSandwichedCounitCell : RawTwoCellExpr adjunctionModeSignature
    (composePath adjunctionLeftThenRight adjunctionLeftThenRight) adjunctionLeftThenRight :=
  (RawTwoCellExpr.whiskerLeft leftOnlyPath
      ((RawTwoCellExpr.whiskerRight rightOnlyPath
          (RawTwoCellExpr.gen AdjunctionTwoCell.counit : RawTwoCellExpr adjunctionModeSignature
            adjunctionRightThenLeft
            (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
        : RawTwoCellExpr adjunctionModeSignature
            (composePath adjunctionRightThenLeft rightOnlyPath)
            (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
              rightOnlyPath)))
    : RawTwoCellExpr adjunctionModeSignature
        (composePath leftOnlyPath (composePath adjunctionRightThenLeft rightOnlyPath))
        (composePath leftOnlyPath
          (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
            rightOnlyPath)))

/-- ★ A THREE-atom turnback cell at the walking adjunction: unit, then a whisker-shifted unit,
then a whisker-sandwiched counit — `nil => [left,right]` through `[left,right,left,right]`.
Exercises `vcomp`, `whiskerLeft`, `whiskerRight`, cup AND cap in one fixture. -/
def threeAtomTurnbackCell : RawTwoCellExpr adjunctionModeSignature
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.gen AdjunctionTwoCell.unit)
    (RawTwoCellExpr.vcomp whiskerShiftedUnitCell whiskerSandwichedCounitCell)

/-- The fixture is turnback-only — every generator a cup or cap.  `rfl`. -/
theorem threeAtomTurnbackCell_isTurnbackOnly : threeAtomTurnbackCell.isTurnbackOnly = true := rfl

/-- The window seed for the fire: two prefix wires `[0, 1]`, empty window, fresh frontier `2`. -/
def arcSegmentFireSeedState : ArcWireState := ArcWireState.mk [0, 1] [] 2 0 [] []

/-- The fire seed is well-formed (fresh, forest, non-degenerate). -/
theorem arcSegmentFireSeedState_isWellFormed : WellFormedArcState arcSegmentFireSeedState :=
  ⟨by unfold ArcStateFresh arcSegmentFireSeedState; decide, trivial, by decide⟩

/-- ★ **The engine FIRED on the three-atom cell** — the segment action instantiated end to end:
running the fixture at window start `2` (left whisker `leftThenRight`, prefix `[0, 1]`) from the
fire seed yields SOME two-wire cod segment with the prefix byte-intact and full probe transport.
(The concrete openWires are pinned `rfl` below — this theorem exercises the GENERAL engine.) -/
theorem arcSegmentRun_firedOnThreeAtomCell :
    ∃ codSegment,
      (runArcCell arcSegmentFireSeedState adjunctionLeftThenRight
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
          threeAtomTurnbackCell).openWires
        = [0, 1] ++ (codSegment ++ [])
      ∧ codSegment.length = adjunctionLeftThenRight.length
      ∧ (∀ probe,
          unionFindRootOf arcSegmentFireSeedState.links probe
            < arcSegmentFireSeedState.nextFresh →
          arcProbeDisjointFromSegment arcSegmentFireSeedState.links probe [] →
          unionFindRootOf (runArcCell arcSegmentFireSeedState adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell).links probe
              = unionFindRootOf arcSegmentFireSeedState.links probe
            ∧ arcProbeDisjointFromSegment (runArcCell arcSegmentFireSeedState
                adjunctionLeftThenRight
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                threeAtomTurnbackCell).links probe codSegment
            ∧ (∀ otherNode,
                isSameComponent arcSegmentFireSeedState.links probe otherNode = false →
                isSameComponent (runArcCell arcSegmentFireSeedState adjunctionLeftThenRight
                    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                    threeAtomTurnbackCell).links probe otherNode = false)) :=
  arcCellSegmentRun_ofWellFormed threeAtomTurnbackCell adjunctionLeftThenRight
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) arcSegmentFireSeedState
    [0, 1] [] [] arcSegmentFireSeedState_isWellFormed threeAtomTurnbackCell_isTurnbackOnly
    rfl rfl rfl

/-- The concrete openWires after the three-atom run: prefix `[0, 1]` byte-intact, cod segment
`[2, 6]` — the outer cup's left leg and the inner cup's right leg survive; the sandwiched cap
consumed wires `3` and `5` (positions `3`/`4`, i.e. window-relative `1`/`2`).  The machine-checked
value the engine's ∃ names.  `rfl`. -/
theorem arcSegmentRun_threeAtomCell_openWires :
    (runArcCell arcSegmentFireSeedState adjunctionLeftThenRight
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        threeAtomTurnbackCell).openWires = [0, 1, 2, 6] := rfl

/-- The concrete probe transport, fired: probe `0` (root `0 < 2`, trivially guarded on the empty
window) keeps root `0` through all three atoms.  `rfl`. -/
theorem arcSegmentRun_threeAtomCell_probeRootStable :
    unionFindRootOf (runArcCell arcSegmentFireSeedState adjunctionLeftThenRight
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        threeAtomTurnbackCell).links 0 = 0 := rfl

/-- The concrete guard output, fired: probe `0` is component-disjoint from both surviving cod
wires (`2` and `6` root in the merged cup component, probe roots at `0`).  `rfl` pair. -/
theorem arcSegmentRun_threeAtomCell_probeDisjoint :
    isSameComponent (runArcCell arcSegmentFireSeedState adjunctionLeftThenRight
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        threeAtomTurnbackCell).links 0 2 = false
      ∧ isSameComponent (runArcCell arcSegmentFireSeedState adjunctionLeftThenRight
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        threeAtomTurnbackCell).links 0 6 = false :=
  ⟨rfl, rfl⟩

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the whole-cell segment-run engine + component-disjointness fold invariant
are SHIPPED.**  One structural induction gives the window decomposition transport, probe root
stability, the evolving-window guard (the r27-named CRUX: guard re-establishment through
intra-cell joins), and general disjointness transport — for every turnback-only cell, over the
`WellFormedArcState` bundle, fired on a three-atom cup/cup/cap cell with whiskers.  `= true`. -/
def fxMode_hasArcCellSegmentRunInvariant : Bool := true

/-- **Honesty pin — the whole-cell disjoint whisker-support target stays OPEN** (this file ships
the invariant engine, not the two-order swap).  `rfl`. -/
theorem arcCellWindowSegmentRun_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN.**  `rfl`. -/
theorem arcCellWindowSegmentRun_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN.**  `rfl`. -/
theorem arcCellWindowSegmentRun_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  `rfl`. -/
theorem arcCellWindowSegmentRun_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
