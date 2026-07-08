import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBlockRotate
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSigmaBundle

/-! # KEYSTONE4 leg 3 — the cross-order trace correspondence + the `componentComm` / `loopsEq` assembly

The two window-disjoint firing orders' union-find partitions are compared through their decoded arc traces
(`wiringArcEvents`, KEYSTONE3).  This file assembles the banked legs into the two order-swap fields of the
block-swap `MatchingComponentSim`:

  * ★ **`wiringDescCoreSwap_alphaTrace` / `wiringDescCoreSwap_betaTrace`** — each generator's trace over its
    BA-order state is the `sigma = blockRotate`-image of its trace over its AB-order state.  The INPUT-node halves
    come from the window-locality geometry (Fact A / Fact B) plus freshness-fixing (a fresh boundary wire is
    below the rotation window, so `blockRotate` fixes it); the OUTPUT-node halves from the fresh output-block
    images (B2); and `wiringArcEvents_map` (B1) folds the two node-list correspondences into the trace
    correspondence.
  * ★ **`wiringDescCoreSwap_componentComm`** — the ORDER-SWAP partition correspondence: reifying both orders'
    links as event folds over the SHARED base (`stepWiring_links_eq_applyJoinEvents` + `applyJoinEvents_append`),
    the BA fold is the block-swapped, `sigma`-renamed AB fold; the rename is invisible at the shared base
    (`componentView_ofFreshRename` through `componentView_applyJoinEvents`), and the block transposition is
    invisible to the partition (`componentView_applyJoinEvents_append_comm`) — the union-find join-order
    independence, the standing keystone claim, now DISCHARGED over the generic engine.  NON-VACUOUS: the
    partition genuinely separates non-connected boundary nodes (it is `diagram.partner`).
  * ★ **`wiringDescCoreSwap_loopsEq`** — the same chain at the cyclomatic (loop-count) level, via the
    UNCONDITIONAL loop reification `stepWiring_loops_eq` and the count-side block exchange
    (`countJoinEventLoops_append_comm`).

The two firings sit at HORIZONTALLY-DISJOINT windows within the open-wire list (`positionA + descA.inputCount ≤
positionB` and `positionB + descB.inputCount ≤ state.openWires.length`); the range discipline is exactly what the
window-locality geometry requires (the past-end degeneracy is refuted separately).  `state.links` is a forest
(the reachable-state invariant `stepWiring` preserves) and `0 < state.nextFresh` (the non-empty-boundary
condition, so `blockRotate` fixes the sentinel `0`).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local helpers -/

/-- The `List.range.loop` length, threaded (`List.length_range` leaks `propext`; reproved by hand). -/
private theorem rangeLoopLength_local :
    (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength_local count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count` (propext-free; the shipped copy is private elsewhere). -/
theorem rangeLength_local (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength_local count []]
  exact Nat.add_zero count

/-- Every element of a slice is bounded when every element of the source is. -/
theorem natListSliceAt_all_lt (bound : Nat) :
    (wires : List Nat) → (∀ wire ∈ wires, wire < bound) → (position count : Nat) →
    ∀ wire ∈ natListSliceAt wires position count, wire < bound
  | _, _, _, 0, wire, wireInSlice => by rw [sliceAt_count_zero] at wireInSlice; cases wireInSlice
  | [], _, _, _, wire, wireInSlice => by rw [sliceAt_nil] at wireInSlice; cases wireInSlice
  | headWire :: tailWires, allBelow, 0, count + 1, wire, wireInSlice => by
      rw [sliceAt_cons_zero_succ] at wireInSlice
      cases wireInSlice with
      | head => exact allBelow headWire (List.Mem.head tailWires)
      | tail _ tailMembership =>
          exact natListSliceAt_all_lt bound tailWires
            (fun innerWire innerMem => allBelow innerWire (List.Mem.tail headWire innerMem)) 0 count wire
            tailMembership
  | headWire :: tailWires, allBelow, position + 1, count, wire, wireInSlice => by
      rw [sliceAt_cons_succ] at wireInSlice
      exact natListSliceAt_all_lt bound tailWires
        (fun innerWire innerMem => allBelow innerWire (List.Mem.tail headWire innerMem)) position count wire
        wireInSlice

/-! ## The two per-block trace correspondences -/

/-- ★ **The alpha (`descA`) trace correspondence.**  `descA`'s trace over the BA-order state
(`stepWiring state positionB descB`) is the `blockRotate`-image of its trace over the shared state.  Its input
wires are the same (Fact A — `descA`'s window is left of `descB`'s, so a disjoint right splice does not touch it —
plus freshness-fixing), and its fresh output block shifts up by `descB.outputCount` (B2 first block). -/
theorem wiringDescCoreSwap_alphaTrace (state : WireState) (positionA positionB : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length) :
    wiringArcEvents (stepWiringInputNodes (stepWiring state positionB descB) positionA descA)
        (stepWiringOutputNodes (stepWiring state positionB descB) descA) descA.inputCount descA.arcs
      = (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
          descA.inputCount descA.arcs).map
          (fun event =>
            (blockRotate state.nextFresh descA.outputCount descB.outputCount event.1,
              blockRotate state.nextFresh descA.outputCount descB.outputCount event.2)) := by
  have sigmaFixesZero : blockRotate state.nextFresh descA.outputCount descB.outputCount 0 = 0 :=
    blockRotate_below state.nextFresh descA.outputCount descB.outputCount 0 nfPos
  have positionBInRange : positionB ≤ state.openWires.length :=
    Nat.le_trans (Nat.le_add_right positionB descB.inputCount) windowB
  -- input correspondence: Fact A (right splice) + freshness fix
  have inputEq : stepWiringInputNodes (stepWiring state positionB descB) positionA descA
      = (stepWiringInputNodes state positionA descA).map
          (blockRotate state.nextFresh descA.outputCount descB.outputCount) := by
    show natListSliceAt (stepWiring state positionB descB).openWires positionA descA.inputCount
        = (natListSliceAt state.openWires positionA descA.inputCount).map
            (blockRotate state.nextFresh descA.outputCount descB.outputCount)
    rw [show (stepWiring state positionB descB).openWires
          = natListInsertAt (natListRemoveManyAt state.openWires positionB descB.inputCount) positionB
              ((List.range descB.outputCount).map (· + state.nextFresh)) from rfl,
      natListSliceAt_spliceRight descB.inputCount ((List.range descB.outputCount).map (· + state.nextFresh))
        state.openWires descA.inputCount positionA positionB disjoint positionBInRange,
      mapFixedOn (blockRotate state.nextFresh descA.outputCount descB.outputCount)
        (natListSliceAt state.openWires positionA descA.inputCount)
        (fun wire wireInSlice =>
          blockRotate_below state.nextFresh descA.outputCount descB.outputCount wire
            (natListSliceAt_all_lt state.nextFresh state.openWires fresh.1 positionA descA.inputCount wire
              wireInSlice))]
  -- output correspondence: B2 first block
  have outputEq : stepWiringOutputNodes (stepWiring state positionB descB) descA
      = (stepWiringOutputNodes state descA).map
          (blockRotate state.nextFresh descA.outputCount descB.outputCount) := by
    show (List.range descA.outputCount).map (· + (stepWiring state positionB descB).nextFresh)
        = ((List.range descA.outputCount).map (· + state.nextFresh)).map
            (blockRotate state.nextFresh descA.outputCount descB.outputCount)
    rw [stepWiring_nextFresh state positionB descB,
      rangeMapAdd_map_blockRotate_first state.nextFresh descA.outputCount descB.outputCount
        (List.range descA.outputCount) (fun index indexMem => mem_range_imp_lt indexMem)]
  rw [inputEq, outputEq,
    wiringArcEvents_map (blockRotate state.nextFresh descA.outputCount descB.outputCount) sigmaFixesZero
      (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA) descA.inputCount
      descA.arcs]

/-- ★ **The beta (`descB`) trace correspondence.**  `descB`'s trace over the shared state is the
`blockRotate`-image of its trace over the AB-order state (`stepWiring state positionA descA`, at the shifted
window).  Its input wires are the same (Fact B — the left splice moves `descB`'s window but not what it reads —
plus freshness-fixing), and its fresh output block shifts down by `descA.outputCount` (B2 second block). -/
theorem wiringDescCoreSwap_betaTrace (state : WireState) (positionA positionB : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length) :
    wiringArcEvents (stepWiringInputNodes state positionB descB) (stepWiringOutputNodes state descB)
        descB.inputCount descB.arcs
      = (wiringArcEvents
            (stepWiringInputNodes (stepWiring state positionA descA)
              (positionB - descA.inputCount + descA.outputCount) descB)
            (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs).map
          (fun event =>
            (blockRotate state.nextFresh descA.outputCount descB.outputCount event.1,
              blockRotate state.nextFresh descA.outputCount descB.outputCount event.2)) := by
  have sigmaFixesZero : blockRotate state.nextFresh descA.outputCount descB.outputCount 0 = 0 :=
    blockRotate_below state.nextFresh descA.outputCount descB.outputCount 0 nfPos
  obtain ⟨extra, extraEq⟩ := Nat.le.dest disjoint
  -- posB' and positionB in terms of extra
  have blockLen : ((List.range descA.outputCount).map (· + state.nextFresh)).length = descA.outputCount := by
    rw [mapLength, rangeLength_local]
  have subEq : positionB - descA.inputCount = positionA + extra := by
    rw [← extraEq, Nat.add_right_comm positionA descA.inputCount extra,
      addSubCancelRight (positionA + extra) descA.inputCount]
  have shiftedPos : positionB - descA.inputCount + descA.outputCount
      = positionA + ((List.range descA.outputCount).map (· + state.nextFresh)).length + extra := by
    rw [subEq, blockLen, Nat.add_right_comm positionA extra descA.outputCount]
  have rangeFactB : positionA + descA.inputCount + extra + descB.inputCount ≤ state.openWires.length := by
    rw [extraEq]; exact windowB
  -- input correspondence: Fact B (left splice shift) + freshness fix
  have factB : stepWiringInputNodes (stepWiring state positionA descA)
        (positionB - descA.inputCount + descA.outputCount) descB
      = natListSliceAt state.openWires positionB descB.inputCount := by
    show natListSliceAt (stepWiring state positionA descA).openWires
          (positionB - descA.inputCount + descA.outputCount) descB.inputCount
        = natListSliceAt state.openWires positionB descB.inputCount
    rw [show (stepWiring state positionA descA).openWires
          = natListInsertAt (natListRemoveManyAt state.openWires positionA descA.inputCount) positionA
              ((List.range descA.outputCount).map (· + state.nextFresh)) from rfl,
      shiftedPos,
      natListSliceAt_spliceLeftShift descA.inputCount ((List.range descA.outputCount).map (· + state.nextFresh))
        state.openWires descB.inputCount positionA extra rangeFactB, extraEq]
  have inputEq : stepWiringInputNodes state positionB descB
      = (stepWiringInputNodes (stepWiring state positionA descA)
            (positionB - descA.inputCount + descA.outputCount) descB).map
          (blockRotate state.nextFresh descA.outputCount descB.outputCount) := by
    show natListSliceAt state.openWires positionB descB.inputCount
        = (stepWiringInputNodes (stepWiring state positionA descA)
            (positionB - descA.inputCount + descA.outputCount) descB).map
          (blockRotate state.nextFresh descA.outputCount descB.outputCount)
    rw [factB,
      mapFixedOn (blockRotate state.nextFresh descA.outputCount descB.outputCount)
        (natListSliceAt state.openWires positionB descB.inputCount)
        (fun wire wireInSlice =>
          blockRotate_below state.nextFresh descA.outputCount descB.outputCount wire
            (natListSliceAt_all_lt state.nextFresh state.openWires fresh.1 positionB descB.inputCount wire
              wireInSlice))]
  -- output correspondence: B2 second block
  have outputEq : stepWiringOutputNodes state descB
      = (stepWiringOutputNodes (stepWiring state positionA descA) descB).map
          (blockRotate state.nextFresh descA.outputCount descB.outputCount) := by
    show (List.range descB.outputCount).map (· + state.nextFresh)
        = ((List.range descB.outputCount).map (· + (stepWiring state positionA descA).nextFresh)).map
            (blockRotate state.nextFresh descA.outputCount descB.outputCount)
    rw [stepWiring_nextFresh state positionA descA,
      rangeMapAdd_map_blockRotate_second state.nextFresh descA.outputCount descB.outputCount
        (List.range descB.outputCount) (fun index indexMem => mem_range_imp_lt indexMem)]
  rw [inputEq, outputEq,
    wiringArcEvents_map (blockRotate state.nextFresh descA.outputCount descB.outputCount) sigmaFixesZero
      (stepWiringInputNodes (stepWiring state positionA descA)
        (positionB - descA.inputCount + descA.outputCount) descB)
      (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs]

/-! ## The order-swap partition correspondence -/

/-- ★ **The ORDER-SWAP `componentComm`: the two window-disjoint firing orders reach `sigma`-corresponding
union-find PARTITIONS.**  Reifying both orders' links as event folds over the SHARED base
(`stepWiring_links_eq_applyJoinEvents` + `applyJoinEvents_append`), the BA fold is the block-swapped,
`sigma`-renamed AB fold (the two trace correspondences + `listMapPairAppend`); the rename is invisible at the
shared base (`componentView_ofFreshRename` lifted by `componentView_applyJoinEvents`), and the block
transposition is invisible to the partition (`componentView_applyJoinEvents_append_comm`).  This is the union-find
join-order independence — the standing keystone claim — DISCHARGED over the generic `stepWiring` engine. -/
theorem wiringDescCoreSwap_componentComm (state : WireState) (positionA positionB : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length) :
    ∀ probeOne probeTwo,
      (unionFindRootOf (stepWiring (stepWiring state positionB descB) positionA descA).links
            (blockRotate state.nextFresh descA.outputCount descB.outputCount probeOne)
          == unionFindRootOf (stepWiring (stepWiring state positionB descB) positionA descA).links
            (blockRotate state.nextFresh descA.outputCount descB.outputCount probeTwo))
        = (unionFindRootOf (stepWiring (stepWiring state positionA descA)
              (positionB - descA.inputCount + descA.outputCount) descB).links probeOne
          == unionFindRootOf (stepWiring (stepWiring state positionA descA)
              (positionB - descA.inputCount + descA.outputCount) descB).links probeTwo) := by
  have baseCorrespondence : ∀ probeOne probeTwo : Nat,
      (unionFindRootOf state.links
            (blockRotate state.nextFresh descA.outputCount descB.outputCount probeOne)
          == unionFindRootOf state.links
            (blockRotate state.nextFresh descA.outputCount descB.outputCount probeTwo))
        = (unionFindRootOf state.links probeOne == unionFindRootOf state.links probeTwo) :=
    fun probeOne probeTwo =>
      componentView_ofFreshRename (blockRotate state.nextFresh descA.outputCount descB.outputCount)
        state.nextFresh state.links fresh.2
        (fun identifier idBelow =>
          blockRotate_below state.nextFresh descA.outputCount descB.outputCount identifier idBelow)
        (blockRotate_mapsAtOrAboveWithin state.nextFresh descA.outputCount descB.outputCount)
        (blockRotate_inj state.nextFresh descA.outputCount descB.outputCount) probeOne probeTwo
  have linksSEq : (stepWiring (stepWiring state positionA descA)
        (positionB - descA.inputCount + descA.outputCount) descB).links
      = applyJoinEvents
          (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
              descA.inputCount descA.arcs
            ++ wiringArcEvents
                (stepWiringInputNodes (stepWiring state positionA descA)
                  (positionB - descA.inputCount + descA.outputCount) descB)
                (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs)
          state.links := by
    rw [stepWiring_links_eq_applyJoinEvents (stepWiring state positionA descA)
        (positionB - descA.inputCount + descA.outputCount) descB,
      stepWiring_links_eq_applyJoinEvents state positionA descA,
      ← applyJoinEvents_append]
  have linksTEq : (stepWiring (stepWiring state positionB descB) positionA descA).links
      = applyJoinEvents
          ((wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA) (positionB - descA.inputCount + descA.outputCount) descB) (stepWiringOutputNodes (stepWiring state positionA descA) descB)
                descB.inputCount descB.arcs
              ++ wiringArcEvents (stepWiringInputNodes state positionA descA)
                  (stepWiringOutputNodes state descA) descA.inputCount descA.arcs).map
            (fun event =>
              (blockRotate state.nextFresh descA.outputCount descB.outputCount event.1,
                blockRotate state.nextFresh descA.outputCount descB.outputCount event.2)))
          state.links := by
    rw [stepWiring_links_eq_applyJoinEvents (stepWiring state positionB descB) positionA descA,
      stepWiring_links_eq_applyJoinEvents state positionB descB,
      ← applyJoinEvents_append,
      wiringDescCoreSwap_alphaTrace state positionA positionB descA descB fresh nfPos disjoint windowB,
      wiringDescCoreSwap_betaTrace state positionA positionB descA descB fresh nfPos disjoint windowB,
      ← listMapPairAppend (blockRotate state.nextFresh descA.outputCount descB.outputCount)
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA) (positionB - descA.inputCount + descA.outputCount) descB) (stepWiringOutputNodes (stepWiring state positionA descA) descB)
          descB.inputCount descB.arcs)
        (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
          descA.inputCount descA.arcs)]
  intro probeOne probeTwo
  rw [linksTEq, linksSEq,
    componentView_applyJoinEvents (blockRotate state.nextFresh descA.outputCount descB.outputCount)
      (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA) (positionB - descA.inputCount + descA.outputCount) descB) (stepWiringOutputNodes (stepWiring state positionA descA) descB)
          descB.inputCount descB.arcs
        ++ wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
            descA.inputCount descA.arcs)
      state.links state.links forest forest baseCorrespondence probeOne probeTwo]
  exact componentView_applyJoinEvents_append_comm
    (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA) (positionB - descA.inputCount + descA.outputCount) descB) (stepWiringOutputNodes (stepWiring state positionA descA) descB)
      descB.inputCount descB.arcs)
    (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
      descA.inputCount descA.arcs)
    state.links forest probeOne probeTwo

/-! ## The order-swap cyclomatic (loop-count) correspondence -/

/-- Regroup helper: `base + p + iP + q + iQ = base + (p + q) + (iP + iQ)`. -/
private theorem loopsRegroup (base pCount iP qCount iQ : Nat) :
    base + pCount + iP + qCount + iQ = base + (pCount + qCount) + (iP + iQ) := by
  rw [Nat.add_right_comm (base + pCount) iP qCount, ← Nat.add_assoc base pCount qCount,
    Nat.add_assoc (base + pCount + qCount) iP iQ]

/-- ★ **The ORDER-SWAP `loopsEq`: the two window-disjoint firing orders close the same number of loops.**  The
loop reification is UNCONDITIONAL (`stepWiring_loops_eq`, KEYSTONE3), so each order's loop total splits into the
two blocks' `countJoinEventLoops` over the shared base plus the internal loops; the block-swap count invariance
(`countJoinEventLoops_map_congr` over the base correspondence + `countJoinEventLoops_append_comm`) equates the two
totals, and the internal-loop sums commute. -/
theorem wiringDescCoreSwap_loopsEq (state : WireState) (positionA positionB : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length) :
    (stepWiring (stepWiring state positionB descB) positionA descA).loops
      = (stepWiring (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB).loops := by
  have baseCorrespondence : ∀ probeOne probeTwo : Nat,
      (unionFindRootOf state.links
            (blockRotate state.nextFresh descA.outputCount descB.outputCount probeOne)
          == unionFindRootOf state.links
            (blockRotate state.nextFresh descA.outputCount descB.outputCount probeTwo))
        = (unionFindRootOf state.links probeOne == unionFindRootOf state.links probeTwo) :=
    fun probeOne probeTwo =>
      componentView_ofFreshRename (blockRotate state.nextFresh descA.outputCount descB.outputCount)
        state.nextFresh state.links fresh.2
        (fun identifier idBelow =>
          blockRotate_below state.nextFresh descA.outputCount descB.outputCount identifier idBelow)
        (blockRotate_mapsAtOrAboveWithin state.nextFresh descA.outputCount descB.outputCount)
        (blockRotate_inj state.nextFresh descA.outputCount descB.outputCount) probeOne probeTwo
  -- the cross-order loop-block equality (append + map-congr + append-comm over the shared base)
  have cntEq : countJoinEventLoops
        (wiringArcEvents (stepWiringInputNodes state positionB descB) (stepWiringOutputNodes state descB)
          descB.inputCount descB.arcs) state.links
      + countJoinEventLoops
          (wiringArcEvents (stepWiringInputNodes (stepWiring state positionB descB) positionA descA)
            (stepWiringOutputNodes (stepWiring state positionB descB) descA) descA.inputCount descA.arcs)
          (applyJoinEvents
            (wiringArcEvents (stepWiringInputNodes state positionB descB) (stepWiringOutputNodes state descB)
              descB.inputCount descB.arcs) state.links)
      = countJoinEventLoops
          (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
            descA.inputCount descA.arcs) state.links
        + countJoinEventLoops
            (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA)
              (positionB - descA.inputCount + descA.outputCount) descB)
              (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs)
            (applyJoinEvents
              (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
                descA.inputCount descA.arcs) state.links) := by
    rw [← countJoinEventLoops_append
        (wiringArcEvents (stepWiringInputNodes state positionB descB) (stepWiringOutputNodes state descB)
          descB.inputCount descB.arcs)
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionB descB) positionA descA)
          (stepWiringOutputNodes (stepWiring state positionB descB) descA) descA.inputCount descA.arcs)
        state.links,
      wiringDescCoreSwap_betaTrace state positionA positionB descA descB fresh nfPos disjoint windowB,
      wiringDescCoreSwap_alphaTrace state positionA positionB descA descB fresh nfPos disjoint windowB,
      ← listMapPairAppend (blockRotate state.nextFresh descA.outputCount descB.outputCount)
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
          (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs)
        (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
          descA.inputCount descA.arcs),
      countJoinEventLoops_map_congr (blockRotate state.nextFresh descA.outputCount descB.outputCount)
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA)
            (positionB - descA.inputCount + descA.outputCount) descB)
            (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs
          ++ wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
              descA.inputCount descA.arcs)
        state.links state.links forest forest baseCorrespondence,
      countJoinEventLoops_append_comm
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
          (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs)
        (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
          descA.inputCount descA.arcs)
        state.links forest,
      countJoinEventLoops_append
        (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
          descA.inputCount descA.arcs)
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
          (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs)
        state.links]
  rw [stepWiring_loops_eq (stepWiring state positionB descB) positionA descA,
    stepWiring_loops_eq state positionB descB,
    stepWiring_links_eq_applyJoinEvents state positionB descB,
    stepWiring_loops_eq (stepWiring state positionA descA)
      (positionB - descA.inputCount + descA.outputCount) descB,
    stepWiring_loops_eq state positionA descA,
    stepWiring_links_eq_applyJoinEvents state positionA descA,
    loopsRegroup state.loops
      (countJoinEventLoops
        (wiringArcEvents (stepWiringInputNodes state positionB descB) (stepWiringOutputNodes state descB)
          descB.inputCount descB.arcs) state.links)
      descB.internalLoops
      (countJoinEventLoops
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionB descB) positionA descA)
          (stepWiringOutputNodes (stepWiring state positionB descB) descA) descA.inputCount descA.arcs)
        (applyJoinEvents
          (wiringArcEvents (stepWiringInputNodes state positionB descB) (stepWiringOutputNodes state descB)
            descB.inputCount descB.arcs) state.links))
      descA.internalLoops,
    loopsRegroup state.loops
      (countJoinEventLoops
        (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
          descA.inputCount descA.arcs) state.links)
      descA.internalLoops
      (countJoinEventLoops
        (wiringArcEvents (stepWiringInputNodes (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
          (stepWiringOutputNodes (stepWiring state positionA descA) descB) descB.inputCount descB.arcs)
        (applyJoinEvents
          (wiringArcEvents (stepWiringInputNodes state positionA descA) (stepWiringOutputNodes state descA)
            descA.inputCount descA.arcs) state.links))
      descB.internalLoops,
    cntEq, Nat.add_comm descB.internalLoops descA.internalLoops]

/-! ## Honesty markers -/

/-- **Honesty marker — the two per-block cross-order trace correspondences are SHIPPED.**
`wiringDescCoreSwap_alphaTrace` / `wiringDescCoreSwap_betaTrace`: each generator's BA-order trace is the
`blockRotate`-image of its AB-order trace, assembled from the window-locality geometry (Fact A / Fact B), the
freshness-fixing of boundary wires, the fresh output-block images (B2), and `wiringArcEvents_map` (B1).  These
drive the order-swap `componentComm` / `loopsEq`.  `= true`. -/
def fxBrauer_hasWiringDescCoreSwapTraces : Bool := true

/-- **Honesty marker — the two ORDER-SWAP `MatchingComponentSim` fields are DISCHARGED over the generic engine.**
`wiringDescCoreSwap_componentComm` proves the union-find join-order independence — the two window-disjoint firing
orders reach `blockRotate`-corresponding PARTITIONS (the standing keystone claim, NON-VACUOUS: the partition is
`diagram.partner`, separating non-connected boundary nodes) — and `wiringDescCoreSwap_loopsEq` the cyclomatic
(loop-count) invariance, both from the reification (`stepWiring_links_eq_applyJoinEvents` /
`stepWiring_loops_eq`) + the block-exchange kit over the shared base.  Under a window-in-range discipline (the
past-end degeneracy is refuted separately) and forest / non-empty-boundary hypotheses.  What remains for the full
`MatchingComponentSim` bundle + the flag flip: the `openMap` four-zone wire-bookkeeping field.  `= true`. -/
def fxBrauer_hasWiringDescCoreSwapOrderSwap : Bool := true

end FX1Poly.Polygraph
