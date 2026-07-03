import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSimInRange

/-! # mode-3 — the counter-shift simulation (the empty-boundary proxy bridge)

The empty-boundary capstone does NOT need the sigma-bundle relaxed to a zero counter.  The
route is a PROXY: the canonical initial state at the empty boundary is `⟨[], [], 0, 0⟩`, where
`nfPos` fails — but the state `⟨[], [], 1, 0⟩` differs only in the fresh counter, satisfies the
FULL conditions package, and the boundary-disciplined trace invariance applies at it verbatim.
What remains is the BRIDGE: the run from the zero-counter seed and the run from the one-counter
seed extract identically, because they are related by the fresh shift `freshShiftAbove 0 1`
(every id one higher on the proxy side).

The wire view of that shift is already banked (`stepAtom_wireView_freshShift`).  This file
ships the LINKS/LOOPS half and the read-off:

  * `MatchingShiftSim` — the counter-OFFSET clone of `MatchingComponentSim`: wires are
    shift-images, the counter runs `delta` ahead (`MatchingComponentSim`'s `nfEq` becomes
    `nfShift` — the component sim is counter-preserving, the shift sim is counter-offset);
  * `stepCup_componentComm_ofShift` — the cup's fresh legs land `delta` higher on the proxy
    side, which is exactly their shift-image (`componentView_unionFindJoin` is rename-generic);
    the cap arm and the loops leg REUSE the sentinel-free in-range clones verbatim (they are
    rename-generic already);
  * `matchingShiftSim_step_ofInRange` / `matchingShiftSim_processSpine_ofBoundaryDiscipline` —
    step stability and the boundary-disciplined fold;
  * `extractDiagram_zeroBoundary_ofShiftSim` — at the EMPTY bottom boundary the rename-relation
    read-off has no boundary ids to fix, so the shift (which moves EVERY id, including `0`)
    feeds `extractDiagram_of_matchingComponentRenameRel` directly;
  * ★ `extractAfterProcessing_emptyBoundary_counterShift` — the payoff: a chained,
    cup/cap-disciplined spine extracts identically from `⟨[], [], 0, 0⟩` and `⟨[], [], 1, 0⟩`.

What remains for the empty-boundary capstone: chain this bridge (on both trace-equivalent
spines) with the boundary-disciplined invariance at the proxy seed — the next brick.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat boolean-equality successor congruence (hand-rolled; Nat's `==` is `decide`-based) -/

private theorem natBeqSuccCongr (a b : Nat) : ((a + 1 == b + 1) = (a == b)) := by
  cases Nat.decEq a b with
  | isTrue areEqual =>
      rw [areEqual]
      exact (decide_eq_true rfl).trans (decide_eq_true rfl).symm
  | isFalse notEqual =>
      exact (decide_eq_false (fun succEq => notEqual (Nat.succ.inj succEq))).trans
        (decide_eq_false notEqual).symm

/-! ## The counter-offset simulation invariant -/

/-- **The counter-shift simulation invariant** — the counter-OFFSET clone of
`MatchingComponentSim`: the proxy state's wires are `freshShiftAbove`-images of the base
state's, its counter runs exactly `delta` ahead, and the partition view / loop count / forest
structure correspond under the shift.  Unlike the component sim (built for the block swap,
where both orders end at the SAME counter), the shift sim relates a run to the SAME run seeded
at a higher counter — the empty-boundary proxy. -/
structure MatchingShiftSim (threshold delta : Nat) (stateS stateT : WireState) : Prop where
  /-- The proxy wires are pointwise shift-images. -/
  openMap : stateT.openWires = stateS.openWires.map (freshShiftAbove threshold delta)
  /-- The proxy counter runs exactly `delta` ahead. -/
  nfShift : stateT.nextFresh = stateS.nextFresh + delta
  /-- The same-component booleans correspond under the shift. -/
  componentComm : ∀ a b,
    (unionFindRootOf stateT.links (freshShiftAbove threshold delta a)
        == unionFindRootOf stateT.links (freshShiftAbove threshold delta b))
      = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b)
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The base links form a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The proxy links form a forest. -/
  forestT : isUnionFindForest stateT.links

/-! ## Step preservation -/

/-- A CUP step preserves the shifted component view: the base joins its fresh legs
`nfS, nfS + 1`; the proxy joins `nfS + delta, nfS + delta + 1` — exactly the legs' shift-images
(both at-or-above the threshold), carried by the rename-generic `componentView_unionFindJoin`. -/
theorem stepCup_componentComm_ofShift (threshold delta : Nat) (stateS stateT : WireState)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (freshShifted : stateT.nextFresh = stateS.nextFresh + delta)
    (thresholdLe : threshold ≤ stateS.nextFresh)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (freshShiftAbove threshold delta a)
          == unionFindRootOf stateT.links (freshShiftAbove threshold delta b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (position : Nat) (a b : Nat) :
    (unionFindRootOf (stepCup stateT position).links (freshShiftAbove threshold delta a)
        == unionFindRootOf (stepCup stateT position).links (freshShiftAbove threshold delta b))
      = (unionFindRootOf (stepCup stateS position).links a
        == unionFindRootOf (stepCup stateS position).links b) := by
  have legZero : stateT.nextFresh = freshShiftAbove threshold delta stateS.nextFresh := by
    rw [freshShiftAbove_ofLe threshold delta stateS.nextFresh thresholdLe, freshShifted]
  have legOne : stateT.nextFresh + 1
      = freshShiftAbove threshold delta (stateS.nextFresh + 1) := by
    rw [freshShiftAbove_ofLe threshold delta (stateS.nextFresh + 1)
        (Nat.le_succ_of_le thresholdLe),
      freshShifted, Nat.add_right_comm stateS.nextFresh delta 1]
  show (unionFindRootOf (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
          (freshShiftAbove threshold delta a)
        == unionFindRootOf (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
          (freshShiftAbove threshold delta b))
      = (unionFindRootOf (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1)) a
        == unionFindRootOf (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
          b)
  rw [legOne, legZero]
  exact componentView_unionFindJoin (freshShiftAbove threshold delta) stateS.links stateT.links
    forestS forestT stateS.nextFresh (stateS.nextFresh + 1) componentComm a b

/-- **Shifted component-view step-preservation (dispatched).**  Cup via the shift-leg lemma;
the cap's two in-range reads commute with the shift (`natListGetAt_map_inRange`) and feed the
rename-generic `stepCap_componentComm` verbatim. -/
theorem stepAtom_componentComm_ofShift {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (threshold delta : Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ stateS.openWires.length)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (freshShifted : stateT.nextFresh = stateS.nextFresh + delta)
    (thresholdLe : threshold ≤ stateS.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map (freshShiftAbove threshold delta))
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (freshShiftAbove threshold delta a)
          == unionFindRootOf stateT.links (freshShiftAbove threshold delta b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (a b : Nat) :
    (unionFindRootOf (stepAtom stateT atom).links (freshShiftAbove threshold delta a)
        == unionFindRootOf (stepAtom stateT atom).links (freshShiftAbove threshold delta b))
      = (unionFindRootOf (stepAtom stateS atom).links a
        == unionFindRootOf (stepAtom stateS atom).links b) := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateT atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateS atom cupArity.1 cupArity.2]
      exact stepCup_componentComm_ofShift threshold delta stateS stateT forestS forestT
        freshShifted thresholdLe componentComm atom.leftContext.length a b
  | inr capArity =>
      rw [capArity.1] at windowInRange
      have posSuccInRange : atom.leftContext.length + 1 < stateS.openWires.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1)) windowInRange
      have posInRange : atom.leftContext.length < stateS.openWires.length :=
        Nat.lt_of_le_of_lt (Nat.le_succ atom.leftContext.length) posSuccInRange
      have hleftCorr : natListGetAt stateT.openWires atom.leftContext.length
          = freshShiftAbove threshold delta
              (natListGetAt stateS.openWires atom.leftContext.length) := by
        rw [openMap]
        exact natListGetAt_map_inRange (freshShiftAbove threshold delta) stateS.openWires
          atom.leftContext.length posInRange
      have hrightCorr : natListGetAt stateT.openWires (atom.leftContext.length + 1)
          = freshShiftAbove threshold delta
              (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
        rw [openMap]
        exact natListGetAt_map_inRange (freshShiftAbove threshold delta) stateS.openWires
          (atom.leftContext.length + 1) posSuccInRange
      rw [stepAtom_ofCapArity stateT atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateS atom capArity.1 capArity.2]
      exact stepCap_componentComm (freshShiftAbove threshold delta) stateS stateT forestS
        forestT componentComm atom.leftContext.length hleftCorr hrightCorr a b

/-! ## Step stability and the boundary-disciplined fold -/

/-- ★ **The shift sim is step-stable from the window range.**  The wire view is the banked
`stepAtom_wireView_freshShift`; the component view is the shift dispatch above; the loops leg
REUSES the rename-generic sentinel-free `stepAtom_loopsEq_ofInRange` verbatim. -/
theorem matchingShiftSim_step_ofInRange {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (threshold delta : Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ stateS.openWires.length)
    (thresholdLe : threshold ≤ stateS.nextFresh)
    (sim : MatchingShiftSim threshold delta stateS stateT) :
    MatchingShiftSim threshold delta (stepAtom stateS atom) (stepAtom stateT atom) where
  openMap := (stepAtom_wireView_freshShift threshold delta stateS stateT atom arity sim.openMap
    sim.nfShift thresholdLe).1
  nfShift := (stepAtom_wireView_freshShift threshold delta stateS stateT atom arity sim.openMap
    sim.nfShift thresholdLe).2
  componentComm := stepAtom_componentComm_ofShift threshold delta stateS stateT atom arity
    windowInRange sim.forestS sim.forestT sim.nfShift thresholdLe sim.openMap sim.componentComm
  loopsEq := stepAtom_loopsEq_ofInRange (freshShiftAbove threshold delta) stateS stateT atom
    arity windowInRange sim.openMap sim.componentComm sim.loopsEq
  forestS := isUnionFindForest_stepAtom stateS atom sim.forestS
  forestT := isUnionFindForest_stepAtom stateT atom sim.forestT

/-- ★ **The shift sim folds under the boundary discipline** — chain + arity + tracking thread
exactly as in the sentinel-free component fold; the threshold bound survives by counter
monotonicity. -/
theorem matchingShiftSim_processSpine_ofBoundaryDiscipline {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (threshold delta : Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (stateS stateT : WireState) → (boundaryLength : Nat) →
    SpineBoundaryChained boundaryLength atoms →
    SpineHasCupCapAtoms atoms →
    stateS.openWires.length = boundaryLength →
    threshold ≤ stateS.nextFresh →
    MatchingShiftSim threshold delta stateS stateT →
    MatchingShiftSim threshold delta (processSpine stateS atoms) (processSpine stateT atoms)
  | [], _, _, _, _, _, _, _, sim => sim
  | atom :: rest, stateS, stateT, boundaryLength, chained, arity, tracks, thresholdLe, sim => by
      show MatchingShiftSim threshold delta (processSpine (stepAtom stateS atom) rest)
        (processSpine (stepAtom stateT atom) rest)
      have headAndTail := spineBoundaryChained_tail chained
      have arityParts := spineHasCupCapAtoms_tail arity
      have windowInRange : atom.leftContext.length + atom.generatorDom.length
          ≤ stateS.openWires.length := by
        rw [tracks, ← headAndTail.1]
        exact Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
          atom.rightContext.length
      exact matchingShiftSim_processSpine_ofBoundaryDiscipline threshold delta rest
        (stepAtom stateS atom) (stepAtom stateT atom) atom.codBoundaryLength
        headAndTail.2 arityParts.2
        (stepAtom_openWires_tracksBoundary stateS atom arityParts.1
          (tracks.trans headAndTail.1.symm))
        (Nat.le_trans thresholdLe (stepAtom_nextFresh_le stateS atom))
        (matchingShiftSim_step_ofInRange threshold delta stateS stateT atom arityParts.1
          windowInRange thresholdLe sim)

/-! ## The zero-boundary read-off and the payoff bridge -/

/-- **At the EMPTY bottom boundary, shift-simulated states extract identically.**  With
`bottomCount = 0` there are no boundary ids to fix, the boundary-node list IS the wire list,
and every read is in range — so the shift (which moves EVERY id, including the id `0` that no
`sigma 0 = 0` sentinel could tolerate) feeds the rename-relation read-off directly. -/
theorem extractDiagram_zeroBoundary_ofShiftSim (threshold delta : Nat)
    (stateS stateT : WireState) (sim : MatchingShiftSim threshold delta stateS stateT) :
    extractDiagram 0 stateS = extractDiagram 0 stateT :=
  extractDiagram_of_matchingComponentRenameRel 0 (freshShiftAbove threshold delta) stateS
    stateT
    { lengthEq := by rw [sim.openMap, mapLength]
      loopsEq := sim.loopsEq
      bnodeCorr := by
        intro index indexInRange
        show natListGetAt stateT.openWires index
          = freshShiftAbove threshold delta (natListGetAt stateS.openWires index)
        rw [sim.openMap]
        exact natListGetAt_map_inRange (freshShiftAbove threshold delta) stateS.openWires
          index
          (by
            show index < stateS.openWires.length
            rw [← Nat.zero_add stateS.openWires.length]
            exact indexInRange)
      componentComm := sim.componentComm }

/-- ★ **The empty-boundary counter-shift bridge.**  A chained, cup/cap-disciplined spine
extracts identically from the DEGENERATE canonical seed `⟨[], [], 0, 0⟩` (where `nfPos` fails)
and the PROXY seed `⟨[], [], 1, 0⟩` (where the full conditions package holds): the two runs are
shift-simulated by `freshShiftAbove 0 1` from the base pair — empty wires, empty links, counter
one ahead, and the empty-links component view survives the everywhere-shift because roots of
empty links are the nodes themselves and boolean equality is successor-invariant. -/
theorem extractAfterProcessing_emptyBoundary_counterShift {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (chained : SpineBoundaryChained 0 atoms)
    (arity : SpineHasCupCapAtoms atoms) :
    extractAfterProcessing 0 { openWires := [], links := [], nextFresh := 0, loops := 0 } atoms
      = extractAfterProcessing 0 { openWires := [], links := [], nextFresh := 1, loops := 0 }
          atoms :=
  extractDiagram_zeroBoundary_ofShiftSim 0 1 _ _
    (matchingShiftSim_processSpine_ofBoundaryDiscipline 0 1 atoms
      { openWires := [], links := [], nextFresh := 0, loops := 0 }
      { openWires := [], links := [], nextFresh := 1, loops := 0 }
      0 chained arity rfl (Nat.le_refl 0)
      { openMap := rfl
        nfShift := rfl
        componentComm := fun a b => by
          rw [freshShiftAbove_ofLe 0 1 a (Nat.zero_le a),
            freshShiftAbove_ofLe 0 1 b (Nat.zero_le b)]
          exact natBeqSuccCongr a b
        loopsEq := rfl
        forestS := True.intro
        forestT := True.intro })

/-! ## Honesty marker -/

/-- **Honesty marker — the empty-boundary counter-shift bridge is SHIPPED.**  The counter-offset
simulation (`MatchingShiftSim`, wires shift-imaged + counter `delta` ahead) is step-stable and
folds under the boundary discipline (reusing the banked wire-view equivariance and the
rename-generic sentinel-free cap/loops legs), reads off to extract equality at the empty bottom
boundary, and yields `extractAfterProcessing_emptyBoundary_counterShift`: disciplined spines
extract identically from `⟨[], [], 0, 0⟩` and `⟨[], [], 1, 0⟩`.  This makes the sigma-bundle's
`nfPos` premise moot at the empty boundary — the degenerate seed is exchanged for the proxy
seed where the full conditions hold.  NOT yet covered: the empty-boundary soundness capstone
itself (proxy conditions + chain/arity transport along the trace equivalence + the three-step
chain through the proxy) — the next brick.  `= true`. -/
def fxMode_hasEmptyBoundaryCounterShiftBridge : Bool := true

end FX1Poly.Polygraph
