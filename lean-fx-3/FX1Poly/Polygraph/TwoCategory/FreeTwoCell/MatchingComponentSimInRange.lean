import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline

/-! # mode-3 — the SENTINEL-FREE component simulation (the empty-boundary substrate)

The shipped component-sim chain (`matchingComponentSim_step` / `_processSpine` /
`matchingComponentRenameRel_of_matchingComponentSim` / `_full_of_coreSim`) threads the cap-read
sentinel `sigma 0 = 0` through every window read (`natListGetAt_map`'s out-of-range arm defaults
to `0`, so the rename must fix it).  At the EMPTY source boundary that sentinel is
unsatisfiable: the initial state is `⟨[], [], 0, 0⟩`, fresh ids start at `0`, and the block-swap
rotation `blockRotate 0 wA wB` MUST move `0`.  What makes the sentinel moot is the boundary
discipline shipped in `SpineBoundaryChain` / `SpineArityDiscipline`: every read of a chained,
tracked, cup/cap-disciplined spine is IN RANGE, where `natListGetAt_map_inRange` commutes reads
with the rename unconditionally.

This file clones the component-sim chain sentinel-free:

  * `stepAtom_componentComm_ofInRange` / `stepAtom_loopsEq_ofInRange` — the two read sites,
    arity-dispatched (cup needs no reads; the cap's two reads are in range from the window
    premise);
  * `matchingComponentSim_step_ofInRange` — the six-field invariant is step-stable given the
    window range instead of the sentinel;
  * `matchingComponentSim_processSpine_ofBoundaryDiscipline` — the fold, threading the boundary
    chain + arity discipline + `openWires.length`-tracking exactly as the boundary-disciplined
    trace induction does;
  * `matchingComponentRenameRel_of_matchingComponentSim_ofInRange` — the rename-relation
    read-off (its `bnodeCorr` premise is ALREADY range-bounded, so the sentinel was never
    needed there);
  * `matchingComponentRenameRel_ofCoreSim_boundaryDiscipline` — the sentinel-free suffix peel
    over any chained, disciplined, tracked atom list.

What remains for the empty-boundary capstone: the sigma-bundle witness at a possibly-zero
shared counter (the `blockRotate` fixing conjuncts lose the `sigma 0 = 0` leg) and the
weak-conditions trace induction consuming this chain — the next bricks.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## List-length helpers (hand-rolled; core `List.length_append` / `List.length_range` leak) -/

private theorem natListAppendLength : (front back : List Nat) →
    (front ++ back).length = front.length + back.length
  | [], back => (Nat.zero_add back.length).symm
  | head :: tail, back => by
      show (tail ++ back).length + 1 = tail.length + 1 + back.length
      rw [natListAppendLength tail back,
        Nat.add_right_comm tail.length back.length 1]

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

/-! ## The two read sites, sentinel-free -/

/-- **Component-view step-preservation from the window range** — the sentinel-free clone of
`stepAtom_componentComm`: a cup needs no reads (`stepCup_componentComm` as-is); the cap's two
window reads are IN RANGE from the window premise, so `natListGetAt_map_inRange` commutes them
with the rename without any fixed sentinel. -/
theorem stepAtom_componentComm_ofInRange {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ stateS.openWires.length)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (a b : Nat) :
    (unionFindRootOf (stepAtom stateT atom).links (sigma a)
        == unionFindRootOf (stepAtom stateT atom).links (sigma b))
      = (unionFindRootOf (stepAtom stateS atom).links a
        == unionFindRootOf (stepAtom stateS atom).links b) := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateT atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateS atom cupArity.1 cupArity.2]
      exact stepCup_componentComm sigma stateS stateT forestS forestT nfEq fixesAbove
        componentComm atom.leftContext.length a b
  | inr capArity =>
      rw [capArity.1] at windowInRange
      have posSuccInRange : atom.leftContext.length + 1 < stateS.openWires.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1)) windowInRange
      have posInRange : atom.leftContext.length < stateS.openWires.length :=
        Nat.lt_of_le_of_lt (Nat.le_succ atom.leftContext.length) posSuccInRange
      have hleftCorr : natListGetAt stateT.openWires atom.leftContext.length
          = sigma (natListGetAt stateS.openWires atom.leftContext.length) := by
        rw [openMap]
        exact natListGetAt_map_inRange sigma stateS.openWires atom.leftContext.length
          posInRange
      have hrightCorr : natListGetAt stateT.openWires (atom.leftContext.length + 1)
          = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
        rw [openMap]
        exact natListGetAt_map_inRange sigma stateS.openWires (atom.leftContext.length + 1)
          posSuccInRange
      rw [stepAtom_ofCapArity stateT atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateS atom capArity.1 capArity.2]
      exact stepCap_componentComm sigma stateS stateT forestS forestT componentComm
        atom.leftContext.length hleftCorr hrightCorr a b

/-- **Loop-count step-preservation from the window range** — the sentinel-free clone of
`stepAtom_loopsEq_ofComponentView`: cup leaves loops untouched; the cap's increment condition
agrees on both states through the two in-range reads and the component view. -/
theorem stepAtom_loopsEq_ofInRange {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ stateS.openWires.length)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (hloops : stateT.loops = stateS.loops) :
    (stepAtom stateT atom).loops = (stepAtom stateS atom).loops := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateT atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateS atom cupArity.1 cupArity.2,
        stepCup_loops, stepCup_loops]
      exact hloops
  | inr capArity =>
      rw [capArity.1] at windowInRange
      have posSuccInRange : atom.leftContext.length + 1 < stateS.openWires.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1)) windowInRange
      have posInRange : atom.leftContext.length < stateS.openWires.length :=
        Nat.lt_of_le_of_lt (Nat.le_succ atom.leftContext.length) posSuccInRange
      have hleftCorr : natListGetAt stateT.openWires atom.leftContext.length
          = sigma (natListGetAt stateS.openWires atom.leftContext.length) := by
        rw [openMap]
        exact natListGetAt_map_inRange sigma stateS.openWires atom.leftContext.length
          posInRange
      have hrightCorr : natListGetAt stateT.openWires (atom.leftContext.length + 1)
          = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
        rw [openMap]
        exact natListGetAt_map_inRange sigma stateS.openWires (atom.leftContext.length + 1)
          posSuccInRange
      rw [stepAtom_ofCapArity stateT atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateS atom capArity.1 capArity.2,
        stepCap_loops, stepCap_loops]
      have hsc : isSameComponent stateT.links
            (natListGetAt stateT.openWires atom.leftContext.length)
            (natListGetAt stateT.openWires (atom.leftContext.length + 1))
          = isSameComponent stateS.links
            (natListGetAt stateS.openWires atom.leftContext.length)
            (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
        show (unionFindRootOf stateT.links
                (natListGetAt stateT.openWires atom.leftContext.length)
              == unionFindRootOf stateT.links
                (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
           = (unionFindRootOf stateS.links
                (natListGetAt stateS.openWires atom.leftContext.length)
              == unionFindRootOf stateS.links
                (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
        rw [hleftCorr, hrightCorr]
        exact componentComm (natListGetAt stateS.openWires atom.leftContext.length)
          (natListGetAt stateS.openWires (atom.leftContext.length + 1))
      rw [hsc, hloops]

/-! ## The sentinel-free step and fold -/

/-- ★ **The component-level invariant is step-stable from the window range** — the sentinel-free
clone of `matchingComponentSim_step`: the cup/cap arity and the in-range window replace
`sigma 0 = 0`. -/
theorem matchingComponentSim_step_ofInRange {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ stateS.openWires.length)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : MatchingComponentSim sigma stateS stateT) :
    MatchingComponentSim sigma (stepAtom stateS atom) (stepAtom stateT atom) where
  openMap := stepAtom_openWires_map sigma stateS stateT atom sim.openMap sim.nfEq fixesAbove
  nfEq := stepAtom_nextFresh_eq stateS stateT atom sim.nfEq
  componentComm := stepAtom_componentComm_ofInRange sigma stateS stateT atom arity
    windowInRange sim.forestS sim.forestT sim.nfEq sim.openMap fixesAbove sim.componentComm
  loopsEq := stepAtom_loopsEq_ofInRange sigma stateS stateT atom arity windowInRange
    sim.openMap sim.componentComm sim.loopsEq
  forestS := isUnionFindForest_stepAtom stateS atom sim.forestS
  forestT := isUnionFindForest_stepAtom stateT atom sim.forestT

/-- ★ **The component-level invariant folds under the boundary discipline** — the sentinel-free
clone of `matchingComponentSim_processSpine`: the boundary chain pins each atom's firing width
to the tracked `openWires.length` (the right whisker context as slack gives the window range),
the arity discipline supplies the cup/cap dispatch, and the state tracking steps by
`stepAtom_openWires_tracksBoundary`. -/
theorem matchingComponentSim_processSpine_ofBoundaryDiscipline {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (stateS stateT : WireState) → (boundaryLength : Nat) →
    SpineBoundaryChained boundaryLength atoms →
    SpineHasCupCapAtoms atoms →
    stateS.openWires.length = boundaryLength →
    (∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) →
    MatchingComponentSim sigma stateS stateT →
    MatchingComponentSim sigma (processSpine stateS atoms) (processSpine stateT atoms)
  | [], _, _, _, _, _, _, _, sim => sim
  | atom :: rest, stateS, stateT, boundaryLength, chained, arity, tracks, fixesAbove, sim => by
      show MatchingComponentSim sigma (processSpine (stepAtom stateS atom) rest)
        (processSpine (stepAtom stateT atom) rest)
      have headAndTail := spineBoundaryChained_tail chained
      have arityParts := spineHasCupCapAtoms_tail arity
      have windowInRange : atom.leftContext.length + atom.generatorDom.length
          ≤ stateS.openWires.length := by
        rw [tracks, ← headAndTail.1]
        exact Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
          atom.rightContext.length
      exact matchingComponentSim_processSpine_ofBoundaryDiscipline sigma rest
        (stepAtom stateS atom) (stepAtom stateT atom) atom.codBoundaryLength
        headAndTail.2 arityParts.2
        (stepAtom_openWires_tracksBoundary stateS atom arityParts.1
          (tracks.trans headAndTail.1.symm))
        (fun identifier idAtLeast =>
          fixesAbove identifier (Nat.le_trans (stepAtom_nextFresh_le stateS atom) idAtLeast))
        (matchingComponentSim_step_ofInRange sigma stateS stateT atom arityParts.1
          windowInRange fixesAbove sim)

/-! ## The sentinel-free read-off and peel -/

/-- ★ **The rename-relation read-off, sentinel-free** — the clone of
`matchingComponentRenameRel_of_matchingComponentSim`: the `bnodeCorr` premise is ALREADY
range-bounded (`index < bottomCount + openWires.length` is exactly the boundary-node list's
length), so `natListGetAt_map_inRange` discharges the read and the sentinel was never
necessary at this site. -/
theorem matchingComponentRenameRel_of_matchingComponentSim_ofInRange (bottomCount : Nat)
    (sigma : Nat → Nat)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : WireState) (sim : MatchingComponentSim sigma stateS stateT) :
    MatchingComponentRenameRel bottomCount sigma stateS stateT where
  lengthEq := by rw [sim.openMap, mapLength]
  loopsEq := sim.loopsEq
  bnodeCorr := by
    intro index indexInRange
    have hbnd : matchingBoundaryNodes bottomCount stateT
        = (matchingBoundaryNodes bottomCount stateS).map sigma := by
      show List.range bottomCount ++ stateT.openWires
        = (List.range bottomCount ++ stateS.openWires).map sigma
      rw [sim.openMap, mapAppend, mapFixedOn sigma (List.range bottomCount)
        (fun identifier identifierInRange => fixesBoundary identifier
          (mem_range_imp_lt identifierInRange))]
    rw [hbnd]
    exact natListGetAt_map_inRange sigma (matchingBoundaryNodes bottomCount stateS) index
      (by
        show index < (List.range bottomCount ++ stateS.openWires).length
        rw [natListAppendLength (List.range bottomCount) stateS.openWires,
          rangeLength bottomCount]
        exact indexInRange)
  componentComm := sim.componentComm

/-- ★ **The sentinel-free suffix peel** — a core `MatchingComponentSim` carried over ANY
chained, cup/cap-disciplined, tracked atom list yields the full rename relation, with no
`sigma 0 = 0` anywhere: the consumer converts the `runMatchingCell`-then-`rest` shape via
`processSpine_spineDiff` and supplies the peeled list's discipline from the boundary-chain
kit. -/
theorem matchingComponentRenameRel_ofCoreSim_boundaryDiscipline {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (bottomCount : Nat)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (peeledAtoms : List (SpineAtom signature sourceMode targetMode))
    (redexCore reductCore : WireState) (boundaryLength : Nat)
    (chained : SpineBoundaryChained boundaryLength peeledAtoms)
    (arity : SpineHasCupCapAtoms peeledAtoms)
    (tracks : redexCore.openWires.length = boundaryLength)
    (fixesAbove : ∀ identifier, redexCore.nextFresh ≤ identifier → sigma identifier = identifier)
    (coreSim : MatchingComponentSim sigma redexCore reductCore) :
    MatchingComponentRenameRel bottomCount sigma
      (processSpine redexCore peeledAtoms) (processSpine reductCore peeledAtoms) :=
  matchingComponentRenameRel_of_matchingComponentSim_ofInRange bottomCount sigma fixesBoundary
    _ _
    (matchingComponentSim_processSpine_ofBoundaryDiscipline sigma peeledAtoms redexCore
      reductCore boundaryLength chained arity tracks fixesAbove coreSim)

/-! ## Honesty marker -/

/-- **Honesty marker — the SENTINEL-FREE component-sim chain is SHIPPED.**  Step stability,
fold, rename-relation read-off, and suffix peel of `MatchingComponentSim` with the cap-read
sentinel `sigma 0 = 0` replaced by the boundary discipline (chain + cup/cap arity +
`openWires.length`-tracking) — every window read is in range, so `natListGetAt_map_inRange`
commutes reads with the rename unconditionally.  This unblocks renames that MOVE `0`, which the
empty-boundary block rotation (`blockRotate 0 wA wB`) must.  NOT yet covered: the sigma-bundle
core witness at a possibly-zero shared counter and the weak-conditions trace induction feeding
this chain — the remaining empty-boundary bricks.  `= true`. -/
def fxMode_hasSentinelFreeComponentSim : Bool := true

end FX1Poly.Polygraph
