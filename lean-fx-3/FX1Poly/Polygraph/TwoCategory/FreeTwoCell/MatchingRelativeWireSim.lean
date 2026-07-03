import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # MatchingRelativeWireSim — the kinematic layer of the relative run (MODE3-D brick D1)

The `vcompRight` field compares a spine's run from its OWN canonical seed with its run from
the post-α mid-state — the "action factors through the diagram" (Joyal–Street) leg.  Whatever
route the dynamics takes, its backbone is the KINEMATIC fact installed here: running the SAME
spine from two states keeps the open wires in positional bijection under a wire map `sigma`,
with the fresh allocations corresponding through the counters — UNCONDITIONALLY, because the
wire plumbing never reads the union-find:

* a CUP splices two fresh legs at the same position in both runs (`natListInsertAt_map` +
  the counter correspondence);
* a CAP drops the two wires at the same position in BOTH of its branches
  (`stepCap_openWires` is branch-independent), so the correspondence survives even when the
  two runs take DIFFERENT same-component branches — exactly the divergence the dynamics
  layer will have to account for in `links` / `loops`;
* no window bounds are needed anywhere (the list identities are total).

`sigma` generalizes both pad shifts (`freshShiftAbove threshold delta` on the right,
`freshShiftAbove 0 delta` on the left) to an arbitrary wire map; the counter correspondence
is stated additively (`sigma (canonical + offset) = relative + offset`) so it is preserved
verbatim as both counters advance in lockstep — no subtraction anywhere.

The mid-state instance of `sigma` (read the seed wires positionally, shift the counter) and
the dynamics layer (the partition-join invariant on `links` / `loops`) are the next MODE3-D
bricks. -/

namespace FX1Poly.Polygraph

/-! ## The relative-run wire simulation -/

/-- ★ **The relative-run wire correspondence**: the relative state's open wires are the
`sigma`-images of the canonical state's open wires, and `sigma` maps the canonical run's
future fresh identifiers to the relative run's future fresh identifiers offset-for-offset.
Only the wire fields are related — `links` and `loops` diverge contentfully between the runs
(a cap can close a loop in one and join in the other) and belong to the dynamics layer. -/
structure MatchingRelativeWireSim (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState) : Prop where
  /-- The relative open wires are the `sigma`-images of the canonical open wires. -/
  openMap : stateRelative.openWires = stateCanonical.openWires.map sigma
  /-- `sigma` maps canonical fresh identifiers to relative fresh identifiers,
  offset-for-offset from the current counters. -/
  freshCorr : ∀ offset, sigma (stateCanonical.nextFresh + offset)
    = stateRelative.nextFresh + offset

/-! ## Step preservation -/

/-- ★ **A CUP step preserves the wire correspondence at any position.**  Both runs splice
their own two fresh legs at the same position; the counter correspondence identifies the
legs (`sigma` at offsets `0` and `1`) and re-establishes itself at offset `2 + offset`. -/
theorem matchingRelativeWireSim_stepCup (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState) (position : Nat)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    MatchingRelativeWireSim sigma
      (stepCup stateCanonical position) (stepCup stateRelative position) := by
  have freshZero : sigma stateCanonical.nextFresh = stateRelative.nextFresh :=
    sim.freshCorr 0
  have freshOne : sigma (stateCanonical.nextFresh + 1) = stateRelative.nextFresh + 1 :=
    sim.freshCorr 1
  have openMapAfter : (stepCup stateRelative position).openWires
      = ((stepCup stateCanonical position).openWires).map sigma := by
    rw [stepCup_openWires stateRelative position, stepCup_openWires stateCanonical position,
      natListInsertAt_map sigma stateCanonical.openWires position
        [stateCanonical.nextFresh, stateCanonical.nextFresh + 1],
      sim.openMap]
    show natListInsertAt (stateCanonical.openWires.map sigma) position
        [stateRelative.nextFresh, stateRelative.nextFresh + 1]
      = natListInsertAt (stateCanonical.openWires.map sigma) position
        [sigma stateCanonical.nextFresh, sigma (stateCanonical.nextFresh + 1)]
    rw [freshZero, freshOne]
  have freshCorrAfter : ∀ offset,
      sigma ((stepCup stateCanonical position).nextFresh + offset)
        = (stepCup stateRelative position).nextFresh + offset := by
    intro offset
    rw [stepCup_nextFresh stateCanonical position, stepCup_nextFresh stateRelative position,
      Nat.add_assoc stateCanonical.nextFresh 2 offset,
      Nat.add_assoc stateRelative.nextFresh 2 offset]
    exact sim.freshCorr (2 + offset)
  exact { openMap := openMapAfter, freshCorr := freshCorrAfter }

/-- ★ **A CAP step preserves the wire correspondence at any position** — even when the two
runs take DIFFERENT same-component branches: both branches drop the same two positions
(`stepCap_openWires`) and leave the counter untouched (`stepCap_nextFresh`). -/
theorem matchingRelativeWireSim_stepCap (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState) (position : Nat)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    MatchingRelativeWireSim sigma
      (stepCap stateCanonical position) (stepCap stateRelative position) := by
  have openMapAfter : (stepCap stateRelative position).openWires
      = ((stepCap stateCanonical position).openWires).map sigma := by
    rw [stepCap_openWires stateRelative position, stepCap_openWires stateCanonical position,
      natListRemoveTwoAt_map sigma stateCanonical.openWires position,
      sim.openMap]
  have freshCorrAfter : ∀ offset,
      sigma ((stepCap stateCanonical position).nextFresh + offset)
        = (stepCap stateRelative position).nextFresh + offset := by
    intro offset
    rw [stepCap_nextFresh stateCanonical position, stepCap_nextFresh stateRelative position]
    exact sim.freshCorr offset
  exact { openMap := openMapAfter, freshCorr := freshCorrAfter }

/-- One cup/cap-disciplined atom preserves the wire correspondence — the arity dichotomy
dispatches both runs to the same step at the atom's own live position. -/
theorem matchingRelativeWireSim_stepAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    MatchingRelativeWireSim sigma
      (stepAtom stateCanonical atom) (stepAtom stateRelative atom) := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateCanonical atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateRelative atom cupArity.1 cupArity.2]
      exact matchingRelativeWireSim_stepCup sigma stateCanonical stateRelative
        atom.leftContext.length sim
  | inr capArity =>
      rw [stepAtom_ofCapArity stateCanonical atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateRelative atom capArity.1 capArity.2]
      exact matchingRelativeWireSim_stepCap sigma stateCanonical stateRelative
        atom.leftContext.length sim

/-! ## The fold -/

/-- ★ **The wire correspondence folds over any cup/cap-disciplined spine** — no boundary
chain, no window bounds: the wire plumbing is total. -/
theorem matchingRelativeWireSim_processSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (stateCanonical stateRelative : WireState) →
    SpineHasCupCapAtoms atoms →
    MatchingRelativeWireSim sigma stateCanonical stateRelative →
    MatchingRelativeWireSim sigma
      (processSpine stateCanonical atoms) (processSpine stateRelative atoms)
  | [], _, _, _, sim => sim
  | atom :: restAtoms, stateCanonical, stateRelative, arity, sim => by
      show MatchingRelativeWireSim sigma
        (processSpine (stepAtom stateCanonical atom) restAtoms)
        (processSpine (stepAtom stateRelative atom) restAtoms)
      have arityParts := spineHasCupCapAtoms_tail arity
      exact matchingRelativeWireSim_processSpine sigma restAtoms
        (stepAtom stateCanonical atom) (stepAtom stateRelative atom) arityParts.2
        (matchingRelativeWireSim_stepAtom sigma stateCanonical stateRelative atom
          arityParts.1 sim)

/-! ## Honesty marker -/

/-- **Honesty marker — the relative-run WIRE simulation is SHIPPED (MODE3-D brick D1).**
Running the same cup/cap-disciplined spine from two states keeps the open wires in
positional `sigma`-bijection and the fresh counters in additive correspondence,
unconditionally (both cap branches drop the same wires).  NOT yet shipped: the mid-state
`sigma` instance (positional seed read + counter shift) and the DYNAMICS layer — the
`links` / `loops` partition-join invariant that the vcompRight / Joyal–Street leg actually
turns on.  `= true`. -/
def fxMode_hasMatchingRelativeWireSim : Bool := true

end FX1Poly.Polygraph
