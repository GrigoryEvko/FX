import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeJoinEvents
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeWireSeed

/-! # MatchingRelativeDynamics — the relative run reads off the renamed trace (MODE3-D D4a)

The assembly substrate for the vcompRight leg: EVERY observable of a run from an arbitrary
relative state is a pure function of the CANONICAL trace, its `sigma`-rename, and the relative
state's own data —

* `processSpine_links_ofRelativeSim` — the run's `links` are the renamed canonical trace
  folded over the relative state's links (trace faithfulness + the D3 rename);
* `processSpine_loops_ofRelativeSim` — the run's `loops` are the relative state's plus the
  renamed trace's already-connected count (freshness-conditioned, as the faithfulness is);
* `processSpine_openWires_ofRelativeSim` — the run's final wires are the `sigma`-image of the
  canonical run's final wires (the D1 wire-sim fold, read off);
* the MID-STATE instantiations (`…_ofMidState`) at the concrete `relativeWireMap` and the
  canonical seed — the exact forms the vcompRight composite consumes at the post-alpha state;
* the provenance package (`canonicalMatchingSeed_wireStateFresh`,
  `processSpine_fromSeed_wireStateFresh`, `processSpine_fromSeed_nextFresh_pos`) — the
  mid-state produced by running the FIRST cell from a positive-boundary canonical seed
  satisfies the freshness/positivity conditions the loops leg needs.

With this brick the vcompRight residue is a statement about two EVENT LISTS acting on one
links list — no runs, no wire states: two traces with equal seed-fold extracts must act
identically on the (fresh-disjoint, forest) mid-state links.  That gluing is the next brick. -/

namespace FX1Poly.Polygraph

/-! ## The generic-sigma read-off -/

/-- ★ **The relative run's `links` are the renamed canonical trace folded over the relative
links** — trace faithfulness at the relative state rewritten along the D3 trace rename. -/
theorem processSpine_links_ofRelativeSim {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (stateCanonical stateRelative : WireState) (boundaryLength : Nat)
    (chained : SpineBoundaryChained boundaryLength atoms)
    (arity : SpineHasCupCapAtoms atoms)
    (tracks : stateCanonical.openWires.length = boundaryLength)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    (processSpine stateRelative atoms).links
      = applyJoinEvents
          ((spineJoinEvents atoms stateCanonical).map
            (fun event => (sigma event.1, sigma event.2)))
          stateRelative.links := by
  rw [processSpine_links_eq_applyJoinEvents atoms stateRelative,
    spineJoinEvents_ofRelativeWireSim sigma atoms stateCanonical stateRelative
      boundaryLength chained arity tracks sim]

/-- ★ **The relative run's `loops` are the relative state's plus the renamed trace's
already-connected count** — loops faithfulness at the relative state (freshness-conditioned)
rewritten along the D3 trace rename. -/
theorem processSpine_loops_ofRelativeSim {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (stateCanonical stateRelative : WireState) (boundaryLength : Nat)
    (chained : SpineBoundaryChained boundaryLength atoms)
    (arity : SpineHasCupCapAtoms atoms)
    (tracks : stateCanonical.openWires.length = boundaryLength)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative)
    (fresh : WireStateFresh stateRelative) (nfPos : 0 < stateRelative.nextFresh) :
    (processSpine stateRelative atoms).loops
      = stateRelative.loops
        + countJoinEventLoops
            ((spineJoinEvents atoms stateCanonical).map
              (fun event => (sigma event.1, sigma event.2)))
            stateRelative.links := by
  rw [processSpine_loops_eq_addJoinEventLoops atoms stateRelative fresh nfPos,
    spineJoinEvents_ofRelativeWireSim sigma atoms stateCanonical stateRelative
      boundaryLength chained arity tracks sim]

/-- The relative run's final wires are the `sigma`-image of the canonical run's final wires —
the D1 wire-sim fold, read off at its `openMap` field. -/
theorem processSpine_openWires_ofRelativeSim {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (stateCanonical stateRelative : WireState)
    (arity : SpineHasCupCapAtoms atoms)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    (processSpine stateRelative atoms).openWires
      = (processSpine stateCanonical atoms).openWires.map sigma :=
  (matchingRelativeWireSim_processSpine sigma atoms stateCanonical stateRelative
    arity sim).openMap

/-! ## The mid-state provenance package -/

/-- The canonical seed is fresh — `wireStateFresh_initial` re-pinned at the named seed. -/
theorem canonicalMatchingSeed_wireStateFresh (bottomCount : Nat) :
    WireStateFresh (canonicalMatchingSeed bottomCount) :=
  wireStateFresh_initial bottomCount

/-- Any run from a POSITIVE-boundary canonical seed lands in a fresh state — the mid-state
produced by the composite's first cell satisfies the loops leg's freshness condition. -/
theorem processSpine_fromSeed_wireStateFresh {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    WireStateFresh (processSpine (canonicalMatchingSeed bottomCount) atoms) :=
  processSpine_wireStateFresh atoms (canonicalMatchingSeed bottomCount)
    (canonicalMatchingSeed_wireStateFresh bottomCount) bottomPos

/-- Any run from a positive-boundary canonical seed keeps a positive counter — the seed's
counter is the boundary count and the fold never lowers it. -/
theorem processSpine_fromSeed_nextFresh_pos {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    0 < (processSpine (canonicalMatchingSeed bottomCount) atoms).nextFresh :=
  Nat.lt_of_lt_of_le bottomPos
    (processSpine_nextFresh_le atoms (canonicalMatchingSeed bottomCount))

/-! ## The mid-state instantiations -/

/-- ★ **Mid-state links read-off** — a disciplined run from ANY state tracking the boundary
has links equal to the canonical trace, renamed by the state's own mid-state wire map, folded
over the state's links. -/
theorem processSpine_links_ofMidState {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (midState : WireState) (boundaryLength : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (chained : SpineBoundaryChained boundaryLength atoms)
    (arity : SpineHasCupCapAtoms atoms)
    (midTracks : midState.openWires.length = boundaryLength) :
    (processSpine midState atoms).links
      = applyJoinEvents
          ((spineJoinEvents atoms (canonicalMatchingSeed boundaryLength)).map
            (fun event =>
              (relativeWireMap midState.openWires midState.nextFresh event.1,
                relativeWireMap midState.openWires midState.nextFresh event.2)))
          midState.links :=
  processSpine_links_ofRelativeSim
    (relativeWireMap midState.openWires midState.nextFresh) atoms
    (canonicalMatchingSeed boundaryLength) midState boundaryLength chained arity
    (canonicalMatchingSeed_wireCount boundaryLength)
    (matchingRelativeWireSim_initial_ofTracks midState boundaryLength midTracks)

/-- ★ **Mid-state loops read-off** — the run's loop total is the mid-state's plus the renamed
canonical trace's already-connected count over the mid-state's links. -/
theorem processSpine_loops_ofMidState {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (midState : WireState) (boundaryLength : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (chained : SpineBoundaryChained boundaryLength atoms)
    (arity : SpineHasCupCapAtoms atoms)
    (midTracks : midState.openWires.length = boundaryLength)
    (fresh : WireStateFresh midState) (nfPos : 0 < midState.nextFresh) :
    (processSpine midState atoms).loops
      = midState.loops
        + countJoinEventLoops
            ((spineJoinEvents atoms (canonicalMatchingSeed boundaryLength)).map
              (fun event =>
                (relativeWireMap midState.openWires midState.nextFresh event.1,
                  relativeWireMap midState.openWires midState.nextFresh event.2)))
            midState.links :=
  processSpine_loops_ofRelativeSim
    (relativeWireMap midState.openWires midState.nextFresh) atoms
    (canonicalMatchingSeed boundaryLength) midState boundaryLength chained arity
    (canonicalMatchingSeed_wireCount boundaryLength)
    (matchingRelativeWireSim_initial_ofTracks midState boundaryLength midTracks)
    fresh nfPos

/-- **Mid-state wires read-off** — the run's final wires are the mid-state wire-map image of
the canonical run's final wires. -/
theorem processSpine_openWires_ofMidState {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (midState : WireState) (boundaryLength : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (arity : SpineHasCupCapAtoms atoms)
    (midTracks : midState.openWires.length = boundaryLength) :
    (processSpine midState atoms).openWires
      = (processSpine (canonicalMatchingSeed boundaryLength) atoms).openWires.map
          (relativeWireMap midState.openWires midState.nextFresh) :=
  processSpine_openWires_ofRelativeSim
    (relativeWireMap midState.openWires midState.nextFresh) atoms
    (canonicalMatchingSeed boundaryLength) midState arity
    (matchingRelativeWireSim_initial_ofTracks midState boundaryLength midTracks)

/-! ## Honesty marker -/

/-- **Honesty marker — the relative-run dynamics package is SHIPPED (MODE3-D brick D4a).**
Links, loops, and final wires of a disciplined run from any boundary-tracking state are pure
functions of the canonical trace, its rename by the state's mid-state wire map, and the
state's own data (`…_ofRelativeSim` / `…_ofMidState`), with the freshness/positivity
provenance for composite mid-states (`processSpine_fromSeed_wireStateFresh` /
`…_nextFresh_pos`, positive boundary).  NOT yet shipped: the event-list GLUING — two canonical
traces with equal seed-fold extracts act identically (component view on the composite
boundary + loop increment) on any fresh-disjoint forest links list — the genuine
Temperley–Lieb residue of vcompRight, now stated with no runs in it.  `= true`. -/
def fxMode_hasMatchingRelativeDynamics : Bool := true

end FX1Poly.Polygraph
