import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeDynamics
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCompositeView
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingMidLoopAgreement

/-! # MatchingCompositeExtract — the two mid-state runs extract identically (MODE3-D, SAT-D5)

The run-level assembly: two disciplined second-half spines whose CANONICAL runs extract
identically produce identical extracts when run from the SAME mid-state.  Everything reduces
to the shipped event-level gluing through the D4a kinematics:

* the composite links/wires/loops read off as pure functions of the canonical traces, their
  rename by the mid-state wire map, and the mid-state's own data (`…_ofMidState`);
* the canonical runs' links and loops read off over the empty seed
  (`processSpine_links_eq_applyJoinEvents` / `…_loops_eq_addJoinEventLoops`);
* the extract equality reconstructs the connectivity-view simulation
  (`matchingConnectivityViewSim_ofExtractEq`), which drives the VIEW leg
  (`compositeBoundaryView_agrees_ofExtractEq`) at the composite boundary reads and the LOOP
  leg (`countJoinEventLoops_overMidLinks_agrees_ofViewSim`) at the loop increments;
* `extractDiagram_eq_of_connectivityView` reassembles the composite extract equality from
  the three agreement fields.

★ `processSpine_extract_eq_ofCanonicalExtractEq` — the mid-state provenance hypotheses
(freshness, positivity, forest, zone discipline, base bound) are exactly what the composite
mid-state of a vcompRight run supplies (SAT-D6's plumbing).  Raw Lean 4 + Init;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **Equal canonical extracts transfer to any shared disciplined mid-state.**  The
composite extracts agree field by field: wire counts through the rename's length
preservation, loop totals through the LOOP-leg gluing, and the boundary partner matching
through the VIEW-leg gluing at the composite boundary reads. -/
theorem processSpine_extract_eq_ofCanonicalExtractEq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (baseCount boundaryLength : Nat) (midState : WireState)
    (atomsAlpha atomsBeta : List (SpineAtom signature sourceMode targetMode))
    (chainedAlpha : SpineBoundaryChained boundaryLength atomsAlpha)
    (arityAlpha : SpineHasCupCapAtoms atomsAlpha)
    (chainedBeta : SpineBoundaryChained boundaryLength atomsBeta)
    (arityBeta : SpineHasCupCapAtoms atomsBeta)
    (midTracks : midState.openWires.length = boundaryLength)
    (boundaryPos : 0 < boundaryLength)
    (fresh : WireStateFresh midState) (nfPos : 0 < midState.nextFresh)
    (forest : isUnionFindForest midState.links)
    (discipline : RelativeWireZoneDiscipline midState.openWires midState.nextFresh)
    (baseBelow : baseCount ≤ midState.nextFresh)
    (extractsEqual :
      extractDiagram boundaryLength
          (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha)
        = extractDiagram boundaryLength
            (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta)) :
    extractDiagram baseCount (processSpine midState atomsAlpha)
      = extractDiagram baseCount (processSpine midState atomsBeta) := by
  have linksAlpha : (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha).links
      = applyJoinEvents
          (spineJoinEvents atomsAlpha (canonicalMatchingSeed boundaryLength)) [] :=
    processSpine_links_eq_applyJoinEvents atomsAlpha (canonicalMatchingSeed boundaryLength)
  have linksBeta : (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta).links
      = applyJoinEvents
          (spineJoinEvents atomsBeta (canonicalMatchingSeed boundaryLength)) [] :=
    processSpine_links_eq_applyJoinEvents atomsBeta (canonicalMatchingSeed boundaryLength)
  have loopsAlpha : (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha).loops
      = countJoinEventLoops
          (spineJoinEvents atomsAlpha (canonicalMatchingSeed boundaryLength)) [] :=
    (processSpine_loops_eq_addJoinEventLoops atomsAlpha
      (canonicalMatchingSeed boundaryLength)
      (canonicalMatchingSeed_wireStateFresh boundaryLength) boundaryPos).trans
      (Nat.zero_add _)
  have loopsBeta : (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta).loops
      = countJoinEventLoops
          (spineJoinEvents atomsBeta (canonicalMatchingSeed boundaryLength)) [] :=
    (processSpine_loops_eq_addJoinEventLoops atomsBeta
      (canonicalMatchingSeed boundaryLength)
      (canonicalMatchingSeed_wireStateFresh boundaryLength) boundaryPos).trans
      (Nat.zero_add _)
  have viewSim : MatchingConnectivityViewSim boundaryLength
      (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta) :=
    matchingConnectivityViewSim_ofExtractEq boundaryLength
      (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta) extractsEqual
  have baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midState.links →
      leftNode < midState.nextFresh ∧ rightNode < midState.nextFresh :=
    fun leftNode rightNode membership => fresh.2 (leftNode, rightNode) membership
  have compositeLengthAlpha : (processSpine midState atomsAlpha).openWires.length
      = (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length
      := by
    rw [processSpine_openWires_ofMidState midState boundaryLength atomsAlpha arityAlpha
      midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  have compositeLengthBeta : (processSpine midState atomsBeta).openWires.length
      = (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta).openWires.length
      := by
    rw [processSpine_openWires_ofMidState midState boundaryLength atomsBeta arityBeta
      midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  apply extractDiagram_eq_of_connectivityView
  · rw [compositeLengthAlpha, compositeLengthBeta]
    exact viewSim.lengthEq
  · rw [processSpine_loops_ofMidState midState boundaryLength atomsAlpha chainedAlpha
        arityAlpha midTracks fresh nfPos,
      processSpine_loops_ofMidState midState boundaryLength atomsBeta chainedBeta
        arityBeta midTracks fresh nfPos,
      countJoinEventLoops_overMidLinks_agrees_ofViewSim midState.openWires
        midState.nextFresh discipline boundaryLength midTracks
        (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha)
        (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta)
        (spineJoinEvents atomsAlpha (canonicalMatchingSeed boundaryLength))
        (spineJoinEvents atomsBeta (canonicalMatchingSeed boundaryLength))
        midState.links linksAlpha linksBeta loopsAlpha loopsBeta viewSim forest baseBounded]
  · intro firstIndex secondIndex firstBound secondBound
    have firstBoundCanonical : firstIndex < baseCount
        + (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length
        := by
      rw [← compositeLengthAlpha]
      exact firstBound
    have secondBoundCanonical : secondIndex < baseCount
        + (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length
        := by
      rw [← compositeLengthAlpha]
      exact secondBound
    show isSameComponent (processSpine midState atomsAlpha).links
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsAlpha).openWires)
          firstIndex)
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsAlpha).openWires)
          secondIndex)
      = isSameComponent (processSpine midState atomsBeta).links
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsBeta).openWires)
          firstIndex)
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsBeta).openWires)
          secondIndex)
    rw [processSpine_links_ofMidState midState boundaryLength atomsAlpha chainedAlpha
        arityAlpha midTracks,
      processSpine_openWires_ofMidState midState boundaryLength atomsAlpha arityAlpha
        midTracks,
      processSpine_links_ofMidState midState boundaryLength atomsBeta chainedBeta
        arityBeta midTracks,
      processSpine_openWires_ofMidState midState boundaryLength atomsBeta arityBeta
        midTracks]
    exact compositeBoundaryView_agrees_ofExtractEq midState.openWires midState.nextFresh
      discipline boundaryLength midTracks baseCount baseBelow
      (processSpine (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (processSpine (canonicalMatchingSeed boundaryLength) atomsBeta)
      (spineJoinEvents atomsAlpha (canonicalMatchingSeed boundaryLength))
      (spineJoinEvents atomsBeta (canonicalMatchingSeed boundaryLength))
      midState.links linksAlpha linksBeta extractsEqual forest baseBounded
      firstIndex secondIndex firstBoundCanonical secondBoundCanonical

/-- **Honesty marker — SAT-D5 is PROVED: the two mid-state runs extract identically.**
Equal canonical extracts + a shared disciplined mid-state force equal composite extracts,
assembled from the VIEW-leg and LOOP-leg gluings through the D4a read-offs.  NOT yet
shipped: the SAT-D6 plumbing discharging the mid-state provenance (freshness, forest, zone
discipline) for the actual vcompRight composite mid-states and the empty-boundary dispatch. -/
def fxMode_hasCompositeExtractAgreement : Bool := true

end FX1Poly.Polygraph
