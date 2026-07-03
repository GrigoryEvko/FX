import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeWireSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # MatchingRelativeJoinEvents — the relative run's trace is the sigma-rename (MODE3-D D3)

The dynamics layer of the relative run, reduced to DATA: the join-event trace depends only
on the wire evolution (positions and counters), and the relative-run wire simulation relates
exactly that evolution — so the relative run's trace is the pointwise `sigma` pair-rename of
the canonical run's trace:

* `stepAtomJoinEvents_ofRelativeWireSim` — per atom: a cup's events are the two fresh legs
  (`freshCorr` at offsets `0` and `1`), a cap's events are its two window reads (`openMap`
  read through `natListGetAt_map_inRange`, in range by the boundary discipline);
* `spineJoinEvents_ofRelativeWireSim` — the fold, threading the boundary chain + cup/cap
  arity + wire-count tracking on the CANONICAL side exactly as the pad-sim folds do.

Combined with the SHIPPED trace faithfulness (`processSpine_links_eq_applyJoinEvents`,
`processSpine_loops_eq_addJoinEventLoops`), this reduces the whole vcompRight / Joyal–Street
action question to a statement about EVENT LISTS: the relative run's links are the renamed
canonical trace folded over the mid-state's links, and its loops are the mid-state's plus
the renamed trace's already-connected count.  The remaining Temperley–Lieb content — two
traces with equal seed-fold extracts act identically on any fresh-disjoint forest — is the
next MODE3-D brick, now run-free. -/

namespace FX1Poly.Polygraph

/-! ## List plumbing (private copy — core map/append lemmas leak propext) -/

private theorem listMapAppend {Element ResultElement : Type}
    (mapped : Element → ResultElement) :
    (first : List Element) → (second : List Element) →
    (first ++ second).map mapped = first.map mapped ++ second.map mapped
  | [], _ => rfl
  | head :: firstRest, second =>
      congrArg (mapped head :: ·) (listMapAppend mapped firstRest second)

/-! ## The per-atom trace correspondence -/

/-- ★ **One cup/cap atom's join events under the relative run are the `sigma`-renames of its
canonical events.**  A cup emits the two fresh legs — corresponding through `freshCorr` at
offsets `0` and `1`; a cap emits its two window reads — corresponding through `openMap`
(`natListGetAt_map_inRange`, in range by the window bound). -/
theorem stepAtomJoinEvents_ofRelativeWireSim {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ stateCanonical.openWires.length)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    stepAtomJoinEvents stateRelative atom
      = (stepAtomJoinEvents stateCanonical atom).map
          (fun event => (sigma event.1, sigma event.2)) := by
  cases arity with
  | inl cupArity =>
      have freshZero : sigma stateCanonical.nextFresh = stateRelative.nextFresh :=
        sim.freshCorr 0
      have freshOne : sigma (stateCanonical.nextFresh + 1) = stateRelative.nextFresh + 1 :=
        sim.freshCorr 1
      rw [stepAtomJoinEvents_ofCupArity stateRelative atom cupArity.1 cupArity.2,
        stepAtomJoinEvents_ofCupArity stateCanonical atom cupArity.1 cupArity.2]
      show [(stateRelative.nextFresh, stateRelative.nextFresh + 1)]
        = [(sigma stateCanonical.nextFresh, sigma (stateCanonical.nextFresh + 1))]
      rw [freshZero, freshOne]
  | inr capArity =>
      rw [capArity.1] at windowInRange
      have positionSuccLt : atom.leftContext.length + 1 < stateCanonical.openWires.length :=
        windowInRange
      have positionLt : atom.leftContext.length < stateCanonical.openWires.length :=
        Nat.lt_of_succ_lt positionSuccLt
      have readZero : natListGetAt stateRelative.openWires atom.leftContext.length
          = sigma (natListGetAt stateCanonical.openWires atom.leftContext.length) := by
        rw [sim.openMap]
        exact natListGetAt_map_inRange sigma stateCanonical.openWires
          atom.leftContext.length positionLt
      have readOne : natListGetAt stateRelative.openWires (atom.leftContext.length + 1)
          = sigma (natListGetAt stateCanonical.openWires (atom.leftContext.length + 1)) := by
        rw [sim.openMap]
        exact natListGetAt_map_inRange sigma stateCanonical.openWires
          (atom.leftContext.length + 1) positionSuccLt
      rw [stepAtomJoinEvents_ofCapArity stateRelative atom capArity.1 capArity.2,
        stepAtomJoinEvents_ofCapArity stateCanonical atom capArity.1 capArity.2]
      show [(natListGetAt stateRelative.openWires atom.leftContext.length,
            natListGetAt stateRelative.openWires (atom.leftContext.length + 1))]
        = [(sigma (natListGetAt stateCanonical.openWires atom.leftContext.length),
            sigma (natListGetAt stateCanonical.openWires (atom.leftContext.length + 1)))]
      rw [readZero, readOne]

/-! ## The fold -/

/-- ★ **The relative run's whole trace is the `sigma`-rename of the canonical run's trace**
— by structural induction over the spine, threading the boundary chain + cup/cap arity +
wire-count tracking on the CANONICAL side and stepping the wire simulation along both
runs. -/
theorem spineJoinEvents_ofRelativeWireSim {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (sigma : Nat → Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (stateCanonical stateRelative : WireState) → (boundaryLength : Nat) →
    SpineBoundaryChained boundaryLength atoms →
    SpineHasCupCapAtoms atoms →
    stateCanonical.openWires.length = boundaryLength →
    MatchingRelativeWireSim sigma stateCanonical stateRelative →
    spineJoinEvents atoms stateRelative
      = (spineJoinEvents atoms stateCanonical).map
          (fun event => (sigma event.1, sigma event.2))
  | [], _, _, _, _, _, _, _ => rfl
  | atom :: restAtoms, stateCanonical, stateRelative, boundaryLength, chained, arity,
      tracks, sim => by
      show stepAtomJoinEvents stateRelative atom
            ++ spineJoinEvents restAtoms (stepAtom stateRelative atom)
        = ((stepAtomJoinEvents stateCanonical atom
            ++ spineJoinEvents restAtoms (stepAtom stateCanonical atom)).map
            (fun event => (sigma event.1, sigma event.2)))
      have headAndTail := spineBoundaryChained_tail chained
      have arityParts := spineHasCupCapAtoms_tail arity
      have windowInRange : atom.leftContext.length + atom.generatorDom.length
          ≤ stateCanonical.openWires.length := by
        rw [tracks, ← headAndTail.1]
        exact Nat.le_add_right
          (atom.leftContext.length + atom.generatorDom.length)
          atom.rightContext.length
      rw [listMapAppend (fun event : Nat × Nat => (sigma event.1, sigma event.2))
          (stepAtomJoinEvents stateCanonical atom)
          (spineJoinEvents restAtoms (stepAtom stateCanonical atom)),
        stepAtomJoinEvents_ofRelativeWireSim sigma stateCanonical stateRelative atom
          arityParts.1 windowInRange sim,
        spineJoinEvents_ofRelativeWireSim sigma restAtoms (stepAtom stateCanonical atom)
          (stepAtom stateRelative atom) atom.codBoundaryLength headAndTail.2 arityParts.2
          (stepAtom_openWires_tracksBoundary stateCanonical atom arityParts.1
            (tracks.trans headAndTail.1.symm))
          (matchingRelativeWireSim_stepAtom sigma stateCanonical stateRelative atom
            arityParts.1 sim)]

/-! ## Honesty marker -/

/-- **Honesty marker — the relative-run TRACE correspondence is SHIPPED (MODE3-D brick
D3).**  Under the boundary-chained cup/cap discipline, the relative run's join-event trace
is the pointwise `sigma` pair-rename of the canonical run's trace
(`spineJoinEvents_ofRelativeWireSim`).  With the shipped trace faithfulness
(`processSpine_links_eq_applyJoinEvents` / `processSpine_loops_eq_addJoinEventLoops`), the
relative run's `links` are the renamed canonical trace folded over the mid-state's links
and its `loops` are the mid-state's plus the renamed trace's already-connected count — the
vcompRight / Joyal–Street action question is now RUN-FREE.  NOT yet shipped: the event-list
gluing itself — two traces with equal seed-fold extracts act identically on any
fresh-disjoint forest — the remaining MODE3-D content.  `= true`. -/
def fxMode_hasMatchingRelativeJoinEventCorrespondence : Bool := true

end FX1Poly.Polygraph
