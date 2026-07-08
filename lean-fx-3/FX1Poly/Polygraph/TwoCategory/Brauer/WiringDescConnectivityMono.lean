import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescComponentSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # KEYSTONE8 ingredient — connectivity MONOTONICITY of the wiring engine (a generator step never disconnects)

The state-parametric `relationAgrees` premise the shipped `whisker` move (`Brauer/WiringDescConv.lean`) consumes is
a same-component EQUALITY between the two post-word states over every in-range boundary index.  That equality
factors into two inequalities.  This file ships the CONNECTIVITY-MONOTONE half — the direction that holds
UNCONDITIONALLY (no freshness, no window locality): a generator step, and hence the whole `processBrauer` fold, only
ever ADDS union-find connections; it never SEVERS a component.  So any pair of nodes already in the same component
of the incoming state stays in the same component after firing any word.

This is the fold-lift of the single-join monotonicity `isSameComponent_unionFindJoin_ofBase`
(`FreeTwoCell/MatchingComponentAlgebra.lean`) through the generic arc fold `stepWiringArcs` (each step either leaves
`links` untouched — the loop branch — or `unionFindJoin`s two decoded endpoints — the join branch, where the base
membership survives by the single-join lemma, forest-conditioned via `isUnionFindForest_unionFindJoin`).  It is the
crossing-inclusive analog of the arc route's connectivity monotonicity, and one of the two halves of the standing
same-component window-locality subsystem the FULL Brauer soundness flip rides.

## Honest scope

This closes ONLY the base-survives (`isSameComponent = true`) direction, over ARBITRARY nodes.  It is NOT a
`relationAgrees`: a `relationAgrees` compares `matchingSameComponent` at the BOUNDARY indices, whose window ports
read FRESH node ids after a collapse word, and additionally needs the CONVERSE direction (a boundary-preserving word
introduces no SPURIOUS off-window connection) — the freshness-conditioned window-locality half, which is NOT in this
file and remains the standing brick.  So `fxBrauer_hasBrauerSoundness` STAYS `false`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic arc fold is connectivity-monotone -/

/-- ★ **The generic arc fold never disconnects.**  If `probeOne` and `probeTwo` already share a component of the
incoming `links`, they still share a component after the whole `stepWiringArcs` fold: each step either leaves
`links` untouched (loop branch) or `unionFindJoin`s two decoded endpoints, and base same-component membership
survives a join by `isSameComponent_unionFindJoin_ofBase` (forest-conditioned, the forest carried across the join
by `isUnionFindForest_unionFindJoin`).  Structural on the arc list. -/
theorem stepWiringArcs_isSameComponent_ofBase
    (inputNodes outputNodes : List Nat) (inputCount probeOne probeTwo : Nat) :
    (arcs : List (Nat × Nat)) → (loopsAcc : Nat) → (links : List (Nat × Nat)) →
    isUnionFindForest links →
    isSameComponent links probeOne probeTwo = true →
    isSameComponent (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc links).fst
        probeOne probeTwo = true
  | [], _, _, _, base => base
  | (firstTag, secondTag) :: rest, loopsAcc, links, forest, base => by
      show isSameComponent (stepWiringArcs inputNodes outputNodes inputCount
          ((firstTag, secondTag) :: rest) loopsAcc links).fst probeOne probeTwo = true
      dsimp only [stepWiringArcs]
      split
      · exact stepWiringArcs_isSameComponent_ofBase inputNodes outputNodes inputCount probeOne probeTwo
          rest (loopsAcc + 1) links forest base
      · exact stepWiringArcs_isSameComponent_ofBase inputNodes outputNodes inputCount probeOne probeTwo
          rest loopsAcc
          (unionFindJoin links
            (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
            (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
          (isUnionFindForest_unionFindJoin links _ _ forest)
          (isSameComponent_unionFindJoin_ofBase links forest
            (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
            (wiringEndpointNode inputNodes outputNodes inputCount secondTag)
            probeOne probeTwo base)

/-! ## One `stepWiring` step is connectivity-monotone -/

/-- ★ **One `stepWiring` step never disconnects.**  Its links are the arc fold's output over the incoming (forest)
links, so base same-component membership survives by `stepWiringArcs_isSameComponent_ofBase`. -/
theorem stepWiring_isSameComponent_ofBase (state : WireState) (position : Nat) (desc : WiringDesc)
    (forest : isUnionFindForest state.links) (probeOne probeTwo : Nat)
    (base : isSameComponent state.links probeOne probeTwo = true) :
    isSameComponent (stepWiring state position desc).links probeOne probeTwo = true :=
  stepWiringArcs_isSameComponent_ofBase
    (natListSliceAt state.openWires position desc.inputCount)
    ((List.range desc.outputCount).map (· + state.nextFresh))
    desc.inputCount probeOne probeTwo desc.arcs 0 state.links forest base

/-! ## The whole `processBrauer` fold is connectivity-monotone -/

/-- ★ **The whole `processBrauer` fold never disconnects.**  Firing ANY word of Brauer atoms preserves every
same-component membership of the incoming (forest) state: per atom, the forest is carried across by
`stepWiring_links_isUnionFindForest` and base membership survives by `stepWiring_isSameComponent_ofBase`.
Structural on the atom list.  So convertibility-preserving surgery is connectivity-monotone — a boundary word can
only add wires between components, never cut one — which is the unconditional half of the standing same-component
window-locality residual. -/
theorem processBrauer_isSameComponent_ofBase :
    (atoms : List BrauerAtom) → (state : WireState) →
    isUnionFindForest state.links →
    (probeOne probeTwo : Nat) →
    isSameComponent state.links probeOne probeTwo = true →
    isSameComponent (processBrauer state atoms).links probeOne probeTwo = true
  | [], _, _, _, _, base => base
  | atom :: rest, state, forest, probeOne, probeTwo, base =>
      processBrauer_isSameComponent_ofBase rest (stepBrauerAtom state atom)
        (stepWiring_links_isUnionFindForest state atom.position atom.wiring forest)
        probeOne probeTwo
        (stepWiring_isSameComponent_ofBase state atom.position atom.wiring forest probeOne probeTwo base)

/-! ## Honesty marker -/

/-- **Honesty marker — the connectivity-monotone half of the same-component window-locality subsystem is SHIPPED.**
`processBrauer_isSameComponent_ofBase` proves any Brauer word only ADDS union-find connections — it never severs a
component — so every same-component membership of the incoming forest state survives firing the word, over ARBITRARY
nodes, unconditionally on freshness / window / offset (the single-join monotonicity `isSameComponent_unionFindJoin_ofBase`
lifted through the generic arc fold `stepWiringArcs` and the atom fold).  This is ONE of the two halves of the
`relationAgrees` premise the shipped `whisker` move consumes; the CONVERSE (a boundary-preserving collapse word
introduces no spurious off-window connection, and its window ports reconnect to the same off-window components) is
the freshness-conditioned window-locality half — NOT built here, still the standing brick.  So this does NOT flip
`fxBrauer_hasBrauerSoundness`.  `= true`. -/
def fxBrauer_hasConnectivityMonotonicity : Bool := true

end FX1Poly.Polygraph
