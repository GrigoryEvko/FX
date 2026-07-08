import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCoreSwap

/-! # KEYSTONE4 leg 4 — the block-swap `MatchingComponentSim` bundle + the extract-commute (modulo `openMap`)

Every field of the block-swap `MatchingComponentSim` between the two window-disjoint firing orders is now banked
EXCEPT the open-wire correspondence:

  * `nfEq` — the state-parametric fresh-counter commutation (`disjointWindow_nextFresh_commute`, KEYSTONE1);
  * `componentComm` — the union-find join-order independence (`wiringDescCoreSwap_componentComm`, KEYSTONE4/3);
  * `loopsEq` — the cyclomatic invariance (`wiringDescCoreSwap_loopsEq`, KEYSTONE4/3);
  * `forestS` / `forestT` — the reachable-state forest invariant (`stepWiring_links_isUnionFindForest`, twice).

This file composes all of them into the full bundle and reads it off to the boundary-diagram commutation, carrying
the ONE remaining field — `openMap`, the four-zone open-wire correspondence
`BA.openWires = AB.openWires.map (blockRotate lo wA wB)` (fixed prefix / shifted A-window / un-shifted B-window /
fixed suffix) — as an EXPLICIT hypothesis.  So the entire disjoint-window surgery is discharged modulo that single
wire-bookkeeping identity:

  * ★ **`wiringDescCoreSwap_componentSim_ofOpenMap`** — the six-field `MatchingComponentSim` bundle;
  * ★ **`wiringDescCoreSwap_extract_ofOpenMap`** — the boundary-diagram commutation (the range-conditioned residual
    body), via `matchingComponentRenameRel_of_matchingComponentSim` + `extractDiagram_of_matchingComponentRenameRel`.

## The single remaining residual (NOT flipped)

`openMap` is the four-zone open-wire correspondence over the nested disjoint splices
(`natListInsertAt ∘ natListRemoveManyAt`).  It is TRUE (every KEYSTONE1 smoke exhibits it — e.g.
`disjointWindow_crossingCup_commute` literally shows the two orders' open wires `blockRotate`-related) but its
general zero-axiom proof is the standing wire-bookkeeping brick; until it lands,
`fxBrauer_hasWiringDescDisjointWindowFreshProof` / `fxBrauer_hasBrauerSoundness` stay `false`.  A secondary residual
is discharging the `windowsInRange` premise on reachable diagram states (a straightforward reachability invariant).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The full bundle, modulo `openMap` -/

/-- ★ **The block-swap `MatchingComponentSim` bundle, carrying `openMap` as its one explicit hypothesis.**  From a
fresh, forest, non-empty-boundary state with `descA`'s window disjointly left of `descB`'s and in range, the two
transposed firing orders (AB = alpha-then-beta, BA = beta-then-alpha) are `MatchingComponentSim`-related by
`blockRotate state.nextFresh descA.outputCount descB.outputCount`.  Five of six fields are banked; the sixth,
`openMap`, is the input hypothesis. -/
theorem wiringDescCoreSwap_componentSim_ofOpenMap (state : WireState) (positionA positionB : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length)
    (openMap : (stepWiring (stepWiring state positionB descB) positionA descA).openWires
        = ((stepWiring (stepWiring state positionA descA)
            (positionB - descA.inputCount + descA.outputCount) descB).openWires).map
          (blockRotate state.nextFresh descA.outputCount descB.outputCount)) :
    MatchingComponentSim (blockRotate state.nextFresh descA.outputCount descB.outputCount)
      (stepWiring (stepWiring state positionA descA)
        (positionB - descA.inputCount + descA.outputCount) descB)
      (stepWiring (stepWiring state positionB descB) positionA descA) where
  openMap := openMap
  nfEq :=
    disjointWindow_nextFresh_commute state positionA positionB positionA
      (positionB - descA.inputCount + descA.outputCount) descA descB
  componentComm :=
    wiringDescCoreSwap_componentComm state positionA positionB descA descB fresh nfPos forest disjoint windowB
  loopsEq :=
    wiringDescCoreSwap_loopsEq state positionA positionB descA descB fresh nfPos forest disjoint windowB
  forestS :=
    stepWiring_links_isUnionFindForest (stepWiring state positionA descA)
      (positionB - descA.inputCount + descA.outputCount) descB
      (stepWiring_links_isUnionFindForest state positionA descA forest)
  forestT :=
    stepWiring_links_isUnionFindForest (stepWiring state positionB descB) positionA descA
      (stepWiring_links_isUnionFindForest state positionB descB forest)

/-! ## The boundary-diagram commutation (range-conditioned residual body), modulo `openMap` -/

/-- ★ **The boundary-diagram commutes across the two window-disjoint firing orders — modulo `openMap`.**  Reads the
full bundle off to the matching extract through `matchingComponentRenameRel_of_matchingComponentSim` (the
`blockRotate` boundary-fixing from `bottomCount ≤ nextFresh`) and `extractDiagram_of_matchingComponentRenameRel`.
This is the freshness-and-range-conditioned `WiringDescDisjointWindowFresh` body, with `openMap` as the last
explicit hypothesis. -/
theorem wiringDescCoreSwap_extract_ofOpenMap (state : WireState) (positionA positionB bottomCount : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links)
    (bottomBound : bottomCount ≤ state.nextFresh)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length)
    (openMap : (stepWiring (stepWiring state positionB descB) positionA descA).openWires
        = ((stepWiring (stepWiring state positionA descA)
            (positionB - descA.inputCount + descA.outputCount) descB).openWires).map
          (blockRotate state.nextFresh descA.outputCount descB.outputCount)) :
    extractDiagram bottomCount
        (stepWiring (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
      = extractDiagram bottomCount
        (stepWiring (stepWiring state positionB descB) positionA descA) :=
  extractDiagram_of_matchingComponentRenameRel bottomCount
    (blockRotate state.nextFresh descA.outputCount descB.outputCount) _ _
    (matchingComponentRenameRel_of_matchingComponentSim bottomCount
      (blockRotate state.nextFresh descA.outputCount descB.outputCount)
      (blockRotate_below state.nextFresh descA.outputCount descB.outputCount 0 nfPos)
      (fun identifier identifierBelow =>
        blockRotate_below state.nextFresh descA.outputCount descB.outputCount identifier
          (Nat.lt_of_lt_of_le identifierBelow bottomBound))
      _ _
      (wiringDescCoreSwap_componentSim_ofOpenMap state positionA positionB descA descB fresh nfPos forest
        disjoint windowB openMap))

/-! ## Honesty marker -/

/-- **Honesty marker — the block-swap `MatchingComponentSim` bundle + boundary-diagram commutation are ASSEMBLED
modulo `openMap`.**  `wiringDescCoreSwap_componentSim_ofOpenMap` composes the five banked fields (`nfEq` /
`componentComm` / `loopsEq` / two forests) with `openMap` as its one explicit hypothesis, and
`wiringDescCoreSwap_extract_ofOpenMap` reads it off to the boundary-diagram commutation.  The ENTIRE
disjoint-window surgery is thus discharged modulo the single wire-bookkeeping identity `openMap` (the four-zone
open-wire correspondence over the nested disjoint splices) — the precise final residual.  `= true`. -/
def fxBrauer_hasWiringDescCoreSwapBundleModuloOpenMap : Bool := true

end FX1Poly.Polygraph
