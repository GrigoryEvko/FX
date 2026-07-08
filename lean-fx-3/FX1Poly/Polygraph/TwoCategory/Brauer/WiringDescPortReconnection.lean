import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityOffConfined
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConv
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSim

/-! # KEYSTONE11 ingredient — PORT-RECONNECTION: the third `relationAgrees` ingredient + the whisker assembly bridge

The shipped same-component word-locality subsystem has two halves at word granularity:

  * the MONOTONE half (`processBrauer_isSameComponent_ofBase`, `Brauer/WiringDescConnectivityMono.lean`) — a Brauer
    word never DISCONNECTS: every base same-component membership survives firing any word;
  * the CONVERSE (off-support) half (`processBrauer_isSameComponent_offConfined`,
    `Brauer/WiringDescConnectivityOffConfined.lean`) — a word whose events are confined off two probes introduces NO
    spurious connection.

The word-level `relationAgrees` the shipped `whisker` move (`Brauer/WiringDescConv.lean`) consumes compares
`matchingSameComponent` at the BOUNDARY INDICES.  A collapse / braid word replaces its window's open wires with FRESH
outputs, so the window boundary slot reads a FRESH node id in the fired state versus the base port in the unfired
state.  Bridging that index-vs-node mismatch is exactly PORT-RECONNECTION: the fresh in-window boundary ports
reconnect to the SAME off-window components as the base ports they replace.  It is FALSE for a generic `WiringDesc`
word (a crossing PERMUTES its window ports) but TRUE for each Brauer relation, because both sides carry the same
boundary matching (Barbier, *Diagram categories of Brauer type*, arXiv:2406.18436, Def 2.1 — a Brauer diagram IS the
boundary pairing; Müller–Wrazidlo, arXiv:1902.05517, Rem 3.4 — the A1 zig-zag `= 1`, A4 double-crossing `= 1 ⊗ 1`,
A5 Yang–Baxter same permutation).

## What this file SHIPS (each piece zero-axiom, structural)

  * ★ **`isSameComponent_unionFindJoin_eq_ofSecondDisconnected`** — the SECOND-endpoint mirror of the shipped
    first-endpoint converse (`isSameComponent_unionFindJoin_eq_ofFirstDisconnected`): a join whose SECOND endpoint is
    disconnected from both probes is invisible to them.  This is the exact single-join converse tool the off-support
    half LACKED for an IN-WINDOW join — a crossing / cup arc joins an OLD window strand (possibly in a probe's
    component, so first-disconnected does NOT apply) to a FRESH output (the second endpoint, always disconnected from
    old probes).  The genuinely-new converse building block for port-reconnection.
  * ★ **`stepWiring_crossing_reconnects`** — the crossing generator's TRANSPOSITION reconnection at the links level:
    firing one crossing reconnects its fresh output port `1` to input window port `0` and output port `0` to input
    port `1`.  Offset- and base-parametric (the window nodes stay abstract), via the join reification
    (`stepWiring_links_eq_applyJoinEvents`) + `isSameComponent_unionFindJoin_joined` / `…_ofBase`.  This is the R2
    half of the net-identity: two crossings reconnect each window port to itself (composing this transposition with
    itself).
  * ★ **`relationAgrees_of_matchingComponentRenameRel`** + **`brauerConv_of_matchingComponentRenameRel`** — the
    ASSEMBLY BRIDGE: a `MatchingComponentRenameRel` witness (its `bnodeCorr` = port-reconnection, its `componentComm`
    = partition correspondence) yields the `whisker` move's `relationAgrees` DIRECTLY, and hence a full `BrauerConv`
    convertibility.  This wires the three ingredients — monotone + converse (through `componentComm`) + port-
    reconnection (through `bnodeCorr`) — into one reusable term, so a per-relation net-identity witness flips into a
    contextual convertibility with a single `exact`.

## Honest scope — this does NOT flip `fxBrauer_hasBrauerSoundness`

A per-relation `relationAgrees` needs a full net-identity `MatchingComponentRenameRel` witness: its `bnodeCorr` (the
open-wire positional surgery that maps the boundary index to the reconnected node — this file ships the crossing's
links-level reconnection, the surgery to the boundary index at arbitrary offset is the residual) AND its
`componentComm` over ALL nodes (the freshness-threaded fold converse combining the monotone half with the
second-endpoint converse below).  For the collapse trio (snake / snakeMirror / R2) both sides collapse to the
boundary identity, so the witness is net-identity and buildable; for the overlapping-window R1 (cap-slide) and R3
(Yang–Baxter) the `componentComm` is the cross-order partition independence whose only known renaming route is
REFUTED (`fxBrauer_hasWiringDescBlockSwapWitness = false`, `MatchingGodementComponentCoreSwap`).  So no relation's
`relationAgrees` closes this round; `fxBrauer_hasBrauerSoundness` STAYS `false`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The second-endpoint single-join converse — the in-window port-reconnection tool -/

/-- ★ **One join whose SECOND endpoint is disconnected from both probes is invisible to them.**  The mirror of the
shipped first-endpoint converse (`isSameComponent_unionFindJoin_eq_ofFirstDisconnected`): in the flat-disjunction
characterization `isSameComponent_unionFindJoin`, the disconnected SECOND endpoint `joinRight` carries the false
factor of both off-support disjuncts (`… && secondNode~probeTwo` directly, `… && probeOne~secondNode` after the
symmetry flip), so the join leaves the two probes' same-component view equal to the base view.  Forest-conditioned on
the base only.  This is the exact converse the off-support half needs for an IN-WINDOW join: a crossing / cup arc
joins an OLD window strand (its FIRST endpoint, possibly in a probe's component) to a FRESH output (its SECOND
endpoint, always disconnected from old probes), so first-disconnected does not apply but second-disconnected does. -/
theorem isSameComponent_unionFindJoin_eq_ofSecondDisconnected (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight probeOne probeTwo : Nat)
    (rightProbeOne : isSameComponent links joinRight probeOne = false)
    (rightProbeTwo : isSameComponent links joinRight probeTwo = false) :
    isSameComponent (unionFindJoin links joinLeft joinRight) probeOne probeTwo
      = isSameComponent links probeOne probeTwo := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOne probeTwo, rightProbeTwo,
    show isSameComponent links probeOne joinRight = false from
      (isSameComponent_symm links probeOne joinRight).trans rightProbeOne]
  cases hbase : isSameComponent links probeOne probeTwo <;>
    cases isSameComponent links joinLeft probeOne <;>
    cases isSameComponent links joinLeft probeTwo <;> rfl

/-! ## The crossing's transposition reconnection at the links level -/

/-- ★ **One crossing reconnects its window ports, transposed.**  Firing a single crossing at `position` allocates two
fresh output ports and connects: input window port `0` to output port `1`, and input window port `1` to output port
`0` (the transposition).  Read off the join reification `stepWiring_links_eq_applyJoinEvents` — the crossing's two
arcs `[(0,3),(1,2)]` decode to the two joins `(in₀, out₁)` and `(in₁, out₀)` — with the first join's connection
surviving the second by monotonicity (`isSameComponent_unionFindJoin_ofBase`) and the second by
`isSameComponent_unionFindJoin_joined`.  Offset- and base-parametric: the window nodes stay abstract.  Composing this
transposition with itself is the R2 net-identity — each window port reconnects to the strand it started on. -/
theorem stepWiring_crossing_reconnects (state : WireState) (position : Nat)
    (forest : isUnionFindForest state.links) :
    isSameComponent (stepWiring state position crossingWiring).links
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 0)
        (natListGetAt (stepWiringOutputNodes state crossingWiring) 1) = true
    ∧ isSameComponent (stepWiring state position crossingWiring).links
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 1)
        (natListGetAt (stepWiringOutputNodes state crossingWiring) 0) = true := by
  have hlinks : (stepWiring state position crossingWiring).links
      = unionFindJoin
          (unionFindJoin state.links
            (natListGetAt (stepWiringInputNodes state position crossingWiring) 0)
            (natListGetAt (stepWiringOutputNodes state crossingWiring) 1))
          (natListGetAt (stepWiringInputNodes state position crossingWiring) 1)
          (natListGetAt (stepWiringOutputNodes state crossingWiring) 0) := by
    rw [stepWiring_links_eq_applyJoinEvents state position crossingWiring]; rfl
  refine ⟨?_, ?_⟩
  · rw [hlinks]
    exact isSameComponent_unionFindJoin_ofBase
      (unionFindJoin state.links
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 0)
        (natListGetAt (stepWiringOutputNodes state crossingWiring) 1))
      (isUnionFindForest_unionFindJoin state.links _ _ forest)
      (natListGetAt (stepWiringInputNodes state position crossingWiring) 1)
      (natListGetAt (stepWiringOutputNodes state crossingWiring) 0)
      (natListGetAt (stepWiringInputNodes state position crossingWiring) 0)
      (natListGetAt (stepWiringOutputNodes state crossingWiring) 1)
      (isSameComponent_unionFindJoin_joined state.links forest
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 0)
        (natListGetAt (stepWiringOutputNodes state crossingWiring) 1))
  · rw [hlinks]
    exact isSameComponent_unionFindJoin_joined
      (unionFindJoin state.links
        (natListGetAt (stepWiringInputNodes state position crossingWiring) 0)
        (natListGetAt (stepWiringOutputNodes state crossingWiring) 1))
      (isUnionFindForest_unionFindJoin state.links _ _ forest)
      (natListGetAt (stepWiringInputNodes state position crossingWiring) 1)
      (natListGetAt (stepWiringOutputNodes state crossingWiring) 0)

/-! ## The whisker assembly bridge -/

/-- ★ **A `MatchingComponentRenameRel` witness yields the `whisker` move's `relationAgrees`.**  The boundary
same-component booleans of the two states agree because the boundary nodes correspond under `sigma` (`bnodeCorr` =
port-reconnection) and the roots correspond under `sigma` (`componentComm` = partition correspondence, the
freshness-threaded combination of the monotone + off-support halves).  This is the exact `relationAgrees` shape the
`whisker` constructor consumes — the extracted first half of `extractDiagram_of_matchingComponentRenameRel`, now
exposed as the standalone port-reconnection assembly. -/
theorem relationAgrees_of_matchingComponentRenameRel (bottomCount : Nat) (sigma : Nat → Nat)
    (firstState secondState : WireState)
    (rel : MatchingComponentRenameRel bottomCount sigma firstState secondState) :
    ∀ firstIndex secondIndex,
      firstIndex < bottomCount + firstState.openWires.length →
      secondIndex < bottomCount + firstState.openWires.length →
      matchingSameComponent bottomCount firstState firstIndex secondIndex
        = matchingSameComponent bottomCount secondState firstIndex secondIndex := by
  intro firstIndex secondIndex firstBelow secondBelow
  show (unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
        == unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex))
     = (unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
        == unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex))
  rw [rel.bnodeCorr firstIndex firstBelow, rel.bnodeCorr secondIndex secondBelow]
  exact (rel.componentComm
    (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
    (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex)).symm

/-- ★ **A per-relation net-identity `MatchingComponentRenameRel` witness at the two post-prefix states flips into a
contextual `BrauerConv`.**  Feeds the shipped `whisker` move: `lengthsAgree` / `loopsAgree` come straight from the
witness's `lengthEq` / `loopsEq`, and `relationAgrees` from `relationAgrees_of_matchingComponentRenameRel`.  So once
a relation's net-identity witness (port-reconnection `bnodeCorr` + partition `componentComm`) is built at the two
post-prefix states, its arbitrary-context whiskering is a single `exact` — the assembly the flip rides. -/
theorem brauerConv_of_matchingComponentRenameRel (bottomCount : Nat)
    (prefixAtoms wordLeft wordRight : List BrauerAtom) (sigma : Nat → Nat)
    (rel : MatchingComponentRenameRel bottomCount sigma
        (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft)
        (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)) :
    BrauerConv bottomCount (prefixAtoms ++ wordLeft) (prefixAtoms ++ wordRight) :=
  BrauerConv.whisker bottomCount prefixAtoms wordLeft wordRight rel.lengthEq.symm rel.loopsEq.symm
    (relationAgrees_of_matchingComponentRenameRel bottomCount sigma _ _ rel)

/-! ## Honesty markers -/

/-- **Honesty marker — the second-endpoint single-join converse (the in-window port-reconnection tool) is SHIPPED.**
`isSameComponent_unionFindJoin_eq_ofSecondDisconnected` mirrors the shipped first-endpoint converse for the case a
join's SECOND endpoint (a fresh output, always disconnected from old probes) is the disconnected one, while the FIRST
endpoint (an old window strand) may sit in a probe's component.  This is the exact single-join converse the
off-support half LACKED for an in-window crossing / cup arc.  `= true`. -/
def fxBrauer_hasSecondEndpointJoinConverse : Bool := true

/-- **Honesty marker — the crossing's transposition reconnection is SHIPPED at the links level.**
`stepWiring_crossing_reconnects` proves one crossing reconnects its fresh output ports to its input window ports
(transposed), offset- and base-parametric, via the join reification.  This is the R2 half of the net-identity port-
reconnection (its self-composition reconnects each window port to its original strand — the boundary identity both
sides of R2 carry).  The residual to a full `relationAgrees` is the open-wire positional surgery mapping the boundary
INDEX to this reconnected node at arbitrary offset, plus the `componentComm` freshness-threaded fold converse.
`= true`. -/
def fxBrauer_hasCrossingPortReconnection : Bool := true

/-- **Honesty marker — the port-reconnection => `relationAgrees` => `BrauerConv` assembly bridge is SHIPPED.**
`relationAgrees_of_matchingComponentRenameRel` extracts the `whisker` move's `relationAgrees` from a
`MatchingComponentRenameRel` witness (its `bnodeCorr` = port-reconnection, its `componentComm` = the monotone +
off-support partition correspondence), and `brauerConv_of_matchingComponentRenameRel` feeds it plus the witness's
length / loop agreement into the shipped `whisker` move, yielding a full contextual `BrauerConv`.  So a per-relation
net-identity witness flips into an arbitrary-context convertibility with one `exact`.  `= true`. -/
def fxBrauer_hasPortReconnectionAssemblyBridge : Bool := true

/-- **Honesty marker — no relation's `relationAgrees` closes this round; `fxBrauer_hasBrauerSoundness` STAYS
`false`.**  A per-relation `relationAgrees` needs a full net-identity `MatchingComponentRenameRel` witness at the two
post-prefix states: the `bnodeCorr` open-wire positional surgery (this file ships the crossing's links-level
reconnection; the surgery to the boundary index at arbitrary offset is the residual) AND the `componentComm`
freshness-threaded fold converse (this file ships the second-endpoint single-join converse tool; the fold-level
threading combining it with the monotone half is the residual).  For the collapse trio (snake / snakeMirror / R2)
the witness is net-identity and buildable; for the overlapping-window R1 (cap-slide) and R3 (Yang–Baxter) the
`componentComm` is the cross-order partition independence whose only known renaming route is REFUTED
(`fxBrauer_hasWiringDescBlockSwapWitness = false`).  So `fxBrauer_hasBrauerSoundness` stays `false`, its residual now
sharpened to the two per-relation witness fields (`bnodeCorr` surgery + `componentComm` threading) over the shipped
assembly bridge.  `= false`. -/
def fxBrauer_hasBrauerSoundnessPortReconnectionResidual : Bool := false

end FX1Poly.Polygraph
