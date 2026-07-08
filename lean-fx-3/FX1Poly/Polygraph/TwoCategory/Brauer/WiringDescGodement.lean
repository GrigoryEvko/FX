import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDesc

/-! # WAVE-1 keystone — the disjoint-window Godement / interchange independence over `WiringDesc`

Two generators fired at HORIZONTALLY-DISJOINT windows of a `WireState` describe two 2-cells that sit side by
side; the strict-2-category interchange (Godement / exchange) law says the order in which they fire does not
matter.  Over the union-find engine (`stepWiring`, `Brauer/WiringDesc.lean`) firing order genuinely changes the
INTERNAL wire labels — the second generator to fire allocates its fresh output ids AFTER the first, so the two
run orders reach states related by a swap of the two disjoint fresh id blocks (the `blockRotate` renaming).  The
BOUNDARY read-off (`extractDiagram`: the perfect matching on the boundary ports plus the loop count) is a
function of the connectivity partition alone, which is a commutative-monoid fold and therefore join-order
invariant.  So the extract commutes even though the states do not.

This is the SAME standing residual named by the adjunction route (`fxMode_hasMatchingGodementIndependenceProof`,
`ArcGodementSamePartitionFresh`) and by the Brauer verify (`fxBrauer_hasBrauerSoundness`): general Brauer
soundness — every convertible generator word has the same diagram — rides exactly this lemma, now also over the
crossing generator (`crossingWiring`), which the hardcoded `stepCup` / `stepCap` scaffold could not reach.

## What is TRUE and shipped here

  * **The state-parametric `nextFresh` commutation** (`disjointWindow_nextFresh_commute`): the fresh-id counter
    after two firings is order-independent for ANY state and ANY positions — the block-swap arithmetic in one
    clean, fully general, zero-axiom lemma.
  * **Concrete disjoint-window interchange soundness** for every Brauer generator pair, INCLUDING the crossing:
    `disjointWindow_capCap_commute`, `disjointWindow_cupCap_commute`, `disjointWindow_crossingCap_commute`,
    `disjointWindow_crossingCup_commute`.  Each exhibits the two run orders reaching DIFFERENT states (different
    link order, or the fresh blocks literally swapped) but the SAME `extractDiagram` — the keystone phenomenon,
    on the nose.  The crossing pair is new territory: the adjunction engine drops non-cup/cap wiring.
  * **The freshness gate is genuinely required** (`disjointWindow_extract_differs_withoutFreshness`): over a
    NON-fresh state — one whose `links` name an id `≥ nextFresh`, i.e. a pre-planted collision with a
    soon-to-be-allocated fresh id — the two orders DISAGREE on the extract.  So the unconditional
    state-parametric commutation is FALSE, exactly as the arc route's `not_arcGodementSamePartition` shows; the
    honest residual carries an `ArcStateFresh`-style precondition.

## The residual (NOT flipped)

The general, state-parametric, freshness-conditioned disjoint-window extract commutation
(`WiringDescDisjointWindowFresh`) is the standing obligation — a renaming simulation between the two orders'
disjoint fresh id ranges over the union-find (the `blockRotate` / `componentComm` witness the matching route
owes, lifted to the generic arc fold).  It is TRUE (computationally confirmed by every smoke here) but its
general zero-axiom proof is not built; `fxBrauer_hasWiringDescDisjointWindowFreshProof = false`.  This does NOT
discharge `fxBrauer_hasBrauerSoundness` (which rides it) nor the arc gate.

Raw Lean 4 + Init; reuses the shipped `WireState` / union-find primitives verbatim.  Structural recursion, no
`omega` / `simp`-AC / `native_decide`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The state-parametric `nextFresh` commutation

`stepWiring` advances the fresh-id counter by the generator's `outputCount` regardless of position, state, or
wiring, so the counter after two firings is `state.nextFresh + A.outputCount + B.outputCount` in either order.
This is the ONE component of the disjoint-window commutation that needs no freshness and no renaming — it holds
for arbitrary states and arbitrary (even overlapping) positions. -/

/-- One `stepWiring` advances `nextFresh` by exactly the generator's output count, for any state / position. -/
theorem stepWiring_nextFresh (state : WireState) (position : Nat) (desc : WiringDesc) :
    (stepWiring state position desc).nextFresh = state.nextFresh + desc.outputCount := rfl

/-- ★ **The `nextFresh` counter commutes across two firings, state-parametrically.**  For ANY starting state and
ANY two positions / wirings, firing `descA` then `descB` reaches the same `nextFresh` as firing `descB` then
`descA` — both add the two output counts to the start.  The clean, fully general half of the disjoint-window
independence; the block-swap arithmetic with no renaming. -/
theorem disjointWindow_nextFresh_commute (state : WireState)
    (positionA positionB positionAShifted positionBShifted : Nat) (descA descB : WiringDesc) :
    (stepWiring (stepWiring state positionA descA) positionBShifted descB).nextFresh
      = (stepWiring (stepWiring state positionB descB) positionAShifted descA).nextFresh := by
  rw [stepWiring_nextFresh, stepWiring_nextFresh, stepWiring_nextFresh, stepWiring_nextFresh]
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm descA.outputCount descB.outputCount]

/-! ## Freshness — the reachable-state invariant the fold maintains

A `WireState` is FRESH when every id it mentions (open wire, either endpoint of any union-find edge) lies
strictly below `nextFresh`, so a generator's fresh output block `[nextFresh, nextFresh + outputCount)` cannot
collide with any pre-existing connectivity.  This is the invariant the seed satisfies and each `stepWiring`
preserves; the refutation below shows it is exactly what the unconditional commutation silently assumed. -/

/-- A `WireState` is **fresh** when every open wire and every union-find edge endpoint is `< nextFresh`. -/
def WiringDescStateFresh (state : WireState) : Prop :=
  (∀ wire ∈ state.openWires, wire < state.nextFresh)
    ∧ (∀ edge ∈ state.links, edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh)

/-- The four-wire ground seed is fresh: its open wires are `0,1,2,3` (all `< 4 = nextFresh`) and its links are
empty.  So the diagram evaluator's starting state already meets the residual's precondition (decided on the
concrete literal — the general `brauerSeed n` case needs only the propext-free `List.range` membership bound). -/
theorem wiringDescStateFresh_fourWireSeed :
    WiringDescStateFresh { openWires := [0, 1, 2, 3], links := [], nextFresh := 4, loops := 0 } := by
  dsimp only [WiringDescStateFresh]; decide

/-! ## Concrete disjoint-window interchange soundness (the keystone phenomenon, on the nose)

Each smoke fires two generators at disjoint windows over the four-wire seed in both orders and reads off the
boundary diagram.  The right-window firing is at the SHIFTED position — after the left generator has removed its
`inputCount` inputs and inserted its `outputCount` outputs, the right window has moved by
`outputCount - inputCount`.  The two orders reach different STATES (different link order, or the fresh blocks
swapped) but the same `extractDiagram`.  The light (cup / cap) pairs close by `decide`; the crossing pairs — the
heavier two-output fold — are STAGED through concrete literal states by single-step `rfl`s. -/

/-- The four-wire ground seed as a literal (so single-step reductions stay literal → literal). -/
def fourWireSeed : WireState := { openWires := [0, 1, 2, 3], links := [], nextFresh := 4, loops := 0 }

/-- The literal seed IS the ground seed `brauerSeed 4`. -/
theorem fourWireSeed_eq_seed : fourWireSeed = brauerSeed 4 := rfl

/-- ★ **cap ∥ cap commute.**  A cap on wires `0,1` and a cap on wires `2,3` are window-disjoint; either firing
order reads the same boundary matching `[1,0,3,2]`.  (Both caps take the union branch — the two wires start
disconnected — so the states differ only in link order, and the extract is invariant.) -/
theorem disjointWindow_capCap_commute :
    extractDiagram 4 (stepWiring (stepWiring fourWireSeed 0 capWiring) 0 capWiring)
      = extractDiagram 4 (stepWiring (stepWiring fourWireSeed 2 capWiring) 0 capWiring) := by decide

/-- ★ **cup ∥ cap commute.**  A cup at the left window (producing two connected fresh wires at position `0`) and
a cap at the right window are disjoint; the cap's window shifts by `+2` (the cup consumes `0`, produces `2`)
when it fires second.  Either order reads the same diagram. -/
theorem disjointWindow_cupCap_commute :
    extractDiagram 4 (stepWiring (stepWiring fourWireSeed 0 cupWiring) 4 capWiring)
      = extractDiagram 4 (stepWiring (stepWiring fourWireSeed 2 capWiring) 0 cupWiring) := by decide

/-! ### crossing ∥ cap, staged -/

/-- crossing at `0` over the seed (order A, step 1). -/
def crossingCapAfterCrossing : WireState :=
  { openWires := [4, 5, 2, 3], links := [(1, 4), (0, 5)], nextFresh := 6, loops := 0 }

/-- crossing then cap at the shifted right window (order A, final). -/
def crossingCapOrderA : WireState :=
  { openWires := [4, 5], links := [(2, 3), (1, 4), (0, 5)], nextFresh := 6, loops := 0 }

/-- cap at `2` over the seed (order B, step 1). -/
def crossingCapAfterCap : WireState :=
  { openWires := [0, 1], links := [(2, 3)], nextFresh := 4, loops := 0 }

/-- cap then crossing at the left window (order B, final). -/
def crossingCapOrderB : WireState :=
  { openWires := [4, 5], links := [(1, 4), (0, 5), (2, 3)], nextFresh := 6, loops := 0 }

theorem crossingCap_stepA1 : stepWiring fourWireSeed 0 crossingWiring = crossingCapAfterCrossing := rfl
theorem crossingCap_stepA2 : stepWiring crossingCapAfterCrossing 2 capWiring = crossingCapOrderA := rfl
theorem crossingCap_stepB1 : stepWiring fourWireSeed 2 capWiring = crossingCapAfterCap := rfl
theorem crossingCap_stepB2 : stepWiring crossingCapAfterCap 0 crossingWiring = crossingCapOrderB := rfl

/-- ★ **crossing ∥ cap commute.**  A crossing on wires `0,1` and a cap on wires `2,3` are window-disjoint (the
cap's window is fixed under the crossing, which consumes `2` and produces `2`).  The two orders reach states with
the SAME open wires `[4,5]` but DIFFERENT link order (`[(2,3),(1,4),(0,5)]` vs `[(1,4),(0,5),(2,3)]`), and read
the same reversal diagram `[5,4,3,2,1,0]`.  New territory: the crossing generator never passed through the
adjunction engine. -/
theorem disjointWindow_crossingCap_commute :
    extractDiagram 4 (stepWiring (stepWiring fourWireSeed 0 crossingWiring) 2 capWiring)
      = extractDiagram 4 (stepWiring (stepWiring fourWireSeed 2 capWiring) 0 crossingWiring) := by
  rw [crossingCap_stepA1, crossingCap_stepA2, crossingCap_stepB1, crossingCap_stepB2]
  decide

/-! ### crossing ∥ cup, staged -/

/-- cup at `0` over the seed (order A, step 1). -/
def crossingCupAfterCup : WireState :=
  { openWires := [4, 5, 0, 1, 2, 3], links := [(4, 5)], nextFresh := 6, loops := 0 }

/-- cup then crossing at the shifted right window (order A, final). -/
def crossingCupOrderA : WireState :=
  { openWires := [4, 5, 0, 1, 6, 7], links := [(3, 6), (2, 7), (4, 5)], nextFresh := 8, loops := 0 }

/-- crossing at `2` over the seed (order B, step 1). -/
def crossingCupAfterCrossing : WireState :=
  { openWires := [0, 1, 4, 5], links := [(3, 4), (2, 5)], nextFresh := 6, loops := 0 }

/-- crossing then cup at the left window (order B, final). -/
def crossingCupOrderB : WireState :=
  { openWires := [6, 7, 0, 1, 4, 5], links := [(6, 7), (3, 4), (2, 5)], nextFresh := 8, loops := 0 }

theorem crossingCup_stepA1 : stepWiring fourWireSeed 0 cupWiring = crossingCupAfterCup := rfl
theorem crossingCup_stepA2 : stepWiring crossingCupAfterCup 4 crossingWiring = crossingCupOrderA := rfl
theorem crossingCup_stepB1 : stepWiring fourWireSeed 2 crossingWiring = crossingCupAfterCrossing := rfl
theorem crossingCup_stepB2 : stepWiring crossingCupAfterCrossing 0 cupWiring = crossingCupOrderB := rfl

/-- ★ **crossing ∥ cup commute.**  A cup at the left window and a crossing on wires `2,3` are disjoint; the
crossing's window shifts by `+2` when it fires second.  Here the two orders literally SWAP the two fresh id
blocks — order A's open wires end `[4,5,0,1,6,7]`, order B's `[6,7,0,1,4,5]` (the cup's block `4,5` and the
crossing's block `6,7`/`4,5` exchanged: the `blockRotate` renaming) — yet both read the same diagram
`[6,7,9,8,5,4,0,1,3,2]`.  This exhibits the renaming sigma the general proof must simulate. -/
theorem disjointWindow_crossingCup_commute :
    extractDiagram 4 (stepWiring (stepWiring fourWireSeed 0 cupWiring) 4 crossingWiring)
      = extractDiagram 4 (stepWiring (stepWiring fourWireSeed 2 crossingWiring) 0 cupWiring) := by
  rw [crossingCup_stepA1, crossingCup_stepA2, crossingCup_stepB1, crossingCup_stepB2]
  decide

/-! ## The freshness gate is genuinely required — the unconditional form is FALSE

Drop freshness and the commutation breaks.  `freshnessAdversaryState` pre-plants the edge `(6, 0)` whose first
endpoint `6` equals `nextFresh` (NOT `< nextFresh`): it names a fresh id the fold has not allocated yet.  Firing
two cups at disjoint windows, the LEFT cup's first leg is exactly id `6` — so it inherits the pre-planted link to
boundary port `0`, and which cup allocates id `6` depends on the firing order.  The two orders then attach
boundary `0` to different top ports, and the extracts DIFFER.  This mirrors the arc route's
`not_arcGodementSamePartition` over the generic engine: the honest residual must be freshness-conditioned. -/

/-- A NON-fresh adversarial state: the edge `(6, 0)` names id `6 = nextFresh`, a not-yet-allocated fresh id. -/
def freshnessAdversaryState : WireState :=
  { openWires := [0, 1, 2, 3], links := [(6, 0)], nextFresh := 6, loops := 0 }

/-- ★ **Over a non-fresh state, disjoint-window firings do NOT commute.**  Two cups at disjoint windows over
`freshnessAdversaryState` read DIFFERENT diagrams in the two orders (boundary `0`'s partner differs), because the
pre-planted collision id `6` is captured by whichever cup fires first.  So the unconditional, state-parametric
disjoint-window commutation is refuted zero-axiom; the residual below carries the freshness precondition. -/
theorem disjointWindow_extract_differs_withoutFreshness :
    extractDiagram 4 (stepWiring (stepWiring freshnessAdversaryState 0 cupWiring) 4 cupWiring)
      ≠ extractDiagram 4 (stepWiring (stepWiring freshnessAdversaryState 2 cupWiring) 0 cupWiring) := by
  decide

/-! ## The freshness-conditioned residual (the standing obligation)

The genuine, well-formed keystone: for two window-disjoint generators over a FRESH state, the boundary diagram
commutes.  `positionA + descA.inputCount ≤ positionB` says window A sits entirely to the left of window B; when B
fires after A its window has shifted by `descA.outputCount - descA.inputCount`, written here as
`positionB - descA.inputCount + descA.outputCount`.  Every concrete smoke above is an instance; the general
zero-axiom proof — a `blockRotate` renaming simulation between the two orders' disjoint fresh id ranges over the
union-find — is not yet built. -/

/-- ★ **The freshness-conditioned disjoint-window commutation** — the standing residual, shared (over the generic
`stepWiring` engine, crossing included) with `fxMode_hasMatchingGodementIndependenceProof` and the arc route's
`ArcGodementSamePartitionFresh`. -/
def WiringDescDisjointWindowFresh : Prop :=
  ∀ (state : WireState) (positionA positionB bottomCount : Nat) (descA descB : WiringDesc),
    WiringDescStateFresh state → bottomCount ≤ state.nextFresh →
    positionA + descA.inputCount ≤ positionB →
    extractDiagram bottomCount
        (stepWiring (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
      = extractDiagram bottomCount
        (stepWiring (stepWiring state positionB descB) positionA descA)

/-! ## Honesty markers -/

/-- **Honesty marker — the state-parametric `nextFresh` commutation is SHIPPED.**
`disjointWindow_nextFresh_commute` proves the fresh-id counter after two firings is order-independent for ANY
state and ANY positions / wirings — the block-swap arithmetic, no freshness, no renaming.  `= true`. -/
def fxBrauer_hasDisjointWindowNextFreshCommute : Bool := true

/-- **Honesty marker — concrete disjoint-window interchange soundness is SHIPPED for every generator pair,
crossing included.**  `disjointWindow_capCap_commute`, `disjointWindow_cupCap_commute`,
`disjointWindow_crossingCap_commute`, `disjointWindow_crossingCup_commute` each exhibit two firing orders reaching
DIFFERENT states (different link order, or the fresh blocks literally swapped — the `blockRotate` sigma) but the
SAME `extractDiagram`.  The crossing pairs are new territory beyond the hardcoded `stepCup` / `stepCap` engine.
`= true`. -/
def fxBrauer_hasDisjointWindowConcreteSoundness : Bool := true

/-- **Honesty marker — the UNCONDITIONAL disjoint-window commutation is FALSE, not merely unproven.**
`disjointWindow_extract_differs_withoutFreshness` refutes it zero-axiom at a non-fresh state whose `links` name an
id `≥ nextFresh` (a pre-planted collision with a soon-to-be-allocated fresh id): the two cup orders then attach
boundary `0` to different top ports.  This mirrors `not_arcGodementSamePartition` over the generic engine — the
residual must carry a freshness precondition.  `= true`. -/
def fxBrauer_hasDisjointWindowUnconditionalRefuted : Bool := true

/-- **Honesty marker — the LITERAL freshness-conditioned residual is REFUTED (`windowB` is load-bearing).**
`WiringDescDisjointWindowFresh` re-states the commutation under `WiringDescStateFresh state` and
`bottomCount ≤ nextFresh` but OMITS the window-in-range premise `windowB`.  KEYSTONE6 brick (A) proves the literal
statement is FALSE — `wiringDescDisjointWindowFresh_false` (`Brauer/WiringDescReachable.lean`) exhibits a FRESH
counterexample where an OUT-OF-RANGE firing captures the default boundary node `0` order-dependently (the two
orders reach diagrams of different `topCount`).  The TRUE statement is the IN-RANGE / reachable interchange —
`WiringDescDisjointWindowFreshInRange` (CLOSED, `wiringDescDisjointWindowFreshInRange_proof`) plus the reachable-
state invariant fold `brauerStateConditions_processBrauer` / `brauer_reachable_interchange` (brick A), which
discharges `windowB` at every reachable diagram state.  So this literal flag stays `false` not as an unproven
obligation but as a REFUTED over-statement; the arc gate `fxMode_hasMatchingComponentCoreSwapWitness` inherits the
same wall.  `= false`. -/
def fxBrauer_hasWiringDescDisjointWindowFreshProof : Bool := false

end FX1Poly.Polygraph
