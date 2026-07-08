import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescOpenMap

/-! # KEYSTONE6 brick (A) — the reachable-state invariant + the refutation of the literal residual

The in-range disjoint-window interchange (`wiringDescCoreSwap_extract`, `WiringDescDisjointWindowFreshInRange`,
`Brauer/WiringDescOpenMap.lean`) carries three preconditions the disjoint-window surgery genuinely consumes:
`WiringDescStateFresh state`, `isUnionFindForest state.links`, `0 < state.nextFresh` — plus `windowB` (the firing
window sits inside the open-wire list).  This file closes TWO things about the gap to the LITERAL,
`windowB`-free residual `WiringDescDisjointWindowFresh` (`Brauer/WiringDescGodement.lean`):

## What is CLOSED (brick A, constructive)

  * ★ **`wiringDescStateFresh_stepWiring`** — one `stepWiring` step PRESERVES freshness (every mentioned id
    `< nextFresh`), for ANY position / wiring (even out of range — an out-of-range read defaults to node `0`, still
    below `nextFresh` by `0 < nextFresh`).  The genuinely-new fold lemma: the arc fold `stepWiringArcs` keeps every
    union-find edge endpoint bounded (`stepWiringArcs_all_lt`, via `unionFindJoin_all_lt` +
    `unionFindRootOf_lt_of_fresh` per join), and the splice of the fresh output block into the input-removed list
    stays bounded (`natListInsertAt_all_lt` / `natListRemoveManyAt_all_lt`).
  * ★ **`BrauerStateConditions` + `brauerStateConditions_processBrauer`** — the four reachable-state invariants
    (`fresh` / `forest` / `nfPos` / `bottomLe`) are PRESERVED along the WHOLE `processBrauer` fold, from the
    `brauerSeed` (which satisfies them for `0 < bottomCount`).  So EVERY reachable diagram state meets exactly the
    in-range interchange's preconditions.
  * ★ **`brauer_reachable_interchange`** — the disjoint-window interchange holds at EVERY reachable diagram state
    `processBrauer (brauerSeed bottomCount) prefixAtoms`, for any in-range disjoint pair, UNCONDITIONALLY on the
    prefix word — the reachable-state Godement law, `windowB` the sole remaining site condition (automatically met
    when the two generators fire in range).

## What is REFUTED (brick A, the honest wall)

  * ★ **`wiringDescDisjointWindowFresh_false`** — the LITERAL `WiringDescDisjointWindowFresh` (which omits
    `windowB`) is FALSE, refuted zero-axiom by `decide` at a FRESH state.  Counterexample: over
    `⟨[0,1,5,2], [], 6, 0⟩` (fresh) an identity strand fired OUT OF RANGE at position `4` and a cup at position `5`
    (disjoint: `4 + 1 ≤ 5`) reach DIFFERENT diagrams in the two orders — even different `topCount` (`7` vs `6`).
    An out-of-range read snaps to the default node `0`, which is a genuine boundary wire, so which order captures
    it changes the boundary matching.  Note `disjoint + windowB` forces `descA` in range too, so this
    counterexample lives exactly in the `¬windowB` regime — `windowB` is LOAD-BEARING, not bookkeeping.  Hence
    `fxBrauer_hasWiringDescDisjointWindowFreshProof` STAYS `false`, now sharpened from "unproven" to "refuted".

The honest resolution: the interchange law is the IN-RANGE / reachable-state statement (CLOSED); the literal
`windowB`-free form is not merely open but false, and the arc route's analogous
`fxMode_hasMatchingComponentCoreSwapWitness` inherits the same wall.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Block-removal membership and bound -/

/-- Every surviving wire of a generic-width block removal is a member of the original list.  Structural on the
removal's own matcher (count, then list / position). -/
theorem mem_natListRemoveManyAt :
    (wires : List Nat) → (position count x : Nat) →
    x ∈ natListRemoveManyAt wires position count → x ∈ wires
  | wires, position, 0, _, hx => by rw [removeManyAt_zero wires position] at hx; exact hx
  | [], _, _ + 1, _, hx => by cases hx
  | headWire :: restWires, 0, count + 1, x, hx => by
      rw [removeManyAt_zero_cons headWire restWires count] at hx
      exact List.Mem.tail headWire (mem_natListRemoveManyAt restWires 0 count x hx)
  | headWire :: restWires, position + 1, count, x, hx => by
      rw [removeManyAt_succ_cons headWire restWires position count] at hx
      cases hx with
      | head => exact List.Mem.head _
      | tail _ tailMembership =>
          exact List.Mem.tail headWire (mem_natListRemoveManyAt restWires position count x tailMembership)

/-- A block removal keeps every surviving wire bounded. -/
theorem natListRemoveManyAt_all_lt (bound : Nat) (wires : List Nat) (position count : Nat)
    (allBelow : ∀ wire ∈ wires, wire < bound) :
    ∀ wire ∈ natListRemoveManyAt wires position count, wire < bound :=
  fun wire wireInRemoved => allBelow wire (mem_natListRemoveManyAt wires position count wire wireInRemoved)

/-! ## The decoded endpoint node is bounded -/

/-- A decoded wiring endpoint node is bounded: both branches of `wiringEndpointNode` read (`natListGetAt`) a
bounded node list, defaulting past-the-end to `0` (`< bound` by `0 < bound`). -/
theorem wiringEndpointNode_lt (bound : Nat) (nfPos : 0 < bound) (inputNodes outputNodes : List Nat)
    (inputCount tag : Nat)
    (inputBelow : ∀ wire ∈ inputNodes, wire < bound) (outputBelow : ∀ wire ∈ outputNodes, wire < bound) :
    wiringEndpointNode inputNodes outputNodes inputCount tag < bound := by
  show (if tag < inputCount then natListGetAt inputNodes tag else natListGetAt outputNodes (tag - inputCount))
      < bound
  split
  · exact natListGetAt_lt bound nfPos inputNodes tag inputBelow
  · exact natListGetAt_lt bound nfPos outputNodes (tag - inputCount) outputBelow

/-! ## The arc fold preserves the union-find bound -/

/-- ★ **The generic arc fold keeps every union-find edge endpoint bounded.**  Each `stepWiringArcs` step either
leaves `links` untouched (loop branch) or `unionFindJoin`s two decoded endpoint nodes (both bounded by
`wiringEndpointNode_lt`, their roots bounded by `unionFindRootOf_lt_of_fresh`, the join bounded by
`unionFindJoin_all_lt`); structural on the arc list. -/
theorem stepWiringArcs_all_lt (bound : Nat) (nfPos : 0 < bound) (inputNodes outputNodes : List Nat)
    (inputCount : Nat)
    (inputBelow : ∀ wire ∈ inputNodes, wire < bound) (outputBelow : ∀ wire ∈ outputNodes, wire < bound) :
    (arcs : List (Nat × Nat)) → (loopsAcc : Nat) → (links : List (Nat × Nat)) →
    (∀ edge ∈ links, edge.1 < bound ∧ edge.2 < bound) →
    ∀ edge ∈ (stepWiringArcs inputNodes outputNodes inputCount arcs loopsAcc links).fst,
      edge.1 < bound ∧ edge.2 < bound
  | [], _, links, linksBelow => linksBelow
  | (firstTag, secondTag) :: rest, loopsAcc, links, linksBelow => by
      show ∀ edge ∈ (stepWiringArcs inputNodes outputNodes inputCount ((firstTag, secondTag) :: rest) loopsAcc
          links).fst, edge.1 < bound ∧ edge.2 < bound
      dsimp only [stepWiringArcs]
      cases hbranch : isSameComponent links (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
          (wiringEndpointNode inputNodes outputNodes inputCount secondTag) with
      | true =>
          exact stepWiringArcs_all_lt bound nfPos inputNodes outputNodes inputCount inputBelow outputBelow rest
            (loopsAcc + 1) links linksBelow
      | false =>
          exact stepWiringArcs_all_lt bound nfPos inputNodes outputNodes inputCount inputBelow outputBelow rest
            loopsAcc
            (unionFindJoin links (wiringEndpointNode inputNodes outputNodes inputCount firstTag)
              (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
            (unionFindJoin_all_lt bound links _ _ linksBelow
              (unionFindRootOf_lt_of_fresh links bound (fun edge edgeMem => (linksBelow edge edgeMem).2) _
                (wiringEndpointNode_lt bound nfPos inputNodes outputNodes inputCount firstTag inputBelow
                  outputBelow))
              (unionFindRootOf_lt_of_fresh links bound (fun edge edgeMem => (linksBelow edge edgeMem).2) _
                (wiringEndpointNode_lt bound nfPos inputNodes outputNodes inputCount secondTag inputBelow
                  outputBelow)))

/-! ## One `stepWiring` step preserves freshness -/

/-- ★ **One `stepWiring` step preserves freshness** — for ANY position / wiring (out-of-range reads default to `0`,
still below `nextFresh` by `nfPos`).  The open wires stay bounded (`natListRemoveManyAt_all_lt` +
`natListInsertAt_all_lt`, the fresh output block below `nextFresh + outputCount` by `map_add_lt`), and the arc-fold
links stay bounded (`stepWiringArcs_all_lt`).  The genuinely-new reachable-state invariant lemma. -/
theorem wiringDescStateFresh_stepWiring (state : WireState) (position : Nat) (desc : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh) :
    WiringDescStateFresh (stepWiring state position desc) := by
  obtain ⟨hopen, hlinks⟩ := fresh
  have hle : state.nextFresh ≤ state.nextFresh + desc.outputCount := Nat.le_add_right _ _
  have hNewPos : 0 < state.nextFresh + desc.outputCount := Nat.lt_of_lt_of_le nfPos hle
  have hOpenOld : ∀ wire ∈ state.openWires, wire < state.nextFresh + desc.outputCount :=
    fun wire wireMem => Nat.lt_of_lt_of_le (hopen wire wireMem) hle
  have hOutBlock : ∀ node ∈ (List.range desc.outputCount).map (· + state.nextFresh),
      node < state.nextFresh + desc.outputCount :=
    fun node nodeMem =>
      map_add_lt state.nextFresh desc.outputCount (List.range desc.outputCount)
        (fun index indexMem => mem_range_imp_lt indexMem) node nodeMem
  have hLinksOld : ∀ edge ∈ state.links,
      edge.1 < state.nextFresh + desc.outputCount ∧ edge.2 < state.nextFresh + desc.outputCount :=
    fun edge edgeMem =>
      ⟨Nat.lt_of_lt_of_le (hlinks edge edgeMem).1 hle, Nat.lt_of_lt_of_le (hlinks edge edgeMem).2 hle⟩
  have hInputNodes : ∀ node ∈ natListSliceAt state.openWires position desc.inputCount,
      node < state.nextFresh + desc.outputCount :=
    fun node nodeMem =>
      natListSliceAt_all_lt (state.nextFresh + desc.outputCount) state.openWires hOpenOld position
        desc.inputCount node nodeMem
  refine ⟨?_, ?_⟩
  · show ∀ wire ∈ natListInsertAt (natListRemoveManyAt state.openWires position desc.inputCount) position
        ((List.range desc.outputCount).map (· + state.nextFresh)), wire < state.nextFresh + desc.outputCount
    exact natListInsertAt_all_lt (state.nextFresh + desc.outputCount)
      (natListRemoveManyAt state.openWires position desc.inputCount) position
      ((List.range desc.outputCount).map (· + state.nextFresh))
      (natListRemoveManyAt_all_lt (state.nextFresh + desc.outputCount) state.openWires position desc.inputCount
        hOpenOld)
      hOutBlock
  · show ∀ edge ∈ (stepWiringArcs (natListSliceAt state.openWires position desc.inputCount)
        ((List.range desc.outputCount).map (· + state.nextFresh)) desc.inputCount desc.arcs 0 state.links).fst,
        edge.1 < state.nextFresh + desc.outputCount ∧ edge.2 < state.nextFresh + desc.outputCount
    exact stepWiringArcs_all_lt (state.nextFresh + desc.outputCount) hNewPos
      (natListSliceAt state.openWires position desc.inputCount)
      ((List.range desc.outputCount).map (· + state.nextFresh)) desc.inputCount hInputNodes hOutBlock
      desc.arcs 0 state.links hLinksOld

/-! ## The four reachable-state invariants, threaded along the fold -/

/-- ★ The four invariants every reachable diagram state satisfies — exactly the in-range interchange's
preconditions.  `fresh` (every id `< nextFresh`), `forest` (the union-find is a rooted forest), `nfPos`
(non-empty boundary), `bottomLe` (the bottom boundary fits below the counter). -/
structure BrauerStateConditions (bottomCount : Nat) (state : WireState) : Prop where
  /-- Every open wire and every union-find edge endpoint is below `nextFresh`. -/
  fresh : WiringDescStateFresh state
  /-- The union-find `links` form a rooted forest. -/
  forest : isUnionFindForest state.links
  /-- The fresh-id counter is positive (a non-empty boundary). -/
  nfPos : 0 < state.nextFresh
  /-- The bottom boundary count fits below the fresh-id counter. -/
  bottomLe : bottomCount ≤ state.nextFresh

/-- ★ **One Brauer atom preserves all four invariants.**  `fresh` by `wiringDescStateFresh_stepWiring`, `forest` by
`stepWiring_links_isUnionFindForest`, `nfPos` / `bottomLe` because `nextFresh` only grows
(`stepWiring_nextFresh`). -/
theorem brauerStateConditions_stepBrauerAtom (bottomCount : Nat) (state : WireState) (atom : BrauerAtom)
    (cond : BrauerStateConditions bottomCount state) :
    BrauerStateConditions bottomCount (stepBrauerAtom state atom) where
  fresh := wiringDescStateFresh_stepWiring state atom.position atom.wiring cond.fresh cond.nfPos
  forest := stepWiring_links_isUnionFindForest state atom.position atom.wiring cond.forest
  nfPos := Nat.lt_of_lt_of_le cond.nfPos (Nat.le_add_right state.nextFresh atom.wiring.outputCount)
  bottomLe := Nat.le_trans cond.bottomLe (Nat.le_add_right state.nextFresh atom.wiring.outputCount)

/-- ★ **The WHOLE `processBrauer` fold preserves all four invariants.**  Structural on the atom list. -/
theorem brauerStateConditions_processBrauer (bottomCount : Nat) :
    (atoms : List BrauerAtom) → (state : WireState) → BrauerStateConditions bottomCount state →
    BrauerStateConditions bottomCount (processBrauer state atoms)
  | [], _, cond => cond
  | atom :: rest, state, cond =>
      brauerStateConditions_processBrauer bottomCount rest (stepBrauerAtom state atom)
        (brauerStateConditions_stepBrauerAtom bottomCount state atom cond)

/-- The `brauerSeed` satisfies all four invariants when the boundary is non-empty. -/
theorem brauerStateConditions_seed (bottomCount : Nat) (bottomPos : 0 < bottomCount) :
    BrauerStateConditions bottomCount (brauerSeed bottomCount) where
  fresh := ⟨fun _ wireInRange => mem_range_imp_lt wireInRange, fun _ edgeInNil => by cases edgeInNil⟩
  forest := isUnionFindForest_nil
  nfPos := bottomPos
  bottomLe := Nat.le_refl bottomCount

/-- ★ **Every reachable diagram state satisfies the four in-range interchange preconditions.** -/
theorem brauerReachable_conditions (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (atoms : List BrauerAtom) :
    BrauerStateConditions bottomCount (processBrauer (brauerSeed bottomCount) atoms) :=
  brauerStateConditions_processBrauer bottomCount atoms (brauerSeed bottomCount)
    (brauerStateConditions_seed bottomCount bottomPos)

/-! ## The reachable-state interchange -/

/-- ★ **The disjoint-window interchange holds at EVERY reachable diagram state.**  For any prefix word, at the
reachable state `processBrauer (brauerSeed bottomCount) prefixAtoms`, two generators fired at an in-range disjoint
pair commute at the boundary — UNCONDITIONALLY on the prefix (the reachability fold discharges `fresh` / `forest` /
`nfPos` / `bottomLe`).  `windowB` is the sole remaining site condition, automatically met when both generators
fire in range. -/
theorem brauer_reachable_interchange (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (positionA positionB : Nat) (descA descB : WiringDesc)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount
        ≤ (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) :
    extractDiagram bottomCount
        (stepWiring (stepWiring (processBrauer (brauerSeed bottomCount) prefixAtoms) positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
      = extractDiagram bottomCount
        (stepWiring (stepWiring (processBrauer (brauerSeed bottomCount) prefixAtoms) positionB descB)
          positionA descA) := by
  have cond := brauerReachable_conditions bottomCount bottomPos prefixAtoms
  exact wiringDescCoreSwap_extract (processBrauer (brauerSeed bottomCount) prefixAtoms) positionA positionB
    bottomCount descA descB cond.fresh cond.nfPos cond.forest cond.bottomLe disjoint windowB

/-! ## The literal residual is FALSE — the honest wall -/

/-- The fresh adversarial state for the refutation: `⟨[0,1,5,2], [], 6, 0⟩` is fresh (every wire `0,1,5,2 < 6`,
links empty) but its open-wire list has length `4 < 6 = nextFresh`, so a window at position `4`/`5` is out of
range. -/
def outOfRangeFreshState : WireState := { openWires := [0, 1, 5, 2], links := [], nextFresh := 6, loops := 0 }

/-- The adversarial state is fresh. -/
theorem outOfRangeFreshState_fresh : WiringDescStateFresh outOfRangeFreshState := by
  dsimp only [WiringDescStateFresh, outOfRangeFreshState]; decide

/-- ★ **The LITERAL `WiringDescDisjointWindowFresh` is FALSE.**  Over the FRESH state
`outOfRangeFreshState = ⟨[0,1,5,2], [], 6, 0⟩`, an identity strand fired OUT OF RANGE at position `4` and a cup at
position `5` are disjoint (`4 + 1 ≤ 5`) yet reach DIFFERENT boundary diagrams in the two firing orders — even
different `topCount` (AB order `7`, BA order `6`).  An out-of-range read snaps to the default node `0`, a genuine
boundary wire, whose capture is order-dependent.  Since `disjoint + windowB` would force `positionA` in range too,
this counterexample lives exactly in the `¬windowB` regime: `windowB` is LOAD-BEARING.  Refuted zero-axiom by
`decide`; the residual can only ever be the IN-RANGE / reachable statement. -/
theorem wiringDescDisjointWindowFresh_false : ¬ WiringDescDisjointWindowFresh := by
  intro hyp
  have collision := hyp outOfRangeFreshState 4 5 1 identityWiring cupWiring outOfRangeFreshState_fresh
    (by decide) (by decide)
  exact absurd collision (by decide)

/-! ## Honesty markers -/

/-- **Honesty marker — one `stepWiring` step preserves freshness, for ANY position.**
`wiringDescStateFresh_stepWiring`: the arc fold keeps every union-find edge bounded (`stepWiringArcs_all_lt`) and
the splice of the fresh output block stays bounded, even out of range (default node `0 < nextFresh` by `nfPos`).
The genuinely-new reachable-state invariant lemma.  `= true`. -/
def fxBrauer_hasWiringDescStateFreshStep : Bool := true

/-- **Honesty marker — the four reachable-state invariants are threaded along the WHOLE fold.**
`brauerStateConditions_processBrauer` propagates `fresh` / `forest` / `nfPos` / `bottomLe` from the seed
(`brauerStateConditions_seed`, for `0 < bottomCount`) through every atom, so `brauerReachable_conditions` shows
EVERY reachable diagram state meets exactly the in-range interchange's preconditions, and
`brauer_reachable_interchange` reads the disjoint-window Godement law off at every reachable state
unconditionally on the prefix.  `= true`. -/
def fxBrauer_hasReachableStateInvariant : Bool := true

/-- **Honesty marker — the LITERAL `WiringDescDisjointWindowFresh` is REFUTED, not merely unproven.**
`wiringDescDisjointWindowFresh_false` exhibits a FRESH counterexample where an out-of-range firing captures the
default boundary node `0` in an order-dependent way — the two orders reach diagrams of different `topCount`.  Since
`disjoint + windowB` forces the firing in range, the counterexample is exactly the `¬windowB` degeneracy: the
`windowB` hypothesis is LOAD-BEARING.  So `fxBrauer_hasWiringDescDisjointWindowFreshProof` stays `false` sharpened
to "refuted"; the true statement is the IN-RANGE / reachable interchange (CLOSED,
`fxBrauer_hasWiringDescDisjointWindowFreshInRangeProof` + `fxBrauer_hasReachableStateInvariant`), and the arc
route's analogous `fxMode_hasMatchingComponentCoreSwapWitness` inherits the same wall.  `= true`. -/
def fxBrauer_hasWiringDescDisjointWindowFreshRefuted : Bool := true

end FX1Poly.Polygraph
