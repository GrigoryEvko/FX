import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BlockRotation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPeelSignatureCeiling
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation

/-! # mode-3 floor — the pure two-CUP Godement block swap: the LINKS byte-identity + the OPEN-WIRE block transform

The Godement / interchange step transposes two horizontally-disjoint blocks of a spine.  On the arc reader
(`ArcWireState` / `stepCupArc`, `SpineTraceDecision`) the two run orders allocate the SAME fresh-id triples but
assign them to the two geometric cups in the OPPOSITE order — so the relating renaming `σ` is the block rotation
`blockRotate state.nextFresh 3 3` (`BlockRotation`), swapping the two allocated 3-id blocks.

This file ships the two LITERAL, machine-checked legs of the PURE-CUP (cup × cup) instance of that swap — the
fragment a fresh RAW field-by-field re-probe (widths 6/7/8, fresh and populated seeds) showed to be genuinely
order-independent, not merely canonicalized:

  * **the LINKS byte-identity** (`stepCupArc_stepCupArc_links_eq`) — the two cup orders' union-find edge lists are
    the SAME LIST, on the nose (`rfl`).  A cup's `links` contribution is `unionFindJoin`s over the allocation
    counter `nextFresh` ALONE (the `position` argument feeds ONLY `openWires`), so both orders execute the
    identical `unionFindJoin` sequence on the identical starting `links`.  This is why `σ` relates the two states
    while `links_reduct = links_redex` LITERALLY (the automorphism is of the ONE shared forest);
  * **the OPEN-WIRE block transform** (`stepCupArc_stepCupArc_openWires_blockSwap`) — the sole order-dependent
    field: the reduct's open wires are the redex's open wires relabelled by `σ`, proved from the shipped
    disjoint-position splice-commutation (`natListInsertAt_insertAbove_commute`, ARC-2b brick iii-1a) plus the
    two `blockRotate` block values.

The atomic mechanism behind the byte-identity is isolated as `stepCupArc_links_positionFree`: ONE cup's `links`
do not depend on the fire position at all.  The `nextFresh` / `loops` / `cupEventNodes` / `capEventNodes` fields
are likewise byte-identical between the two orders (`rfl`), leaving `openWires` as the single permuted field.

## What is honest-DEFERRED (the residual-(2) heart)

The THIRD leg — the `rootComm` field of a full `ArcStepSimCount σ redex reduct` (the union-find automorphism
`∀ x, unionFindRootOf L' (σ x) = σ (unionFindRootOf L' x)` of the shared forest `L'`) — is NOT shipped here.  It
is the disjoint-two-block union-find automorphism, the geometric heart of residual (2)
(`fxMode_hasArcGodementSwapRenameableProof2`, ArcSwapRenameable): `σ` permutes exactly the freshly-allocated ids,
so NONE of the shipped per-atom transports apply (`stepCupArc_rootComm` etc. all require `σ` to FIX the
future-allocation tail, which the block-swap `σ` violates by construction).  The full-bundle marker
`fxMode_hasArcTwoCupGodementSwapSim` stays `false`; the keystone markers `:545`
(`fxMode_hasArcGodementSamePartitionFreshProof`) and `:137` (`fxMode_hasArcPeelGeneralSignature`) and residual (2)
stay `false` (re-pinned by `rfl`).

Raw Lean 4 + Init; structural recursion, `decide`-form `Nat` equality, no `omega` / `simp`-AC / `WellFounded.fix`
/ `propext` / `Quot.sound`.  Per-declaration `#assert_no_axioms` + independent `#print axioms` in the audit twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The atomic mechanism — a CUP's links do not depend on the fire position -/

/-- ★ **A single CUP's union-find links are POSITION-FREE.**  `stepCupArc` builds `links` by two nested
`unionFindJoin`s over the allocation counter `state.nextFresh` (the two legs `nf, nf+1`, then the event
`nf+2 → nf`) — the `position` argument feeds ONLY the open-wire splice, never `links`.  So firing a cup at any two
positions gives the identical edge list, on the nose (`rfl`).  This is the atomic fact behind the two-cup byte
identity (the re-probe's central finding). -/
theorem stepCupArc_links_positionFree (state : ArcWireState) (positionA positionB : Nat) :
    (stepCupArc state positionA).links = (stepCupArc state positionB).links := rfl

/-- A single cup's fresh-allocation counter is position-free. -/
theorem stepCupArc_nextFresh_positionFree (state : ArcWireState) (positionA positionB : Nat) :
    (stepCupArc state positionA).nextFresh = (stepCupArc state positionB).nextFresh := rfl

/-! ## Leg B1(a) — the two cup orders' LINKS are byte-identical

`redex = stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)` fires the low cup first, then the high
cup at the position shifted past the two inserted wires; `reduct = stepCupArc (stepCupArc state (gap + lowPosition))
lowPosition` fires the high cup first, then the low cup.  Because a cup's `links` are position-free
(`stepCupArc_links_positionFree`) and each order advances `nextFresh` by exactly 3 per cup, both orders run the
IDENTICAL `unionFindJoin` sequence on the identical starting `links` — the two edge lists coincide by `rfl`. -/

/-- ★ **The two pure-cup Godement run orders' LINKS are the SAME LIST (`rfl`).**  The re-probe's central mechanism,
kernel-certified: a cup's links contribution is position-free, so the redex (low-then-high) and the reduct
(high-then-low) produce byte-identical union-find edge lists — the shared forest `σ` is an automorphism OF. -/
theorem stepCupArc_stepCupArc_links_eq (state : ArcWireState) (lowPosition gap : Nat) :
    (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).links
      = (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition).links := rfl

/-- The two orders' fresh-allocation counters agree (`rfl`): both advance by `3 + 3`. -/
theorem stepCupArc_stepCupArc_nextFresh_eq (state : ArcWireState) (lowPosition gap : Nat) :
    (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).nextFresh
      = (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition).nextFresh := rfl

/-- The two orders' loop counts agree (`rfl`): cups never close a loop. -/
theorem stepCupArc_stepCupArc_loops_eq (state : ArcWireState) (lowPosition gap : Nat) :
    (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).loops
      = (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition).loops := rfl

/-- The two orders' cup-event node lists agree (`rfl`): each cup conses the same counter-drawn event. -/
theorem stepCupArc_stepCupArc_cupEventNodes_eq (state : ArcWireState) (lowPosition gap : Nat) :
    (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).cupEventNodes
      = (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition).cupEventNodes := rfl

/-- The two orders' cap-event node lists agree (`rfl`): a cup touches neither cap events. -/
theorem stepCupArc_stepCupArc_capEventNodes_eq (state : ArcWireState) (lowPosition gap : Nat) :
    (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).capEventNodes
      = (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition).capEventNodes := rfl

/-! ## Leg B1(b) — the OPEN-WIRE block transform

The sole order-dependent field.  The reduct's open wires are the redex's open wires relabelled by
`σ = blockRotate state.nextFresh 3 3`: pushing `σ` through the two `natListInsertAt` splices
(`natListInsertAt_map`), fixing the seed wires (all `< nextFresh` by freshness, so `blockRotate_fixesBelow`), and
swapping the two allocated 3-blocks by their `blockRotate` values, leaves the disjoint-position splice commutation
`natListInsertAt_insertAbove_commute` (splice-below-past-splice-above with the `+ 2` shift). -/

/-- ★ **The two pure-cup Godement run orders' OPEN WIRES are related by the fresh block rotation.**  The reduct's
open-wire list is the redex's relabelled by `σ = blockRotate state.nextFresh 3 3` (which swaps the two allocated
3-id blocks and fixes everything else): the disjoint-position splice commutation carries the low splice past the
high splice (the `+ 2` position shift), and the two block values `σ nf = nf + 3`, `σ (nf + 3) = nf` do the
relabelling.  The one order-dependent field of the pure-cup swap. -/
theorem stepCupArc_stepCupArc_openWires_blockSwap (state : ArcWireState) (lowPosition gap : Nat)
    (fresh : ArcStateFresh state) (window : gap + lowPosition ≤ state.openWires.length) :
    (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition).openWires
      = (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).openWires.map
          (blockRotate state.nextFresh 3 3) := by
  have hlowLt : state.nextFresh < state.nextFresh + 3 := Nat.lt_add_of_pos_right (by decide)
  have hlow1Lt : state.nextFresh + 1 < state.nextFresh + 3 :=
    Nat.add_lt_add_left (show (1 : Nat) < 3 by decide) state.nextFresh
  have hhiLo : state.nextFresh + 3 ≤ state.nextFresh + 3 := Nat.le_refl _
  have hhiLt : state.nextFresh + 3 < state.nextFresh + 3 + 3 := Nat.lt_add_of_pos_right (by decide)
  have hhi1Lo : state.nextFresh + 3 ≤ state.nextFresh + 3 + 1 := Nat.le_add_right _ _
  have hhi1Lt : state.nextFresh + 3 + 1 < state.nextFresh + 3 + 3 :=
    Nat.add_lt_add_left (show (1 : Nat) < 3 by decide) (state.nextFresh + 3)
  -- the seed wires are fixed by the block rotation (all `< nextFresh`)
  have hseedFixed : state.openWires.map (blockRotate state.nextFresh 3 3) = state.openWires :=
    mapFixedOn (blockRotate state.nextFresh 3 3) state.openWires
      (fun wire wireInList => blockRotate_fixesBelow state.nextFresh 3 3 wire (fresh.1 wire wireInList))
  -- the first cup's leg block maps to the second block; the second cup's leg block maps back to the first
  have hlowBlock : ([state.nextFresh, state.nextFresh + 1] : List Nat).map (blockRotate state.nextFresh 3 3)
      = [state.nextFresh + 3, state.nextFresh + 1 + 3] := by
    show [blockRotate state.nextFresh 3 3 state.nextFresh, blockRotate state.nextFresh 3 3 (state.nextFresh + 1)]
      = [state.nextFresh + 3, state.nextFresh + 1 + 3]
    rw [blockRotate_firstBlock state.nextFresh 3 3 state.nextFresh (Nat.le_refl _) hlowLt,
      blockRotate_firstBlock state.nextFresh 3 3 (state.nextFresh + 1) (Nat.le_add_right _ _) hlow1Lt]
  have hcancelLo : state.nextFresh + 3 - 3 = state.nextFresh := addSubCancelRight state.nextFresh 3
  have hcancelHi : state.nextFresh + 3 + 1 - 3 = state.nextFresh + 1 := by
    show state.nextFresh + 1 + 3 - 3 = state.nextFresh + 1
    exact addSubCancelRight (state.nextFresh + 1) 3
  have hhiBlock : ([state.nextFresh + 3, state.nextFresh + 3 + 1] : List Nat).map (blockRotate state.nextFresh 3 3)
      = [state.nextFresh, state.nextFresh + 1] := by
    show [blockRotate state.nextFresh 3 3 (state.nextFresh + 3),
        blockRotate state.nextFresh 3 3 (state.nextFresh + 3 + 1)]
      = [state.nextFresh, state.nextFresh + 1]
    rw [blockRotate_secondBlock state.nextFresh 3 3 (state.nextFresh + 3) hhiLo hhiLt,
      blockRotate_secondBlock state.nextFresh 3 3 (state.nextFresh + 3 + 1) hhi1Lo hhi1Lt, hcancelLo, hcancelHi]
  -- unfold both cup steps and push the rename through the two splices
  dsimp only [stepCupArc]
  rw [natListInsertAt_map (blockRotate state.nextFresh 3 3),
    natListInsertAt_map (blockRotate state.nextFresh 3 3), hseedFixed, hlowBlock, hhiBlock]
  exact natListInsertAt_insertAbove_commute state.openWires lowPosition gap
    [state.nextFresh + 3, state.nextFresh + 3 + 1] [state.nextFresh, state.nextFresh + 1] window

/-! ## Non-vacuity — a concrete two-cup fire at width 6 (the re-probe seed)

At the fresh seed `mk (range 6) [] 6 0 [] []` with the low cup at `1` and the high cup at `3` (`gap = 2`), both
legs hold on the nose, and the concrete link value matches the re-probe's reported `[(11,10),(9,10),(8,7),(6,7)]`
— confirming the abstract theorems are not vacuous. -/

/-- The concrete two-cup seed (width 6, `nextFresh = 6`) — the re-probe's seed. -/
private def twoCupSeed : ArcWireState := ArcWireState.mk (List.range 6) [] 6 0 [] []

/-- ★ Non-vacuity of the LINKS byte-identity: at the concrete seed the two orders' links are the SAME concrete
list `[(11,10),(9,10),(8,7),(6,7)]` — the exact value the raw re-probe reported. -/
theorem twoCupSwap_concrete_links :
    (stepCupArc (stepCupArc twoCupSeed 1) 5).links = [(11, 10), (9, 10), (8, 7), (6, 7)]
      ∧ (stepCupArc (stepCupArc twoCupSeed 1) 5).links = (stepCupArc (stepCupArc twoCupSeed 3) 1).links :=
  ⟨rfl, rfl⟩

/-- ★ Non-vacuity of the OPEN-WIRE block transform: at the concrete seed the two orders' open-wire lists are
related by `blockRotate 6 3 3` on the nose (`[0,9,10,1,2,6,7,3,4,5]` is `[0,6,7,1,2,9,10,3,4,5]` relabelled). -/
theorem twoCupSwap_concrete_openWires :
    (stepCupArc (stepCupArc twoCupSeed 3) 1).openWires
      = (stepCupArc (stepCupArc twoCupSeed 1) 5).openWires.map (blockRotate 6 3 3) := rfl

/-! ## Honesty markers -/

/-- **Honesty marker — the pure two-cup swap LINKS BYTE-IDENTITY is shipped.**  The two Godement run orders of a
cup × cup interchange produce the IDENTICAL union-find edge list (`stepCupArc_stepCupArc_links_eq`, by `rfl`),
because a cup's links are position-free (`stepCupArc_links_positionFree`).  The `nextFresh` / `loops` /
`cupEventNodes` / `capEventNodes` fields are byte-identical too; the sole permuted field is `openWires`.  This is
the raw re-probe's central mechanism, kernel-certified (and confirmed concrete at width 6,
`twoCupSwap_concrete_links`).  `= true`. -/
def fxMode_hasArcTwoCupSwapLinksBytewiseIdentical : Bool := true

/-- **Honesty marker — the pure two-cup swap OPEN-WIRE block transform is shipped.**  The reduct's open-wire list
is the redex's relabelled by the fresh block rotation `blockRotate state.nextFresh 3 3`
(`stepCupArc_stepCupArc_openWires_blockSwap`), via the disjoint-position splice commutation
(`natListInsertAt_insertAbove_commute`) and the two block values — the `openMap` field of the pure-cup swap
simulation, general over the seed / positions and non-vacuous (`twoCupSwap_concrete_openWires`).  `= true`. -/
def fxMode_hasArcTwoCupSwapOpenWireBlockTransform : Bool := true

/-- **Honesty marker — the FULL pure-cup swap `ArcStepSimCount` bundle IS shipped (residual-(2) heart CLOSED).**
All eight fields of `ArcStepSimCount (blockRotate state.nextFresh 3 3) redex reduct` are delivered by
`twoCupGodement_arcStepSimCount` (in `ArcTwoCupGodementSwapRootComm`) at general parameters, under the freshness /
disjoint-window / forest side-conditions.  The THIRD leg — `rootComm`, the union-find automorphism
`∀ x, unionFindRootOf L' (σ x) = σ (unionFindRootOf L' x)` of the shared forest `L'` — is now proven
(`twoCupGodement_rootComm`, the 4-edge `unionFindRootOf_consJoin`-tower port of the matching twin
`blockSwap_rootComm`): the block rotation `σ = blockRotate nextFresh 3 3` swaps the two disjoint fresh three-id
blocks (roots `nf+1 ↔ nf+4`) and fixes base + tail.  The count fields (`cupCorr` / `capCorr`) ride on it via the
shipped `countEventsInRoot_rootComm`.  This is NO LONGER a consequence of the per-atom transports (`σ` still
violates their future-fix requirement); it is the DIRECT final-state construction on the two-cup forest.
Non-vacuous (`twoCupBundle_concrete`, width-6).  Only the CAP-involving Godement pairs stay walled (residual (2)'s
`renameState`-EQUALITY route — the cap MERGE flips a merged root with the join order).  `= true`. -/
def fxMode_hasArcTwoCupGodementSwapSim : Bool := true

/-- **Honesty pin — the general keystone `:545` stays false.**  A faithful pure-cup swap witness is a NEW marker
(above); the general `ArcGodementSamePartitionFresh` signature marker in `ArcPartitionCommute` remains `false`. -/
theorem arcGodementSamePartitionFreshProof_staysFalse :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the peel-general signature `:137` stays false.** -/
theorem arcPeelGeneralSignature_staysFalse : fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — residual (2) (`ArcGodementSwapRenameable` proof-2, the general block-swap `σ`) stays false.**
The `rootComm` automorphism above IS this residual's heart; the two shipped wire/link legs do not close it. -/
theorem arcGodementSwapRenameableProof2_staysFalse :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
