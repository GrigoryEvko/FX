import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWellFormedStateBundle
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapRootComm
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCompoundBlockTransposition

/-! # MODE-COMMUTE r25 — the position-disjoint atom-swap `ArcStepSimCount` brick over the bundle

## What this ships (the base of residual (2))

The whole-cell disjoint-whisker interchange (`fxMode_hasDisjointWhiskerSupport`, r23) rests on ONE
remaining obligation, residual (2): the base `ArcStepSimCount` between the two Godement cores
(`ArcGodementCoreSwapSimCount`, `fxMode_hasArcGodementSwapRenameableProof2 = false`).  The literature
(Mazurkiewicz trace independence — actions on disjoint resources commute; the parallel-moves
disjoint-redex diamond — contracting at disjoint positions is order-independent with empty residual;
Delpeuch-Vicary's string-diagram exchange side-condition "share no common edges") all give the SAME
lemma shape: two 2-cell atoms whose windows are horizontally disjoint commute, up to the block swap
that reconciles their opposite fresh-id allocations.

r25 delivers the ATOM level of that brick for the CUP arm, RE-STATED over the r24 `WellFormedArcState`
bundle:

  * `arcDisjointCupSwapSimCount_ofWellFormed` — for two disjoint cups at `lowPosition` and
    `gap + 2 + lowPosition` (redex) versus `gap + lowPosition` and `lowPosition` (reduct), the two run
    orders are `ArcStepSimCount`-related by `compoundFreshBlockTransposition state.nextFresh 3 3` (the
    r22 compound carrier), reading the freshness / forest hypotheses OFF the bundle ONCE.  Genuine
    consumption of the shipped general cup-swap sim (`twoCupGodement_arcStepSimCount`), tied to the r22
    block-transposition carrier (`blockRotate_eq_compoundFreshBlockTransposition`, definitional);
  * `arcDisjointCupSwap_redexWellFormed` / `_reductWellFormed` — both run orders land BACK in the
    bundle, genuine consumption of the r24 cup-step preservation (`wellFormedArcState_stepCupArc`,
    twice each) — the closure the whole-cell suffix fold rides.

## The probes (HONESTY LAW — wide truth-probes before universals)

  * the cup arm is FIRED at a concrete disjoint-window well-formed seed, a full eight-field
    `ArcStepSimCount` with machine-checked open-wire block-swap snapshots;
  * the CAP arm and the MIXED cup-cap arm are exercised at the SCALAR level (loops / open-wires /
    `nextFresh` / event-node lists agree across the two disjoint-window orders; the links differ,
    demanding the block-swap `sigma` the full sim would supply — r26);
  * the OVERLAPPING-cap NEGATIVE control (`arcOverlappingCapSwap_loopsDiffer`) BITES: two caps sharing
    a wire diverge in their loop count (0 versus 1) even on a WELL-FORMED state, so the position-
    disjointness premise is load-bearing, not decorative.  The disjoint-window contrast
    (`arcDisjointCapSwap_loopsAgree_contrast`) shows the guard does NOT bite when the windows separate.
    (Finding: the guard bites on CONNECTIVITY — caps — not on positions; cups commute up to the block
    swap regardless, which is why the shipped cup arm carries only the position-VALIDITY `window`
    premise.)

## The pin stays false — the honest r26 whole-cell bill

`fxMode_hasArcGodementSwapRenameableProof2` (ArcSwapRenameable.lean:3046, `:= false`) is NOT flipped:
its bill demands `ArcGodementCoreSwapSimCount` over ARBITRARY cells, and r25 delivers only the
CUP-arm ATOM swap.  The line is byte-intact; the pin is re-recorded `false` here by `rfl`.  What the
r26 assembly still owes, in dependency order:

  1. the CAP-arm and MIXED-arm disjoint atom swaps — a `twoCapGodement_rootComm` analog transporting
     the cap MERGE counts across disjoint components (the scalar probes below confirm they are
     `ArcStepSimCount`-true; only the general `rootComm` is unbuilt);
  2. `atomPastCell` (single-spine induction) — one atom of `cellAlphaUpper` commuting past the whole
     `cellBeta` spine, threading the position shift;
  3. `cellPastCell` (double-spine induction) — folding `atomPastCell` over `cellAlphaUpper`'s spine ⇒
     `ArcGodementCoreSwapSimCount` over arbitrary cells ⇒ the literal delivery that flips the pin.

`fxMode_hasDisjointWhiskerSupport` / `fxMode_hasArcPartitionCommuteProof` /
`fxMode_hasArcGodementSamePartitionFreshProof` all stay `false` (the whole-cell assembly, and the
machine-refuted `ArcGodementSamePartitionFresh` keystone whose cyclic counterexample the bundle's
`isForest` field EXCLUDES rather than re-proves).

Raw Lean 4 + Init; every brick a term-mode composition of shipped levers, every scalar probe a `rfl`
computation, the negative control a structural `decide`.  Per-declaration `#assert_no_axioms` +
independent `#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The r22 carrier bridge -/

/-- The r22 block-rotation carrier `blockRotate` and the r22 compound fresh-block transposition
`compoundFreshBlockTransposition` are DEFINITIONALLY the same map (both unfold to
`arcFreshBlockTransposition`).  This is the seam that lets the shipped cup-swap sim (stated at
`blockRotate`) be read at the compound carrier the whole-cell assembly threads. -/
theorem blockRotate_eq_compoundFreshBlockTransposition (baseFresh widthFirst widthSecond : Nat) :
    blockRotate baseFresh widthFirst widthSecond
      = compoundFreshBlockTransposition baseFresh widthFirst widthSecond := rfl

/-! ## The brick — the disjoint cup swap `ArcStepSimCount` over the `WellFormedArcState` bundle -/

/-- ★ **The position-disjoint cup-swap simulation over the bundle (residual-(2) atom base, cup arm).**
Two cups at horizontally-disjoint windows — the low cup at `lowPosition`, the high cup at
`gap + 2 + lowPosition` after the low cup shifts it right by two (redex), versus the high cup at
`gap + lowPosition` then the low cup at `lowPosition` (reduct) — fired on a `WellFormedArcState` are
`ArcStepSimCount`-related by `compoundFreshBlockTransposition state.nextFresh 3 3`, the r22 compound
carrier that swaps the two disjoint fresh three-id blocks the two orders allocate in opposite order.
The freshness and forest hypotheses are read OFF the bundle ONCE (`wellFormed.isFresh` /
`wellFormed.isForest`), exactly the r24 joint-simulation consumption pattern; the `window` premise is
the position-VALIDITY `gap + lowPosition <= state.openWires.length` (cups commute up to the block swap
regardless of window overlap — the disjointness only becomes load-bearing on the cap arm).  Genuine
consumption of the shipped general cup-swap sim `twoCupGodement_arcStepSimCount`. -/
theorem arcDisjointCupSwapSimCount_ofWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state)
    (window : gap + lowPosition ≤ state.openWires.length) :
    ArcStepSimCount (compoundFreshBlockTransposition state.nextFresh 3 3)
      (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition))
      (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition) :=
  twoCupGodement_arcStepSimCount state lowPosition gap wellFormed.isFresh window wellFormed.isForest

/-- ★ **The redex order lands back in the bundle** — genuine consumption of the r24 cup-step
preservation, applied twice, so every state the disjoint cup swap reaches from a well-formed seed is
itself well-formed (the closure the whole-cell suffix fold runs over). -/
theorem arcDisjointCupSwap_redexWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)) :=
  wellFormedArcState_stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)
    (wellFormedArcState_stepCupArc state lowPosition wellFormed)

/-- ★ **The reduct order lands back in the bundle** — the mirror of the redex closure. -/
theorem arcDisjointCupSwap_reductWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition) :=
  wellFormedArcState_stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition
    (wellFormedArcState_stepCupArc state (gap + lowPosition) wellFormed)

/-! ## The cup arm fired at a concrete disjoint-window well-formed seed -/

/-- A concrete well-formed seed: four open wires `[0,1,2,3]`, no links, fresh frontier `4`. -/
def disjointCupSwapSeed : ArcWireState := ArcWireState.mk [0, 1, 2, 3] [] 4 0 [] []

/-- The disjoint-cup seed is well-formed (all ids below `4`, empty forest, `4 > 0`). -/
theorem disjointCupSwapSeed_isWellFormed : WellFormedArcState disjointCupSwapSeed :=
  ⟨by unfold ArcStateFresh disjointCupSwapSeed; decide,
   by show isUnionFindForest ([] : List (Nat × Nat)); exact isUnionFindForest_nil,
   by decide⟩

/-- ★ **The cup arm FIRED** — a full eight-field `ArcStepSimCount` for two disjoint cups (low at `0`,
high at `4`; reduct high at `2`, low at `0`) at the block swap `compoundFreshBlockTransposition 4 3 3`,
via the bundle brick.  The `rootComm` / `cupCorr` / `capCorr` fields (each a universal over `Nat`,
undecidable by `decide`) are discharged BY THE BRICK, not by computation. -/
theorem arcDisjointCupSwapFire :
    ArcStepSimCount (compoundFreshBlockTransposition disjointCupSwapSeed.nextFresh 3 3)
      (stepCupArc (stepCupArc disjointCupSwapSeed 0) 4)
      (stepCupArc (stepCupArc disjointCupSwapSeed 2) 0) :=
  arcDisjointCupSwapSimCount_ofWellFormed disjointCupSwapSeed 0 2 disjointCupSwapSeed_isWellFormed
    (by decide)

/-- The redex order's open wires: the low cup's legs `4,5` sit left, the high cup's `7,8` right. -/
theorem arcDisjointCupSwapFire_redexOpenWires :
    (stepCupArc (stepCupArc disjointCupSwapSeed 0) 4).openWires = [4, 5, 0, 1, 7, 8, 2, 3] := rfl

/-- The reduct order's open wires: the block-swapped image — `7,8` left, `4,5` right (the high cup
fired first, so it drew the low ids).  Distinct from the redex on the nose; the brick's `openMap`
relates them by the block swap. -/
theorem arcDisjointCupSwapFire_reductOpenWires :
    (stepCupArc (stepCupArc disjointCupSwapSeed 2) 0).openWires = [7, 8, 0, 1, 4, 5, 2, 3] := rfl

/-- Both orders share the fresh frontier `10` (`nfEq` witnessed concretely). -/
theorem arcDisjointCupSwapFire_nextFreshAgree :
    (stepCupArc (stepCupArc disjointCupSwapSeed 0) 4).nextFresh
      = (stepCupArc (stepCupArc disjointCupSwapSeed 2) 0).nextFresh := rfl

/-! ## The CAP arm — scalar disjoint-commutation probes (the full sim is r26) -/

/-- A seed with two independent pre-connected pairs `[(30,31),(32,33)]` over wires `[30,31,32,33]`. -/
def disjointCapPairSeed : ArcWireState := ArcWireState.mk [30, 31, 32, 33] [(30, 31), (32, 33)] 34 0 [] []

/-- Two disjoint caps (low window then the shifted low position; high window then low) AGREE on their
loop count (both `2` — each cap closes its own pre-connected pair regardless of order). -/
theorem disjointCapSwap_loopsAgree :
    (stepCapArc (stepCapArc disjointCapPairSeed 0) 0).loops
      = (stepCapArc (stepCapArc disjointCapPairSeed 2) 0).loops := rfl

/-- The two disjoint-cap orders AGREE on their open wires (both empty — all four consumed). -/
theorem disjointCapSwap_openWiresAgree :
    (stepCapArc (stepCapArc disjointCapPairSeed 0) 0).openWires
      = (stepCapArc (stepCapArc disjointCapPairSeed 2) 0).openWires := rfl

/-- The two disjoint-cap orders AGREE on their fresh frontier (both `36`). -/
theorem disjointCapSwap_nextFreshAgree :
    (stepCapArc (stepCapArc disjointCapPairSeed 0) 0).nextFresh
      = (stepCapArc (stepCapArc disjointCapPairSeed 2) 0).nextFresh := rfl

/-- The two disjoint-cap orders AGREE on their cap-event node LIST (`[35,34]` — first-fired cap draws
`34`, second `35`, in both orders).  The links DIFFER (event `34` attaches to a different component),
which is exactly the block-swap `sigma` content the full `ArcStepSimCount` (r26) would carry. -/
theorem disjointCapSwap_capEventNodesAgree :
    (stepCapArc (stepCapArc disjointCapPairSeed 0) 0).capEventNodes
      = (stepCapArc (stepCapArc disjointCapPairSeed 2) 0).capEventNodes := rfl

/-! ## The MIXED cup-cap arm — scalar disjoint-commutation probe (the full sim is r26) -/

/-- A seed with a pre-connected pair `[(42,43)]` on the right over wires `[40,41,42,43]`. -/
def disjointCupCapSeed : ArcWireState := ArcWireState.mk [40, 41, 42, 43] [(42, 43)] 44 0 [] []

/-- A left cup then the right cap (shifted right by the cup's two legs) versus the right cap then the
left cup AGREE on their loop count (both `1` — the right cap closes its pair either way). -/
theorem disjointCupCapSwap_loopsAgree :
    (stepCapArc (stepCupArc disjointCupCapSeed 0) 4).loops
      = (stepCupArc (stepCapArc disjointCupCapSeed 2) 0).loops := rfl

/-- The mixed cup-cap orders AGREE on their fresh frontier (both `48`).  The open wires DIFFER on the
nose (the cup draws `44,45` in one order, `45,46` in the other), demanding the block swap the full
`ArcStepSimCount` (r26) supplies. -/
theorem disjointCupCapSwap_nextFreshAgree :
    (stepCapArc (stepCupArc disjointCupCapSeed 0) 4).nextFresh
      = (stepCupArc (stepCapArc disjointCupCapSeed 2) 0).nextFresh := rfl

/-! ## The negative control — the disjointness guard BITES on overlapping caps -/

/-- A WELL-FORMED seed with a single pre-connection `[(10,13)]` bridging the outermost wires of
`[10,11,12,13]`, fresh frontier `14`. -/
def overlappingCapSeed : ArcWireState := ArcWireState.mk [10, 11, 12, 13] [(10, 13)] 14 0 [] []

/-- The overlapping-cap seed IS well-formed — the negative control fires on a genuine bundle member,
not on garbage (the guard bites purely from window overlap, not from ill-formedness). -/
theorem overlappingCapSeed_isWellFormed : WellFormedArcState overlappingCapSeed :=
  ⟨by unfold ArcStateFresh overlappingCapSeed; decide,
   by
     show isUnionFindForest [(10, 13)]
     rw [isUnionFindForest_cons]
     exact ⟨rfl, rfl, by decide, trivial⟩,
   by decide⟩

/-- ★ **The NEGATIVE control — the guard BITES.**  Two caps at OVERLAPPING windows (`[0,2)` and
`[1,3)`, sharing wire `11`) DIVERGE in their loop count between the two orders (`0` versus `1`): firing
the `[1,3)` cap first pre-connects the component the `[0,2)` cap then closes as a loop, whereas the
other order does not.  So `loopsEq` — a field the disjoint-atom-swap `ArcStepSimCount` must satisfy —
FAILS when the windows overlap.  The horizontal-disjointness premise is load-bearing.  Structural
`decide` on the computed loop counts. -/
theorem arcOverlappingCapSwap_loopsDiffer :
    (stepCapArc (stepCapArc overlappingCapSeed 0) 1).loops
      ≠ (stepCapArc (stepCapArc overlappingCapSeed 1) 0).loops := by decide

/-- ★ **The disjoint-window CONTRAST — the guard does NOT bite.**  The SAME cap machinery at DISJOINT
windows agrees on its loop count (both `2`), confirming the divergence above is caused by window
OVERLAP, not by caps per se. -/
theorem arcDisjointCapSwap_loopsAgree_contrast :
    (stepCapArc (stepCapArc disjointCapPairSeed 0) 0).loops
      = (stepCapArc (stepCapArc disjointCapPairSeed 2) 0).loops := rfl

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the position-disjoint CUP-swap `ArcStepSimCount` brick is SHIPPED over the
bundle.**  `arcDisjointCupSwapSimCount_ofWellFormed` restates the shipped general cup-swap sim over the
r24 `WellFormedArcState` carrier (reading the freshness / forest triple off the bundle once) at the r22
compound block-transposition carrier, with both run orders closed back into the bundle
(`_redexWellFormed` / `_reductWellFormed`).  Fired at a concrete disjoint-window seed; the cap and mixed
arms probed at the scalar level; the overlapping-cap negative control bites.  The CAP / MIXED full
`ArcStepSimCount` and the atom-to-cell double induction are r26.  `= true`. -/
def fxMode_hasDisjointCupSwapSimOverBundle : Bool := true

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN.**  r25 delivers only the CUP-arm
ATOM swap; the pin's bill demands `ArcGodementCoreSwapSimCount` over ARBITRARY cells (the cap/mixed atom
arms plus `atomPastCell` -> `cellPastCell`).  The `ArcSwapRenameable.lean:3046` line is byte-intact and
its marker stays `false`. -/
theorem arcDisjointCupSwap_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the whole-cell disjoint whisker-support list-equality stays OPEN (r26 assembly).** -/
theorem arcDisjointCupSwap_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN (inseparable from residual (2)).** -/
theorem arcDisjointCupSwap_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  The bundle's
`isForest` field EXCLUDES its cyclic counterexample rather than re-proving it. -/
theorem arcDisjointCupSwap_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
