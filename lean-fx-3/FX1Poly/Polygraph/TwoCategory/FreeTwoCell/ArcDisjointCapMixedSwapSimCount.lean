import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapSimCount

/-! # MODE-COMMUTE r26 — the CAP x CAP and MIXED disjoint atom-swap arms over the bundle

## What this ships (extending r25's cup arm to the cap and mixed atoms)

r25 (`ArcDisjointAtomSwapSimCount`) shipped the CUP-arm atom swap as a full eight-field `ArcStepSimCount`
over the `WellFormedArcState` bundle (via the shipped cup engine `twoCupGodement_arcStepSimCount`), and
probed the CAP and MIXED arms only at the SCALAR level — explicitly deferring "the block-swap `sigma` the
full sim would supply" to r26, because for a cap the two run orders' `links` are PERMUTATIONS (the fresh
event attaches to a different wire in each order), not byte-equal as they are for a cup.

r26 SUPPLIES and MACHINE-VERIFIES that block-swap `sigma` for all three remaining atom arms, on the
concrete node support (originals + fresh events + a fresh margin), and closes both run orders of each arm
back into the r24 bundle.  For each arm the EXHIBITED carrier is a `blockRotate` reconciling the two
orders' opposite fresh-id allocations:

  * **CAP x CAP** (two disjoint caps): `sigma = blockRotate nextFresh 1 1` (two singleton cap-event
    blocks).  The two orders' open wires are EQUAL on the nose (each cap consumes its own pair), and
    `sigma` is a union-find automorphism carrying the permuted links: `openMap`, `rootComm`, `cupCorr`,
    `capCorr` all hold on the support (kernel-decided), `nfEq` / `loopsEq` / `capEventNodes` by `rfl`.

  * **MIXED cup-then-cap** (cup left of cap): `sigma = blockRotate nextFresh 3 1` (a 3-id cup block above
    a 1-id cap block).  `openMap` here is a genuine relabeling (`reduct = redex.map sigma`), and the same
    four count/root fields hold on the support.

  * **MIXED cap-then-cup** (cup left of cap, cap fired at the shifted position): `sigma =
    blockRotate nextFresh 1 3`.  Same shape, mirror widths.

Both run orders of each arm close back into the bundle via the r24 cup/cap step preservation
(`wellFormedArcState_stepCapArc` / `_stepCupArc`, applied twice) — the closure the whole-cell suffix fold
(r27) runs over.

## The honest guard — window-disjointness is INSUFFICIENT for `rootComm` (the r26 finding)

r25's negative control showed the guard bites on CONNECTIVITY for the `loops` field: two caps at
OVERLAPPING windows diverge in loop count (`0` vs `1`).  r26 SHARPENS this for the `rootComm` field, which
is the genuine cap-arm wall: two caps at horizontally DISJOINT windows (positions `[0,2)` and `[2,4)`) whose
reads nevertheless share a union-find component STILL diverge in the merged root — the two orders assign an
original wire the roots `83` vs `81`.  Because that wire and both candidate roots are original ids (below
`nextFresh`, hence fixed by any boundary-fixing `sigma`), NO such `sigma` can satisfy `rootComm`.  So the
honest cap x cap guard is not window-disjointness but COMPONENT-disjoint reads — mirroring the shipped
`arcNonDisjointRootLevelDiffers` root-flip probe and the Petri/Mazurkiewicz preset-and-postset independence
condition (the loop/root closure is a POSTSET phenomenon, so preset-only disjointness is too weak).

## The pin stays false — the r27 whole-cell suffix-fold bill

`fxMode_hasArcGodementSwapRenameableProof2` (`ArcSwapRenameable.lean:3046`, `:= false`) is NOT flipped.  Its
bill (residual (2)) demands the explicit block-swap `sigma` witnessing `ArcGodementCoreSwapSimCount` over
ARBITRARY cells — the WHOLE two-block Godement interchange, all eight `ArcStepSimCount` fields between the
two full-cell cores, with the geometric fitting invariant supplying block-disjointness.  r26 delivers the
three ATOM bricks the whole-cell fold consumes, not the fold itself; per the flip law the bill demands
strictly more than the three atom arms, so the line is byte-intact and re-recorded `false` here by `rfl`.
The residual, precisely:

  1. [DEFERRED to r27] `atomPastCell` (single-spine induction) — one atom of `cellAlphaUpper` commuting
     past the whole `cellBeta` spine, threading the cap-aware position shift (each `cellBeta` atom shifts
     the passing atom's window by `+2` for a cup, `-2` for a cap), base = the r26 atom arm, step folded via
     `arcStepSimCount_processArcSpine_ofWellFormed` over the bundle;
  2. [DEFERRED to r27] `cellPastCell` (double-spine induction) — folding `atomPastCell` over
     `cellAlphaUpper`'s spine, whose disjointness invariant IS the geometric fitting the pin bill names
     (`cellAlphaUpper` fires strictly left of `cellBeta`, so the reads stay component-disjoint — discharging
     the r26 `readsDisjoint` guard from horizontal geometry) — yielding `ArcGodementCoreSwapSimCount` over
     arbitrary cells, the literal delivery that flips the pin.

The whole-cell pins (`fxMode_hasDisjointWhiskerSupport`, `fxMode_hasArcPartitionCommuteProof`,
`fxMode_hasArcGodementSamePartitionFreshProof`) all stay `false` (re-recorded by `rfl`).

Raw Lean 4 + Init; each arm's carrier is EXHIBITED and its fields kernel-decided on the concrete support,
each closure a term-mode composition of the r24 preservation, each negative control a structural `decide`.
Per-declaration `#assert_no_axioms` + independent `#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Arm 1 — CAP x CAP, two disjoint caps, carrier `blockRotate nextFresh 1 1` -/

/-- A well-formed seed for the disjoint cap x cap arm: six open wires in three pre-connected pairs
`[(50,51),(52,53),(54,55)]`, fresh frontier `56`. -/
def capCapDisjointSeed : ArcWireState := ArcWireState.mk [50, 51, 52, 53, 54, 55] [(50, 51), (52, 53), (54, 55)] 56 0 [] []

/-- The three-pair seed's link list is an acyclic union-find forest (each child parentless in its tail, each
edge non-loop).  Via `isUnionFindForest_cons`, propext-free. -/
theorem capCapDisjointSeed_isForest : isUnionFindForest capCapDisjointSeed.links := by
  show isUnionFindForest [(50, 51), (52, 53), (54, 55)]
  rw [isUnionFindForest_cons]
  refine ⟨rfl, rfl, by decide, ?_⟩
  rw [isUnionFindForest_cons]
  refine ⟨rfl, rfl, by decide, ?_⟩
  rw [isUnionFindForest_cons]
  exact ⟨rfl, rfl, by decide, trivial⟩

/-- The disjoint cap x cap seed is well-formed (all ids `< 56`, acyclic forest, `56 > 0`). -/
theorem capCapDisjointSeed_isWellFormed : WellFormedArcState capCapDisjointSeed :=
  ⟨by unfold ArcStateFresh capCapDisjointSeed; decide, capCapDisjointSeed_isForest, by decide⟩

/-- The REDEX order: the low cap at window `[0,2)`, then the high cap at the shifted window `[2,4)` (the low
cap's removal of two wires pulled the high window down by two). -/
def capCapDisjointRedex : ArcWireState := stepCapArc (stepCapArc capCapDisjointSeed 0) 2

/-- The REDUCT order: the high cap at window `[4,6)` first, then the low cap at `[0,2)`. -/
def capCapDisjointReduct : ArcWireState := stepCapArc (stepCapArc capCapDisjointSeed 4) 0

/-- ★ **The redex order lands back in the bundle** — the r24 cap-step preservation applied twice, at general
`(lowPosition, gap)`. -/
theorem capCapDisjointSwap_redexWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCapArc (stepCapArc state lowPosition) (gap + lowPosition)) :=
  wellFormedArcState_stepCapArc (stepCapArc state lowPosition) (gap + lowPosition)
    (wellFormedArcState_stepCapArc state lowPosition wellFormed)

/-- ★ **The reduct order lands back in the bundle** — the mirror of the redex closure. -/
theorem capCapDisjointSwap_reductWellFormed (state : ArcWireState) (lowPosition gap : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition) :=
  wellFormedArcState_stepCapArc (stepCapArc state (gap + 2 + lowPosition)) lowPosition
    (wellFormedArcState_stepCapArc state (gap + 2 + lowPosition) wellFormed)

/-- ★ **Both cap x cap orders closed into the bundle, fired concretely** (redex order). -/
theorem capCapDisjointRedex_isWellFormed : WellFormedArcState capCapDisjointRedex :=
  capCapDisjointSwap_redexWellFormed capCapDisjointSeed 0 2 capCapDisjointSeed_isWellFormed

/-- ★ **Both cap x cap orders closed into the bundle, fired concretely** (reduct order). -/
theorem capCapDisjointReduct_isWellFormed : WellFormedArcState capCapDisjointReduct :=
  capCapDisjointSwap_reductWellFormed capCapDisjointSeed 0 2 capCapDisjointSeed_isWellFormed

/-- The two disjoint cap orders share `nextFresh` (`58` — each cap allocates one event). -/
theorem capCapDisjointSwap_nextFreshAgree : capCapDisjointRedex.nextFresh = capCapDisjointReduct.nextFresh := rfl

/-- The two disjoint cap orders share `loops` (`2` — each cap closes its own pre-connected pair). -/
theorem capCapDisjointSwap_loopsAgree : capCapDisjointReduct.loops = capCapDisjointRedex.loops := rfl

/-- The two disjoint cap orders share the cap-event node list (`[57,56]`). -/
theorem capCapDisjointSwap_capEventNodesAgree :
    capCapDisjointReduct.capEventNodes = capCapDisjointRedex.capEventNodes := rfl

/-- ★ **The `openMap` field** — the reduct open wires are the block-swap image of the redex open wires (both
survive to `[52,53]`, fixed by `blockRotate 56 1 1`). -/
theorem capCapDisjointSwap_openMap :
    capCapDisjointReduct.openWires = capCapDisjointRedex.openWires.map (blockRotate 56 1 1) := by decide

/-- ★ **The `rootComm` field on the support** — the block-swap `blockRotate 56 1 1` is a union-find
automorphism between the two cap orders on every mentioned node (originals `50..55`, cap events `56,57`, and
a fresh margin `58,59`): `reduct.root (sigma node) = sigma (redex.root node)`.  Kernel-decided. -/
theorem capCapDisjointSwap_rootCommOnSupport :
    ([50, 51, 52, 53, 54, 55, 56, 57, 58, 59].all fun node =>
        unionFindRootOf capCapDisjointReduct.links (blockRotate 56 1 1 node)
          == blockRotate 56 1 1 (unionFindRootOf capCapDisjointRedex.links node)) = true := by decide

/-- ★ **The `cupCorr` field on the support** — the per-root cup-event counts correspond under the block swap
(both empty here; the correspondence is the vacuous zero on every root). -/
theorem capCapDisjointSwap_cupCorrOnSupport :
    ([50, 51, 52, 53, 54, 55, 56, 57, 58, 59].all fun root =>
        countEventsInRoot capCapDisjointReduct.links (blockRotate 56 1 1 root) capCapDisjointReduct.cupEventNodes
          == countEventsInRoot capCapDisjointRedex.links root capCapDisjointRedex.cupEventNodes) = true := by decide

/-- ★ **The `capCorr` field on the support** — the per-root cap-event counts correspond under the block swap
(the cap MERGE redistributes the two cap events sigma-isomorphically). -/
theorem capCapDisjointSwap_capCorrOnSupport :
    ([50, 51, 52, 53, 54, 55, 56, 57, 58, 59].all fun root =>
        countEventsInRoot capCapDisjointReduct.links (blockRotate 56 1 1 root) capCapDisjointReduct.capEventNodes
          == countEventsInRoot capCapDisjointRedex.links root capCapDisjointRedex.capEventNodes) = true := by decide

/-! ## Arm 2 — MIXED cup-then-cap, carrier `blockRotate nextFresh 3 1` -/

/-- A well-formed seed for the mixed cup-then-cap arm: four open wires with the right pair pre-connected
`[(42,43)]`, fresh frontier `44`. -/
def mixedCupCapSeed : ArcWireState := ArcWireState.mk [40, 41, 42, 43] [(42, 43)] 44 0 [] []

/-- The mixed cup-then-cap seed's single link `(42,43)` is an acyclic forest. -/
theorem mixedCupCapSeed_isForest : isUnionFindForest mixedCupCapSeed.links := by
  show isUnionFindForest [(42, 43)]
  rw [isUnionFindForest_cons]
  exact ⟨rfl, rfl, by decide, trivial⟩

/-- The mixed cup-then-cap seed is well-formed (all ids `< 44`, acyclic forest, `44 > 0`). -/
theorem mixedCupCapSeed_isWellFormed : WellFormedArcState mixedCupCapSeed :=
  ⟨by unfold ArcStateFresh mixedCupCapSeed; decide, mixedCupCapSeed_isForest, by decide⟩

/-- The REDEX order: the left cup, then the right cap at the shifted position `4` (the cup's two legs pushed
the cap window right by two). -/
def mixedCupCapRedex : ArcWireState := stepCapArc (stepCupArc mixedCupCapSeed 0) 4

/-- The REDUCT order: the right cap at position `2` first, then the left cup at position `0`. -/
def mixedCupCapReduct : ArcWireState := stepCupArc (stepCapArc mixedCupCapSeed 2) 0

/-- ★ **The mixed cup-then-cap redex order lands back in the bundle** (cup preservation on the cap-step
result). -/
theorem mixedCupCapSwap_redexWellFormed (state : ArcWireState) (cupPosition gap : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCapArc (stepCupArc state cupPosition) (gap + 2 + cupPosition)) :=
  wellFormedArcState_stepCapArc (stepCupArc state cupPosition) (gap + 2 + cupPosition)
    (wellFormedArcState_stepCupArc state cupPosition wellFormed)

/-- ★ **The mixed cup-then-cap reduct order lands back in the bundle** (cap-then-cup preservation). -/
theorem mixedCupCapSwap_reductWellFormed (state : ArcWireState) (cupPosition gap : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCupArc (stepCapArc state (gap + cupPosition)) cupPosition) :=
  wellFormedArcState_stepCupArc (stepCapArc state (gap + cupPosition)) cupPosition
    (wellFormedArcState_stepCapArc state (gap + cupPosition) wellFormed)

/-- ★ **The mixed cup-then-cap redex order closed into the bundle, fired concretely.** -/
theorem mixedCupCapRedex_isWellFormed : WellFormedArcState mixedCupCapRedex :=
  mixedCupCapSwap_redexWellFormed mixedCupCapSeed 0 2 mixedCupCapSeed_isWellFormed

/-- ★ **The mixed cup-then-cap reduct order closed into the bundle, fired concretely.** -/
theorem mixedCupCapReduct_isWellFormed : WellFormedArcState mixedCupCapReduct :=
  mixedCupCapSwap_reductWellFormed mixedCupCapSeed 0 2 mixedCupCapSeed_isWellFormed

/-- The mixed cup-then-cap orders share `nextFresh` (`48` — cup allocates three, cap one). -/
theorem mixedCupCapSwap_nextFreshAgree : mixedCupCapRedex.nextFresh = mixedCupCapReduct.nextFresh := rfl

/-- The mixed cup-then-cap orders share `loops` (`1` — the right cap closes its pair either way). -/
theorem mixedCupCapSwap_loopsAgree : mixedCupCapReduct.loops = mixedCupCapRedex.loops := rfl

/-- ★ **The `openMap` field** — the reduct open wires are the block-swap image of the redex open wires under
`blockRotate 44 3 1` (a genuine relabeling: `[44,45,40,41]` maps to `[45,46,40,41]`). -/
theorem mixedCupCapSwap_openMap :
    mixedCupCapReduct.openWires = mixedCupCapRedex.openWires.map (blockRotate 44 3 1) := by decide

/-- ★ **The `rootComm` field on the support** — `blockRotate 44 3 1` is a union-find automorphism between the
two mixed cup-then-cap orders on every mentioned node (originals `40..43`, cup legs `44,45`, cup event `46`,
cap event `47`, margin `48,49`). -/
theorem mixedCupCapSwap_rootCommOnSupport :
    ([40, 41, 42, 43, 44, 45, 46, 47, 48, 49].all fun node =>
        unionFindRootOf mixedCupCapReduct.links (blockRotate 44 3 1 node)
          == blockRotate 44 3 1 (unionFindRootOf mixedCupCapRedex.links node)) = true := by decide

/-- ★ **The `cupCorr` field on the support** — the per-root cup-event counts correspond under the block swap. -/
theorem mixedCupCapSwap_cupCorrOnSupport :
    ([40, 41, 42, 43, 44, 45, 46, 47, 48, 49].all fun root =>
        countEventsInRoot mixedCupCapReduct.links (blockRotate 44 3 1 root) mixedCupCapReduct.cupEventNodes
          == countEventsInRoot mixedCupCapRedex.links root mixedCupCapRedex.cupEventNodes) = true := by decide

/-- ★ **The `capCorr` field on the support** — the per-root cap-event counts correspond under the block swap. -/
theorem mixedCupCapSwap_capCorrOnSupport :
    ([40, 41, 42, 43, 44, 45, 46, 47, 48, 49].all fun root =>
        countEventsInRoot mixedCupCapReduct.links (blockRotate 44 3 1 root) mixedCupCapReduct.capEventNodes
          == countEventsInRoot mixedCupCapRedex.links root mixedCupCapRedex.capEventNodes) = true := by decide

/-! ## Arm 3 — MIXED cap-then-cup, carrier `blockRotate nextFresh 1 3` -/

/-- A well-formed seed for the mixed cap-then-cup arm: four open wires with the left pair pre-connected
`[(60,61)]`, fresh frontier `64`. -/
def mixedCapCupSeed : ArcWireState := ArcWireState.mk [60, 61, 62, 63] [(60, 61)] 64 0 [] []

/-- The mixed cap-then-cup seed's single link `(60,61)` is an acyclic forest. -/
theorem mixedCapCupSeed_isForest : isUnionFindForest mixedCapCupSeed.links := by
  show isUnionFindForest [(60, 61)]
  rw [isUnionFindForest_cons]
  exact ⟨rfl, rfl, by decide, trivial⟩

/-- The mixed cap-then-cup seed is well-formed (all ids `< 64`, acyclic forest, `64 > 0`). -/
theorem mixedCapCupSeed_isWellFormed : WellFormedArcState mixedCapCupSeed :=
  ⟨by unfold ArcStateFresh mixedCapCupSeed; decide, mixedCapCupSeed_isForest, by decide⟩

/-- The CAP-FIRST order: the left cap at position `0`, then the cup spliced at the front (position `0`). -/
def mixedCapCupCapFirst : ArcWireState := stepCupArc (stepCapArc mixedCapCupSeed 0) 0

/-- The CUP-FIRST order: the cup at the front first, then the left cap at the shifted position `2`. -/
def mixedCapCupCupFirst : ArcWireState := stepCapArc (stepCupArc mixedCapCupSeed 0) 2

/-- ★ **The cap-first order lands back in the bundle** (cup preservation on the cap-step result). -/
theorem mixedCapCupSwap_capFirstWellFormed (state : ArcWireState) (position : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCupArc (stepCapArc state position) position) :=
  wellFormedArcState_stepCupArc (stepCapArc state position) position
    (wellFormedArcState_stepCapArc state position wellFormed)

/-- ★ **The cup-first order lands back in the bundle** (cap preservation on the cup-step result). -/
theorem mixedCapCupSwap_cupFirstWellFormed (state : ArcWireState) (cupPosition capPosition : Nat)
    (wellFormed : WellFormedArcState state) :
    WellFormedArcState (stepCapArc (stepCupArc state cupPosition) capPosition) :=
  wellFormedArcState_stepCapArc (stepCupArc state cupPosition) capPosition
    (wellFormedArcState_stepCupArc state cupPosition wellFormed)

/-- ★ **The cap-first order closed into the bundle, fired concretely.** -/
theorem mixedCapCupCapFirst_isWellFormed : WellFormedArcState mixedCapCupCapFirst :=
  mixedCapCupSwap_capFirstWellFormed mixedCapCupSeed 0 mixedCapCupSeed_isWellFormed

/-- ★ **The cup-first order closed into the bundle, fired concretely.** -/
theorem mixedCapCupCupFirst_isWellFormed : WellFormedArcState mixedCapCupCupFirst :=
  mixedCapCupSwap_cupFirstWellFormed mixedCapCupSeed 0 2 mixedCapCupSeed_isWellFormed

/-- The mixed cap-then-cup orders share `nextFresh` (`68`). -/
theorem mixedCapCupSwap_nextFreshAgree : mixedCapCupCapFirst.nextFresh = mixedCapCupCupFirst.nextFresh := rfl

/-- The mixed cap-then-cup orders share `loops` (`1`). -/
theorem mixedCapCupSwap_loopsAgree : mixedCapCupCupFirst.loops = mixedCapCupCapFirst.loops := rfl

/-- ★ **The `openMap` field** — the cup-first open wires are the block-swap image of the cap-first open wires
under `blockRotate 64 1 3` (`[65,66,62,63]` maps to `[64,65,62,63]`). -/
theorem mixedCapCupSwap_openMap :
    mixedCapCupCupFirst.openWires = mixedCapCupCapFirst.openWires.map (blockRotate 64 1 3) := by decide

/-- ★ **The `rootComm` field on the support** — `blockRotate 64 1 3` is a union-find automorphism between the
two mixed cap-then-cup orders on every mentioned node (originals `60..63`, events `64..67`, margin `68,69`). -/
theorem mixedCapCupSwap_rootCommOnSupport :
    ([60, 61, 62, 63, 64, 65, 66, 67, 68, 69].all fun node =>
        unionFindRootOf mixedCapCupCupFirst.links (blockRotate 64 1 3 node)
          == blockRotate 64 1 3 (unionFindRootOf mixedCapCupCapFirst.links node)) = true := by decide

/-- ★ **The `cupCorr` field on the support** — the per-root cup-event counts correspond under the block swap. -/
theorem mixedCapCupSwap_cupCorrOnSupport :
    ([60, 61, 62, 63, 64, 65, 66, 67, 68, 69].all fun root =>
        countEventsInRoot mixedCapCupCupFirst.links (blockRotate 64 1 3 root) mixedCapCupCupFirst.cupEventNodes
          == countEventsInRoot mixedCapCupCapFirst.links root mixedCapCupCapFirst.cupEventNodes) = true := by decide

/-- ★ **The `capCorr` field on the support** — the per-root cap-event counts correspond under the block swap. -/
theorem mixedCapCupSwap_capCorrOnSupport :
    ([60, 61, 62, 63, 64, 65, 66, 67, 68, 69].all fun root =>
        countEventsInRoot mixedCapCupCupFirst.links (blockRotate 64 1 3 root) mixedCapCupCupFirst.capEventNodes
          == countEventsInRoot mixedCapCupCapFirst.links root mixedCapCupCapFirst.capEventNodes) = true := by decide

/-! ## Negative control A — window-disjoint but COMPONENT-shared caps break `rootComm` (r26 finding) -/

/-- A WELL-FORMED seed whose two disjoint cap windows read a SHARED component: four open wires
`[80,81,82,83]` bridged `[(80,82)]` (wire at position `0` and wire at position `2` are the same component),
fresh frontier `84`. -/
def capCapComponentShareSeed : ArcWireState := ArcWireState.mk [80, 81, 82, 83] [(80, 82)] 84 0 [] []

/-- The component-share seed's single bridge link `(80,82)` is an acyclic forest. -/
theorem capCapComponentShareSeed_isForest : isUnionFindForest capCapComponentShareSeed.links := by
  show isUnionFindForest [(80, 82)]
  rw [isUnionFindForest_cons]
  exact ⟨rfl, rfl, by decide, trivial⟩

/-- The component-share seed IS well-formed — the control fires on a genuine bundle member, not garbage. -/
theorem capCapComponentShareSeed_isWellFormed : WellFormedArcState capCapComponentShareSeed :=
  ⟨by unfold ArcStateFresh capCapComponentShareSeed; decide, capCapComponentShareSeed_isForest, by decide⟩

/-- The two disjoint windows read the SAME component — the wire at position `0` (`80`) and the wire at
position `2` (`82`) share a union-find root. -/
theorem capCapComponentShareSeed_readsShareComponent :
    isSameComponent capCapComponentShareSeed.links
      (natListGetAt capCapComponentShareSeed.openWires 0)
      (natListGetAt capCapComponentShareSeed.openWires 2) = true := by decide

/-- The REDEX order on the component-share seed: cap at `[0,2)` then cap at the shifted `[0,2)` (`gap = 0`). -/
def capCapComponentShareRedex : ArcWireState := stepCapArc (stepCapArc capCapComponentShareSeed 0) 0

/-- The REDUCT order on the component-share seed: cap at `[2,4)` then cap at `[0,2)`. -/
def capCapComponentShareReduct : ArcWireState := stepCapArc (stepCapArc capCapComponentShareSeed 2) 0

/-- ★ **The NEGATIVE control — window-disjointness is INSUFFICIENT for `rootComm`.**  On the well-formed
disjoint-window seed whose reads share a component, the two cap orders assign the original wire `80` DIFFERENT
merged roots (`83` in the redex, `81` in the reduct).  Since `80` and both candidate roots are original ids
(`< 84 = nextFresh`), any boundary-fixing `sigma` fixes all three, so `rootComm`
(`reduct.root (sigma 80) = sigma (redex.root 80)`) would demand `81 = 83` — false.  So NO block-swap `sigma`
reconciles the two orders when the reads share a component: the honest cap x cap guard is COMPONENT-disjoint
reads, not window-disjointness.  Structural `decide`. -/
theorem capCapComponentShareSwap_rootDiverges :
    unionFindRootOf capCapComponentShareRedex.links 80
      ≠ unionFindRootOf capCapComponentShareReduct.links 80 := by decide

/-- The two divergent merged roots, made explicit: `83` (redex) versus `81` (reduct). -/
theorem capCapComponentShareSwap_rootValues :
    unionFindRootOf capCapComponentShareRedex.links 80 = 83
      ∧ unionFindRootOf capCapComponentShareReduct.links 80 = 81 := by decide

/-! ## Negative control B — window-OVERLAPPING caps break `loopsEq` (r25 finding, re-fired fresh) -/

/-- A fresh WELL-FORMED seed with a single pre-connection `[(20,23)]` bridging the outermost wires of
`[20,21,22,23]`, fresh frontier `24`. -/
def overlappingCapControlSeed : ArcWireState := ArcWireState.mk [20, 21, 22, 23] [(20, 23)] 24 0 [] []

/-- The overlapping-cap control seed's bridge link `(20,23)` is an acyclic forest. -/
theorem overlappingCapControlSeed_isForest : isUnionFindForest overlappingCapControlSeed.links := by
  show isUnionFindForest [(20, 23)]
  rw [isUnionFindForest_cons]
  exact ⟨rfl, rfl, by decide, trivial⟩

/-- The overlapping-cap control seed IS well-formed — the guard bites from window overlap, not ill-formedness. -/
theorem overlappingCapControlSeed_isWellFormed : WellFormedArcState overlappingCapControlSeed :=
  ⟨by unfold ArcStateFresh overlappingCapControlSeed; decide, overlappingCapControlSeed_isForest, by decide⟩

/-- ★ **The NEGATIVE control — the guard bites on `loopsEq` for OVERLAPPING windows.**  Two caps at
overlapping windows `[0,2)` and `[1,3)` (sharing wire `21`) diverge in loop count between the two orders
(`0` versus `1`): firing the `[1,3)` cap first pre-connects the component the `[0,2)` cap then closes as a
loop.  So `loopsEq` — a field the disjoint atom swap must satisfy — FAILS when the windows overlap. -/
theorem overlappingCapControlSwap_loopsDiffer :
    (stepCapArc (stepCapArc overlappingCapControlSeed 0) 1).loops
      ≠ (stepCapArc (stepCapArc overlappingCapControlSeed 1) 0).loops := by decide

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the CAP x CAP and MIXED disjoint atom-swap arms are VERIFIED over the bundle.**  For
all three remaining atom arms (cap x cap `blockRotate nextFresh 1 1`, mixed cup-then-cap
`blockRotate nextFresh 3 1`, mixed cap-then-cup `blockRotate nextFresh 1 3`) the block-swap carrier is
EXHIBITED and its `openMap` / `rootComm` / `cupCorr` / `capCorr` fields kernel-decided on the concrete node
support, `nfEq` / `loopsEq` / event-lists by `rfl`, and both run orders closed back into the r24 bundle.
The honest cap-arm guard is SHARPENED to COMPONENT-disjoint reads: the window-disjoint-but-component-shared
negative control breaks `rootComm` (roots `83` vs `81`), the window-overlap control breaks `loopsEq`
(`0` vs `1`).  The full unbounded `ArcStepSimCount` term (the automorphism over ALL `Nat`) and the
atom-to-cell double induction are r27.  `= true`. -/
def fxMode_hasDisjointCapMixedSwapSupportVerified : Bool := true

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN.**  r26 delivers the three disjoint
ATOM arms; the pin's bill demands `ArcGodementCoreSwapSimCount` over ARBITRARY cells — the whole-cell suffix
fold (`atomPastCell` -> `cellPastCell`), which is r27.  The `ArcSwapRenameable.lean:3046` line is byte-intact
and its marker stays `false`. -/
theorem arcDisjointCapMixedSwap_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the whole-cell disjoint whisker-support list-equality stays OPEN (r27 assembly).** -/
theorem arcDisjointCapMixedSwap_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN (inseparable from residual (2)).** -/
theorem arcDisjointCapMixedSwap_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  The bundle's
`isForest` field EXCLUDES its cyclic counterexample rather than re-proving it. -/
theorem arcDisjointCapMixedSwap_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
