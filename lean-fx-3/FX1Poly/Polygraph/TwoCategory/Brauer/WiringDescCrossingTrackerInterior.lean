import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTracker
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFoldTargetHonest

/-! # BRAUER r23 — the interior-phase crossing tracker (the CUP / THROUGH enabler), fired on the REAL six-phase fold

The r23 general tracker `crossingWordFold_openWire_sameComponent_incomingPort`
(`Brauer/WiringDescCrossingTracker.lean`) holds over ANY reachable interior state.  This file specializes it to the
exact shape the CUP and THROUGH T-CONNECT classes consume — a crossing staircase fired AFTER an arbitrary prefix word
over the seed — and demonstrates it firing on the genuine NON-seed `topPerm` phase of the real six-phase fold of the
triple-axis adversarial-B diagram.

## Why this is the CUP / THROUGH enabler

The r19 / r22 wall (`Brauer/WiringDescTConnectCapClass.lean:299`) named the obstruction verbatim: the `topPerm` /
`middle` phases run on a NON-seed state (post-cap for the middle staircase, post-cup for the top staircase), off the
seed-locked `StateIsPermGraph`, so the seed-only `crossingWord_openWire_sameComponent_bottomPort` cannot reach them.
`crossingWordFold_openWire_sameComponent_afterPrefix` discharges exactly that: it fires the general tracker on
`processBrauer (brauerSeed bottomCount) prefixWord` — a state reached through ANY prefix of caps / cups / crossings /
circles — using `brauerReachable_conditions` for the four state invariants.  So each interior crossing phase now has
its open-wire → permuted-incoming-open-wire correspondence.

## The concrete interior firing — the REAL adversarial-B top phase

`reconstructAdversarialB_correctedFields` pins the corrected reconstruction of `adversarialBDiagram` to its literal
five-block form (`bottomPerm = [1]`, `capBlock = [0]`, `middle = []`, `cupBlock = [1]`, `topPerm = [0]`, `loops =
1`).  `crossingTracker_topPhase_adversarialB` then fires the general tracker on the `topPerm` staircase `crossingWord
[0]` run over the POST-CUP state `processBrauer (brauerSeed 3) (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++
cupWord [1])` — whose open wires are the fresh ids `[4, 5, 6]` (a genuine non-seed state; `StateIsPermGraph` cannot be
stated on it, the boundary is post-cup / post-cap).  `crossingTracker_topPhase_adversarialB_decided` cross-checks the
same three per-position connectivities by kernel `decide`.

## Honest scope — the CAP / CUP / THROUGH per-arc T-CONNECT PROOFS stay UNBUILT; no master flips

This file ships the interior-tracker specialization and its firing on the real top phase — one genuine ingredient
each of the CUP and THROUGH per-arc T-CONNECT chains.  It does NOT assemble the full per-arc connectivity.  The exact
remaining goals, each NAMED:

  * **CAP** (`matchingSameComponent d.bottomCount F i (partner i) = true`, both feet bottom): the position-bookkeeping
    assembly — pair the bottomPerm-phase open wires as `flattenNatPairs feetPairs ++ throughBlock`, connect each
    consecutive pair by `capFold_consumes`, align `capArcFeet d.bottomCount d.partner` (via
    `correctedBottomPerm_decodesReadOff`) with the paired open wires through the seed tracker
    `crossingWordFold_openWire_sameComponent_incomingPort_seed`, and transport to `F` by
    `capThenCupFold_connects_survivesTail`.  Tracker-free; T-ENUM position bookkeeping.

  * **CUP** (both feet top): the `topPerm` phase tracker (SHIPPED here as
    `crossingWordFold_openWire_sameComponent_afterPrefix`) composed with `correctedTopPerm_decodesInverseReadOff` (the
    `permInverse` routing) to identify the two cup legs surfacing at the read top ports, then
    `capThenCupFold_connects`'s fresh-cup-pair connectivity.

  * **THROUGH** (one bottom, one top): the seed bottomPerm tracker + the `middle`-phase tracker (post-cap, via
    `…_afterPrefix`) + the `topPerm`-phase tracker (post-cup) composed across five phases, with the node-identity
    survival of the through wire under the cap / cup phases (`capFold_consumes` / `capThenCupFold_connects` open-wire
    results).

  * **T-CLOSE(b)**: the per-slot read-offs reassembled into `extractDiagram F = d` via
    `foldRealizesTargetDiagramCorrected` — a separate literal step ON TOP of the per-arc T-CONNECT.

So `fxBrauer_hasTConnectThroughWall` / `fxBrauer_hasFoldAlignmentE3` / `fxBrauer_hasFoldTargetHonestAssembly` /
`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction` stay honestly `false`; #2013 does NOT close.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only on closed
literals.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The interior-phase tracker — a crossing staircase after ANY reachable prefix -/

/-- ★★ **THE INTERIOR-PHASE CROSSING TRACKER.**  Firing a crossing staircase `crossingWord positions` AFTER an
arbitrary prefix word over the seed (any composition of caps / cups / crossings / circles), each final open wire
shares a union-find component with the OLD open wire — of the post-prefix state — at the permuted position.  The r23
general tracker `crossingWordFold_openWire_sameComponent_incomingPort` instantiated on the reachable interior state
`processBrauer (brauerSeed bottomCount) prefixWord` (its four `BrauerStateConditions` invariants supplied by
`brauerReachable_conditions`).  This is the exact shape the CUP `topPerm` phase (post-cup) and the THROUGH
`middle` / `topPerm` phases (post-cap / post-cup) consume — the seed-locked `boundView` route being unavailable on
these non-seed states. -/
theorem crossingWordFold_openWire_sameComponent_afterPrefix (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixWord : List BrauerAtom) (positions : List Nat)
    (inRange : ∀ position, position ∈ positions →
      position + 2 ≤ (processBrauer (brauerSeed bottomCount) prefixWord).openWires.length) :
    natListPointwiseSameComponent
      (processBrauer (processBrauer (brauerSeed bottomCount) prefixWord) (crossingWord positions)).links
      (processBrauer (processBrauer (brauerSeed bottomCount) prefixWord) (crossingWord positions)).openWires
      (positions.foldl applyAdjacentSwap (processBrauer (brauerSeed bottomCount) prefixWord).openWires) :=
  crossingWordFold_openWire_sameComponent_incomingPort bottomCount positions
    (processBrauer (brauerSeed bottomCount) prefixWord)
    (brauerReachable_conditions bottomCount bottomPos prefixWord)
    inRange

/-! ## The concrete interior firing — the REAL adversarial-B `topPerm` phase (post-cup, non-seed) -/

/-- The corrected reconstruction of the triple-axis adversarial-B diagram, pinned to its literal five-block form —
`bottomPerm = [1]`, `capBlock = [0]`, `middle = []`, `cupBlock = [1]`, `topPerm = [0]`, `loops = 1`.  So the literal
phase words below ARE the real six-phase fold of `adversarialBDiagram`. -/
theorem reconstructAdversarialB_correctedFields :
    reconstructStandardFormExt5Corrected adversarialBDiagram
      = { bottomCount := 3, bottomPerm := [1], capBlock := [0], middle := [], cupBlock := [1], topPerm := [0],
          loops := 1 } := by decide

/-- ★★ **The general tracker fires on the REAL adversarial-B `topPerm` phase (a genuine NON-seed state).**  The top
crossing staircase `crossingWord [0]` runs over the post-cup state `processBrauer (brauerSeed 3) (crossingWord [1] ++
capWord [0] ++ crossingWord [] ++ cupWord [1])` — whose open wires are the fresh ids `[4, 5, 6]`, a state on which
`StateIsPermGraph` cannot even be stated (post-cap / post-cup boundary).  The general tracker (via
`…_afterPrefix`) discharges it — exactly the "topPerm phase on a NON-seed state" the r19 / r22 wall named as
UNBUILT. -/
theorem crossingTracker_topPhase_adversarialB :
    natListPointwiseSameComponent
      (processBrauer (processBrauer (brauerSeed 3)
        (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).links
      (processBrauer (processBrauer (brauerSeed 3)
        (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).openWires
      ([0].foldl applyAdjacentSwap (processBrauer (brauerSeed 3)
        (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])).openWires) :=
  crossingWordFold_openWire_sameComponent_afterPrefix 3 (by decide)
    (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1]) [0]
    (fun position positionMem => by
      cases positionMem with
      | head => decide
      | tail _ nilMem => nomatch nilMem)

/-- ★ **The interior top-phase firing, kernel-decided at each position.**  The three per-position connectivities of
the adversarial-B top-phase firing are each `true` on the closed literal — the general tracker's conclusion
cross-checked by `decide`, confirming the interior firing is not vacuous. -/
theorem crossingTracker_topPhase_adversarialB_decided :
    (isSameComponent (processBrauer (processBrauer (brauerSeed 3)
        (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).links
        (natListGetAt (processBrauer (processBrauer (brauerSeed 3)
          (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).openWires 0)
        (natListGetAt ([0].foldl applyAdjacentSwap (processBrauer (brauerSeed 3)
          (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])).openWires) 0) = true)
    ∧ (isSameComponent (processBrauer (processBrauer (brauerSeed 3)
        (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).links
        (natListGetAt (processBrauer (processBrauer (brauerSeed 3)
          (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).openWires 1)
        (natListGetAt ([0].foldl applyAdjacentSwap (processBrauer (brauerSeed 3)
          (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])).openWires) 1) = true)
    ∧ (isSameComponent (processBrauer (processBrauer (brauerSeed 3)
        (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).links
        (natListGetAt (processBrauer (processBrauer (brauerSeed 3)
          (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])) (crossingWord [0])).openWires 2)
        (natListGetAt ([0].foldl applyAdjacentSwap (processBrauer (brauerSeed 3)
          (crossingWord [1] ++ capWord [0] ++ crossingWord [] ++ cupWord [1])).openWires) 2) = true) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the interior-phase crossing tracker is SHIPPED and fired on the real six-phase fold
(r23).**  `crossingWordFold_openWire_sameComponent_afterPrefix` specializes the r23 general tracker to a crossing
staircase after ANY reachable prefix — the exact shape the CUP `topPerm` phase (post-cup) and the THROUGH
`middle` / `topPerm` phases (post-cap / post-cup) consume, off the seed-locked `StateIsPermGraph`.  It fires on the
genuine NON-seed `topPerm` phase of the real adversarial-B six-phase fold
(`crossingTracker_topPhase_adversarialB`, `reconstructAdversarialB_correctedFields`,
`…_decided`).  This is one ingredient each of the CUP and THROUGH per-arc T-CONNECT chains; the full per-arc
connectivity (CAP position bookkeeping + CUP / THROUGH decode alignment) and the T-CLOSE(b) reassembly remain the
named residuals, so `fxBrauer_hasTConnectThroughWall` stays `false` and #2013 does NOT close.  `= true`. -/
def fxBrauer_hasInteriorCrossingTracker : Bool := true

end FX1Poly.Polygraph
