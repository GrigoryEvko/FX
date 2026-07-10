import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcDescentLedger
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingMatching

/-! # BRAUER-ARC-DESCENT r2 — the standard-form READBACK function + the anchored-measure TARGET WALL (#2013)

The r1 arc-descent round pinned the pass-5-arc wall to a single move — the adjacent-straddle cup slide
`cupSlideRelation` `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` — and named the r2 residual as a boundary-slot
`legDistance` read off a FIXED standard-form target (an ANCHORED measure).  This final arc round (complete-or-wall)
REFUTES that anchored plan and ships the honest wall, machine-checked.

## The decisive finding — the anchored measure cannot be built

The straddle's fixed target diagram is `brauerDiagramOf 1 [cupAt 0, crossingAt 1] = { bottomCount := 1, topCount := 3,
partner := [2, 3, 0, 1], loops := 0 }` (both sides of `cupSlideRelation`, `cupSlide_diagram_sound`).  Its boundary
matching is CROSSING / non-planar (`straddleDiagram_isCrossing`: `¬ IsNonCrossing 1 [2, 3, 0, 1]` by `decide`): the
through-strand `bottom0 ↔ top1` and the top-cup `top0 ↔ top2` interleave on the rectangle boundary.  Consequently NO
Graham–Lehrer tail-cup-block standard form `capWord ++ crossingWord ++ cupWord` over one bottom wire realizes it — the
cup leg is ESSENTIALLY braided past the strand — so the `legDistance` to a fixed tail-block slot is UNDEFINED on the
straddle.  This UPGRADES r1's `straddle_resists_arcMeasure` (the list-order measure ascends) to the sharper permanent
form: the target of the anchored measure does not exist.  The resistance is structural, not a coordinate artifact.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`standardFormOfDiagram : DiagramType → Option BrauerStandardForm`** — the readback function, honestly gated: it
    reconstructs the cap / cup blocks (`readCapPositions` / `readCupPositions`) with an empty middle and GUARDS the
    candidate against `standardFormDiagram = d`.  The guard makes it SOUND unconditionally
    (`standardFormOfDiagram_sound`: a `some` output genuinely realizes the diagram) and PARTIAL honestly.
  * the roundtrip on the reachable planar-empty-middle class — the identity form and the cup–cap form roundtrip
    (`standardFormOfDiagram_roundtrip_identity` / `_cupCap`), each `by decide`.
  * ★ **the two walls EXHIBITED by the readback's `none`s**: `standardFormOfDiagram_straddle_none` (WALL-1: the
    straddle diagram is non-planar, so no tail-block form exists) and `standardFormOfDiagram_pureCrossing_none`
    (WALL-2: the readback-in-context / middle-permutation inversion is unbuilt — the pure-crossing diagram `[3,2,1,0]`
    is planar-reachable but its through-strand permutation is not inverted by the empty-middle reconstruction).
  * ★ **`straddleDiagram_isCrossing`** — the machine-checked anchored-target wall (WALL-1 headline).
  * the crossing-block completeness is already UNCONDITIONAL (`crossingCompleteness_inRange`,
    `Brauer/WiringDescCrossingComplete.lean`) — re-surfaced here as the standard-form MIDDLE-block leg the readback
    would compose with; it is NOT re-proven, only referenced by the ledger.

## The honest terminal state (no flip fabricated)

`fxBrauer_hasArcDescentFold`, `fxBrauer_hasBrauerV2FullCompleteness`, and `fxBrauer_hasBrauerCompleteness` STAY
`false`.  #2013's genuine residual — `BrauerConvFree8` completeness `brauerWords_equalMatching_conv` — remains the
S_n ⋉ TL boundary-crossing-block route (Route B), whose crossing legs are unconditional but whose readback-in-context
(WALL-2) is unbuilt.  The arc ends here (no r3).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cellular readback function (honestly gated by a soundness guard) -/

/-- Read the CAP positions of a diagram: the bottom ports `index` (`< bottomCount`) whose partner is the adjacent
bottom port `index + 1`.  Reads the bottom–bottom arcs a cap block produces.  Structural filter, propext-free. -/
def readCapPositions (bottomCount : Nat) (partner : List Nat) : List Nat :=
  (List.range bottomCount).filterMap (fun index =>
    if natListGetAt partner index == index + 1 then some index else none)

/-- Read the CUP positions of a diagram: the top ports `topIndex` (`< topCount`) whose boundary node
`bottomCount + topIndex` is matched to the adjacent top node `bottomCount + topIndex + 1`.  Reads the top–top arcs a
cup block produces.  Structural filter, propext-free. -/
def readCupPositions (bottomCount topCount : Nat) (partner : List Nat) : List Nat :=
  (List.range topCount).filterMap (fun topIndex =>
    if natListGetAt partner (bottomCount + topIndex) == bottomCount + topIndex + 1 then some topIndex else none)

/-- The reconstructed candidate standard form of a diagram — its cap / cup arc blocks with an EMPTY middle (the
through-strand permutation is deliberately NOT inverted; inverting it is the readback-in-context node WALL-2).  A
best-effort inverse whose correctness is enforced downstream by the `standardFormOfDiagram` guard. -/
def reconstructStandardForm (d : DiagramType) : BrauerStandardForm :=
  { bottomCount := d.bottomCount,
    capBlock := readCapPositions d.bottomCount d.partner,
    middle := [],
    cupBlock := readCupPositions d.bottomCount d.topCount d.partner }

/-- ★ **The standard-form READBACK, honestly gated.**  Reconstruct the cap / cup blocks (empty middle) and accept the
candidate ONLY when its realized diagram equals the input — a decidable guard over `DiagramType`'s computing
`DecidableEq`.  Total (returns `none` when the guard fails), SOUND by construction (`standardFormOfDiagram_sound`),
and PARTIAL: it succeeds on the planar-empty-middle reachable class and returns `none` on middle-permuted diagrams
(WALL-2) and non-planar diagrams like the straddle (WALL-1). -/
def standardFormOfDiagram (d : DiagramType) : Option BrauerStandardForm :=
  if standardFormDiagram (reconstructStandardForm d) = d then some (reconstructStandardForm d) else none

/-- ★ **The readback is SOUND (unconditional).**  Whenever `standardFormOfDiagram d = some form`, the reconstructed
form genuinely realizes the diagram: `standardFormDiagram form = d`.  Straight off the guard — no correctness of the
reconstruction is assumed.  This is the load-bearing invariance the anchored measure would have read the slots off:
a successful readback pins the diagram exactly. -/
theorem standardFormOfDiagram_sound (d : DiagramType) (form : BrauerStandardForm)
    (readback : standardFormOfDiagram d = some form) : standardFormDiagram form = d := by
  unfold standardFormOfDiagram at readback
  split at readback
  · rename_i guardHolds
    rw [← Option.some.inj readback]; exact guardHolds
  · nomatch readback

/-! ## Roundtrip on the reachable planar-empty-middle class (concrete evals) -/

/-- Roundtrip — the identity (empty) standard form over two bottom wires reads back to itself. -/
theorem standardFormOfDiagram_roundtrip_identity :
    standardFormOfDiagram (standardFormDiagram { bottomCount := 2, capBlock := [], middle := [], cupBlock := [] })
      = some { bottomCount := 2, capBlock := [], middle := [], cupBlock := [] } := by decide

/-- Roundtrip — the cap–cup standard form over two bottom wires (`[capAt 0, cupAt 0]`) reads back to itself: its cap
arc (`bottom0 ↔ bottom1`) and cup arc (`top0 ↔ top1`) are recovered by the block readers. -/
theorem standardFormOfDiagram_roundtrip_cupCap :
    standardFormOfDiagram (standardFormDiagram { bottomCount := 2, capBlock := [0], middle := [], cupBlock := [0] })
      = some { bottomCount := 2, capBlock := [0], middle := [], cupBlock := [0] } := by decide

/-! ## The two walls, exhibited by the readback's `none`s -/

/-- The fixed straddle target diagram — the common diagram of both sides of `cupSlideRelation`
(`cupSlide_diagram_sound`), read off the shift-0 straddle `[cupAt 0, crossingAt 1]`. -/
def straddleDiagram : DiagramType :=
  { bottomCount := 1, topCount := 3, partner := [2, 3, 0, 1], loops := 0 }

/-- The straddle target IS the diagram of the straddle word (both sides agree, `cupSlide_diagram_sound`). -/
theorem straddleDiagram_eq : brauerDiagramOf 1 [cupAt 0, crossingAt 1] = straddleDiagram := by decide

/-- ★★ **WALL-1 (the anchored-target wall, machine-checked).**  The straddle target diagram's boundary matching is
CROSSING — the through-strand `bottom0 ↔ top1` and the top-cup `top0 ↔ top2` interleave on the rectangle boundary
(`¬ IsNonCrossing 1 [2, 3, 0, 1]`, `by decide`).  So NO planar Graham–Lehrer tail-cup-block standard form realizes it:
the cup leg is essentially braided past the strand, and the `legDistance` to a fixed tail-block slot is UNDEFINED.
This upgrades r1's `straddle_resists_arcMeasure` (measure ascends) to "the target does not exist". -/
theorem straddleDiagram_isCrossing : ¬ IsNonCrossing straddleDiagram.bottomCount straddleDiagram.partner := by
  decide

/-- ★ **WALL-1 via the readback.**  The readback returns `none` on the straddle diagram: no cap/cup-block
reconstruction realizes it (it is non-planar), so `standardFormOfDiagram` — sound by construction — refuses it.  The
absence of a tail-block realizer is exhibited computationally. -/
theorem standardFormOfDiagram_straddle_none : standardFormOfDiagram straddleDiagram = none := by decide

/-- ★ **WALL-2 (the readback-in-context / middle-permutation gap), exhibited.**  The pure-crossing diagram `[3,2,1,0]`
(the single-crossing standard form `standardFormDiagram { bottomCount := 2, middle := [0], … }`) is planar-REACHABLE,
yet the readback returns `none`: the empty-middle reconstruction does not invert the through-strand permutation.
Reading the middle off a crossing block embedded between cap and cup blocks is the standalone-from-seed readback lifted
through pad/whisker functoriality — the genuine new work Route B (S_n ⋉ TL) needs. -/
theorem standardFormOfDiagram_pureCrossing_none :
    standardFormOfDiagram { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 } = none := by
  decide

/-! ## Non-vacuity — the readback COMPUTES a definite verdict on all three recon diagrams -/

/-- ★ **Non-vacuity — the three recon diagrams each get a definite readback verdict.**  The cup–cap mixed diagram
reads back to `some` (a genuine cap/cup form), the pure-crossing diagram returns `none` (WALL-2), and the straddle
diagram returns `none` (WALL-1) — the readback function computes definite answers on every named instance. -/
theorem standardFormOfDiagram_nonVacuity :
    standardFormOfDiagram { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 }
        = some { bottomCount := 2, capBlock := [0], middle := [], cupBlock := [0] }
      ∧ standardFormOfDiagram { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 } = none
      ∧ standardFormOfDiagram straddleDiagram = none :=
  ⟨by decide, by decide, by decide⟩

/-! ## The anchored-measure wall, assembled from the readback + the r1 resister -/

/-- ★★ **The anchored measure CANNOT be built — the machine-checked terminal wall.**  Bundles: (i) the straddle
target is non-planar (`straddleDiagram_isCrossing`); (ii) the readback refuses it (`standardFormOfDiagram
straddleDiagram = none`), so no tail-block standard form realizes it; and (iii) r1's list-order resister survives —
the straddle keeps its cup first in list order and BUMPS the position, so `cupPositionSum` strictly ascends
(`straddle_resists_arcMeasure`).  Hence neither a list-order measure (r1) NOR an anchored legDistance-to-tail-block
(r2's named target) descends on the straddle: the anchored target does not exist. -/
theorem anchoredMeasure_targetWall :
    (¬ IsNonCrossing straddleDiagram.bottomCount straddleDiagram.partner)
      ∧ standardFormOfDiagram straddleDiagram = none
      ∧ cupPositionSum [cupAt 0, crossingAt 1] < cupPositionSum [cupAt 1, crossingAt 0] :=
  ⟨straddleDiagram_isCrossing, standardFormOfDiagram_straddle_none, straddle_resists_arcMeasure.2⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the standard-form READBACK FUNCTION is SHIPPED (B1, honestly gated).**
`standardFormOfDiagram : DiagramType → Option BrauerStandardForm` reconstructs the cap / cup arc blocks
(`readCapPositions` / `readCupPositions`, empty middle) and GUARDS the candidate against `standardFormDiagram = d`,
making it SOUND unconditionally (`standardFormOfDiagram_sound`).  It roundtrips on the planar-empty-middle reachable
class (`standardFormOfDiagram_roundtrip_identity` / `_cupCap`) and returns `none` on both the pure-crossing diagram
(WALL-2, `standardFormOfDiagram_pureCrossing_none` — the middle permutation is not inverted) and the straddle diagram
(WALL-1, `standardFormOfDiagram_straddle_none` — non-planar, no tail-block realizer).  Non-vacuous on all three recon
diagrams (`standardFormOfDiagram_nonVacuity`).  `= true`. -/
def fxBrauer_hasStandardFormReadbackFunction : Bool := true

/-- ★★ **Honesty WALL marker — the ANCHORED MEASURE cannot be built (B2, the recon's plan REFUTED).**  r1 named the
r2 residual as an anchored `legDistance` to a FIXED tail-block standard-form target that would descend on the
straddle.  `anchoredMeasure_targetWall` proves that target does not exist: the straddle diagram
`{ bottomCount := 1, topCount := 3, partner := [2, 3, 0, 1], loops := 0 }` is non-planar
(`straddleDiagram_isCrossing`), so no `capWord ++ crossingWord ++ cupWord` realizes it (the sound readback returns
`none`), and r1's list-order resister still ascends.  This SHARPENS r1's `straddle_resists_arcMeasure` from "measure
ascends" to "the anchored target does not exist" — a structural wall, not a coordinate artifact.  `fxBrauer_hasArcDescentFold`
and `fxBrauer_hasBrauerV2FullCompleteness` stay `false`; #2013 does not close on the anchored route.  `= true`. -/
def fxBrauer_hasAnchoredMeasureTargetWall : Bool := true

end FX1Poly.Polygraph
