import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCupChain

/-! # BRAUER r26 — THE THROUGH CHAIN: the width-12 monster probe + the honest 5-phase scope

The CAP chain (seed tracker, one phase) and the CUP chain (`Brauer/WiringDescTConnectCupChain.lean`: one interior
`topPerm` tracker post-cup) are SHIPPED zero-axiom.  The THROUGH class is the recon's risk pole: a through arc joins a
BOTTOM foot `i` (through-bottom rank `r`) to a TOP foot `bottomCount + t` (through-top rank `topRank`), and closing it
needs the through wire's NODE to survive a never-severed connectivity chain across ALL FIVE phases —

    F.openWires[t] ~[topPerm tracker + GAP β + correctedTopPerm decode + r26 keystone] S4.openWires[topRank]
                  =[append-left, topRank < throughBlock.length]                        S3.openWires[topRank]
                  ~[middle tracker + GAP β + correctedMiddle decode + throughStrandPerm[topRank] = r] S2.openWires[r]
                  =[dropFrontPairs read, r-th through wire survives the cap block]      S1.openWires[capFeet.len + r]
                  ~[seed bottomPerm tracker + correctedBottomPerm decode]               i

— three trackers (seed `bottomPerm`, interior `middle` post-cap, interior `topPerm` post-cup), TWO decodes
(`correctedMiddle_decodesReadOff` for P3, `correctedTopPerm_decodesInverseReadOff` for P5), the P3 rank glue
`throughStrandPerm[topRank] = r`, and the P5 `natIndexOfValue order t = topRank` (the SAME r26 rank↔position keystone
the CUP general used).

## What this file ships — the width-12 monster probe (eval FIRST, per the recon self-attack)

`monsterDiagram = {6, 6, [1,0,3,2,6,7,4,5,9,8,11,10], loops := 1}` mixes 2 caps (`0↔1`, `2↔3`), 2 THROUGHS
(`4↔top0`, `5↔top1`), 2 cups (`top2↔top3`, `top4↔top5`), and 1 loop — extending the boundary-8 probe ceiling to 12.
`monsterWidth12Arcs` kernel-decides that all six arcs (both THROUGHS included) are same-component in the width-12
corrected six-phase fold, and `monsterWidth12NonArcs` that three non-arcs are disconnected — the ground truth every
seam of the THROUGH general must reproduce, witnessed on the widest closed literal.

## Honest scope — the THROUGH GENERAL is the standing wall (no fabricated flip)

Every per-seam ingredient is shipped (the three trackers, both decodes, the keystone, the `dropFrontPairs` /
append-left reads, the width chain `cupChainS3Width`), but the FIVE-PHASE node-survival COMPOSITION — tracking the
through wire's node from the seed through cap-survival, the middle routing (`throughStrandPerm[topRank] = r`), the
cup-survival, and the `topPerm` routing — is NOT assembled here.  So the master `fxBrauer_hasTConnectThroughWall` stays
`false`, and with it `fxBrauer_hasFoldAlignmentE3` / `fxBrauer_hasFoldTargetHonestAssembly` / the tag-correspondence /
completeness masters; #2013 does NOT close.

Raw Lean 4 + Init; `decide` only on the closed-literal monster probes.  Per-declaration `#assert_no_axioms` in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The width-12 monster (2 caps + 2 throughs + 2 cups + 1 loop) -/

/-- The width-12 monster diagram: bottom `0↔1`, `2↔3` capped; bottoms `4`, `5` through to tops `0`, `1`; tops `2↔3`,
`4↔5` cupped; one loop.  A boundary involution on `6 + 6` ports — the recon's self-attack #5 witness. -/
def monsterDiagram : DiagramType :=
  { bottomCount := 6, topCount := 6, partner := [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10], loops := 1 }

/-- The monster is a boundary involution: length `12`, self-inverse, fixed-point-free (each field `decide`-checked). -/
theorem monster_isBoundaryInvolution :
    IsBoundaryInvolution (monsterDiagram.bottomCount + monsterDiagram.topCount) monsterDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★ **The width-12 monster ARC probe (eval FIRST).**  All six arcs — the two caps `0↔1`, `2↔3`, the two THROUGHS
`4↔top0` (`4`, `6`) and `5↔top1` (`5`, `7`), and the two cups `top2↔top3` (`8`, `9`) and `top4↔top5` (`10`, `11`) —
are same-component in the width-12 corrected six-phase fold (circle included).  The ground truth the THROUGH general's
five seams must reproduce, kernel-decided on the widest closed literal (boundary 12). -/
theorem monsterWidth12Arcs :
    (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 0 1 = true)
    ∧ (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 2 3 = true)
    ∧ (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 4 6 = true)
    ∧ (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 5 7 = true)
    ∧ (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 8 9 = true)
    ∧ (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 10 11 = true) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ★ **The width-12 monster NON-ARC probe (T-DISJOINT witnessed).**  A cap–cap cross `0↔2`, a through–through cross
`4↔5`, and a cup–cup cross `8↔10` are each DISCONNECTED in the width-12 fold — so the arc probe is not vacuously
all-true, and the through wires join their own tops only. -/
theorem monsterWidth12NonArcs :
    (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 0 2 = false)
    ∧ (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 4 5 = false)
    ∧ (matchingSameComponent 6 (processBrauer (brauerSeed 6)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))) 8 10 = false) :=
  ⟨by decide, by decide, by decide⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the THROUGH width-12 monster is PROBED (r26, eval FIRST).**  `monsterWidth12Arcs` /
`monsterWidth12NonArcs` extend the per-arc-class connectivity ground truth to boundary 12 on a diagram mixing all four
arc classes plus a loop (the recon self-attack #5), with both THROUGH strands `4↔top0`, `5↔top1` same-component and
the through–through cross disconnected.  A NEW ingredient marker; it flips NO master.  `= true`. -/
def fxBrauer_hasThroughWidth12Probe : Bool := true

/-- **Honesty WALL marker — the THROUGH GENERAL five-phase node-survival is UNBUILT (the r26 risk pole).**  Every
per-seam ingredient is shipped — the seed `bottomPerm` tracker (P1), the cap-survival `dropFrontPairs` read (P2), the
interior `middle` tracker + `correctedMiddle_decodesReadOff` + the P3 rank glue `throughStrandPerm[topRank] = r`, the
cup-survival append-left read (P4), the interior `topPerm` tracker + `correctedTopPerm_decodesInverseReadOff` + the r26
rank↔position keystone `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange` (P5, the SAME keystone the CUP
general used) — but the five-phase composition tracking the through wire's node from the seed to its read top port is
NOT assembled.  So `fxBrauer_hasTConnectThroughWall` stays honestly `false`, and with it `fxBrauer_hasFoldAlignmentE3`,
`fxBrauer_hasFoldTargetHonestAssembly`, the tag-correspondence and completeness masters; #2013 does NOT close.
`= false`. -/
def fxBrauer_hasThroughClassGeneral : Bool := false

end FX1Poly.Polygraph
