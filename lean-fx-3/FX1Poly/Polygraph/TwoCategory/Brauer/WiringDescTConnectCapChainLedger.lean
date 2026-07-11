import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChain
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTrackerInterior

/-! # BRAUER r24 — the cap chain ROUTED + the CUP / THROUGH probes + walls + the exact #2013 ledger

The r24 CAP chain (`Brauer/WiringDescTConnectCapChain.lean`) proved `capArcConnect_general` /
`capArcMatching_general`: the GENERAL per-arc CAP-class T-CONNECT.  This file FEEDS that `partnerShares` datum through
the r22 routing collapse `partnerIndexOf_reads_arc_general` to the UNCONDITIONAL per-arc partner read-off for the CAP
class, probes the CUP / THROUGH chains concretely (the recon's B2 / B3 witnesses), names their exact residual gaps,
and records the machine-checked #2013 state — with NO fabricated flip.

## B4 (partial) — the CAP class's UNCONDITIONAL partner read-off (GENERAL)

`partnerIndexOf_readsCapArc_general`: for EVERY well-formed boundary involution `d` and every cap-arc rank, the
extractor's partner map reads exactly the arc's partner off the corrected six-phase fold state — the r22 routing
collapse fed by the r24 `capArcMatching_general`.  This is the per-slot read-off datum `extractDiagram F = d` consumes,
now discharged in general FOR THE CAP CLASS.  The CUP and THROUGH slots stay the residual (their `partnerShares` is
not yet general — see B2 / B3), so `extractDiagram F = d` does NOT close.

## B2 (CUP) — probed on the nested crossing cups; the general proof stays WALLED at GAP β

The recon's CUP witness `nestedCupsDiagram = {0, 4, [3,2,1,0]}` (fully nested crossing cups).  Its top staircase
decodes to `permInverse (throughStrandTops ++ cupArcTops) = [0, 2, 3, 1]` (`cupChainTopDecodeProbe_nestedCups`) and
its two cup arcs `top0↔top3`, `top1↔top2` are same-component in the fold (`cupChainJoinProbe_nestedCups`), the non-arc
`top0↔top1` disconnected.  The GENERAL CUP T-CONNECT stays WALLED at **GAP β — the base-permute bridge**:
`natListGetAt (topPerm.foldl applyAdjacentSwap S4.openWires) index = natListGetAt S4.openWires
(natListGetAt (permuteOfCrossingWord S4.openWires.length topPerm) index)`.  The CAP tracker runs on the SEED
(base `= List.range`, where the target is definitionally `permuteOfCrossingWord`), so CAP needs no such bridge; the CUP
`topPerm` phase runs on the POST-CUP non-seed state `S4`, so it needs the general base ≠ range read-through — UNBUILT.
The other CUP ingredients ARE shipped: the interior tracker `crossingWordFold_openWire_sameComponent_afterPrefix`
(r23), `correctedTopPerm_decodesInverseReadOff` (r19), and the cup fresh-pair connectivity `capThenCupFold_connects`.

## B3 (THROUGH) — probed on adversarial-B; the general proof stays WALLED at GAP β + GAP γ + 5-phase arithmetic

The recon's THROUGH witness is adversarial-B's `1↔top1` (`throughChainProbe_adversarialB`).  The GENERAL THROUGH
T-CONNECT is the heaviest chain: it needs **GAP β** (base-permute, shared with CUP) for the `middle` and `topPerm`
phases, **GAP γ** (that `throughStrandPerm` is a genuine range-permutation with a roundtrip — only its boundedness
`throughStrandPerm_isBounded` is shipped, not distinctness / roundtrip), and the 5-phase rank arithmetic threading a
bottom rank through `throughStrandPerm`, the cup-preserved position, and `topPerm`⁻¹.  All UNBUILT — r25.

## Honest scope — CAP landed and routed; CUP / THROUGH and the master flips are NOT; #2013 does NOT close

`fxBrauer_hasTConnectCapClassRouted = true` is a NEW INGREDIENT marker (the general cap-class partner read-off).  It
flips NO master.  The general per-arc T-CONNECT still needs CUP + THROUGH (GAP β / γ), and `extractDiagram F = d`
needs ALL slots, so `fxBrauer_hasTConnectThroughWall`, `fxBrauer_hasFoldAlignmentE3`,
`fxBrauer_hasFoldTargetHonestAssembly`, the tag-correspondence masters and the completeness masters all stay `false`.
**#2013 does NOT close; T-ENUM / E3 stays the r25 target.**

Raw Lean 4 + Init; `rfl`-conjunction the kernel checks + `decide` on closed literals.  Per-declaration
`#assert_no_axioms` in the audit twin; independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## B4 (partial) — the CAP class's unconditional partner read-off (GENERAL) -/

/-- ★★★ **THE CAP-CLASS PARTNER READ-OFF (GENERAL).**  For EVERY well-formed boundary involution `d` and every cap-arc
rank, the extractor's partner map reads exactly the arc's partner off the corrected six-phase fold state.  The r24
`capArcMatching_general` (the general cap-class `partnerShares`) fed through the r22 routing collapse
`partnerIndexOf_reads_arc_general` — the per-slot read-off `extractDiagram F = d` consumes, now UNCONDITIONAL for the
CAP class.  Range / distinctness premises discharged from `capArcFeetIndices_mem_sound` (smaller foot `< bottomCount`,
partner `< bottomCount`, foot `< partner`). -/
theorem partnerIndexOf_readsCapArc_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (rank : Nat) (rankLt : rank < (capArcFeetIndices d.bottomCount d.partner).length) :
    partnerIndexOf
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (matchingBoundaryNodes d.bottomCount
          (processBrauer (brauerSeed d.bottomCount)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))))
        (d.bottomCount + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length)
        (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank)
      = natListGetAt d.partner (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank) := by
  have iMem := natListGetAtMemCap (capArcFeetIndices d.bottomCount d.partner) rank rankLt
  have bounds := capArcFeetIndices_mem_sound d.bottomCount d.partner
    (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank) iMem
  exact partnerIndexOf_reads_arc_general d bottomPos wf
    (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank)
    (natListGetAt d.partner (natListGetAt (capArcFeetIndices d.bottomCount d.partner) rank))
    (Nat.lt_of_lt_of_le bounds.1 (Nat.le_add_right _ _))
    (Nat.lt_of_lt_of_le bounds.2.1 (Nat.le_add_right _ _))
    (Nat.ne_of_lt bounds.2.2).symm
    (capArcMatching_general d bottomPos wf rank rankLt)

/-- ★★ **The general cap read-off FIRES on the all-caps witness (rank `0`, arc `0↔3`).**  The unconditional cap-class
read-off exercised on `capClassAllCapsDiagram` — boundary index `0`'s partner reads `3`. -/
theorem partnerIndexOf_readsCapArc_firesAllCaps_zero :
    partnerIndexOf
        (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).links
        (matchingBoundaryNodes 4
          (processBrauer (brauerSeed 4)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))))
        (4 + (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).openWires.length)
        (natListGetAt (capArcFeetIndices 4 capClassAllCapsDiagram.partner) 0)
      = natListGetAt capClassAllCapsDiagram.partner
          (natListGetAt (capArcFeetIndices 4 capClassAllCapsDiagram.partner) 0) :=
  partnerIndexOf_readsCapArc_general capClassAllCapsDiagram (by decide) isBoundaryInvolution_allCapsBoundary 0
    (by decide)

/-! ## B2 (CUP) — the concrete probe on the nested crossing cups (eval FIRST) -/

/-- ★ **CUP-chain TOP-DECODE probe (nested cups `{0,4,[3,2,1,0]}`).**  The corrected `topPerm` staircase decodes to
`permInverse (throughStrandTops ++ cupArcTops) = [0, 2, 3, 1]` — the INVERTED routing the cup side (crossings applied
AFTER the cups) requires.  Kernel-decided. -/
theorem cupChainTopDecodeProbe_nestedCups :
    permuteOfCrossingWord 4 (reconstructStandardFormExt5Corrected nestedCupsDiagram).topPerm
      = permInverse (throughStrandTops 0 4 nestedCupsDiagram.partner
          ++ cupArcTops 0 4 nestedCupsDiagram.partner) := by decide

/-- ★ **CUP-chain JOIN probe (nested cups).**  The two nested cup arcs `top0↔top3`, `top1↔top2` are each same-component
in the fold, and the non-arc `top0↔top1` is disconnected — the CUP join witnessed concretely (the fact the general
CUP T-CONNECT would prove, blocked at GAP β). -/
theorem cupChainJoinProbe_nestedCups :
    (matchingSameComponent 0
        (processBrauer (brauerSeed 0)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram))) 0 3 = true)
    ∧ (matchingSameComponent 0
        (processBrauer (brauerSeed 0)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram))) 1 2 = true)
    ∧ (matchingSameComponent 0
        (processBrauer (brauerSeed 0)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram))) 0 1 = false) :=
  ⟨by decide, by decide, by decide⟩

/-! ## B3 (THROUGH) — the concrete probe on adversarial-B (eval FIRST) -/

/-- ★ **THROUGH-chain JOIN probe (adversarial-B).**  The through strand `1↔top1` (boundary indices `1`, `4`) is
same-component in the full six-phase fold; the non-arc `1↔top0` (`1`, `3`) is disconnected — the THROUGH join
witnessed concretely (the fact the general THROUGH T-CONNECT would prove, blocked at GAP β + GAP γ + the 5-phase
arithmetic). -/
theorem throughChainProbe_adversarialB :
    (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 1 4 = true)
    ∧ (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 1 3 = false) :=
  ⟨by decide, by decide⟩

/-! ## B4 / B5 — the honesty markers + the exact #2013 ledger -/

/-- ★★ **Honesty marker — the CAP-class partner READ-OFF is SHIPPED GENERAL (r24).**  `partnerIndexOf_readsCapArc_general`
feeds the r24 `capArcMatching_general` (the general cap-class `partnerShares`) through the r22 routing collapse to the
UNCONDITIONAL per-arc partner read-off for the CAP class — the per-slot `extractDiagram F = d` datum, discharged in
general for cap arcs.  One ingredient of the full assembly; it flips NO master (CUP / THROUGH slots are not yet
general, so `extractDiagram F = d` does not close).  `= true`. -/
def fxBrauer_hasTConnectCapClassRouted : Bool := true

/-- ★★★ **THE BRAUER r24 CAP-CHAIN LEDGER — MACHINE-CHECKED.**  The two NEW ingredient markers
(`fxBrauer_hasTConnectCapClass` = the general per-arc CAP-class T-CONNECT `capArcConnect_general` /
`capArcMatching_general`, `fxBrauer_hasTConnectCapClassRouted` = its routed unconditional partner read-off) are
`true`, on top of the shipped upstream true markers (the r23 general / interior crossing trackers, the r22 routing
collapse); and EVERY master wall — the through-strand per-arc T-CONNECT (`fxBrauer_hasTConnectThroughWall`, still
walled by GAP β for CUP and GAP β + γ for THROUGH), the E3 fold alignment (`fxBrauer_hasFoldAlignmentE3`), the honest
six-phase assembly (`fxBrauer_hasFoldTargetHonestAssembly`), the tag-correspondence masters, and the completeness
masters — is `false`.  A `rfl`-conjunction: r24 assembled the CAP chain in general and routed it, but the CUP /
THROUGH chains (GAP β base-permute bridge, GAP γ `throughStrandPerm` range-permutation) are unbuilt, so no master flip
is fabricated and #2013 does NOT close — T-ENUM / E3 stays the r25 target. -/
theorem fxBrauer_r24CapChainLedger :
    (fxBrauer_hasTConnectCapClass = true
      ∧ fxBrauer_hasTConnectCapClassRouted = true)
    ∧ (fxBrauer_hasGeneralCrossingTracker = true
      ∧ fxBrauer_hasInteriorCrossingTracker = true
      ∧ fxBrauer_hasTConnectRoutingCollapse = true)
    ∧ (fxBrauer_hasTConnectThroughWall = false
      ∧ fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

end FX1Poly.Polygraph
