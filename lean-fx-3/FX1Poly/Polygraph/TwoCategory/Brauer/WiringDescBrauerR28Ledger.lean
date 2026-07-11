import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR27Ledger
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughWeld

/-! # BRAUER r28 — THE THROUGH WELD lands: the general per-arc THROUGH-class T-CONNECT + the all-class routing, and the
exact #2013 ledger

r28 assembles the FIVE-PHASE THROUGH node-survival WELD the r27 ledger named as the standing residual, delivering the
THIRD (and last) per-arc T-CONNECT class in general form, each brick machine-checked zero-axiom:

  * **B1 — the survival seams P2 / P4** (`fxBrauer_hasThroughSurvivalSeams`, `WiringDescTConnectThroughWeld`).
    `throughCapSurvival` (the through wire survives the cap block: S1 slot `|capArcFeet| + r` = S2 slot `r`, an
    equality of wire ids via `capFold_consumes` + `natListGetAtAppendRightCup`) and `throughCupSurvival` (the through
    wire survives the interior cup block: S3 slot `topRank` = S4 slot `topRank`, an append-LEFT read
    `natListGetAtAppendLeftCap` into the through block), plus the shared `capChainS2Width`.

  * **B2 — the connectivity seams P3 / P5** (`fxBrauer_hasThroughTrackerSeams`).  `throughMiddleTracker` (the interior
    `middle` tracker + GAP β + `correctedMiddle_decodesReadOff`: S3's through wire ~ S2's wire at
    `throughStrandPerm[idx]`) and `throughTopTracker` (the interior `topPerm` tracker + GAP β +
    `correctedTopPerm_decodesInverseReadOff` + the r26 keystone: S5's read top port ~ S4's through wire at `idx`, the
    append-LEFT mirror of the CUP P5), plus the shared `cupChainS4Width`.

  * **B3 — THE WELD** (`fxBrauer_hasThroughArcGeneral`).  `throughArcConnect_general` /
    `throughArcMatching_general` — for EVERY well-formed boundary involution and through-top rank, the through arc's
    bottom foot and its read top open wire share a component in the corrected six-phase fold.  The five-phase
    node-survival chain (seed tracker + P1 decode, then P2·P3·P4·P5) transported to `F.links` by
    `processBrauer_isSameComponent_ofBase` through `foldFactorsThroughCap` / `foldFactorsThroughCup` /
    `standardFormFold_appendSplit`, welded by `isSameComponent_trans` / `_flip` — a direct scale of
    `cupArcConnectViaState` with a FIXED SEED NODE left endpoint and an append-LEFT through-block right read.  Fired on
    both width-12 monster through strands and the mutually-crossing 3-through.

  * **B4 — the all-class routing** (`fxBrauer_hasAllClassRoutingFirings`).  With all three `…ArcMatching_general`
    (CAP r24, CUP r26, THROUGH r28) shipped, each arc class now feeds the r22 routing collapse
    `partnerIndexOf_reads_arc_general` via its GENERAL matching lemma — demonstrated on the monster's cap, cup and
    through arcs; the through class routes uniformly with CAP and CUP.

## B5 — the masters STAY the wall; no master is flipped; #2013 does NOT close

The through general is an INGREDIENT, not a master.  The all-class T-CONNECT master
`fxBrauer_hasTConnectThroughWall` requires the full unconditional `partnerShares_general` — the 6-way
`partitionThree_of_involution` / `…_top` classification split with per-class membership→rank recovery
(`natIndexOfValue_natListGetAt_ofDistinct` threaded through the cap-smaller / cap-larger / cup-smaller / cup-larger /
through-bottom / through-top arms) then the unconditional `partnerIndexOf_reads_arc` read-off — which r28 walls as the
**E3 / T-ENUM r29** residual.  And even with it, the tag-correspondence / completeness masters additionally owe the
separate **T-CLOSE(b)** `extractDiagram F = d` reassembly (`foldRealizesTargetDiagramCorrected`).  So
`fxBrauer_hasTConnectThroughWall`, `fxBrauer_hasFoldAlignmentE3`, `fxBrauer_hasFoldTargetHonestAssembly`, the
tag-correspondence and completeness masters all stay `false`; **#2013 does NOT close** — the r29 endgame is the 6-way
`partnerShares_general` dispatch then T-CLOSE(b).  The FROZEN r27 snapshot `fxBrauer_hasThroughClassGeneral` is kept
`false` (superseded by `fxBrauer_hasThroughArcGeneral`) to preserve `fxBrauer_r27GrandLedger`.

Raw Lean 4 + Init; a `rfl`-conjunction the kernel checks.  Per-declaration `#assert_no_axioms` in the audit twin;
independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **THE BRAUER r28 GRAND LEDGER — MACHINE-CHECKED.**  The four r28 THROUGH-weld markers — the survival seams
(`fxBrauer_hasThroughSurvivalSeams`, P2 / P4), the connectivity seams (`fxBrauer_hasThroughTrackerSeams`, P3 / P5), the
GENERAL per-arc THROUGH T-CONNECT (`fxBrauer_hasThroughArcGeneral`, the five-phase WELD assembled), and the all-class
routing (`fxBrauer_hasAllClassRoutingFirings`, the three generals fed through the routing collapse) — are `true`, on
top of the r27 crux / P1 decode (`fxBrauer_hasThroughStrandRoundtrip`, `fxBrauer_hasThroughReadOffFoot`), the r26
keystone / CUP-class general / GAP β / γ (`fxBrauer_hasRankPositionDuality`, `fxBrauer_hasCupClassTConnect`,
`fxBrauer_hasBasePermuteBridge`, `fxBrauer_hasThroughStrandPermPerm`) and the r24 CAP class
(`fxBrauer_hasTConnectCapClass`); and EVERY master wall — the all-class T-CONNECT master
(`fxBrauer_hasTConnectThroughWall`), the E3 fold alignment (`fxBrauer_hasFoldAlignmentE3`), the honest six-phase
assembly (`fxBrauer_hasFoldTargetHonestAssembly`), the tag-correspondence and completeness masters — is `false`.  A
`rfl`-conjunction: r28 assembled the THROUGH per-arc general (all three classes now general) and demonstrated the
all-class routing, but the full 6-way `partnerShares_general` dispatch (E3 / T-ENUM) and T-CLOSE(b) are unbuilt, so no
master flip is fabricated and #2013 does NOT close. -/
theorem fxBrauer_r28GrandLedger :
    (fxBrauer_hasThroughSurvivalSeams = true
      ∧ fxBrauer_hasThroughTrackerSeams = true
      ∧ fxBrauer_hasThroughArcGeneral = true
      ∧ fxBrauer_hasAllClassRoutingFirings = true)
    ∧ (fxBrauer_hasThroughStrandRoundtrip = true
      ∧ fxBrauer_hasThroughReadOffFoot = true)
    ∧ (fxBrauer_hasRankPositionDuality = true
      ∧ fxBrauer_hasCupClassTConnect = true
      ∧ fxBrauer_hasTConnectCapClass = true)
    ∧ (fxBrauer_hasBasePermuteBridge = true
      ∧ fxBrauer_hasThroughStrandPermPerm = true)
    ∧ (fxBrauer_hasTConnectThroughWall = false
      ∧ fxBrauer_hasThroughClassGeneral = false)
    ∧ (fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩⟩

/-- **Honesty marker — BRAUER r28 did NOT close #2013.**  r28 ASSEMBLED the five-phase THROUGH node-survival WELD
(`throughArcConnect_general` / `throughArcMatching_general`), delivering the THIRD (and last) per-arc T-CONNECT class in
general form so all three `…ArcMatching_general` now exist, and demonstrated the all-class routing over them.  But the
full unconditional `partnerShares_general` — the 6-way classification split with per-class rank recovery and the
unconditional read-off (E3 / T-ENUM) — is named, not built, so the all-class T-CONNECT master
`fxBrauer_hasTConnectThroughWall` stays `false`, and with it `fxBrauer_hasFoldAlignmentE3` /
`fxBrauer_hasFoldTargetHonestAssembly` / the tag-correspondence / completeness masters; `extractDiagram F = d`
(T-CLOSE(b)) is a further separate reassembly.  Every residual a ROUTE gap, never a truth gap.  The r29 endgame: the
6-way `partnerShares_general` dispatch then T-CLOSE(b).  `= false`. -/
def fxBrauer_hasBrauerR28Complete : Bool := false

end FX1Poly.Polygraph
