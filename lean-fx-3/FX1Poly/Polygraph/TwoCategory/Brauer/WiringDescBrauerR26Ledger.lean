import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR25Ledger
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughChain

/-! # BRAUER r26 — the RANK↔POSITION keystone + the GENERAL CUP-class T-CONNECT, and the exact #2013 ledger

r26 lands the r25 CUP residual and the shared keystone, each machine-checked zero-axiom:

  * **The RANK ↔ POSITION DUALITY** (`fxBrauer_hasRankPositionDuality`, `WiringDescRankPositionDuality`).
    `natIndexOfValue_natListGetAt_ofDistinct` : for a distinct / range-permutation `order`,
    `natIndexOfValue order (natListGetAt order position) = position`; its `permInverse` form
    `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange` IS the `permInverse` cup-rank arithmetic the r25 ledger
    named as the CUP wall.  The single shared keystone unlocking CUP P5 and THROUGH P3 / P5 — public propext-free
    re-proofs of the conjugator-private roundtrip + injectivity.

  * **The GENERAL per-arc CUP-class T-CONNECT** (`fxBrauer_hasCupClassTConnect`, `WiringDescTConnectCupChain`).
    `cupArcConnect_general` : for EVERY well-formed involution (`0 < bottomCount`) and every cup rank, the cup arc's two
    TOP legs share a union-find component in the corrected six-phase fold; `cupArcMatching_general` lifts it to the
    `partnerShares` matching datum.  The weld (`cupArcConnectViaState`): `foldFactorsThroughCup` + `cupChainS3Width` +
    `cupFold_creates_atOffset` (post-cup split) + the r23 interior tracker + the r25 GAP β + the r19 `correctedTopPerm`
    decode + the r26 keystone, with `circleFold_openWires` carrying the target past the circle phase.  Fired on
    adversarial-B `3↔5`.  The r25 CUP residual — CLOSED.

  * **The THROUGH width-12 monster probe** (`fxBrauer_hasThroughWidth12Probe`, `WiringDescTConnectThroughChain`).
    `monsterWidth12Arcs` / `monsterWidth12NonArcs` extend the per-arc-class connectivity ground truth to boundary 12 on
    a diagram mixing all four arc classes + a loop (both THROUGH strands same-component, T-DISJOINT witnessed).

## B4 — the ALL-CLASS T-CONNECT stays WALLED at the THROUGH GENERAL; no master is flipped

The all-class per-arc T-CONNECT needs, for every well-formed involution, the per-arc `partnerShares` in ALL four
boundary classes.  CAP (r24) and now CUP (r26) are general; THROUGH is not.  The exact jammed goal, with its named
nodes:

    for a through arc (bottom foot i = throughStrandBottoms[r], top foot bottomCount + t, t = throughStrandTops[topRank]):
      matchingSameComponent d.bottomCount F i (d.bottomCount + t) = true

blocked ONLY at the FIVE-PHASE node-survival COMPOSITION `fxBrauer_hasThroughClassGeneral = false`.  Every per-seam
ingredient is shipped — the seed `bottomPerm` tracker (P1), the `dropFrontPairs` cap-survival read (P2), the interior
`middle` tracker + `correctedMiddle_decodesReadOff` + the P3 rank glue `throughStrandPerm[topRank] = r`, the append-left
cup-survival read (P4), the interior `topPerm` tracker + `correctedTopPerm_decodesInverseReadOff` + the r26 keystone
`natIndexOfValue order t = topRank` (P5) — but the composition tracking node `i`'s connectivity through all five phases
is NOT assembled.  With three of six dispatch cases (the through-bottom and through-top arms) unbuilt, the classifier
`allClassArcMatching_general` and the GENERAL unconditional read-off do not land.

So `fxBrauer_hasTConnectThroughWall` stays honestly `false`, and with it `fxBrauer_hasFoldAlignmentE3`,
`fxBrauer_hasFoldTargetHonestAssembly`, the tag-correspondence masters and the completeness masters.  **#2013 does NOT
close; the THROUGH 5-phase assembly is the r27 target** (the CUP residual having closed).  Even were THROUGH to land,
E3 / T-ENUM additionally owes the separate T-CLOSE(b) `extractDiagram F = d` reassembly.  NO flip is fabricated.

Raw Lean 4 + Init; a `rfl`-conjunction the kernel checks.  Per-declaration `#assert_no_axioms` in the audit twin;
independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **THE BRAUER r26 GRAND LEDGER — MACHINE-CHECKED.**  The r26 markers — the rank↔position keystone
(`fxBrauer_hasRankPositionDuality`), the CUP chain factorization kit (`fxBrauer_hasCupChainFactorKit`), the GENERAL
per-arc CUP-class T-CONNECT (`fxBrauer_hasCupClassTConnect`, the r25 CUP residual CLOSED), and the THROUGH width-12
monster probe (`fxBrauer_hasThroughWidth12Probe`) — are `true`, on top of the r24 general CAP-class T-CONNECT
(`fxBrauer_hasTConnectCapClass`) and the r25 GAP β / γ witnesses (`fxBrauer_hasBasePermuteBridge`,
`fxBrauer_hasThroughStrandPermPerm`); and EVERY master wall — the THROUGH GENERAL (`fxBrauer_hasThroughClassGeneral`),
the through-strand T-CONNECT (`fxBrauer_hasTConnectThroughWall`), the E3 fold alignment
(`fxBrauer_hasFoldAlignmentE3`), the honest six-phase assembly (`fxBrauer_hasFoldTargetHonestAssembly`), the
tag-correspondence and completeness masters — is `false`.  A `rfl`-conjunction: r26 CLOSED the CUP class general and
shipped the shared keystone, but the THROUGH 5-phase node-survival composition is unbuilt, so no master flip is
fabricated and #2013 does NOT close — the THROUGH assembly is the r27 target. -/
theorem fxBrauer_r26GrandLedger :
    (fxBrauer_hasRankPositionDuality = true
      ∧ fxBrauer_hasCupChainFactorKit = true
      ∧ fxBrauer_hasCupClassTConnect = true
      ∧ fxBrauer_hasThroughWidth12Probe = true)
    ∧ (fxBrauer_hasTConnectCapClass = true
      ∧ fxBrauer_hasBasePermuteBridge = true
      ∧ fxBrauer_hasThroughStrandPermPerm = true)
    ∧ (fxBrauer_hasThroughClassGeneral = false
      ∧ fxBrauer_hasTConnectThroughWall = false)
    ∧ (fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Honesty marker — BRAUER r26 did NOT close #2013.**  r26 CLOSED the r25 CUP residual — the GENERAL per-arc
CUP-class T-CONNECT (`cupArcConnect_general` / `cupArcMatching_general`) via the shared rank↔position keystone — and
probed the THROUGH class to boundary 12.  But the THROUGH GENERAL's five-phase node-survival composition is named, not
built (`fxBrauer_hasThroughClassGeneral = false`), so the all-class T-CONNECT does not close, `extractDiagram F = d`
does not close, and the tag-correspondence and completeness masters stay `false`.  Every residual a ROUTE gap, never a
truth gap (the THROUGH connectivity is probed general-shape-true at boundary 12).  `= false`. -/
def fxBrauer_hasBrauerR26Complete : Bool := false

end FX1Poly.Polygraph
