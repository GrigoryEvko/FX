import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFoldLoops
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR28Ledger

/-! # BRAUER r29 — THE GRAND LEDGER: the unconditional dispatch lands; T-CLOSE(b) is ONE field open

r29 shipped the endgame SPINE and reduced #2013 to a single named field.

## Shipped (true)

  * **The unconditional six-arm dispatch** (`fxBrauer_hasUnconditionalPartnerShares`, B2): `partnerShares_general`
    proves the per-arc T-CONNECT datum `matchingSameComponent d.bottomCount F probeIndex (partner probeIndex) = true`
    for EVERY well-formed boundary involution and EVERY boundary port — the 6-way `partitionThree_of_involution` /
    `…_top` classification (cap-smaller/larger, through-bottom, cup-smaller/larger, through-top) over the three
    shipped per-arc generals (CAP r24, CUP r26, THROUGH r28), with value→rank recovery
    (`natIndexOfValueRoundtrip`) and the `matchingSameComponent_symm` flip.  `partnerIndexOf_reads_arc_unconditional`
    feeds it into the r22 routing collapse — the extractor reads `partner probeIndex` off the fold for every in-range
    port, no per-witness hypothesis.  This DISCHARGES the semantic content of the frozen wall
    `fxBrauer_hasTConnectThroughWall`.

  * **T-CLOSE(b) three of four fields** (B3): `extractDiagram d.bottomCount F = d` closes `bottomCount` (`rfl`),
    `topCount` (`foldOpenWiresWidth_correctedWord`), and `partner` (`extractDiagram_partner_correctedWord`, the whole
    B2 dispatch list-assembled).  `extractDiagram_correctedWord_ofLoopsField` reduces the ENTIRE
    `foldRealizesTargetDiagramCorrected` to the sole residual `F.loops = d.loops`.

## The r29 residual — the loops field (`fxBrauer_hasFoldLoopsCorrectness = false`)

`F.loops = d.loops` has no shipped scaffold (B3 wall): a circle-loop accounting `(processBrauer state (circleWord
n)).loops = state.loops + n` (a clean structural induction, unbuilt) and a boundary-word-adds-0-loops leg needing a
FRESH connectivity invariant (no cap in the corrected fold ever fires on a pre-connected pair).  It holds decidably on
every shipped witness (all-loop `{0,0,[],3}`, adversarial-B, monster) — the corrected extractor is empirically total
— but is unproven in general.

## The r30 endgame (named)

If the loops field lands, `foldRealizesTargetDiagramCorrected` closes in general via
`foldRealizesTargetDiagramCorrected_ofLoopsField`, whereupon the tag-correspondence masters
(`fxBrauer_hasTagCorrDisjoint` / `…Extraction`), the fold-alignment master (`fxBrauer_hasFoldAlignmentE3`), the honest
assembly (`fxBrauer_hasFoldTargetHonestAssembly`), and the completeness / decision wiring
(`fxBrauer_hasBrauerCompleteness` / `…V2FullCompleteness` / `fxBrauer_hasFreeBrauerStraighteningNF`) flip together —
the #2013 close.  Until then every master stays honestly `false`.

Raw Lean 4 + Init.  A `rfl`-conjunction the kernel checks.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **THE BRAUER r29 GRAND LEDGER — MACHINE-CHECKED.**  The r29 endgame spine is `true`: the unconditional
six-arm `partnerShares_general` dispatch (`fxBrauer_hasUnconditionalPartnerShares`), on top of the three shipped
per-arc generals (CAP `fxBrauer_hasTConnectCapClass`, CUP `fxBrauer_hasCupClassTConnect`, THROUGH
`fxBrauer_hasThroughArcGeneral`), the r28 all-class routing (`fxBrauer_hasAllClassRoutingFirings`), and the r19
corrected fold target (`fxBrauer_hasFoldTargetCorrected`).  Every WALL is `false`: the r29 loops-field residual
(`fxBrauer_hasFoldLoopsCorrectness` — the sole thing standing between r29 and T-CLOSE(b)), the FROZEN through-wall
anchor (`fxBrauer_hasTConnectThroughWall`, kept `false` per the r28 additive precedent to preserve the r22/r25/r26/r27
grand ledgers), the frozen r27 snapshot (`fxBrauer_hasThroughClassGeneral`), the fold-alignment / honest-assembly
masters, the tag-correspondence masters, and the completeness masters.  A `rfl`-conjunction: r29 discharges the
per-arc T-CONNECT UNCONDITIONALLY and closes T-CLOSE(b) to ONE field, but the loops field is unbuilt, so no master
flips and #2013 does NOT close. -/
theorem fxBrauer_r29GrandLedger :
    (fxBrauer_hasUnconditionalPartnerShares = true)
    ∧ (fxBrauer_hasTConnectCapClass = true
      ∧ fxBrauer_hasCupClassTConnect = true
      ∧ fxBrauer_hasThroughArcGeneral = true
      ∧ fxBrauer_hasAllClassRoutingFirings = true)
    ∧ (fxBrauer_hasFoldTargetCorrected = true)
    ∧ (fxBrauer_hasFoldLoopsCorrectness = false)
    ∧ (fxBrauer_hasTConnectThroughWall = false
      ∧ fxBrauer_hasThroughClassGeneral = false)
    ∧ (fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Honesty marker — #2013 (WP-BRAUER-4) is NOT complete after r29; the loops field is the sole residual.**
The endgame spine (unconditional dispatch + T-CLOSE(b) three fields) is shipped; the loops field
(`fxBrauer_hasFoldLoopsCorrectness = false`) is the one honest wall between r29 and the #2013 close.  `= false`. -/
def fxBrauer_hasBrauerR29Complete : Bool := false

end FX1Poly.Polygraph
