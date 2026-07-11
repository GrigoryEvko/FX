import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTrackerInterior
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapClass

/-! # BRAUER r23 — the tracker ledger: the exact #2013 state (NO fabricated flip)

r23 built the r19-named fresh-id bridge — the GENERAL non-seed crossing open-wire tracker
`crossingWordFold_openWire_sameComponent_incomingPort` (`Brauer/WiringDescCrossingTracker.lean`) — by a fresh
structural induction (dropping every seed-locked `StateIsPermGraph` field), and specialized it to the interior
phases `crossingWordFold_openWire_sameComponent_afterPrefix`
(`Brauer/WiringDescCrossingTrackerInterior.lean`), firing it on the REAL adversarial-B `topPerm` phase over its
post-cup NON-seed state.  This ledger records the exact marker state — machine-checked by `rfl` — with NO fabricated
flip.

## What FLIPPED (nothing among the masters — two NEW ingredient markers went true)

  * `fxBrauer_hasGeneralCrossingTracker = true` — the general non-seed tracker (the r19 fresh-id bridge, the literal
    precondition the r19 / r22 wall names).
  * `fxBrauer_hasInteriorCrossingTracker = true` — the tracker specialized to a crossing staircase after ANY
    reachable prefix, fired on the real six-phase `topPerm` phase.

Both are INGREDIENTS (one each of the CUP and THROUGH per-arc T-CONNECT chains), not masters — they flip no master.

## What STAYS WALLED (every master `false`; #2013 does NOT close — the exact residual goals)

  * `fxBrauer_hasTConnectThroughWall = false` — the GENERAL per-arc T-CONNECT
    `matchingSameComponent d.bottomCount F i (partner i) = true` across all three arc classes is NOT assembled.  The
    tracker (its named precondition) is now built; what remains is the per-class decode alignment:
      - **CAP**: pair the bottomPerm-phase open wires as `flattenNatPairs feetPairs ++ throughBlock`, connect each
        consecutive pair by `capFold_consumes`, align `capArcFeet` (`correctedBottomPerm_decodesReadOff`) through
        `crossingWordFold_openWire_sameComponent_incomingPort_seed`, transport by
        `capThenCupFold_connects_survivesTail`;
      - **CUP**: the `topPerm` tracker (`…_afterPrefix`) + `correctedTopPerm_decodesInverseReadOff` +
        `capThenCupFold_connects` fresh-cup-pair connectivity;
      - **THROUGH**: seed bottomPerm tracker + `middle` tracker (post-cap) + `topPerm` tracker (post-cup) composed
        across five phases with node-identity survival under the cap / cup phases.
  * `fxBrauer_hasFoldAlignmentE3 = false`, `fxBrauer_hasFoldTargetHonestAssembly = false` — the six-phase
    `foldRealizesTargetDiagram` assembly (per-arc T-CONNECT + T-CLOSE(b) `extractDiagram F = d` reassembly).
  * `fxBrauer_hasTagCorrDisjoint = false`, `fxBrauer_hasTagCorrExtraction = false` — the tag-correspondence masters
    (need per-arc T-CONNECT + T-CLOSE).
  * `fxBrauer_hasBrauerV2FullCompleteness = false`, `fxBrauer_hasBrauerCompleteness = false`,
    `fxBrauer_hasFreeBrauerStraighteningNF = false` — the classical Brauer / TL straightening normal form
    (out of scope).

So **#2013 does NOT close** this round.  If the per-arc T-CONNECT + T-CLOSE(b) lands (CAP + CUP + THROUGH consuming
this tracker, then the `extractDiagram F = d` reassembly), T-ENUM / E3 closes — that is the r24 target.

Raw Lean 4 + Init; `rfl`-conjunction the kernel checks.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **The BRAUER r23 TRACKER LEDGER — MACHINE-CHECKED.**  The two NEW ingredient markers
(`fxBrauer_hasGeneralCrossingTracker` = the r19 fresh-id bridge, `fxBrauer_hasInteriorCrossingTracker` = its interior
specialization fired on the real fold) are `true`, on top of the shipped upstream true markers (the r18 crossing
staircase connectivity, the r22 routing collapse + per-class probes); and EVERY master wall — the through-strand
fresh-id per-arc T-CONNECT (`fxBrauer_hasTConnectThroughWall`), the E3 fold alignment
(`fxBrauer_hasFoldAlignmentE3`), the honest six-phase assembly (`fxBrauer_hasFoldTargetHonestAssembly`), the
tag-correspondence masters, and the completeness masters — is `false`.  A `rfl`-conjunction: r23 built the
r19-named tracker (the wall's own precondition) but the GENERAL per-arc T-CONNECT proof and its T-CLOSE(b)
reassembly are unbuilt, so no master flip is fabricated and #2013 does NOT close. -/
theorem fxBrauer_r23TrackerLedger :
    (fxBrauer_hasGeneralCrossingTracker = true
      ∧ fxBrauer_hasInteriorCrossingTracker = true)
    ∧ (fxBrauer_hasCrossingStaircaseConnectivity = true
      ∧ fxBrauer_hasTConnectRoutingCollapse = true
      ∧ fxBrauer_hasTConnectPerClassProbed = true)
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
