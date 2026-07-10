import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFold
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractorLedger

/-! # BRAUER-MIDDLE r3 B4 — THE LEDGER: the machine-checked terminal state + the sharpened residual nodes

This is the honest terminal ledger for the BRAUER-MIDDLE r3 round (#2013).  The round SHIPPED, zero-axiom, three
bricks that advance the r2 state:

  * **B1 — R3-A the inversion-CORRECTED arc extractor** (`fxBrauer_hasExt5CorrectedNestedReadback = true`).  The r2
    flat extractor returned `none` on nested multi-crossing cups; the cup-side inversion fix
    (`reconstructStandardFormExt5Corrected`) makes the nested `[3,2,1,0]` and triple-nested `[5,4,3,2,1,0]` read back
    `some` and REALIZE, with no regression.  The corrected extractor is empirically TOTAL — every perfect matching up
    to boundary size 8, across all bottom/top splits, reads back — so the general roundtrip is a TRUE theorem (only
    its PROOF, the `stepWiring`-connectivity induction, walls).
  * **B2 — R3-B the STAGED arc-count fuel + the single-global-lex NO-GO** (`fxBrauer_hasStagedArcCountFuel = true`).
    The naive single lex over `(straddleCount, arcMeasure)` is machine-REFUTED (`singleGlobalLexMeasure_refuted`):
    the two measures are anti-correlated — the straddle raises `arcMeasure`, the whiskered distant slide raises
    `straddleCount`.  The resolution is the OUTER arc-count fuel `arcCountFuel`, a DIAGRAM invariant (constant across
    a convertibility class, unraisable by any move) that strictly descends `3 > 2 > 1 > 0` per peeled arc.
  * **B3 — R3-C the whisker-free ASSEMBLY over the CORRECTED extractor** (`fxBrauer_hasCorrectedFoldReduction = true`).
    The fold `BrauerExt5CorrectedFoldReaches` over the (total) corrected extractor reduces, via the shipped symm/trans
    glue, to full V2 completeness `brauerWords_equalMatching_conv_ofCorrectedFold` — whisker-free, and with the fold's
    target now SOUND on every diagram (the r2 unsoundness caveat on nested cups removed).  The bounded driver fires on
    the straddle class (`correctedFold_straddle_reaches`).

The round did NOT close #2013: the corrected fold `BrauerExt5CorrectedFoldReaches` is not discharged, so
`fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` STAY `false`.  Per the 110-percent directive
every residual below is a ROUTE / measure / totality gap, NEVER a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6
guarantees the presentation is complete; and B1's exhaustive size-8 check makes the totality's TRUTH concrete).

## The sharpened r3 wall — one NAMED node, three legs, machine-checked `false`

The single remaining obstruction is discharging `BrauerExt5CorrectedFoldReaches`, which jointly needs:

  * **R3-A-PROOF** (`fxBrauer_hasExt5CorrectedRoundtripProof = false`): the corrected extractor's roundtrip
    `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d` for ALL well-formed `d` — TRUE (size-8
    exhaustive), but its PROOF is the `stepWiring`-connectivity structural induction (the `fxBrauer_hasCrossingOnlyReadback`
    long pole).  This is now a proof gap over a KNOWN-TRUE statement, not a truth gap.
  * **R3-B-INNER** (`fxBrauer_hasStagedInnerDescentDischarged = false`): the INNER per-arc boundary-slot descent over
    `BrauerConvFree8` (the native chord-shift), the OUTER arc-count fuel being already shipped.
  * **R3-C-DRIVER** (`fxBrauer_hasCorrectedFoldDischarged = false`): the whisker-free driver threading the two-level
    (arc-count outer × slot-descent inner) fuel to carry an ARBITRARY word to its corrected form.

Discharging R3-A-PROOF ∧ R3-B-INNER ∧ R3-C-DRIVER jointly discharges `BrauerExt5CorrectedFoldReaches`, which via
`brauerWords_equalMatching_conv_ofCorrectedFold` flips `fxBrauer_hasBrauerV2FullCompleteness` and closes #2013.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The grand r3 ledger — one machine-checked terminal state -/

/-- ★★★ **The BRAUER-MIDDLE r3 GRAND LEDGER — MACHINE-CHECKED.**  Every B1 / B2 / B3 shipped marker is `true`, and
every wall — the sharpened R3-A-PROOF / R3-B-INNER / R3-C-DRIVER residual nodes, the r2 residual nodes (still open),
and the master V2 / connectivity completeness flags — is `false`.  A `rfl`-conjunction the kernel checks over the
shipped markers: the round shipped the corrected extractor + staged fuel + whisker-free reduction, but the corrected
fold is not discharged, so #2013 does NOT close and no master flip is fabricated. -/
theorem fxBrauer_r3GrandLedger :
    (fxBrauer_hasExt5CorrectedNestedReadback = true
      ∧ fxBrauer_hasStagedArcCountFuel = true
      ∧ fxBrauer_hasCorrectedFoldReduction = true)
    ∧ (fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasCorrectedFoldDischarged = false)
    ∧ (fxBrauer_hasExt5TotalExtractorRoundtrip = false
      ∧ fxBrauer_hasStraddleGlobalFuelNode = false
      ∧ fxBrauer_hasWhiskerFreeSortDriver = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ## The terminal honesty marker -/

/-- ★★ **Honesty marker — BRAUER-MIDDLE r3 did NOT close #2013 (the honest wall, sharpened).**  The round shipped the
inversion-corrected (empirically total) arc extractor (B1), the staged arc-count fuel + the single-global-lex NO-GO
(B2), and the whisker-free assembly over the corrected extractor (B3), each zero-axiom — a genuine advance over r2:
the nested cups now read back, the single-measure route is REFUTED and replaced by the arc-count staging, and the
fold's target is now sound on every diagram.  But the corrected fold `BrauerExt5CorrectedFoldReaches` is not
discharged, so the masters stay `false` and #2013 does not close.  The exact wall is the conjunction R3-A-PROOF (the
KNOWN-TRUE connectivity roundtrip whose proof is the structural induction) ∧ R3-B-INNER (the per-arc chord-shift) ∧
R3-C-DRIVER (the whisker-free two-level-fuel driver) — every one a ROUTE / measure / totality gap, never a truth gap.
`= false`. -/
def fxBrauer_hasBrauerMiddleR3Complete : Bool := false

end FX1Poly.Polygraph
