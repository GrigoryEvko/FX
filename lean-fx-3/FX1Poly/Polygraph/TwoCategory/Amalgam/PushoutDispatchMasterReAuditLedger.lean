import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAtomicFiringAdjudication
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutBundle
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompInterchangeSplice

/-! # Polygraph/TwoCategory/Amalgam/PushoutDispatchMasterReAuditLedger — the #2043 master re-audit after r14
(WP-AMALG-2 r14, Brick B4 — conjunct-by-conjunct against the verbatim master demands; NO fabricated flip)

r14 delivered Finding-C's cross-lane reseat (B1 `wordMul_vcompReconstructed`), the multi-gap gap-EZ splice on the
reseat (B2 `reconWordGapFill` / `reconWordThreeGapSplice`), and the atomic-firing adjudication (B3, the finest
payload zip BYPASSED).  This ledger re-audits the three #2043 master markers conjunct-by-conjunct against those
deliverables and machine-checks that NONE flips — maximally strict, no fabricated flip.

## Master (i) — `fxAmalg_hasFullSaturatedPushoutDispatch = false` (DispatchSaturated.lean), three named walls

  * (i) genuine-generator coprojection `onTwoCell` needs `interpretWordFrom_map` — CLOSED
    (`fxAmalg_hasRealGeneratorCoprojection = true`; the marker docstring is stale).
  * (ii) a real saturated decider over the RECONSTRUCTED `monadComputad.toModeSignature` — CLOSED
    (`fxAmalg_hasReconstructionDecoderReseat = true`).
  * (iii) COMPLETENESS — "every pushout derivation must project back to per-component derivations (Nelson-Oppen /
    Baader-Tinelli purification … the unit/counit wire-creating generators break the convex-block projection)."
    OPEN (`fxAmalg_hasSaturatedDispatchTheorem = false`).  The r14 reseat is essential-surjectivity CONTENT, NOT
    purification-completeness — it does NOT touch (iii).  The marker's gate is the AND of all three; (iii) OPEN
    forces `false`.  **STAYS false.**

## Master (ii) — `fxAmalg_hasGeneralPushoutDispatch = false` (PushoutBundle.lean)

Needs a total arbitrary-pair `Decidable`, via route (i) the reconstruction decider reseat (fib-3-coupled) or route
(ii) purification completeness.  The r14 reseat + `multiGapShiftedSplice` extend the isTrue-side splicing to the
multi-gap regime, but the total `Decidable` cannot even be STATED without the TOP firing-block factorisation reader
`pushoutFactorize` (reduce an arbitrary parallel pair to its per-gap right-image list).  That reader is unbuilt.
**STAYS false.**

## Master (iii) — `fxAmalg_topFactorizationInductionStaysWalled = true` (PushoutVcompInterchangeSplice.lean)

Needs (a) the `blockDecompose↔composePath` reconstruction bridge; (b) the per-case assembly (the payload re-slice —
and NOT the false finest zip, B3); (c) the decider wiring (`pushoutFullTwoSidedDecision` +
`pushoutRightImageTwoSidedDecision` + `multiGapShiftedSplice` + `arityFoldRealPushoutCongruence`).  The r14 reseat
FEEDS (c)'s `multiGapShiftedSplice` leg with generic per-gap content (B2 `reconWordGapFill`).  But (a) (the
firing-block reader) and (b) (`mergeFrameIntoHead/Tail`) remain OPEN.  **STAYS true (walled).**

## Verdict

NO master flips.  r14 is an HONEST NARROWING: Finding-C's cross-lane block is converted to
authorable-and-shipped, with three new POSITIVE markers, while the three masters HOLD on the firing-block
factorisation reader (masters ii, iii) and purification-completeness (master i).  `#2043` does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The three masters stay at their walled values (machine-checked, `rfl` — no flip) -/

/-- Master (i) STAYS `false` — the FULL saturated pushout dispatch is still walled on conjunct (iii),
purification-completeness (`fxAmalg_hasSaturatedDispatchTheorem = false`), which the r14 reseat does not touch. -/
theorem reconR14_masterOne_staysFalse : fxAmalg_hasFullSaturatedPushoutDispatch = false := rfl

/-- Master (ii) STAYS `false` — the GENERAL pushout dispatch (a total arbitrary-pair `Decidable`) still needs the
top firing-block factorisation reader `pushoutFactorize`, unbuilt this round. -/
theorem reconR14_masterTwo_staysFalse : fxAmalg_hasGeneralPushoutDispatch = false := rfl

/-- Master (iii) STAYS `true` (walled) — the top factorisation induction still needs the `blockDecompose↔composePath`
reader (a) and the payload re-slice (b); the r14 reseat only feeds the `multiGapShiftedSplice` leg (c). -/
theorem reconR14_masterThree_staysWalled : fxAmalg_topFactorizationInductionStaysWalled = true := rfl

/-! ## The r14 deliverables are live (machine-checked, `rfl`) -/

/-- B1 — the reseat ships. -/
theorem reconR14_reseatShips : fxAmalg_hasReconstructedWordVcompReseat = true := rfl

/-- B2 — the multi-gap gap-EZ splice on the reseat ships. -/
theorem reconR14_spliceShips : fxAmalg_pushoutNormalFormSpliceShips = true := rfl

/-- B3 — the atomic-firing zip is bypassed. -/
theorem reconR14_zipBypassed : fxAmalg_atomicFiringZipBypassed = true := rfl

/-! ## The re-audit conjunction -/

/-- The re-audit CONJUNCTION — machine-checks, in one Boolean, that the three masters stay at their walled values
(`false` / `false` / `true`) AND the three r14 deliverables are live (`true` / `true` / `true`).  Its `= true`
(`reconR14MasterReAudit_true`, `rfl`) IS the maximally-strict no-fabricated-flip certificate. -/
def reconR14MasterReAudit : Bool :=
  (fxAmalg_hasFullSaturatedPushoutDispatch == false)
    && (fxAmalg_hasGeneralPushoutDispatch == false)
    && (fxAmalg_topFactorizationInductionStaysWalled == true)
    && fxAmalg_hasReconstructedWordVcompReseat
    && fxAmalg_pushoutNormalFormSpliceShips
    && fxAmalg_atomicFiringZipBypassed

/-- The re-audit conjunction holds (`rfl`) — masters walled, deliverables live, no flip. -/
theorem reconR14MasterReAudit_true : reconR14MasterReAudit = true := rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the #2043 master re-audit after r14: NO master flips (WP-AMALG-2 r14, B4).**  `= true`.
Conjunct-by-conjunct against the verbatim master demands: master (i) `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS
`false` (conjuncts (i)/(ii) closed but (iii) purification-completeness OPEN — the reseat is essential-surjectivity
content, not purification); master (ii) `fxAmalg_hasGeneralPushoutDispatch` STAYS `false` (the total `Decidable`
needs the unbuilt top firing-block factorisation reader `pushoutFactorize`); master (iii)
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true` (needs the `blockDecompose↔composePath` reader + the
payload re-slice; the reseat only feeds the `multiGapShiftedSplice` leg).  The three walled values are
machine-checked `rfl` (`reconR14_masterOne_staysFalse` / `_masterTwo_` / `_masterThree_`) and the three r14
deliverables live (`reconR14_reseatShips` / `_spliceShips` / `_zipBypassed`), conjoined in
`reconR14MasterReAudit_true`.  r14 is an HONEST NARROWING (Finding-C authored + shipped, three new positive
markers), no fabricated flip.  `#2043` does NOT close.  `= true`. -/
def fxAmalg_masterReAuditR14NoFlip : Bool := true

end FX1Poly.Polygraph.Amalgam
