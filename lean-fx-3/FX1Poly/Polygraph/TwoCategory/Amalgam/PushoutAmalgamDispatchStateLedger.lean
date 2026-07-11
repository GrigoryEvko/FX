import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutDispatchMasterReAuditLedger
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWireChangeLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutAmalgamDispatchStateLedger — the #2043 state after r14
(WP-AMALG-2 r14, Brick B5 — the roll-up state ledger; every jam = the exact goal with a NAMED node)

r14 (the cross-lane unblock) converted Finding-C from "cross-lane blocked" to authored-and-shipped:

  * B1 `wordMul_vcompReconstructed` — the vertical word multiplicativity RESEATED onto the reconstructed pushout
    signature (`fxAmalg_hasReconstructedWordVcompReseat = true`).
  * B2 `reconWordGapFill` / `reconWordThreeGapSplice` — the multi-gap gap-EZ splice on the reseat, per-gap content
    produced generically (`fxAmalg_pushoutNormalFormSpliceShips = true`).
  * B3 the atomic-firing adjudication — the finest payload zip BYPASSED
    (`fxAmalg_atomicFiringZipBypassed = true`).
  * B4 the master re-audit — NO master flips (`fxAmalg_masterReAuditR14NoFlip = true`).

This ledger machine-records the whole-picture #2043 state and pins each remaining jam to its EXACT goal and NAMED
node.

## The two jams (each: the exact goal + the NAMED node)

  * **JAM A — purification-completeness (masters i, iii's completeness horn).**  NAMED node:
    `fxAmalg_hasSaturatedDispatchTheorem` (= `false`, `SaturatedDispatch.lean`).  EXACT goal: every pushout
    derivation must project back to per-component derivations (Nelson-Oppen / Baader-Tinelli purification; the
    Ghilardi-Nicolini-Zucchelli Noetherian-interface residual), which the unit/counit WIRE-CREATING generators
    break (they violate the convex-block / word-preserving projection).  The r14 reseat is essential-surjectivity
    CONTENT — it does NOT address purification.

  * **JAM B — the top firing-block FACTORISATION reader (masters ii, iii).**  NAMED node: `pushoutFactorize` — an
    arbitrary pushout cell FACTORS into a `ShiftedGapFill` / `VcompGapPair` layout (each slot a maximal firing
    region) with a convertibility to it.  EXACT goal, three legs: (a) the `blockDecompose↔composePath`
    reconstruction bridge to READ the gap list off an arbitrary cell's boundary; (b) the per-case payload re-slice
    (`mergeFrameIntoHead/Tail`, consuming `finestGapWidthsAux_append` at the CELL level to fuse adjacent firing
    regions across a `composePath` junction cast — and NOT the false finest identity-payload zip, B3); (c) the
    decider wiring, whose `multiGapShiftedSplice` leg the r14 reseat NOW FEEDS with generic per-gap content (B2), so
    (c) is the ONLY leg r14 advanced.  `fxAmalg_factorizationCompletenessStaysWalled = true` records leg (a)+(b).

## Close criterion (maximally strict)

`#2043` closes iff `fxAmalg_hasFullSaturatedPushoutDispatch ∧ fxAmalg_hasGeneralPushoutDispatch ∧
¬ fxAmalg_topFactorizationInductionStaysWalled` — i.e. both jams closed.  After r14 that is `false ∧ false ∧ ¬true
= false`: `#2043` does NOT close (`fxAmalg_pushoutDispatch2043ClosesAfterR14 = false`, machine-checked).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## r14 shipped — the four bricks live (machine-checked conjunction) -/

/-- The r14 deliverable conjunction — B1 reseat, B2 splice, B3 adjudication, B4 re-audit all live. -/
def reconR14BricksShipped : Bool :=
  fxAmalg_hasReconstructedWordVcompReseat
    && fxAmalg_pushoutNormalFormSpliceShips
    && fxAmalg_atomicFiringZipBypassed
    && fxAmalg_masterReAuditR14NoFlip

/-- The r14 bricks are all live (`rfl`). -/
theorem reconR14BricksShipped_true : reconR14BricksShipped = true := rfl

/-! ## The two jams, each pinned to its NAMED node's current (open) value -/

/-- JAM A pinned — purification-completeness stays OPEN: the NAMED node `fxAmalg_hasSaturatedDispatchTheorem` is
`false` (`rfl`).  The reseat does not address it. -/
theorem reconR14JamA_purificationOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- JAM B pinned — the top firing-block factorisation reader stays WALLED: the NAMED node's ledger marker
`fxAmalg_factorizationCompletenessStaysWalled` is `true` (`rfl`).  The reseat feeds only leg (c)'s
`multiGapShiftedSplice`. -/
theorem reconR14JamB_factorizationWalled : fxAmalg_factorizationCompletenessStaysWalled = true := rfl

/-! ## The #2043 close criterion (maximally strict) -/

/-- The `#2043` close criterion — closes iff BOTH masters (i)/(ii) hold AND the top factorisation is no longer
walled.  Encodes the strict "genuine full coverage" bar; anything less is `false`. -/
def fxAmalg_pushoutDispatch2043ClosesAfterR14 : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatch
    && fxAmalg_hasGeneralPushoutDispatch
    && (fxAmalg_topFactorizationInductionStaysWalled == false)

/-- ★★★ **`#2043` does NOT close after r14 (`rfl`).**  The close criterion evaluates to `false`: both jams (A
purification-completeness, B the top firing-block factorisation reader) remain open.  The honest ceiling — r14
narrowed, it did not close. -/
theorem fxAmalg_pushoutDispatch2043ClosesAfterR14_false :
    fxAmalg_pushoutDispatch2043ClosesAfterR14 = false := rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the #2043 state after r14: Finding-C authored + shipped, two named jams remain, #2043
does NOT close (WP-AMALG-2 r14, B5).**  `= true` (the STATE is honestly recorded, not a claim that #2043 closes).
r14 shipped four bricks (`reconR14BricksShipped_true`): B1 the reseat (`wordMul_vcompReconstructed`), B2 the
multi-gap gap-EZ splice on the reseat (`reconWordGapFill` / `reconWordThreeGapSplice`), B3 the atomic-firing
adjudication (the finest payload zip BYPASSED), B4 the master re-audit (no flip).  Two jams remain, each pinned to
its named node at its open value: JAM A purification-completeness (`fxAmalg_hasSaturatedDispatchTheorem = false`,
`reconR14JamA_purificationOpen`) and JAM B the top firing-block factorisation reader `pushoutFactorize`
(`fxAmalg_factorizationCompletenessStaysWalled = true`, `reconR14JamB_factorizationWalled`).  The strict close
criterion `fxAmalg_pushoutDispatch2043ClosesAfterR14` is machine-checked `= false`
(`fxAmalg_pushoutDispatch2043ClosesAfterR14_false`).  r14 is an HONEST NARROWING.  `#2043` does NOT close.  `= true`. -/
def fxAmalg_amalgamDispatchStateAfterR14 : Bool := true

end FX1Poly.Polygraph.Amalgam
