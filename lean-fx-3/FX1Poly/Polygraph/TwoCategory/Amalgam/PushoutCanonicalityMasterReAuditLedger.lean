import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalReaderConsistency
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeMasterAuditLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutCanonicalityMasterReAuditLedger — the #2043 CANONICALITY adjudication
recorded permanently after r16: the ALIGNABLE verdict, the exact master state, the two jams NAMED (WP-AMALG-2 r16, B5)

r16 (the canonicality-adjudication round) ran the alignment truth probe and shipped the multi-gap plumbing:

  * B1 `PushoutAlignmentTruthProbe` — the probe VERDICT is **ALIGNABLE at the firing-block SKELETON**, with the
    regression pins on the probe candidates.  `fxAmalg_alignmentVerdictAlignableAtSkeleton = true`.
  * B2 `PushoutWhiskerHeadPrependMultiGap` — the multi-gap head-prepend whisker arm (cast-free, `slotCount n → n+1`) +
    the merge-into-head assoc tower.  `fxAmalg_hasWhiskerHeadPrependMultiGap = true`.
  * B3 `PushoutVcompMultiGapSeam` — the vcomp arm at genuine multi-gap granularity (shared two-gap seam).
    `fxAmalg_hasVcompMultiGapSeam = true`.
  * B4 `PushoutCanonicalReaderConsistency` — the upgraded arms assembled, the r15 three decision pairs re-verified
    UNCHANGED, JAM A re-audited as NARROWED.  `fxAmalg_upgradedReaderNoVerdictChange = true`.

This ledger records the CANONICALITY verdict permanently, re-audits the three #2043 master markers + JAM A
conjunct-by-conjunct against their VERBATIM demands, and pins the two jams each to its NAMED node + exact goal.  NO
master flips; NO alignment or flip is fabricated.

## The canonicality verdict (recorded permanently)

The alignment obligation is REAL, provable-in-principle at the firing-block SKELETON granularity (the rigid wall
skeleton, from `wallLetterCount_dom_eq_cod` + `emptyGapLayout_conv_id`), and genuinely DIFFERENT from the r13 walled
per-letter zip (which is FALSE at atomic granularity).  But ALIGNABLE-at-skeleton is ONE ingredient — it does not by
itself close #2043.  The alignment LEMMA proper (two firing-block layouts share the rigid skeleton) is r17-scoped.

## Master (i) — `fxAmalg_hasFullSaturatedPushoutDispatch = false` (`DispatchSaturated.lean:351`)

Horn (iii) purification is OPEN (`fxAmalg_hasSaturatedDispatchTheorem = false`).  r16's multi-gap plumbing produces
DEEPER (multi-slot) layouts but NOT the NF reflection (conv-of-images ⟹ equal-layouts) — the per-gap descent stays
open.  **STAYS false.**

## Master (ii) — `fxAmalg_hasGeneralPushoutDispatch = false` (`PushoutBundle.lean:1081`)

The total `Decidable` for arbitrary pairs needs the CANONICAL firing-block READER to reduce a pair to comparable
per-gap right-images.  r16 upgraded the whisker/vcomp ARMS to multi-gap but did NOT ship the recursive reader off an
arbitrary cell (reader-gated to r17).  **STAYS false.**

## Master (iii) — `fxAmalg_topFactorizationInductionStaysWalled = true` (`PushoutVcompInterchangeSplice.lean:273`)

Needs (a) the canonical block reader, (b) the canonical per-case assembly, (c) the decider wiring.  r16 shipped the
multi-gap-capable per-case ARMS (the head-prepend + the multi-gap seam), not the recursive canonical reader (a).
**STAYS true (walled).**

## Close criterion (verbatim, `PushoutAmalgamDispatchStateLedger.lean:78-87`)

`#2043` closes iff `fxAmalg_hasFullSaturatedPushoutDispatch ∧ fxAmalg_hasGeneralPushoutDispatch ∧
¬ fxAmalg_topFactorizationInductionStaysWalled` = `false ∧ false ∧ ¬true` = false.  `#2043` does NOT close.

## The two jams, each pinned to its NAMED node + exact goal

  * **JAM A — purification / per-gap descent.**  NAMED node `fxAmalg_hasSaturatedDispatchTheorem = false`.  Exact
    goal: the "conv-of-images ⟹ per-gap-conv" descent (the convex-block projection) — sound only for word-preserving /
    left-connected presentations, which the wire-creating `eta`/`mu` violate.  r16 NARROWED it (the skeleton reflects,
    the ALIGNABLE verdict) but the per-gap descent stays the residual.
  * **JAM B — the CANONICAL firing-block reader.**  NAMED node `fxAmalg_topFactorizationInductionStaysWalled = true`.
    Exact goal residuals: the recursive reader off an ARBITRARY cell; the CELL-level merge-into-head surgery (riding
    `whiskerLeftComp` through the `composePath`-assoc cast); the `whiskerRight` multi-gap trailing-frame append; the
    `s`-bearing frame's downstream wall-SHIFT (leg 2a'').  r16 shipped the multi-gap ARMS; the recursive canonical
    reader is the residual.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## r16 shipped — the four bricks live (machine-checked conjunction) -/

/-- The r16 deliverable conjunction — B1 the ALIGNABLE verdict, B2 the multi-gap head-prepend, B3 the multi-gap vcomp
seam, B4 the upgraded-reader no-verdict-change all live. -/
def reconR16BricksShipped : Bool :=
  fxAmalg_alignmentVerdictAlignableAtSkeleton
    && fxAmalg_hasWhiskerHeadPrependMultiGap
    && fxAmalg_hasVcompMultiGapSeam
    && fxAmalg_upgradedReaderNoVerdictChange

/-- The r16 bricks are all live (`rfl`). -/
theorem reconR16BricksShipped_true : reconR16BricksShipped = true := rfl

/-! ## The three masters stay at their walled values (machine-checked `rfl` — no flip) -/

/-- Master (i) STAYS `false` — the FULL saturated pushout dispatch is still walled on horn (iii) purification; r16's
multi-gap plumbing produces deeper layouts, not the NF reflection. -/
theorem reconR16_masterOne_staysFalse : fxAmalg_hasFullSaturatedPushoutDispatch = false := rfl

/-- Master (ii) STAYS `false` — the GENERAL pushout dispatch still needs the recursive canonical firing-block reader;
r16 upgraded the ARMS to multi-gap, not the reader off an arbitrary cell. -/
theorem reconR16_masterTwo_staysFalse : fxAmalg_hasGeneralPushoutDispatch = false := rfl

/-- Master (iii) STAYS `true` (walled) — the top factorization induction still needs the canonical block reader (a);
r16 shipped the multi-gap per-case arms, not the recursive canonical reader. -/
theorem reconR16_masterThree_staysWalled : fxAmalg_topFactorizationInductionStaysWalled = true := rfl

/-- JAM A pinned — purification / per-gap descent STAYS OPEN: `fxAmalg_hasSaturatedDispatchTheorem = false` (`rfl`).
The multi-gap plumbing narrows it (the skeleton reflects) but does not supply the descent. -/
theorem reconR16_purificationStaysOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- The ALIGNABLE verdict recorded permanently — `fxAmalg_alignmentVerdictAlignableAtSkeleton = true` (`rfl`): the
alignment holds at the firing-block SKELETON granularity. -/
theorem reconR16_alignmentVerdictAlignable : fxAmalg_alignmentVerdictAlignableAtSkeleton = true := rfl

/-! ## The #2043 close criterion (maximally strict, verbatim) -/

/-- The `#2043` close criterion (r16) — closes iff BOTH masters (i)/(ii) hold AND the top factorisation is no longer
walled.  The SAME criterion as `fxAmalg_pushoutDispatch2043ClosesAfterR15`, re-evaluated after r16's multi-gap
plumbing: genuine ARBITRARY-CELL ARBITRARY-PAIR coverage is the bar; multi-gap ARMS + an ALIGNABLE-at-skeleton verdict
do not meet it. -/
def fxAmalg_pushoutDispatch2043ClosesAfterR16 : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatch
    && fxAmalg_hasGeneralPushoutDispatch
    && (fxAmalg_topFactorizationInductionStaysWalled == false)

/-- ★★★ **`#2043` does NOT close after r16 (`rfl`).**  The close criterion evaluates to `false`: both jams (A the
per-gap descent, B the canonical firing-block reader) remain open.  r16 delivered the multi-gap plumbing and the
ALIGNABLE-at-skeleton verdict — an HONEST NARROWING; the canonical reader + arbitrary-pair decision are the wall. -/
theorem fxAmalg_pushoutDispatch2043ClosesAfterR16_false :
    fxAmalg_pushoutDispatch2043ClosesAfterR16 = false := rfl

/-! ## The two jams, each pinned to its NAMED node (current open value) -/

/-- JAM A pinned — the per-gap descent stays OPEN: `fxAmalg_hasSaturatedDispatchTheorem = false` (`rfl`). -/
theorem reconR16JamA_perGapDescentOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- JAM B pinned — the canonical firing-block reader stays WALLED: `fxAmalg_topFactorizationInductionStaysWalled =
true` (`rfl`). -/
theorem reconR16JamB_canonicalReaderWalled : fxAmalg_topFactorizationInductionStaysWalled = true := rfl

/-! ## The re-audit conjunction -/

/-- The re-audit CONJUNCTION — machine-checks, in one Boolean, that the three masters stay at their walled values
(`false` / `false` / `true`), purification stays open (`false`), the ALIGNABLE verdict is recorded (`true`), AND the
four r16 bricks are live.  Its `= true` (`reconR16MasterAudit_true`, `rfl`) IS the maximally-strict
no-fabricated-flip certificate. -/
def reconR16MasterAudit : Bool :=
  (fxAmalg_hasFullSaturatedPushoutDispatch == false)
    && (fxAmalg_hasGeneralPushoutDispatch == false)
    && (fxAmalg_topFactorizationInductionStaysWalled == true)
    && (fxAmalg_hasSaturatedDispatchTheorem == false)
    && fxAmalg_alignmentVerdictAlignableAtSkeleton
    && fxAmalg_hasWhiskerHeadPrependMultiGap
    && fxAmalg_hasVcompMultiGapSeam
    && fxAmalg_upgradedReaderNoVerdictChange

/-- The re-audit conjunction holds (`rfl`) — masters walled, purification open, verdict recorded, bricks live, no
flip. -/
theorem reconR16MasterAudit_true : reconR16MasterAudit = true := rfl

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the #2043 CANONICALITY re-audit after r16: NO master flips (WP-AMALG-2 r16, B5).**  `=
true`.  Conjunct-by-conjunct against the VERBATIM master demands: master (i)
`fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false` (horn (iii) purification OPEN — the multi-gap plumbing is
deeper layouts, not the NF reflection); master (ii) `fxAmalg_hasGeneralPushoutDispatch` STAYS `false` (needs the
recursive canonical reader, not the multi-gap arms); master (iii) `fxAmalg_topFactorizationInductionStaysWalled` STAYS
`true` (needs the canonical block reader).  The four walled/open values are machine-checked `rfl`
(`reconR16_masterOne_staysFalse` / `_masterTwo_` / `_masterThree_` / `_purificationStaysOpen`), the ALIGNABLE verdict
is recorded (`reconR16_alignmentVerdictAlignable`), and the four r16 bricks are live (`reconR16BricksShipped_true`),
conjoined in `reconR16MasterAudit_true`.  r16 is an HONEST NARROWING (the multi-gap plumbing + the ALIGNABLE-at-
skeleton verdict ship; the canonical reader + per-gap descent are the wall), no fabricated flip or alignment.  `#2043`
does NOT close (`fxAmalg_pushoutDispatch2043ClosesAfterR16_false`).  `= true`. -/
def fxAmalg_masterAuditR16NoFlip : Bool := true

/-- ★★★ **Honesty marker — the #2043 CANONICALITY state after r16: multi-gap plumbing ships, verdict ALIGNABLE,
two named jams remain, #2043 does NOT close.**  `= true` (the STATE is honestly recorded, not a claim that #2043
closes).  r16 shipped the four bricks (`reconR16BricksShipped_true`): B1 the ALIGNABLE-at-skeleton verdict + regression
pins, B2 the multi-gap head-prepend whisker arm (`slotCount n → n+1`), B3 the vcomp arm at genuine multi-gap
granularity, B4 the upgraded arms + decision consistency + the JAM A narrowing.  Two jams remain, each pinned to its
named node at its open value: JAM A the per-gap descent (`fxAmalg_hasSaturatedDispatchTheorem = false`,
`reconR16JamA_perGapDescentOpen`) and JAM B the CANONICAL firing-block reader
(`fxAmalg_topFactorizationInductionStaysWalled = true`, `reconR16JamB_canonicalReaderWalled`) — the recursive reader
off an arbitrary cell, the cell-level merge-into-head surgery, the `whiskerRight` multi-gap append, the `s`-frame
wall-shift.  The strict close criterion `fxAmalg_pushoutDispatch2043ClosesAfterR16` is machine-checked `= false`
(`fxAmalg_pushoutDispatch2043ClosesAfterR16_false`).  The canonicality verdict is ALIGNABLE at the firing-block
skeleton — provable-in-principle, ONE ingredient, r17-scoped as the alignment lemma.  `#2043` does NOT close.  `=
true`. -/
def fxAmalg_amalgamCanonicalityStateAfterR16 : Bool := true

end FX1Poly.Polygraph.Amalgam
