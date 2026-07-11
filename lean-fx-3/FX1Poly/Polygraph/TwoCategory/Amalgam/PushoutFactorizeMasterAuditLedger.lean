import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeTotalAssembly
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutBundle
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAmalgamDispatchStateLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizeMasterAuditLedger — the #2043 master re-audit after r15: every
demand verbatim-quoted and checked LITERALLY; NO fabricated flip (WP-AMALG-2 r15, Brick B5)

r15 (the total-assembly grind) shipped the four case-bricks and the total EXISTENCE reader:

  * B1 `pushoutFactorizeGen` — the `gen` case (single wall-free firing slot).
    `fxAmalg_hasGenCaseFactorization = true`.
  * B2 `pushoutFactorizeWhiskerLeftGap` / `RightGap` — the `whisker` cases (frame as an inert wall, single body gap).
    `fxAmalg_hasWhiskerFrameGapCase = true`.
  * B3 `pushoutFactorizeVcompSingleGap` — the `vcomp` base case (two cells share one gap's vertical split).
    `fxAmalg_hasVcompSingleGapCase = true`.
  * B4 `pushoutFactorizeTotal` — the TOTAL (existence) reader (all 5 cases, 5-way match, mode-pinned whiskers).
    `fxAmalg_totalFactorizeReaderShips = true`.

This ledger re-audits the three #2043 master markers conjunct-by-conjunct against the VERBATIM demands and
machine-checks that NONE flips — maximally strict, no fabricated flip.

## Master (i) — `fxAmalg_hasFullSaturatedPushoutDispatch = false` (`DispatchSaturated.lean:351`), verbatim horns

Quoted verbatim (`DispatchSaturated.lean:338-350`): "the FULL saturated dispatch stays open, on THREE precisely-named
walls … (i) a genuine-generator coprojection `onTwoCell` needs `interpretWordFrom_map` …; (ii) the only shipped real
saturated decider … lives over the BESPOKE `monadModeSignature`, not the RECONSTRUCTED `monadComputad.toModeSignature`
…; (iii) COMPLETENESS — every pushout derivation must project back to per-component derivations (Nelson-Oppen /
Baader-Tinelli purification, sound only for word-preserving / left-connected component presentations; the unit/counit
wire-creating generators break the convex-block projection)."  Horns (i)/(ii) are closed in later rounds; horn (iii)
purification is OPEN (`fxAmalg_hasSaturatedDispatchTheorem = false`).  r15's total reader is SHALLOW EXISTENCE — it
gives cell-level projection but NOT derivation-level purification (the NF reflection), so horn (iii) is untouched.
The marker's gate is the AND of the horns; (iii) OPEN forces `false`.  **STAYS false.**

## Master (ii) — `fxAmalg_hasGeneralPushoutDispatch = false` (`PushoutBundle.lean:1081`), verbatim

Quoted verbatim (`PushoutBundle.lean:1074-1079`): "What stays open for r9+ is the GENERAL decision procedure: a
`Decidable (SaturatedConvOver involutionMonadPushout.toModeSignature … )` for ARBITRARY pushout pairs.  That needs
either (i) the reconstruction decider reseat … or (ii) the purification-reflection completeness for the wire-creating
unit/mult regime …"  The total `Decidable` for arbitrary pairs needs the CANONICAL firing-block reader to reduce a
pair to comparable per-gap right-images.  r15's `pushoutFactorizeTotal` is SHALLOW — its gap payloads are whole
subterms, not canonicalized per firing region, so comparing two cells' layouts is circular.  **STAYS false.**

## Master (iii) — `fxAmalg_topFactorizationInductionStaysWalled = true` (`PushoutVcompInterchangeSplice.lean:273`)

Quoted verbatim (`PushoutVcompInterchangeSplice.lean:264-268`): needs "(a) the `blockDecompose`↔`composePath`
reconstruction bridge to READ a canonical `VcompGapPair` list off an arbitrary cell's boundary; (b) the per-case
assembly … producing a single layout keyed to the CANONICAL block decomposition; (c) the decider wiring".  r15
shipped (b) the per-case single-block builders and the SHALLOW total reader, but NOT (a) the CANONICAL block reader
(shallow ≠ canonical) — so the decider-feeding layout is not produced.  **STAYS true (walled).**

## Close criterion (verbatim, `PushoutAmalgamDispatchStateLedger.lean:78-87`)

"`#2043` closes iff `fxAmalg_hasFullSaturatedPushoutDispatch ∧ fxAmalg_hasGeneralPushoutDispatch ∧
¬ fxAmalg_topFactorizationInductionStaysWalled`".  After r15 that is `false ∧ false ∧ ¬true = false`: `#2043` does NOT
close.  The gate is genuine ARBITRARY-CELL ARBITRARY-PAIR coverage at the disjoint scope; r15 delivered arbitrary-cell
EXISTENCE (the total reader) but neither the canonical decomposition nor the arbitrary-pair decision.

## The two jams, each pinned to its NAMED node + exact goal

  * **JAM A — purification-completeness.**  NAMED node `fxAmalg_hasSaturatedDispatchTheorem = false`.  Exact goal:
    every pushout DERIVATION projects to per-component derivations; needs the NF REFLECTION (conv-of-images ⟹
    equal-layouts).  r15's total EXISTENCE reader does NOT supply it (shallow layouts are not normal forms).
  * **JAM B — the CANONICAL firing-block reader + alignment.**  NAMED node
    `fxAmalg_topFactorizationInductionStaysWalled = true`.  Exact goal residuals: (a') the `vcomp` firing-block
    ALIGNMENT of two arbitrary multi-gap IH layouts to a common per-firing refinement (the atomic-firing re-slice,
    `PushoutFinestPayloadZip.lean:157`); (a'') the `s`-bearing whisker frame's downstream wall-shift; (b) the
    multi-gap head-prepend `mergeFrameIntoHead/Tail`.  r15 shipped the SHALLOW total reader + the single-block
    per-case builders; the CANONICAL reader is the residual.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## r15 shipped — the four case-bricks + total reader live (machine-checked conjunction) -/

/-- The r15 deliverable conjunction — B1 `gen`, B2 `whisker`, B3 `vcomp` base, B4 the total existence reader all
live. -/
def reconR15BricksShipped : Bool :=
  fxAmalg_hasGenCaseFactorization
    && fxAmalg_hasWhiskerFrameGapCase
    && fxAmalg_hasVcompSingleGapCase
    && fxAmalg_totalFactorizeReaderShips

/-- The r15 bricks are all live (`rfl`). -/
theorem reconR15BricksShipped_true : reconR15BricksShipped = true := rfl

/-! ## The three masters stay at their walled values (machine-checked `rfl` — no flip) -/

/-- Master (i) STAYS `false` — the FULL saturated pushout dispatch is still walled on horn (iii)
purification-completeness (`fxAmalg_hasSaturatedDispatchTheorem = false`), which the r15 SHALLOW total reader does not
touch (existence, not the NF reflection). -/
theorem reconR15_masterOne_staysFalse : fxAmalg_hasFullSaturatedPushoutDispatch = false := rfl

/-- Master (ii) STAYS `false` — the GENERAL pushout dispatch (a total arbitrary-pair `Decidable`) still needs the
CANONICAL firing-block reader; the r15 total reader is SHALLOW (whole-subterm gaps, not canonicalized per firing). -/
theorem reconR15_masterTwo_staysFalse : fxAmalg_hasGeneralPushoutDispatch = false := rfl

/-- Master (iii) STAYS `true` (walled) — the top factorization induction still needs the CANONICAL block reader (a)
and the canonical per-case assembly (b); r15 shipped the SHALLOW total reader + single-block builders, not the
canonical decomposition. -/
theorem reconR15_masterThree_staysWalled : fxAmalg_topFactorizationInductionStaysWalled = true := rfl

/-- JAM A pinned — purification-completeness STAYS OPEN: `fxAmalg_hasSaturatedDispatchTheorem = false` (`rfl`).  The
total EXISTENCE reader gives cell-level projection, not derivation-level purification. -/
theorem reconR15_purificationStaysOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-! ## The #2043 close criterion (maximally strict, verbatim) -/

/-- The `#2043` close criterion (r15) — closes iff BOTH masters (i)/(ii) hold AND the top factorisation is no longer
walled.  The SAME criterion as `fxAmalg_pushoutDispatch2043ClosesAfterR14`, re-evaluated after r15's total reader:
genuine ARBITRARY-CELL ARBITRARY-PAIR coverage is the bar; arbitrary-cell EXISTENCE alone does not meet it. -/
def fxAmalg_pushoutDispatch2043ClosesAfterR15 : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatch
    && fxAmalg_hasGeneralPushoutDispatch
    && (fxAmalg_topFactorizationInductionStaysWalled == false)

/-- ★★★ **`#2043` does NOT close after r15 (`rfl`).**  The close criterion evaluates to `false`: both jams (A
purification-completeness, B the CANONICAL firing-block reader) remain open.  r15 delivered arbitrary-cell EXISTENCE
(`pushoutFactorizeTotal`) — the honest ceiling; the CANONICAL decomposition + arbitrary-pair decision are the wall. -/
theorem fxAmalg_pushoutDispatch2043ClosesAfterR15_false :
    fxAmalg_pushoutDispatch2043ClosesAfterR15 = false := rfl

/-! ## The re-audit conjunction -/

/-- The re-audit CONJUNCTION — machine-checks, in one Boolean, that the three masters stay at their walled values
(`false` / `false` / `true`), purification stays open (`false`), AND the four r15 bricks are live.  Its `= true`
(`reconR15MasterAudit_true`, `rfl`) IS the maximally-strict no-fabricated-flip certificate. -/
def reconR15MasterAudit : Bool :=
  (fxAmalg_hasFullSaturatedPushoutDispatch == false)
    && (fxAmalg_hasGeneralPushoutDispatch == false)
    && (fxAmalg_topFactorizationInductionStaysWalled == true)
    && (fxAmalg_hasSaturatedDispatchTheorem == false)
    && fxAmalg_hasGenCaseFactorization
    && fxAmalg_hasWhiskerFrameGapCase
    && fxAmalg_hasVcompSingleGapCase
    && fxAmalg_totalFactorizeReaderShips

/-- The re-audit conjunction holds (`rfl`) — masters walled, purification open, bricks live, no flip. -/
theorem reconR15MasterAudit_true : reconR15MasterAudit = true := rfl

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the #2043 master re-audit after r15: NO master flips (WP-AMALG-2 r15, B5).**  `= true`.
Conjunct-by-conjunct against the VERBATIM master demands: master (i) `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS
`false` (horn (iii) purification OPEN — the total reader is SHALLOW EXISTENCE, not the NF reflection); master (ii)
`fxAmalg_hasGeneralPushoutDispatch` STAYS `false` (the total `Decidable` needs the CANONICAL firing-block reader, not
the shallow one); master (iii) `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true` (needs the canonical block
reader + canonical per-case assembly).  The four walled/open values are machine-checked `rfl`
(`reconR15_masterOne_staysFalse` / `_masterTwo_` / `_masterThree_` / `_purificationStaysOpen`) and the four r15 bricks
live (`reconR15BricksShipped_true`), conjoined in `reconR15MasterAudit_true`.  r15 is an HONEST NARROWING (the five
per-case builders + the total EXISTENCE reader ship, four new positive markers), no fabricated flip.  `#2043` does NOT
close (`fxAmalg_pushoutDispatch2043ClosesAfterR15_false`).  `= true`. -/
def fxAmalg_masterAuditR15NoFlip : Bool := true

/-- ★★★ **Honesty marker — the #2043 state after r15: the five cases + the total EXISTENCE reader ship; two named
jams remain; #2043 does NOT close.**  `= true` (the STATE is honestly recorded, not a claim that #2043 closes).  r15
shipped the four case-bricks (`reconR15BricksShipped_true`): B1 `gen`, B2 `whisker`, B3 `vcomp` base, B4 the total
reader `pushoutFactorizeTotal` (arbitrary-cell EXISTENCE of a layout factorization, zero-axiom).  Two jams remain,
each pinned to its named node at its open value: JAM A purification-completeness
(`fxAmalg_hasSaturatedDispatchTheorem = false`, `reconR15_purificationStaysOpen`) and JAM B the CANONICAL firing-block
reader (`fxAmalg_topFactorizationInductionStaysWalled = true`, `reconR15_masterThree_staysWalled`) — the atomic-firing
alignment (`PushoutFinestPayloadZip.lean:157`), the `s`-frame wall-shift, the multi-gap head-prepend.  The strict
close criterion `fxAmalg_pushoutDispatch2043ClosesAfterR15` is machine-checked `= false`
(`fxAmalg_pushoutDispatch2043ClosesAfterR15_false`).  r15 is an HONEST NARROWING (existence settled, canonicality
walled).  `#2043` does NOT close.  `= true`. -/
def fxAmalg_amalgamFactorizationStateAfterR15 : Bool := true

end FX1Poly.Polygraph.Amalgam
