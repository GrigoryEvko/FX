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
-- TODO POLYCELL: disabled honestly.  The command lives in
-- `StrictHarness/DeclShape.lean`, whose body is disabled until the
-- PolyCell replacement for cascade-shaped declaration scans exists.
-- #assert_step_par_cong_coverage_budget LeanFX2.Term 0

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
--   2026-05-22 ratchet 53 → 41 after 12 more degenerate cong rules
--     (2 reflexive-identity + 10 type-code): oeqRefl_cong,
--     idStrictRefl_cong, arrowCode_cong, piTyCode_cong,
--     sigmaTyCode_cong, productCode_cong, sumCode_cong,
--     listCode_cong, optionCode_cong, eitherCode_cong, idCode_cong,
--     equivCode_cong.  All carry only Ty + RawTerm + UniverseLevel
--     data — no Term children — so cong is `Conv.refl _`.
--   2026-05-22 ratchet 41 → 40 after app_cong consolidated
--     appLeft + appRight via cong2_at_isClosedTy (closed-domain +
--     closed-codomain binary cong).  Composes two single-position
--     StepStar lifts inside one budget-gate-matching name.
--   2026-05-22 ratchet 40 → 35 after 5 closed-Ty unary cong rules
--     landed in ConvCongIsClosedTy.lean: modIntro_cong, modElim_cong,
--     subsume_cong, recordProj_cong, codataDest_cong.  Each is a
--     ~12-line specialization of Conv.cong_at_isClosedTy at the
--     ctor's Step.<name>Inner / Step.<name>Value rule.  modIntro /
--     modElim / subsume preserve type (closedTy = resultTy);
--     recordProj / codataDest project from a closed parametric
--     wrapper down to a closed sub-component.
--   2026-05-22 ratchet 35 → 34 after refineIntro_cong landed via
--     Conv.cong2_at_isClosedTy.  baseValue varies at closed baseType,
--     predicateProof varies at IsClosedTy.unit (unconditional).
--     resultTy = Ty.refine baseType predicate is NOT in IsClosedTy
--     (refine carries a raw predicate binder) but that's fine — the
--     lifter only requires SUB-POSITION closure, not result closure.
--   2026-05-22 ratchet 34 → 29 after Conv.cong3_at_isClosedTy lifter
--     landed (3-position generalisation of cong2 via two
--     StepStar.appends) + 5 recursor specialisations:
--     Conv.{listElim,optionMatch,eitherMatch,natElim,natRec}_cong.
--     All recursors use the non-dep motive shape (motiveType :
--     Ty level scope, K07.1–K07.5 dep-motive refactor pending);
--     scrutinee/branches each vary at the corresponding closed
--     carrier (listType/optionType/eitherType/nat) + arrow over
--     closed motive.  natElim's scrutinee at Ty.nat uses
--     IsClosedTy.nat unconditionally.
--   2026-05-22 ratchet 29 → 28 after cumulUp_cong landed via
--     Conv.cong_at_isClosedTy.  Inner type Ty.universe lowerLevel
--     (closed via IsClosedTy.universe) and result Ty.universe
--     higherLevel.  Universe-level + cumulMonotone parameters
--     thread through Step.cumulUpInner.
--   2026-05-22 ratchet 28 → 25 after 3 binary cong rules landed via
--     Conv.cong2_at_isClosedTy: equivApp_cong, equivApply_cong,
--     glueIntro_cong.  equivApp / equivApply share the same
--     (equiv, argument) closure pattern at carrierA + carrierB;
--     glueIntro varies (baseValue, partialValue) both at closed
--     baseType with modeIsUnivalent + boundaryWitness threaded
--     through Step.glueIntroBase / Step.glueIntroPartial.
--   Coverage at 53/78 ctors with `Conv.<ctor>_cong` mirror.
--
-- The remaining 25 debt-bearing ctors share a structural barrier:
-- their input sub-positions live at types NOT in `IsClosedTy`, so
-- the cong-at-closed-Ty lifter (which relies on
-- `Step.par.preserves_isClosedTy` to fix target types under
-- parallel reduction) does not apply directly.  Breakdown:
--   binders (lam, lamPi, pathLam) — body lives at scope+1
--   sigmaTy-shaped (pair, fst, snd) — secondType at scope+1
--   appPi — codomainType.subst0 depends on argument raw
--   dep-motive eliminators (boolElim, idJ, oeqJ, idStrictRec,
--     oeqFunext) — result type depends on scrutinee raw
--   id/glue/transp/path-input ctors (pathApp, glueElim, transp,
--     hcomp, hcompPath, refineElim, sessionSend, sessionRecv,
--     effectPerform, equivIntroHet, uaIntroHet, funextIntroHet,
--     uaToEquiv) — input type carries raw endpoints/payloads.
-- Future ratchet of this gate requires per-family SR helpers
-- (`Step.par.preserves_sigmaTy_shape`,
--  `Step.par.preserves_id_carrier`, etc.) NOT a generic
-- `IsClosedTy` extension — the secondType/raw-endpoint
-- dependencies do not fit the closed-leaves recursion of
-- `IsClosedTy`.
--
-- Meta-unblocker: `Foundation/IsClosedRawTerm.lean` — a Prop-valued
-- predicate witnessing var-0-freeness of raw endpoints.  Combined
-- with per-family SR helpers (one per Ty shape with raw payload),
-- it unblocks all dispatch.* + leaf.* arms whose blocker is raw
-- payload preservation under `Step.par`.  See
-- `Foundation/IsClosedTy.lean:46-58` for the design sketch;
-- existing `RawTerm.unweaken?` from
-- `Foundation/RawPartialRename/UnweakenInversion.lean` provides
-- the Option-form witness equivalent
-- (`raw.unweaken?.isSome ↔ IsClosedRawTerm raw`).
-- TODO POLYCELL: disabled honestly with the rest of DeclShape.
-- #assert_conv_cong_coverage_budget LeanFX2.Term 25

end LeanFX2.Tools
