import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools


/-! ## Gates: parity + schema + cong (extracted from AuditAll lines 161-217). -/

-- Raw / typed parity gate.  Every constructor of `RawStep.par` must
-- have a same-suffix constructor in `Step.par`.  Catches the failure
-- mode where a raw cubical β rule lands without its typed mirror.
#assert_raw_typed_parity

-- Schematic-payload budget gates.  These do not claim the current payload
-- surface is ideal; they pin today's explicit `RawTerm` / `Nat` constructor
-- payload debt so future rich-kernel edits cannot grow it silently.
#assert_schematic_payload_budget LeanFX2.Ty 12 1
#assert_schematic_payload_budget LeanFX2.Term 39 0

-- Mode-discipline debt gate.  These are known constructors whose names imply
-- strict/univalent-only availability but whose signatures still quantify over
-- arbitrary `mode`.  The budget pins current debt until the ctor signatures
-- acquire real `mode = ...` premises.
#assert_mode_discipline_budget LeanFX2.Term 0

-- Semantic-signature debt gates.  These do not claim the current signatures
-- are sound; they pin the known fake-typing shapes so new ctors cannot repeat
-- them silently and repaired ctors ratchet the budgets downward.
#assert_dependent_eliminator_motive_budget LeanFX2.Term 9
#assert_unit_placeholder_budget LeanFX2.Term 1
#assert_modal_noop_budget LeanFX2.Term 3
#assert_session_no_advance_budget LeanFX2.Term 2
#assert_equiv_coherence_budget LeanFX2.Term 0

-- Rich schema/linkage debt gates.  These pin raw endpoint/tag laundering and
-- missing cubical/session/effect schema evidence at both Ty and Term layers.
#assert_ty_raw_endpoint_budget LeanFX2.Ty 4
#assert_ty_unstructured_schema_budget LeanFX2.Ty 5
#assert_transport_linkage_budget LeanFX2.Term 1
#assert_glue_schema_budget LeanFX2.Term 2
#assert_effect_schema_budget LeanFX2.Term 0
#assert_session_schema_budget LeanFX2.Term 2
#assert_hcomp_kan_budget LeanFX2.Term 1

-- Exact snapshots for the small, high-risk semantic debt classes above.
-- Count budgets catch growth; these catch one-for-one debt replacement.
#assert_term_semantic_debt_snapshots LeanFX2.Term
#assert_ty_schema_debt_snapshots LeanFX2.Ty

-- Exact rich-to-FX1 bridge constructor coverage.  Fragment bridges remain
-- useful, but only exact `FX1Bridge.encodeTermSound_<ctor>` names count as
-- whole-constructor bridge coverage for this matrix.
#assert_bridge_exact_coverage_budget LeanFX2.Term 62

-- Step.par cong-rule coverage matrix.  Every Term constructor with at
-- least one sub-Term position should have a same-suffix
-- `Step.par.<name>Cong` rule so parallel reduction can enter the
-- ctor.  Value ctors (no sub-Term positions) naturally lack a cong
-- rule; the budget accommodates that as architectural fact.  Tight
-- ratchet: any future Term ctor without a cong rule fails the build.
#assert_step_par_cong_coverage_budget LeanFX2.Term 49

-- Conv cong-rule coverage matrix.  For every Term ctor, either
-- `LeanFX2.Conv.<name>Cong` or `LeanFX2.Conv.<name>_cong` should exist
-- so definitional conversion lifts through the ctor.  Either naming
-- convention accepted; budget pins current debt and rejects growth.
-- Today only one Term ctor has a Conv cong mirror — most Conv lifting
-- happens via `Conv.fromStep` chains rather than per-ctor cong rules.
-- This high debt count is a coverage observation, not a regression.
#assert_conv_cong_coverage_budget LeanFX2.Term 74

end LeanFX2.Tools
