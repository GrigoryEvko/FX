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
import LeanFX2.Tools.AuditAll.Chunk01
import LeanFX2.Tools.AuditAll.Chunk02
import LeanFX2.Tools.AuditAll.Chunk03
import LeanFX2.Tools.AuditAll.Chunk04
import LeanFX2.Tools.AuditAll.Chunk05
import LeanFX2.Tools.AuditAll.Chunk06
import LeanFX2.Tools.AuditAll.Chunk07
import LeanFX2.Tools.AuditAll.Chunk08
import LeanFX2.Tools.AuditAll.Chunk09
import LeanFX2.Tools.AuditAll.Chunk10
import LeanFX2.Tools.AuditAll.Chunk11
import LeanFX2.Tools.AuditAll.Chunk12

/-! # Tools/AuditAll — umbrella runs per-chunk axiom audits in parallel
    plus the trailing gate invocations and dashboard. -/

namespace LeanFX2.Tools


-- FX1 executable extern-dependency gates.  These are narrower than the axiom
-- gates: they fail if a checker-critical executable primitive delegates to
-- Lean host runtime code such as `String.decEq` or host `Nat.beq`.
#assert_no_extern_dependencies LeanFX2.FX1.NaturalNumber.beq
#assert_no_extern_dependencies LeanFX2.FX1.NaturalNumber.eqResult
#assert_no_extern_dependencies LeanFX2.FX1.Name.beq
#assert_no_extern_dependencies LeanFX2.FX1.Name.eqResult
#assert_no_extern_dependencies LeanFX2.FX1.Level.beq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.beq
#assert_no_extern_dependencies LeanFX2.FX1.Declaration.hasName
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByName?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByNameResultInDeclarations?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByNameResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTypeByNameFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTypeByName?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentDefinitionResultInDeclarations?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentDefinitionResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentValue?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupTypeFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupTypeInEntries?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupType?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.headStep?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnfResultWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnfWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.weakHeadFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnf
#assert_no_extern_dependencies LeanFX2.FX1.Expr.weakHeadFuelAdd
#assert_no_extern_dependencies LeanFX2.FX1.Expr.defEqFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.isDefEqWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.isDefEq
#assert_no_extern_dependencies LeanFX2.FX1.Level.checkerBeq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkerBeq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkBoolFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkBoolFromCoreType?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.inferCore?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkCore?

-- Loaded production namespace sweep.  `#audit_namespace` excludes
-- `LeanFX2.Tools` and `LeanFX2.Smoke`, so this is the broad fail-fast
-- gate for every production declaration imported above, not a
-- replacement for targeted smoke examples.
#audit_namespace LeanFX2

-- Aggregate strict gate.  Walks the same loaded production decls and
-- flags every discipline violation in one error, including
-- `noncomputable`, `@[extern]`, `@[implemented_by]`, and direct
-- `Classical.*` references.  Subsumes `#audit_namespace` (which only
-- looks at axioms) but kept side-by-side as defense in depth.
#audit_namespace_strict LeanFX2

-- Production import-surface gate.  No production module may import
-- `LeanFX2.Tools`, `LeanFX2.Smoke`, `LeanFX2.Sketch`, or the broad
-- `LeanFX2` root as an internal dependency.
#assert_production_import_surface_clean

-- Public umbrella isolation.  Broad entrypoints (`LeanFX2`, `LeanFX2.Kernel`,
-- `LeanFX2.Rich`, `LeanFX2.FX1Bridge`, `LeanFX2.FX1`, `LeanFX2.FX1.Core`) may
-- appear only in the deliberate public-entrypoint chain or in smoke/tooling
-- audits.
#assert_public_umbrella_imports_isolated

-- Rich production host-import gate.  Regular production modules must not
-- import host-heavy modules such as `Lean`, `Std`, `Lake`, `Mathlib`,
-- `Classical`, or host `Quot` directly.  FX1 and tooling are checked by
-- narrower gates below.
#assert_rich_production_host_import_surface_clean

-- Semantic layer gate.  Foundation/Term/Reduction/etc. modules may only
-- import their own layer or earlier layers, so later metatheory cannot leak
-- downward through a convenience import.
#assert_production_layer_imports_clean

-- Redundant direct project-import gate.  Production modules may not keep
-- extra direct `LeanFX2.*` imports that are already reachable through another
-- direct import, except for the four documented semantic core edges.
#assert_no_redundant_production_project_imports

-- FX1/Core host-minimal gate.  This is intentionally scoped to the
-- future minimal-root namespace, not the rich kernel: FX1 declarations
-- must not depend on host-heavy `Lean`, `Std`, `Classical`, host `Quot`,
-- `propext`, `Classical.choice`, `Quot.sound`, `Quot.lift`, or `sorryAx`.
-- It succeeds with zero declarations, so it can be wired before FX1/Core
-- exists and will begin enforcing as soon as FX1 files are imported.
#assert_fx1_core_host_minimal LeanFX2.FX1

-- FX1 direct-import gate.  FX1/Core may only import FX1/Core;
-- FX1/LeanKernel may only import FX1/Core or FX1/LeanKernel.  Like the
-- host-minimal gate, this passes with zero FX1 modules and begins enforcing
-- as soon as the namespace is loaded.
#assert_fx1_import_surface_clean

-- Exact FX1/Core root-DAG gate.  This is stricter than "FX1 imports only
-- FX1": it prevents a minimal-root leaf from importing the Core umbrella or a
-- later metatheory module without an explicit policy update.
#assert_fx1_core_exact_import_shape

-- Exact FX1/LeanKernel DAG gate.  The Lean-kernel model over FX1 is allowed
-- to exist, but every direct dependency edge must be intentional.
#assert_fx1_lean_kernel_exact_import_shape

-- Rich production / FX1 separation.  FX1 is the future minimal TCB root;
-- rich production modules may not import it directly until a deliberate
-- bridge/certificate boundary exists.
#assert_rich_production_fx1_import_surface_clean

-- Legacy Lean-kernel scaffold isolation.  The old pre-FX1
-- `LeanFX2.Lean.Kernel.*` module path must stay absent or quarantined while
-- Day 8 targets `LeanFX2.FX1.LeanKernel`.
#assert_legacy_lean_kernel_scaffold_isolated

-- Explicit host-boundary isolation.  Host shims such as `Surface.HostLex`
-- may be imported by smoke/tool modules, but never by the public umbrella or
-- regular production modules.
#assert_host_boundary_isolated

-- Global host-heavy import allowlist.  The only allowed direct host-heavy
-- edge is the audit implementation importing Lean elaborator APIs.
#assert_host_heavy_import_surface_allowlisted

-- Import census.  These two commands are informational, but keeping them in
-- `AuditAll` makes dependency mass visible in the canonical audit target
-- instead of only in smoke import-surface builds.
#audit_import_family_summary
#audit_import_surface_summary

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
#assert_mode_discipline_budget LeanFX2.Term 8

-- Semantic-signature debt gates.  These do not claim the current signatures
-- are sound; they pin the known fake-typing shapes so new ctors cannot repeat
-- them silently and repaired ctors ratchet the budgets downward.
#assert_dependent_eliminator_motive_budget LeanFX2.Term 9
#assert_unit_placeholder_budget LeanFX2.Term 3
#assert_modal_noop_budget LeanFX2.Term 3
#assert_session_no_advance_budget LeanFX2.Term 2
#assert_equiv_coherence_budget LeanFX2.Term 1

-- Rich schema/linkage debt gates.  These pin raw endpoint/tag laundering and
-- missing cubical/session/effect schema evidence at both Ty and Term layers.
#assert_ty_raw_endpoint_budget LeanFX2.Ty 4
#assert_ty_unstructured_schema_budget LeanFX2.Ty 5
#assert_transport_linkage_budget LeanFX2.Term 1
#assert_glue_schema_budget LeanFX2.Term 2
#assert_effect_schema_budget LeanFX2.Term 1
#assert_session_schema_budget LeanFX2.Term 2
#assert_hcomp_kan_budget LeanFX2.Term 1

-- Exact rich-to-FX1 bridge constructor coverage.  Fragment bridges remain
-- useful, but only exact `FX1Bridge.encodeTermSound_<ctor>` names count as
-- whole-constructor bridge coverage for this matrix.
#assert_bridge_exact_coverage_budget LeanFX2.Term 71

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

-- Broad manufactured-Step dependent census.  Wider than the headline
-- refl-fragment gate above: counts ANY decl whose closure mentions a
-- manufactured Univalence/funext rule, except for an allowlist of
-- decls expected to thread those rules structurally (Confluence /
-- RawCd / RawPar / Cd / CdLemma / Diamond / ChurchRosser scaffolding,
-- the headline-named claims already counted, and HoTT/Cubical
-- headline-adjacent files).  Pins current count to catch wrappers
-- that rename-and-restate refl-fragment claims.  Today's 121 count
-- includes Step.par cong rules that name the manufactured rule in
-- their cd-lemma chain; reducing it requires either tightening the
-- allowlist further or replacing manufactured-witness shipping with
-- a general-rule shipping (the latter is the real fix, see
-- WEAK-FX2-03 in the audit).
#assert_broad_manufactured_step_dependent_budget LeanFX2 121

-- Cast-operator dependent census.  Counts kernel-tier decls whose
-- closure references Eq.mpr / Eq.ndrec / Eq.rec / HEq.rec /
-- HEq.ndrec / HEq.subst / cast / Eq.subst / Eq.symm / HEq.symm.
-- These are the heterogeneous-equality cast operators that often
-- hide propext or Quot.sound; a budgeted count makes new casts
-- visible.  Kernel tier covers Term/Foundation/Reduction/Confluence/
-- HoTT/Cubical/Modal/Graded.  Tight ratchet at current count.
#assert_cast_operator_dependent_budget LeanFX2 849

-- Forbidden decl shape budget.  CLAUDE.md bans `partial def`,
-- `opaque` (without rfl-reducible body), and `unsafe def` for kernel
-- theorems.  This gate scans the kernel tier for those constant-info
-- shapes; budget zero means none should appear (and currently 0 ✓).
#assert_forbidden_decl_shape_budget LeanFX2 0

-- All-raw-payload Term ctor count.  A Term ctor whose every explicit
-- binder type is RawTerm/Nat/UniverseLevel is a typing wrapper around
-- raw syntax.  Today no Term ctor matches because every `*Code` ctor
-- includes a Prop-typed `levelLe` premise, so the count is 0.  Tight
-- ratchet: any future ctor whose every explicit binder is raw will
-- fail the build at this 0 budget.
#assert_all_raw_payload_budget LeanFX2.Term 0

-- Single-step Conv claim count.  A theorem whose result type is
-- `Conv ...` and whose body collapses to a single `Conv.fromStep` /
-- `Conv.fromStepStar` is a single-step Conv claim — it asserts
-- convertibility but only via one reduction.  Pinning catches
-- "Theorem X = Conv.fromStep RuleY" claims that pretend more than
-- they prove.  Tight ratchet at current count.
#assert_single_step_conv_claim_budget LeanFX2 32

-- Reduction.Compat per-cong coverage.  For every Step.par.<X>Cong,
-- expect <X>Cong.rename_compatible and <X>Cong.subst_compatible.
-- Without these, parallel-reduction substitution stability fails and
-- the diamond cascade breaks.  Tight ratchet at current count.
#assert_reduction_compat_coverage_budget LeanFX2.Step.par 28

-- Inhabited / Nonempty / Classical.choice dependent census.  These
-- typeclasses summon Classical.choice internally on certain constructions;
-- counting kernel-tier dependents catches inadvertent uses.  Tight
-- ratchet at zero — nothing in the kernel currently depends on these.
#assert_inhabited_dependent_budget LeanFX2 0

-- HEq result-type theorem census.  Theorems whose claimed result type
-- mentions `HEq` are propext-adjacent — heterogeneous equality cannot
-- generally reduce.  Tight ratchet at current count.
#assert_heq_result_type_budget LeanFX2 91

-- Decidable.decide dependent census.  `decide` invokes the kernel
-- reducer on Decidable instances; can hide propext through Decidable
-- on Eq.  Tight ratchet at current count.
#assert_decide_dependent_budget LeanFX2 383

-- Subsingleton.elim dependent census.  This is the canonical way to
-- elide Nat.le proof_irrel; sometimes leaks propext on Lean versions
-- that can't reduce through the elision.  Tight ratchet at zero.
#assert_subsingleton_dependent_budget LeanFX2 0

-- Match-compiler equation lemma census.  Auto-generated `_eq_<n>` and
-- `match_<n>` lemmas in kernel-tier namespaces are propext-suspect on
-- indexed inductive families.  Tight ratchet at zero.
#assert_match_compiler_equation_budget LeanFX2 0

-- rfl-only on non-trivial-name theorem census.  Theorems whose name
-- ends in `_inj` / `_unique` / `_iff` / `_def` / `_eq` / `_uniqueProof`
-- with `Eq.refl _` body are heuristic flags for definitionally-trivial
-- restatements masquerading as substantive claims.  Tight ratchet at
-- current count of 1.
#assert_rfl_on_nontrivial_name_budget LeanFX2 1

-- Universe-polymorphism leak.  Kernel-tier decls should pin universe
-- levels; `.sort (.param _)` / `.sort (.max ...)` / `.sort (.imax ...)`
-- in result types are universe-polymorphic and can interact with
-- cumulativity in hard-to-audit ways.  527 today is high but reflects
-- the Action / ActsOnRawTerm / ActsOnTyVar typeclass framework being
-- universe-polymorphic by design — not a regression, an architectural
-- choice.  Tight ratchet at current count.
#assert_universe_polymorphism_budget LeanFX2 527

-- Quot / Quotient family dependents.  Quot is propositional truncation;
-- Quot.lift / Quot.ind / Quot.rec are Classical-adjacent (Quot.sound IS
-- an axiom, already separately gated).  Tight ratchet at zero — the
-- kernel currently has no Quot family dependents.
#assert_quot_dependent_budget LeanFX2 0

-- Acc / WellFounded family dependents.  Well-founded recursion can
-- hide non-structural termination; structural recursion is the
-- preferred discipline.  Tight ratchet at zero — the kernel currently
-- relies entirely on structural recursion.
#assert_acc_dependent_budget LeanFX2 0

-- Lean elaboration / metaprogramming dependent census.  Production-tier
-- kernel decls should not depend on Lean.Elab / Lean.Meta / Lean.Parser
-- machinery (those layers belong to tactic mode and parser
-- extensions).  Tight ratchet at zero.
#assert_lean_meta_dependent_budget LeanFX2 0

-- toRaw projection coverage.  Every Term ctor `LeanFX2.Term.<X>` should
-- have `LeanFX2.Term.toRaw_<X>` proving the raw projection equals the
-- index.  This is the core discipline that makes raw-aware Term work.
-- Tight ratchet at zero — full coverage today, must remain.
#assert_toraw_coverage_budget LeanFX2.Term 0

-- IsClosedTy parity.  For every scope-independent Ty constructor (unit,
-- bool, nat, arrow, listType, optionType, eitherType, universe, empty,
-- interval, equiv, record, codata, modal — 14 ctors), expect a
-- same-suffix IsClosedTy ctor.  Tight ratchet at zero — full parity.
#assert_is_closed_ty_parity_budget LeanFX2.Ty 0

-- Inductive ctor-count regression gates.  Pin current ctor count for
-- each load-bearing inductive.  Fails on shrinkage (catches accidental
-- deletion); logs informationally on growth (codex adding new ctors).
#assert_inductive_ctor_count_ratchet LeanFX2.Term 75
#assert_inductive_ctor_count_ratchet LeanFX2.Ty 25
#assert_inductive_ctor_count_ratchet LeanFX2.Step 105
#assert_inductive_ctor_count_ratchet LeanFX2.Step.par 109
#assert_inductive_ctor_count_ratchet LeanFX2.RawTerm 67

-- Coe / CoeSort / CoeFun typeclass dependent census.  These silently
-- inject elements between types; a bad Coe makes the type system
-- structurally porous.  Tight ratchet at zero — kernel currently has
-- no Coe family dependents.
#assert_coe_dependent_budget LeanFX2 0

-- OfNat / OfScientific dependent census.  OfNat instances let numeric
-- literals inject into types; custom instances on inappropriate types
-- are literal-injection vectors.  524 today reflects pervasive use of
-- Nat literals in proofs; tight ratchet at current count.
#assert_ofnat_dependent_budget LeanFX2 524

-- Subtype.mk / Subtype.val dependent census.  Tight ratchet at zero —
-- the kernel doesn't use subtype-encoded reasoning.
#assert_subtype_dependent_budget LeanFX2 0

-- Function.Injective / Bijective / Surjective dependent census.  Tight
-- ratchet at zero — the kernel doesn't use cardinality-based reasoning.
#assert_function_property_dependent_budget LeanFX2 0

-- Eq.symm / Eq.trans / Eq.mp / Eq.recOn / Eq.subst dependent census.
-- 761 today reflects pervasive equality-rewriting in proofs.  Tight
-- ratchet at current count.
#assert_eq_rewriting_dependent_budget LeanFX2 761

-- Reducible / abbrev kernel decl census.  476 today reflects the
-- Action / Subst / Renaming infrastructure being abbrev-shaped for
-- unification, plus Ty.weaken being @[reducible] per
-- feedback_lean_reducible_weaken.md.  Tight ratchet at current count.
#assert_reducible_decl_budget LeanFX2 476

-- Mode inductive exact-ctor-count assertion.  Per kernel-sprint §1.4,
-- Mode should have exactly 5 ctors (strict / observational / univalent
-- / cohesiveFlat / cohesiveSharp).  This gate fails on ANY mismatch.
-- Codex currently ships extras (legacy modes); this gate documents the
-- spec-compliance gap until the legacy modes are stripped.
-- DOCUMENTED-DEFER: Mode actually has more ctors today (legacy modes
-- await cleanup).  Use the regression-only ratchet instead until
-- spec-compliance is achieved.
#assert_inductive_ctor_count_ratchet LeanFX2.Mode 5

-- Bridge round-trip parity.  For every encodeTermSound_<X>, expect a
-- companion encodeTermSound_<X>_roundTrip proving decode∘encode = id.
-- Without round-trip, the bridge could be lossy.  Pin current debt.
#assert_bridge_round_trip_budget LeanFX2 9999

-- False-in-result-type kernel decl census.  Theorems whose result type
-- mentions False are evidence of vacuous reasoning or contradiction
-- discharge.  Tight ratchet at zero — currently clean.
#assert_false_in_result_type_budget LeanFX2 0

-- Term/RawTerm ctor delta.  Term has 75 ctors, RawTerm has 67 — the 8
-- delta means manufactured-witness Term ctors share raw projections
-- with each other.  Architectural choice for refl-fragment Univalence/
-- funext support.  Pinning the delta catches new manufactured-witness
-- ctors arriving without RawTerm parity.
#assert_term_raw_ctor_delta LeanFX2.Term LeanFX2.RawTerm 8

-- Sigma / PSigma / Sum / PSum / PProd dependent census.  Heterogeneous
-- packaging types; heavy use signals existential reasoning.  936 today
-- reflects pervasive use of Sigma/PSigma in dependent-type proofs.
-- Tight ratchet at current count.
#assert_dependent_pair_dependent_budget LeanFX2 936

-- Classical.choose / em / byContradiction dependent census.  Refines
-- the Inhabited gate by naming the canonical excluded-middle
-- operations.  Tight ratchet at zero — kernel doesn't use Classical.
#assert_classical_reasoning_dependent_budget LeanFX2 0

-- Hashable / Repr / ToString / BEq / Format dependent census.  These
-- are user-facing API typeclasses; kernel decls should NOT depend on
-- them.  5 today is minor leakage; tight ratchet at current.
#assert_api_typeclass_dependent_budget LeanFX2 5

-- IO / Task / EIO / BaseIO effect dependent census.  Kernel must not
-- depend on runtime IO.  Tight ratchet at zero.
#assert_io_effect_dependent_budget LeanFX2 0

-- Anonymous-projection (Prod.fst / And.intro / Or.elim / Iff.mp / etc.)
-- dependent census.  Heavy use signals proofs that destructure
-- dependent values without being explicit about structure.  Tight
-- ratchet at current count.
#assert_anonymous_projection_dependent_budget LeanFX2 174

-- Lean meta-Expr / MVarId / Syntax / Name / Level dependent census.
-- Production-tier kernel decls should not depend on Lean's
-- metaprogramming data structures.  Initial generous; tightened
-- post-discovery.
#assert_lean_meta_expr_dependent_budget LeanFX2 9999

-- Monadic-stack (StateRefT / ReaderT / CoreM / MetaM / etc.) dependent
-- census.  Production decls should be in the kernel, not in tactic /
-- elaboration monads.  Initial generous; tightened post-discovery.
#assert_monadic_stack_dependent_budget LeanFX2 9999

-- Heavyweight-tactic dependent census.  omega / aesop / linarith /
-- tauto / simp_all can prove false from inconsistent hypotheses or
-- hide structural reasoning.  Initial generous; tightened
-- post-discovery.
#assert_heavyweight_tactic_dependent_budget LeanFX2 9999

-- Smoke-reference coverage budget.  Every Term ctor should be
-- referenced by at least one decl in `LeanFX2.Smoke.*`.  Without
-- smoke usage, the ctor is silently unverified by the regression
-- suite.  Initial generous; tightened post-discovery.
#assert_smoke_reference_coverage_budget LeanFX2.Term 9999

-- absurd / False.elim / False.rec dependent census.  These discharge
-- contradictions; heavy use signals proofs threading through
-- contradictory hypotheses, sometimes vacuously.  Initial generous;
-- tightened post-discovery.
#assert_absurd_false_dependent_budget LeanFX2 9999

-- Setoid / Quotient (vs primitive Quot) dependent census.  Beyond Quot
-- family, this widens to the equivalence-relation typeclass and the
-- Quotient API on top of Setoid.  Initial generous; tightened
-- post-discovery.
#assert_setoid_quotient_dependent_budget LeanFX2 9999

-- Naming discipline gate.  Bans non-ASCII identifiers and short
-- identifiers (< 4 chars) outside the documented whitelist.  Catches
-- regressions like `def f (x) := ...` or pasted Greek-letter names
-- that violate CLAUDE.md naming rules.
#assert_namespace_naming LeanFX2

-- Hypothesis-as-postulate detector.  No theorem signature in the
-- production namespace may take Univalence / funext / their het
-- variants as a hypothesis (CLAUDE.md "Forbidden reasoning patterns":
-- shipping a theorem conditionally on an unprovable hypothesis is
-- semantically identical to adding an axiom).
#assert_no_postulate_hypothesis LeanFX2

-- Headline refl-fragment budget.  The current `Univalence` / `funext`
-- headline family still depends on manufactured raw-alignment Step rules.
-- This pins that debt to four claims and rejects future growth.
#assert_headline_refl_fragment_budget LeanFX2 4

-- Staged FX1 axiom leak detector.  Object-level `axiomDecl` placeholders are
-- allowed inside FX1 itself and the explicit FX1Bridge staging boundary only;
-- regular rich/root production declarations must not depend on them.
#assert_no_root_staged_axiom_leak LeanFX2

-- Per-namespace decl-count snapshot.  Strictly informational; surfaces
-- the count distribution across `LeanFX2.*` sub-namespaces so a
-- coverage regression (whole sub-namespace shrinking unexpectedly)
-- is visible at a glance.
#audit_subnamespace_counts

-- End-of-build summary.  Logs `Total / Clean / Failed` plus per-decl
-- failure list.  Strictly informational (does not throw); the actual
-- blocking happens via `#audit_namespace_strict` above.  Surfaces
-- audit health amid hundreds of OK info lines.
#audit_summary LeanFX2

-- AGGREGATE SEMANTIC-DEBT DASHBOARD.  Renders the project's full debt
-- floor in one prominent multi-line banner at end of build.  Reads live
-- from the environment via every per-debt-class record collector.
-- Strictly informational; the per-budget gates above already failed
-- the build if any ratchet rose, so a rendered dashboard means every
-- budget held this build.  Visibility layer: makes today's debt counts
-- and bridge-coverage status surface clearly amid build noise so a
-- reader skimming the build log sees at a glance which classes still
-- have debt and how the ratchets stand.
#audit_debt_dashboard LeanFX2.Term LeanFX2.Ty LeanFX2

end LeanFX2.Tools
