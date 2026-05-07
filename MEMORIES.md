# MEMORIES.md - Codex Digest Of Claude FX Memories

This document summarizes Claude memory files for `/root/iprit/FX` into a Codex-facing operational digest.
It was created at the user request and should be maintained as a local bridge artifact, not as generated Codex memory state.

## Purpose And Authority
- This file is a Codex-facing digest of Claude FX memories requested by the user.
- It is intentionally stored in the repo root as MEMORIES.md for local visibility.
- It summarizes /root/.claude/projects/-root-iprit-FX/memory/*.md.
- It does not mutate ~/.claude and does not mutate ~/.codex generated memories.
- It is not a replacement for current source, AGENTS.md, CLAUDE.md, AXIOMS.md, or user instruction.
- When this document conflicts with the current user, obey the current user.
- When this document conflicts with current repo files, inspect and reason from current repo files.
- When this document contains completion claims, treat them as historical snapshots.
- Before relying on any snapshot, re-run the relevant build, smoke file, or source inspection.
- The most important import is behavioral: use Claude memory as context, not as unquestioned law.

## High Priority Import
- Do not import the stale mandatory full-root-spec preflight rule for lean-fx and lean-fx-2 work.
- For lean-fx and lean-fx-2 work, start from local Lean artifacts, AXIOMS.md, WORKING_RULES.md, kernel-sprint.md, and source.
- Read root fx_design.md, fx_grammar.md, and fx_lexer.md when they are directly relevant to the task.
- Treat FX as a Lean 4 bootstrap project strategically; legacy OCaml/FStarX remains reference scaffolding.
- Preserve intrinsic typing as an architectural constraint for the FX kernel.
- Extrinsic well-scoped syntax plus HasType is explicitly ruled out for the core FX intrinsic kernel path.
- lean-fx and lean-fx-2 proof work must keep zero-axiom and zero-sorry discipline unless the user explicitly changes the bar.
- Use audit evidence rather than prose claims when calling Lean work complete.
- Do not over-obey Claude memory when the user says Claude ignored or failed to update a rule.
- Do not manipulate ~/.claude to make Codex remember; this digest is the requested bridge artifact.

## User And Collaboration Model
- The user is Grigory, a senior compiler and language engineer.
- The user is building FX, a graded dependently typed language with a native compiler trajectory.
- The user has deep experience with OCaml, F*, Lean 4, Z3/SMT, kernels, elaborators, normalizers, and codegen.
- The user prefers direct engineering communication over reassurance.
- The user wants action after enough source reading, not repeated circling.
- The user expects brutal critical analysis, especially about proof and soundness claims.
- The user values atomic commits, build evidence, and explicit remaining-risk statements.
- The user dislikes stale task IDs in source comments and docstrings.
- The user wants project planning tied to authoritative local artifacts.
- The user corrected that Claude task records live under ~/.claude/tasks when task mirroring is requested.

## Workflow Rules Imported
- Do not use worktrees.
- Do not use background agents.
- Do not run git reset, git checkout, or destructive commands without explicit approval.
- Do not amend commits unless explicitly requested.
- Do not create new markdown summaries unless explicitly asked; MEMORIES.md is allowed because asked.
- When implementing, read enough once, form a hypothesis, edit, and test.
- When debugging builds, preserve full relevant output unless the user requests filtering.
- Commit regularly when the user asks for ongoing implementation and commits are in scope.
- Use atomic semantically unified commits.
- Ignore unrelated dirty worktree changes and never revert user changes unless explicitly asked.

## FX Project Philosophy
- FX primary user is an agentic LLM.
- The human provides guidance, direction, and review; the agent writes code and proofs.
- Release builds require 100 percent verification.
- The compiler feedback loop is the development model: generate, check, inspect errors, retry.
- Syntax and grammar should be optimized for LLM token prediction and recovery.
- Unique construct-leading keywords and typed closers are intentional design features.
- Structured diagnostics should provide concrete repair paths.
- Proof obligations should be pushed toward the most automatic level practical.
- Sketch mode can exist, but production progression moves sketch to typed to verified to proven.
- Correct-by-construction is the target, not after-the-fact linting.

## Lean 4 Bootstrap Direction
- FX is pivoting from current F*/OCaml bootstrap scaffolding to Lean 4 stage-0 bootstrap.
- Lean 4 is the strategic host because implementation and proof language align.
- Stage 0 is Lean 4 host infrastructure.
- Stage 1 is the FX compiler written in Lean 4.
- Stage 2 is the FX compiler written in FX and compiled through stage 1.
- Stage 3 is a self-compiled fixpoint check.
- Legacy ocamlx/ml parser and lexer files are reference only.
- Do not frame new stage-1 plans as OCaml-first unless working legacy scaffolding explicitly.
- Lean kernel and Lean metaprogramming are templates and tools, not final FX semantics.
- Lean 4 source clone can be consulted for tactic, match, Eq, HEq, and kernel behavior.

## Naming And Style Rules
- Identifiers in code must be ASCII only.
- Unicode may appear in comments and docstrings when citing spec notation, but not identifiers.
- Ban single-character identifiers except narrow canonical loop/math cases.
- Ban two-character abbreviations such as ty, ex, fn, st, pt, tc, ok, nf.
- Discourage identifiers of three characters or fewer.
- Use nouns for data and state.
- Use verbs for functions, actions, and effectful steps.
- Use adjectives or past participles for transformed values.
- Boolean and Prop names should start with or contain question verbs.
- Question-verb examples include is, has, should, must, can, will, was, and needs.
- Avoid predicate names like ok, valid, good, done, flag, check, b, p, pred.
- Prefer positive predicate names and use not at call sites.
- Do not include task tracker IDs in source comments or docstrings.
- Task IDs can be commit metadata, not source semantics.
- Parser lhs/rhs and spec primitive names such as subst, whnf, beta, eta, iota are accepted exceptions.

## lean-fx Kernel Commitments
- lean-fx is a ground-up intrinsic Lean 4 formalization of the FX kernel.
- Typing is construction, not a separate Prop relation.
- Term inhabitants are well typed by construction.
- Constructor signatures are typing rules.
- Do not reintroduce a separate Typing Prop into the intrinsic kernel path.
- Nat-indexed Allais-McBride style is used to avoid Lean positivity and mutual-index limitations.
- Single-mode contexts in older snapshots later grow toward modalities and cross-mode contexts.
- Lean 4 kernel is accepted as TCB, but FX-specific machinery is audited strictly.
- Parser, elaborator, runtime, and SMT are not kernel trust base unless explicitly promoted.
- Every new kernel function should be checked for axiom dependencies.

## lean-fx-2 Architecture Commitments
- lean-fx-2 is the clean-slate architecture-of-record rewrite.
- Term is indexed by context, type, and RawTerm.
- Term.toRaw should be rfl because raw is a type-level index.
- Subst is one unified record with forTy and forRaw.
- Do not introduce dropNewest or termSingleton variants in lean-fx-2 architecture.
- Conv is existential join over StepStar chains, not an inductive relation with many cong constructors.
- Cumulativity belongs as a Conv rule, not as a Ty constructor.
- Eta is opt-in; βι reduction is default.
- Mode lives at Ctx level; Term ctors carry implicit mode.
- Identity type endpoints are RawTerm to avoid Lean mutual-index restrictions.
- Step, Step.par, StepStar, and Conv carry separate source and target Ty/RawTerm indices where needed.
- Step.pairLeft was removed as unprovable in raw-aware dependent pair typing.
- Subject reduction is not guaranteed by Step signature and must be recovered separately.
- Projection-level confluence is useful but not full typed confluence without subject reduction.
- All project-state claims here are snapshots and require source validation.

## Axiom Audit Discipline
- AXIOMS.md is canonical for trust and audit policy.
- Layer K kernel code forbids propext, Quot.sound, Classical.choice, and FX-specific axioms.
- Layer M metatheory is also pushed to zero axioms in current discipline.
- Layer E evaluator/codegen declarations are also strict unless current AXIOMS.md says otherwise.
- Use #print axioms for quick checks.
- Use #assert_no_axioms or project audit files when available.
- includeStdlib true means stdlib propext and Quot.sound still fail the gate.
- Do not hide axiom dependency by relabeling theorem layer.
- Trace axiom leaks to subordinate declarations and rewrite the source pattern.
- Avoid Classical.choice, funext, Quot, and wildcard match compiler artifacts in kernel paths.
- Prefer constructive direct induction, full enumeration, and explicit congrArg over tactic magic.
- When a fallback axiom is ever considered, document why zero-axiom encoding was impossible.

## Lean Match Compiler Rules
- Wildcard match arms can leak propext.
- Full enumeration on non-dependent inductives is usually clean.
- Full enumeration on dependent inductives with universal indices can be clean.
- Restricted dependent indices may require matching on toRaw shape instead.
- Partial matches on indexed inductives can leak propext via impossible-case equations.
- Overlapping patterns can leak propext even when all cases are reachable.
- Nested match structure avoids multi-argument overlap leaks.
- Use casesOn with explicit index-equality motive when impossible indexed cases must be discharged.
- Use Nat.noConfusion or constructor noConfusion through nomatch for impossible cases.
- Avoid matching on cons-specialized Ctx or n+1 indices when generic binders can be used.
- The Eq cast itself is often innocent; the indexed match that produced it may be the leak.
- String-reading APIs can import axioms in Lean 4 surface code.
- List Char internals plus String.ofList boundary are safer for lexer/schema proofs.
- Two-character literal cons patterns over Char lists can leak propext.
- Large enum wildcard complements should be enumerated explicitly.

## Lean Indexed Inductive Rules
- Use binder-form for functions over indexed inductives.
- Avoid pattern-form implicit indices in definitions and theorem recursion.
- Hoist all but one Nat index out of forall pattern arity for multi-index inductives.
- Do not put level back inside forall merely for uniform-looking signatures.
- Direct Fin structure matches are preferred over Fin.cases and Fin.casesOn.
- Functions in constructor signatures, such as weaken and subst shape helpers, may need @[reducible].
- Level-constraining constructors should carry explicit propositional equality witnesses.
- Ty.universe style constructors should be polymorphic in level plus levelEq witness.
- Ty.cumul as constructor breaks substitution because substituents live at the wrong level.
- Cumulativity should be a conversion/judgment rule rather than a syntax constructor.
- Ty.unweaken from n+1 to n is an axiom trap for dependent Pi cases.
- Use real substitution rather than unweaken for dependent eliminators.

## Substitution And Renaming Patterns
- Function-typed Subst source target as Fin source to Ty target is the successful pattern.
- Function-typed Renaming source target as Fin source to Fin target is the parallel pattern.
- Subst.lift carries source and target structurally under binders.
- This avoids Nat arithmetic equalities such as (scope + 1) + 1 = scope + 2.
- Define weaken through rename when possible.
- Prove rename_congr and rename_compose before depending on weaken.
- Prove substitution compose and singleton lemmas before Term.subst consumers.
- Use pointwise equivalence predicates instead of function equality when funext would leak.
- TermSubst.lift and singleton need casts through subst/rename commute lemmas.
- Beta rules depend on coherent substitution infrastructure.
- Raw-aware Term in lean-fx-2 reduces many bridge obligations to rfl.
- Old lean-fx termSingleton/dropNewest divergence explains bridge beta blockers.

## Proof Pattern Cookbook
- Use Step.parWithBi or analogous paired predicates when a theorem must preserve both a relation and a witness property.
- Construct fresh paired witnesses in each case instead of characterizing opaque theorem output.
- Share the same targetEquality value between relation and witness pieces.
- Use match-with-witness when an Option or Eq witness can discharge nonmatching constructors.
- Free type indices via suffices before cases on typed Terms with opaque indices.
- Use Term.toRaw refutation for typed inversion walls caused by type-index opacity.
- Use raw constructor mismatch to avoid dependent typed noConfusion trouble.
- Use nested injection instead of Prod.mk.injEq.
- Use nomatch for impossible constructor equalities.
- Use mapStep for repetitive refl/trans chain congruence proofs.
- Use dispatch sums when a heterogeneous relation has a true wall constructor.
- Use separate route theorems per dispatch branch when motive-dependent dispatcher is too costly.
- Use BHKM ladder for substitution fusion infrastructure.
- Use Allais paired environments for outer heterogeneous substitution compatibility.
- Reserve Kripke validity/fundamental lemma patterns for later semantic checker soundness layers.

## Cumulativity Decision Matrix
- The chosen path for CUMUL-style heterogeneous substitution is Pattern 2 plus Pattern 3 hybrid.
- Pattern 2 is Benton-Hur-Kennedy-McBride four-lemma substitution ladder.
- Pattern 3 is Allais-style paired-environment simulation.
- Pattern 5 extrinsic well-scoped syntax is ruled out for FX intrinsic kernel goals.
- Use two heterogeneous substitutions when endpoints live at different levels or scopes.
- Do not force a single Subst through viaUp-style heterogeneous endpoints.
- Do not use top-level induction on full heterogeneous ConvCumul when the wall constructor is present.
- Use homogeneous sister relations such as ConvCumulHomo for recursive headlines.
- Provide shims for wall constructors like viaUp.
- Expose classification evidence through dispatch sums when callers can know the branch.
- CwF semantic interpretation is the principled future answer for modal tier semantics.
- Kripke validity is a good fit for later check_sound/fundamental-lemma work, not immediate CUMUL-1.7.

## Confluence And Reduction Snapshots
- lean-fx W8 memory claims typed cd_lemma, diamond, confluence, and canonical_form completed zero-axiom.
- lean-fx-2 memory claims raw confluence, WHNF, and DecConv-facing sound pieces completed zero-axiom.
- These are historical claims; re-run lake build and audit files before relying on them.
- Typed cd_lemma can produce Step.parStar chains rather than single Step.par steps.
- Standard strip confluence can break when diamond returns chains.
- cd monotonicity plus cdIter was the typed confluence workaround.
- Sum-based confluence joins can avoid Nat.max proof axiom leaks.
- RawTerm.cd used full constructor enumeration to stay zero-axiom.
- Raw WHNF soundness proves whnf output reachable via parStar.
- checkConv is sound for positive results but incomplete due to fuel and shallow comparison limits.
- Subject reduction is high ROI because it lifts raw common reducts back to typed terms.
- Eta remains deferred or opt-in because unrestricted eta complicates confluence.

## Parser And Surface Notes
- TokenStream.advance at EOF being a no-op caused an infinite-loop trap in parser loops.
- Every accumulating recursive descent loop must have an EOF arm.
- Every such loop should check parser progress when subparsers can recover without advancing.
- Malformed LLM-generated input is common and must produce diagnostics, not hangs.
- A stale file plus rm alias plus parser loop once caused severe OOM behavior.
- Do not rely on rm alias behavior; scripted deletion needs non-aliased rm and approval when destructive.
- Surface zero-axiom code should avoid wildcard complements over giant enums.
- Keyword and token schema proofs may need full enum cases.
- Avoid String.toList except at documented boundary shims.
- Use String.ofList for clean construction where possible.

## Legacy FStarX And Z3 Notes
- Legacy FStarX notes are mostly for old compiler tasks, not lean-fx kernel tasks.
- z3-iprit tuned values are eager threshold 10 and lazy threshold 24.
- Do not blindly restore upstream eager 15 lazy 100 values for z3-iprit work.
- smt.auto_tune true was part of the custom Z3 setup.
- Never add pattern annotations to Prims WP combinators; they caused huge memory blowups.
- DefCache false pass bug came from caching after non-fatal SMT errors.
- Guard err_count around typechecking prevents storing false pass entries.
- WP if encoding bug dropped else-branch constraints under phase interactions.
- Calc chain failures involved incomplete quantifiers and were not simple pruning issues.
- Seed retry bug involved sending incremental deltas to fresh Z3 processes.
- Pervasives.Native deferred dependency bug can be triggered by apostrophe type variables in fragments.
- Old clean rebuild guidance nuked fcache and build before make 1.full; verify current build system first.

## Reference Codebases And External Context
- ~/Downloads/fx-refs is a curated read-only reference directory.
- BiSikkel and Sikkel inform multimodal type theory and presheaf semantics.
- Idris2 informs quantitative type theory in a production compiler.
- Granule informs user-defined graded semirings.
- Cubical Agda informs HITs and univalence.
- Agda bridge mode informs internal parametricity.
- DynamicIFCTheoremsForFree informs noninterference from parametricity.
- smpst-sr-smer informs mechanized multiparty session type progress and preservation.
- Iris informs separation logic tradeoffs.
- LiquidHaskell informs refinement plus SMT integration.
- CompCert informs verified compiler refinement proof architecture.
- FStar is comparison baseline for what FX diverges from.
- Lean 4 source clone is useful for Init, PropLemmas, Fin, tactic induction, match compiler, and predefinition code.
- Use references before inventing frontier theorem machinery from scratch.
- Deep reference dives should be scoped to the current proof or design obstacle.

## Current-Use Checklist
- Before lean-fx or lean-fx-2 work, read local Lean instructions and relevant source first.
- Check AGENTS.md and project-local CLAUDE.md or WORKING_RULES.md when present.
- Do not read root fx*.md as mandatory ceremony for lean-fx unless relevant.
- Identify whether a memory is architectural, workflow, proof pattern, or stale snapshot.
- For source claims from memories, verify with rg, file reads, lake build, and audit files.
- For Lean proof work, add or update smoke/audit coverage near the change.
- For parser work, include malformed-input negative tests.
- For legacy F* work, verify build targets and environment before applying old commands.
- For destructive shell operations, ask or use approved explicit commands only.
- End work with concise status, tests run, and residual risk.

## Source Memory Index
- `MEMORY.md`: Master Claude FX memory index; useful but contains stale full-spec rule.
- `bug_pervasives_native_leak.md`: FStarX deferred Pervasives.Native bug from apostrophe type variables; legacy compiler note.
- `feedback_ascii_only.md`: ASCII-only identifier rule; import as active project style.
- `feedback_lean_binder_form.md`: Binder-form over indexed inductives; import as active Lean rule.
- `feedback_lean_cd_dominates_unary_wrapper.md`: parWithBi workaround for opaque cd_dominates witnesses; import as proof pattern.
- `feedback_lean_closed_type_sr.md`: Closed-type subject reduction pattern for nat/bool/unit; import as proof pattern.
- `feedback_lean_cumul_subst_mismatch.md`: Ty.cumul constructor breaks substitution; import as architectural rule.
- `feedback_lean_dispatch_sum_dependent_output.md`: Dispatch sum for heterogeneous Prop walls; import as proof/API pattern.
- `feedback_lean_fin_cases_axiom.md`: Avoid Fin.cases; direct Fin structure matching; import as active Lean rule.
- `feedback_lean_free_type_via_suffices.md`: Free type indices via suffices for strong uniqueness; import as proof pattern.
- `feedback_lean_function_typed_subst.md`: Function-typed Subst avoids Nat arithmetic walls; import as design rule.
- `feedback_lean_indexed_partial_match.md`: Indexed partial match leaks propext; import as active Lean rule.
- `feedback_lean_mapStep_pattern.md`: mapStep lifters remove repetitive cong inductions; import as refactor pattern.
- `feedback_lean_match_arity_axioms.md`: Hoist Nat indices out of pattern arity; import as active Lean rule.
- `feedback_lean_match_propext_recipe.md`: Surface-layer match compiler recipes; import when working lexer/parser/schema.
- `feedback_lean_match_witness_pattern.md`: match-with-witness and injection patterns; import as proof pattern.
- `feedback_lean_mutual_index_rule.md`: Lean mutual index limitation; import facts, but extrinsic alternative is ruled out.
- `feedback_lean_mutual_positivity.md`: Nat-indexed Allais-McBride encoding; import as Lean architecture note.
- `feedback_lean_paired_predicate_pattern.md`: Use paired predicate for Step.par plus isBi; import as proof pattern.
- `feedback_lean_pattern3_homogeneous_level.md`: Allais paired-env shipped homogeneous-level; import as cumul note.
- `feedback_lean_propext_cons_index.md`: Avoid cons-specialized indexed matches; use Fin plus varType; import.
- `feedback_lean_reducible_weaken.md`: @[reducible] on shape functions in ctor signatures; import.
- `feedback_lean_subst_lemmas.md`: Term.subst infrastructure path; import as historical technique, verify current.
- `feedback_lean_universe_constructor_block.md`: Level-constraining constructors need Eq witnesses; import.
- `feedback_lean_unweaken_axiom_trap.md`: Ty.unweaken is axiom trap; use real substitution; import.
- `feedback_lean_zero_axiom_match.md`: Zero-axiom match recipe; import as active Lean rule.
- `feedback_no_task_ids_in_code.md`: No task IDs in source comments; import active style rule.
- `feedback_prims_patterns.md`: Never add patterns to Prims WP combinators; legacy F* rule.
- `feedback_read_full_specs.md`: STALE for Codex lean-fx behavior; do not import mandatory preflight.
- `feedback_readable_names.md`: Narrative names and question verbs; import active style rule.
- `feedback_typed_inversion_breakthrough.md`: Term.toRaw plus HEq source inversion; import proof pattern.
- `feedback_workflows.md`: No worktrees/background agents; action bias; import active workflow.
- `project_build_state.md`: Old 2026-03-26 build state; snapshot only, verify before use.
- `project_calc_chain_bug.md`: Legacy calc-chain incomplete quantifier bug; import as old F* caution.
- `project_defcache_fix.md`: DefCache false-pass fix; import as legacy compiler caution.
- `project_fx_agentic_design.md`: FX primary user agentic LLM; import project philosophy.
- `project_lean_bootstrap.md`: Lean 4 bootstrap pivot; import as active direction.
- `project_lean_fx_2_phase6_complete.md`: lean-fx-2 phase snapshot; import but verify source before relying.
- `project_lean_fx_2_state.md`: lean-fx-2 architecture snapshot; import active architecture, verify state.
- `project_lean_fx_confluence_strategy.md`: Typed confluence strategy; historical but useful proof map.
- `project_lean_fx_state.md`: lean-fx intrinsic kernel snapshot; import architecture, verify current.
- `project_lean_fx_v2_refactor.md`: lean-fx mega-refactor snapshot; historical, verify current.
- `project_lean_fx_vs_lean_discipline.md`: What to reuse from Lean vs reimplement; import active discipline.
- `project_parser_eof_trap.md`: Parser EOF/progress trap; import active parser rule.
- `project_phase_c_blockers.md`: Bridge beta blockers; historical lean-fx map, verify current.
- `project_seed_retry_bug.md`: Legacy seed retry bug; import as F* compiler caution.
- `project_stage1_last_error.md`: Legacy stage1 bootstrap divergence; snapshot only.
- `project_term_const.md`: Term.const global environment design; import architecture note.
- `project_test_architecture.md`: Legacy 4-tier tests; import if working FStarX tests.
- `project_ulib_verification.md`: Legacy ulib Z3 verification tactics; import as old F* note.
- `project_w83_confluence_strategy.md`: W8.3 cd-monotonicity path; historical proof map.
- `project_w83_subst_witnessed_blocker.md`: Witnessed subst dependency chain; historical proof map.
- `project_w8_complete.md`: W8 completion snapshot; verify source before relying.
- `project_wave9_status.md`: Wave 9 cascade obstruction; historical proof map.
- `project_wp_encoding_bug.md`: Legacy WP else-branch bug; import caution.
- `project_z3_tuning.md`: z3-iprit tuned thresholds; import legacy solver rule.
- `reference_audit_axiom_semantics.md`: AXIOMS.md summary; import but treat AXIOMS.md as canonical.
- `reference_brrr_project.md`: go-brrr reference overview; import context.
- `reference_build_targets.md`: Legacy build/test targets; verify before use.
- `reference_cumul_subst_pattern_decision.md`: Cumul-subst pattern matrix; import active architectural decision.
- `reference_fx_refs_dir.md`: fx-refs directory map; import as reference lookup guide.
- `reference_lean4_source_clone.md`: Lean source clone paths; import troubleshooting guide.
- `reference_pattern_allais_simulation.md`: Allais paired-env pattern; import cumul architecture.
- `reference_pattern_bhkm_ladder.md`: BHKM ladder; import subst architecture.
- `reference_pattern_cwf_semantic.md`: CwF semantic pattern; import future modal architecture.
- `reference_pattern_extrinsic_wellscoped.md`: Extrinsic pattern ruled out; keep as non-choice.
- `reference_pattern_kripke_validity.md`: Kripke validity for Day 8 soundness, not CUMUL-1.7.
- `reference_rm_alias_trap.md`: rm alias trap; import caution, still require approval for deletion.
- `reference_z3_binary.md`: Custom Z3 and OCaml environment; legacy reference.
- `user_profile.md`: User profile; import communication/project preferences.

## Lean Proof Cookbook Table
- Problem: Wildcard match. Response: Replace with full enumeration or structural recursor.
- Problem: Indexed partial match. Response: Use casesOn with explicit index equality witness.
- Problem: Multi-Nat theorem patterns. Response: Hoist all but one Nat index before colon.
- Problem: Fin.cases. Response: Use direct Fin structure matching.
- Problem: Prod.mk.injEq. Response: Use nested injection.
- Problem: Term destructors fail dep-elim. Response: Free type indices with suffices.
- Problem: Opaque typed inversion. Response: Project through Term.toRaw and refute raw shape.
- Problem: isBi preservation of opaque theorem. Response: Construct parWithBi-valued companion.
- Problem: Repeated RT closure cong. Response: Use mapStep.
- Problem: True heterogeneous wall ctor. Response: Expose dispatch sum and route theorems.
- Problem: Level-fixed Ty constructor. Response: Use polymorphic constructor plus Eq witness.
- Problem: Cumulativity constructor. Response: Move to Conv or judgment rule.
- Problem: Unweaken eliminator. Response: Use real substitution.
- Problem: String read in surface proofs. Response: Isolate boundary and use List Char internally.
- Problem: Function equality temptation. Response: Use pointwise equivalence predicates.

## Feedback Memories
- `feedback_ascii_only.md` -> ASCII-only identifier rule; import as active project style.
- `feedback_lean_binder_form.md` -> Binder-form over indexed inductives; import as active Lean rule.
- `feedback_lean_cd_dominates_unary_wrapper.md` -> parWithBi workaround for opaque cd_dominates witnesses; import as proof pattern.
- `feedback_lean_closed_type_sr.md` -> Closed-type subject reduction pattern for nat/bool/unit; import as proof pattern.
- `feedback_lean_cumul_subst_mismatch.md` -> Ty.cumul constructor breaks substitution; import as architectural rule.
- `feedback_lean_dispatch_sum_dependent_output.md` -> Dispatch sum for heterogeneous Prop walls; import as proof/API pattern.
- `feedback_lean_fin_cases_axiom.md` -> Avoid Fin.cases; direct Fin structure matching; import as active Lean rule.
- `feedback_lean_free_type_via_suffices.md` -> Free type indices via suffices for strong uniqueness; import as proof pattern.
- `feedback_lean_function_typed_subst.md` -> Function-typed Subst avoids Nat arithmetic walls; import as design rule.
- `feedback_lean_indexed_partial_match.md` -> Indexed partial match leaks propext; import as active Lean rule.
- `feedback_lean_mapStep_pattern.md` -> mapStep lifters remove repetitive cong inductions; import as refactor pattern.
- `feedback_lean_match_arity_axioms.md` -> Hoist Nat indices out of pattern arity; import as active Lean rule.
- `feedback_lean_match_propext_recipe.md` -> Surface-layer match compiler recipes; import when working lexer/parser/schema.
- `feedback_lean_match_witness_pattern.md` -> match-with-witness and injection patterns; import as proof pattern.
- `feedback_lean_mutual_index_rule.md` -> Lean mutual index limitation; import facts, but extrinsic alternative is ruled out.
- `feedback_lean_mutual_positivity.md` -> Nat-indexed Allais-McBride encoding; import as Lean architecture note.
- `feedback_lean_paired_predicate_pattern.md` -> Use paired predicate for Step.par plus isBi; import as proof pattern.
- `feedback_lean_pattern3_homogeneous_level.md` -> Allais paired-env shipped homogeneous-level; import as cumul note.
- `feedback_lean_propext_cons_index.md` -> Avoid cons-specialized indexed matches; use Fin plus varType; import.
- `feedback_lean_reducible_weaken.md` -> @[reducible] on shape functions in ctor signatures; import.
- `feedback_lean_subst_lemmas.md` -> Term.subst infrastructure path; import as historical technique, verify current.
- `feedback_lean_universe_constructor_block.md` -> Level-constraining constructors need Eq witnesses; import.
- `feedback_lean_unweaken_axiom_trap.md` -> Ty.unweaken is axiom trap; use real substitution; import.
- `feedback_lean_zero_axiom_match.md` -> Zero-axiom match recipe; import as active Lean rule.
- `feedback_no_task_ids_in_code.md` -> No task IDs in source comments; import active style rule.
- `feedback_prims_patterns.md` -> Never add patterns to Prims WP combinators; legacy F* rule.
- `feedback_read_full_specs.md` -> STALE for Codex lean-fx behavior; do not import mandatory preflight.
- `feedback_readable_names.md` -> Narrative names and question verbs; import active style rule.
- `feedback_typed_inversion_breakthrough.md` -> Term.toRaw plus HEq source inversion; import proof pattern.
- `feedback_workflows.md` -> No worktrees/background agents; action bias; import active workflow.

## Project Memories
- `bug_pervasives_native_leak.md` -> FStarX deferred Pervasives.Native bug from apostrophe type variables; legacy compiler note.
- `project_build_state.md` -> Old 2026-03-26 build state; snapshot only, verify before use.
- `project_calc_chain_bug.md` -> Legacy calc-chain incomplete quantifier bug; import as old F* caution.
- `project_defcache_fix.md` -> DefCache false-pass fix; import as legacy compiler caution.
- `project_fx_agentic_design.md` -> FX primary user agentic LLM; import project philosophy.
- `project_lean_bootstrap.md` -> Lean 4 bootstrap pivot; import as active direction.
- `project_lean_fx_2_phase6_complete.md` -> lean-fx-2 phase snapshot; import but verify source before relying.
- `project_lean_fx_2_state.md` -> lean-fx-2 architecture snapshot; import active architecture, verify state.
- `project_lean_fx_confluence_strategy.md` -> Typed confluence strategy; historical but useful proof map.
- `project_lean_fx_state.md` -> lean-fx intrinsic kernel snapshot; import architecture, verify current.
- `project_lean_fx_v2_refactor.md` -> lean-fx mega-refactor snapshot; historical, verify current.
- `project_lean_fx_vs_lean_discipline.md` -> What to reuse from Lean vs reimplement; import active discipline.
- `project_parser_eof_trap.md` -> Parser EOF/progress trap; import active parser rule.
- `project_phase_c_blockers.md` -> Bridge beta blockers; historical lean-fx map, verify current.
- `project_seed_retry_bug.md` -> Legacy seed retry bug; import as F* compiler caution.
- `project_stage1_last_error.md` -> Legacy stage1 bootstrap divergence; snapshot only.
- `project_term_const.md` -> Term.const global environment design; import architecture note.
- `project_test_architecture.md` -> Legacy 4-tier tests; import if working FStarX tests.
- `project_ulib_verification.md` -> Legacy ulib Z3 verification tactics; import as old F* note.
- `project_w83_confluence_strategy.md` -> W8.3 cd-monotonicity path; historical proof map.
- `project_w83_subst_witnessed_blocker.md` -> Witnessed subst dependency chain; historical proof map.
- `project_w8_complete.md` -> W8 completion snapshot; verify source before relying.
- `project_wave9_status.md` -> Wave 9 cascade obstruction; historical proof map.
- `project_wp_encoding_bug.md` -> Legacy WP else-branch bug; import caution.
- `project_z3_tuning.md` -> z3-iprit tuned thresholds; import legacy solver rule.

## Reference Memories
- `reference_audit_axiom_semantics.md` -> AXIOMS.md summary; import but treat AXIOMS.md as canonical.
- `reference_brrr_project.md` -> go-brrr reference overview; import context.
- `reference_build_targets.md` -> Legacy build/test targets; verify before use.
- `reference_cumul_subst_pattern_decision.md` -> Cumul-subst pattern matrix; import active architectural decision.
- `reference_fx_refs_dir.md` -> fx-refs directory map; import as reference lookup guide.
- `reference_lean4_source_clone.md` -> Lean source clone paths; import troubleshooting guide.
- `reference_pattern_allais_simulation.md` -> Allais paired-env pattern; import cumul architecture.
- `reference_pattern_bhkm_ladder.md` -> BHKM ladder; import subst architecture.
- `reference_pattern_cwf_semantic.md` -> CwF semantic pattern; import future modal architecture.
- `reference_pattern_extrinsic_wellscoped.md` -> Extrinsic pattern ruled out; keep as non-choice.
- `reference_pattern_kripke_validity.md` -> Kripke validity for Day 8 soundness, not CUMUL-1.7.
- `reference_rm_alias_trap.md` -> rm alias trap; import caution, still require approval for deletion.
- `reference_z3_binary.md` -> Custom Z3 and OCaml environment; legacy reference.

## User And Index Memories
- `MEMORY.md` -> Master Claude FX memory index; useful but contains stale full-spec rule.
- `user_profile.md` -> User profile; import communication/project preferences.

## Operational Ledger
001. [Authority] Use this digest as memory import, not as a replacement for current source.
002. [Authority] When a completion claim matters, rebuild or inspect the specific declaration.
003. [StaleRule] Mandatory root full-spec preflight is stale for Codex lean-fx behavior.
004. [StaleRule] Root specs remain valuable when task touches language design or parser spec alignment.
005. [Workflow] No worktrees, no background agents, no hidden parallel branches.
006. [Workflow] Prefer targeted implementation after enough context over repeated broad scans.
007. [Git] Never reset, checkout, or amend without explicit user direction.
008. [Git] Keep unrelated dirty worktree changes intact.
009. [Style] ASCII identifiers are mandatory for code.
010. [Style] Readable names carry semantic weight equal to types.
011. [Style] Predicate names should read like questions.
012. [Style] Do not put Q IDs, issue IDs, or task names in source comments.
013. [FX] FX is a graded dependent language with agentic LLM as primary user.
014. [FX] Proof automation and compiler retry loop are design center, not afterthought.
015. [Bootstrap] Lean 4 is the active host direction for kernel and compiler proofs.
016. [Bootstrap] Legacy F*/OCaml state should be isolated from Lean kernel decisions.
017. [Intrinsic] Correct-by-construction Term remains the kernel goal.
018. [Intrinsic] Extrinsic HasType can be studied but is ruled out for core FX path.
019. [lean-fx] Use zero-axiom audit as completion evidence.
020. [lean-fx] Use binder-form functions over indexed inductives.
021. [lean-fx] Use Nat-indexed scopes where Lean mutual signatures block textbook forms.
022. [lean-fx] Use function-typed substitutions and renamings.
023. [lean-fx] Do not use unweaken as a dependent eliminator substitute.
024. [lean-fx-2] Raw-aware Term index makes typed-to-raw bridge definitional.
025. [lean-fx-2] Unified Subst prevents singleton/dropNewest divergence.
026. [lean-fx-2] Conv as existential join makes congruence derived by mapStep.
027. [lean-fx-2] Subject reduction remains key for typed confluence consumers.
028. [Audit] propext, Quot.sound, and Classical.choice are audit failures in strict layers.
029. [Audit] Avoid funext; use pointwise compatibility.
030. [Audit] Avoid quotient machinery in kernel theorem dependencies.
031. [Match] Full enumeration beats wildcard convenience.
032. [Match] Overlapping patterns can be as bad as wildcards.
033. [Match] toRaw dispatch is a way around restricted typed indices.
034. [Match] nomatch is preferred for impossible constructor equations.
035. [Fin] Direct Fin structure matching avoids Fin.cases propext dependency.
036. [Subst] BHKM ladder supplies fusion laws in strict order.
037. [Subst] Allais simulation supplies paired-environment outer structure.
038. [Cumul] Cumulativity as syntax constructor breaks level-coherent substitution.
039. [Cumul] Use ConvCumulHomo plus viaUp shim or dispatch when heterogeneity is real.
040. [Cumul] Kripke validity belongs later in checker soundness, not immediate CUMUL subst.
041. [Confluence] Typed cd_lemma chain output forced cd-monotonicity strategy.
042. [Confluence] Eta needs separate opt-in treatment.
043. [WHNF] Raw WHNF soundness gives reachability, not completeness.
044. [Parser] EOF and progress checks are mandatory in recovery loops.
045. [Parser] Agent-generated malformed input is normal workload.
046. [Surface] String.toList and friends are axiom-leaking boundaries.
047. [Surface] String.ofList is useful for clean construction.
048. [LegacyZ3] z3-iprit tuning values are eager 10 and lazy 24.
049. [LegacyZ3] Prims WP combinator patterns caused severe instantiation blowup.
050. [LegacyFStarX] DefCache must account for non-fatal errors before storing pass entries.
051. [LegacyFStarX] WP phase1 uvar embedding can make phase2 unsound if stale.
052. [Refs] Check BiSikkel/Sikkel for modal type theory patterns.
053. [Refs] Check smpst-sr-smer for session type mechanization.
054. [Refs] Check CompCert for verified compiler simulation structure.
055. [Refs] Check Lean source for match compiler and Eq/HEq behavior.

## Repeated Extraction Hints
These lines intentionally restate core instructions in stable forms for future memory extraction, but avoid meaningless filler.
- Pass 1.01 [Authority]: Use this digest as memory import, not as a replacement for current source.
- Pass 1.02 [Authority]: When a completion claim matters, rebuild or inspect the specific declaration.
- Pass 1.03 [StaleRule]: Mandatory root full-spec preflight is stale for Codex lean-fx behavior.
- Pass 1.04 [StaleRule]: Root specs remain valuable when task touches language design or parser spec alignment.
- Pass 1.05 [Workflow]: No worktrees, no background agents, no hidden parallel branches.
- Pass 1.06 [Workflow]: Prefer targeted implementation after enough context over repeated broad scans.
- Pass 1.07 [Git]: Never reset, checkout, or amend without explicit user direction.
- Pass 1.08 [Git]: Keep unrelated dirty worktree changes intact.
- Pass 1.09 [Style]: ASCII identifiers are mandatory for code.
- Pass 1.10 [Style]: Readable names carry semantic weight equal to types.
- Pass 1.11 [Style]: Predicate names should read like questions.
- Pass 1.12 [Style]: Do not put Q IDs, issue IDs, or task names in source comments.
- Pass 1.13 [FX]: FX is a graded dependent language with agentic LLM as primary user.
- Pass 1.14 [FX]: Proof automation and compiler retry loop are design center, not afterthought.
- Pass 1.15 [Bootstrap]: Lean 4 is the active host direction for kernel and compiler proofs.
- Pass 1.16 [Bootstrap]: Legacy F*/OCaml state should be isolated from Lean kernel decisions.
- Pass 1.17 [Intrinsic]: Correct-by-construction Term remains the kernel goal.
- Pass 1.18 [Intrinsic]: Extrinsic HasType can be studied but is ruled out for core FX path.
- Pass 1.19 [lean-fx]: Use zero-axiom audit as completion evidence.
- Pass 1.20 [lean-fx]: Use binder-form functions over indexed inductives.
- Pass 1.21 [lean-fx]: Use Nat-indexed scopes where Lean mutual signatures block textbook forms.
- Pass 1.22 [lean-fx]: Use function-typed substitutions and renamings.
- Pass 1.23 [lean-fx]: Do not use unweaken as a dependent eliminator substitute.
- Pass 1.24 [lean-fx-2]: Raw-aware Term index makes typed-to-raw bridge definitional.
- Pass 1.25 [lean-fx-2]: Unified Subst prevents singleton/dropNewest divergence.
- Pass 1.26 [lean-fx-2]: Conv as existential join makes congruence derived by mapStep.
- Pass 1.27 [lean-fx-2]: Subject reduction remains key for typed confluence consumers.
- Pass 1.28 [Audit]: propext, Quot.sound, and Classical.choice are audit failures in strict layers.
- Pass 1.29 [Audit]: Avoid funext; use pointwise compatibility.
- Pass 1.30 [Audit]: Avoid quotient machinery in kernel theorem dependencies.
- Pass 1.31 [Match]: Full enumeration beats wildcard convenience.
- Pass 1.32 [Match]: Overlapping patterns can be as bad as wildcards.
- Pass 1.33 [Match]: toRaw dispatch is a way around restricted typed indices.
- Pass 1.34 [Match]: nomatch is preferred for impossible constructor equations.
- Pass 1.35 [Fin]: Direct Fin structure matching avoids Fin.cases propext dependency.
- Pass 1.36 [Subst]: BHKM ladder supplies fusion laws in strict order.
- Pass 1.37 [Subst]: Allais simulation supplies paired-environment outer structure.
- Pass 1.38 [Cumul]: Cumulativity as syntax constructor breaks level-coherent substitution.
- Pass 1.39 [Cumul]: Use ConvCumulHomo plus viaUp shim or dispatch when heterogeneity is real.
- Pass 1.40 [Cumul]: Kripke validity belongs later in checker soundness, not immediate CUMUL subst.
- Pass 1.41 [Confluence]: Typed cd_lemma chain output forced cd-monotonicity strategy.
- Pass 1.42 [Confluence]: Eta needs separate opt-in treatment.
- Pass 1.43 [WHNF]: Raw WHNF soundness gives reachability, not completeness.
- Pass 1.44 [Parser]: EOF and progress checks are mandatory in recovery loops.
- Pass 1.45 [Parser]: Agent-generated malformed input is normal workload.
- Pass 1.46 [Surface]: String.toList and friends are axiom-leaking boundaries.
- Pass 1.47 [Surface]: String.ofList is useful for clean construction.
- Pass 1.48 [LegacyZ3]: z3-iprit tuning values are eager 10 and lazy 24.
- Pass 1.49 [LegacyZ3]: Prims WP combinator patterns caused severe instantiation blowup.
- Pass 1.50 [LegacyFStarX]: DefCache must account for non-fatal errors before storing pass entries.
- Pass 1.51 [LegacyFStarX]: WP phase1 uvar embedding can make phase2 unsound if stale.
- Pass 1.52 [Refs]: Check BiSikkel/Sikkel for modal type theory patterns.
- Pass 1.53 [Refs]: Check smpst-sr-smer for session type mechanization.
- Pass 1.54 [Refs]: Check CompCert for verified compiler simulation structure.
- Pass 1.55 [Refs]: Check Lean source for match compiler and Eq/HEq behavior.
- Pass 2.01 [Authority]: Use this digest as memory import, not as a replacement for current source.
- Pass 2.02 [Authority]: When a completion claim matters, rebuild or inspect the specific declaration.
- Pass 2.03 [StaleRule]: Mandatory root full-spec preflight is stale for Codex lean-fx behavior.
- Pass 2.04 [StaleRule]: Root specs remain valuable when task touches language design or parser spec alignment.
- Pass 2.05 [Workflow]: No worktrees, no background agents, no hidden parallel branches.
- Pass 2.06 [Workflow]: Prefer targeted implementation after enough context over repeated broad scans.
- Pass 2.07 [Git]: Never reset, checkout, or amend without explicit user direction.
- Pass 2.08 [Git]: Keep unrelated dirty worktree changes intact.
- Pass 2.09 [Style]: ASCII identifiers are mandatory for code.
- Pass 2.10 [Style]: Readable names carry semantic weight equal to types.
- Pass 2.11 [Style]: Predicate names should read like questions.
- Pass 2.12 [Style]: Do not put Q IDs, issue IDs, or task names in source comments.
- Pass 2.13 [FX]: FX is a graded dependent language with agentic LLM as primary user.
- Pass 2.14 [FX]: Proof automation and compiler retry loop are design center, not afterthought.
- Pass 2.15 [Bootstrap]: Lean 4 is the active host direction for kernel and compiler proofs.
- Pass 2.16 [Bootstrap]: Legacy F*/OCaml state should be isolated from Lean kernel decisions.
- Pass 2.17 [Intrinsic]: Correct-by-construction Term remains the kernel goal.
- Pass 2.18 [Intrinsic]: Extrinsic HasType can be studied but is ruled out for core FX path.
- Pass 2.19 [lean-fx]: Use zero-axiom audit as completion evidence.
- Pass 2.20 [lean-fx]: Use binder-form functions over indexed inductives.
- Pass 2.21 [lean-fx]: Use Nat-indexed scopes where Lean mutual signatures block textbook forms.
- Pass 2.22 [lean-fx]: Use function-typed substitutions and renamings.
- Pass 2.23 [lean-fx]: Do not use unweaken as a dependent eliminator substitute.
- Pass 2.24 [lean-fx-2]: Raw-aware Term index makes typed-to-raw bridge definitional.
- Pass 2.25 [lean-fx-2]: Unified Subst prevents singleton/dropNewest divergence.
- Pass 2.26 [lean-fx-2]: Conv as existential join makes congruence derived by mapStep.
- Pass 2.27 [lean-fx-2]: Subject reduction remains key for typed confluence consumers.
- Pass 2.28 [Audit]: propext, Quot.sound, and Classical.choice are audit failures in strict layers.
- Pass 2.29 [Audit]: Avoid funext; use pointwise compatibility.
- Pass 2.30 [Audit]: Avoid quotient machinery in kernel theorem dependencies.
- Pass 2.31 [Match]: Full enumeration beats wildcard convenience.
- Pass 2.32 [Match]: Overlapping patterns can be as bad as wildcards.
- Pass 2.33 [Match]: toRaw dispatch is a way around restricted typed indices.
- Pass 2.34 [Match]: nomatch is preferred for impossible constructor equations.
- Pass 2.35 [Fin]: Direct Fin structure matching avoids Fin.cases propext dependency.
- Pass 2.36 [Subst]: BHKM ladder supplies fusion laws in strict order.
- Pass 2.37 [Subst]: Allais simulation supplies paired-environment outer structure.
- Pass 2.38 [Cumul]: Cumulativity as syntax constructor breaks level-coherent substitution.
- Pass 2.39 [Cumul]: Use ConvCumulHomo plus viaUp shim or dispatch when heterogeneity is real.
- Pass 2.40 [Cumul]: Kripke validity belongs later in checker soundness, not immediate CUMUL subst.
- Pass 2.41 [Confluence]: Typed cd_lemma chain output forced cd-monotonicity strategy.
- Pass 2.42 [Confluence]: Eta needs separate opt-in treatment.
- Pass 2.43 [WHNF]: Raw WHNF soundness gives reachability, not completeness.
- Pass 2.44 [Parser]: EOF and progress checks are mandatory in recovery loops.
- Pass 2.45 [Parser]: Agent-generated malformed input is normal workload.
- Pass 2.46 [Surface]: String.toList and friends are axiom-leaking boundaries.
- Pass 2.47 [Surface]: String.ofList is useful for clean construction.
- Pass 2.48 [LegacyZ3]: z3-iprit tuning values are eager 10 and lazy 24.
- Pass 2.49 [LegacyZ3]: Prims WP combinator patterns caused severe instantiation blowup.
- Pass 2.50 [LegacyFStarX]: DefCache must account for non-fatal errors before storing pass entries.
- Pass 2.51 [LegacyFStarX]: WP phase1 uvar embedding can make phase2 unsound if stale.
- Pass 2.52 [Refs]: Check BiSikkel/Sikkel for modal type theory patterns.
- Pass 2.53 [Refs]: Check smpst-sr-smer for session type mechanization.
- Pass 2.54 [Refs]: Check CompCert for verified compiler simulation structure.
- Pass 2.55 [Refs]: Check Lean source for match compiler and Eq/HEq behavior.
- Pass 3.01 [Authority]: Use this digest as memory import, not as a replacement for current source.
- Pass 3.02 [Authority]: When a completion claim matters, rebuild or inspect the specific declaration.
- Pass 3.03 [StaleRule]: Mandatory root full-spec preflight is stale for Codex lean-fx behavior.
- Pass 3.04 [StaleRule]: Root specs remain valuable when task touches language design or parser spec alignment.
- Pass 3.05 [Workflow]: No worktrees, no background agents, no hidden parallel branches.
- Pass 3.06 [Workflow]: Prefer targeted implementation after enough context over repeated broad scans.
- Pass 3.07 [Git]: Never reset, checkout, or amend without explicit user direction.
- Pass 3.08 [Git]: Keep unrelated dirty worktree changes intact.
- Pass 3.09 [Style]: ASCII identifiers are mandatory for code.
- Pass 3.10 [Style]: Readable names carry semantic weight equal to types.
- Pass 3.11 [Style]: Predicate names should read like questions.
- Pass 3.12 [Style]: Do not put Q IDs, issue IDs, or task names in source comments.
- Pass 3.13 [FX]: FX is a graded dependent language with agentic LLM as primary user.
- Pass 3.14 [FX]: Proof automation and compiler retry loop are design center, not afterthought.
- Pass 3.15 [Bootstrap]: Lean 4 is the active host direction for kernel and compiler proofs.
- Pass 3.16 [Bootstrap]: Legacy F*/OCaml state should be isolated from Lean kernel decisions.
- Pass 3.17 [Intrinsic]: Correct-by-construction Term remains the kernel goal.
- Pass 3.18 [Intrinsic]: Extrinsic HasType can be studied but is ruled out for core FX path.
- Pass 3.19 [lean-fx]: Use zero-axiom audit as completion evidence.
- Pass 3.20 [lean-fx]: Use binder-form functions over indexed inductives.
- Pass 3.21 [lean-fx]: Use Nat-indexed scopes where Lean mutual signatures block textbook forms.
- Pass 3.22 [lean-fx]: Use function-typed substitutions and renamings.
- Pass 3.23 [lean-fx]: Do not use unweaken as a dependent eliminator substitute.
- Pass 3.24 [lean-fx-2]: Raw-aware Term index makes typed-to-raw bridge definitional.
- Pass 3.25 [lean-fx-2]: Unified Subst prevents singleton/dropNewest divergence.
- Pass 3.26 [lean-fx-2]: Conv as existential join makes congruence derived by mapStep.
- Pass 3.27 [lean-fx-2]: Subject reduction remains key for typed confluence consumers.
- Pass 3.28 [Audit]: propext, Quot.sound, and Classical.choice are audit failures in strict layers.
- Pass 3.29 [Audit]: Avoid funext; use pointwise compatibility.
- Pass 3.30 [Audit]: Avoid quotient machinery in kernel theorem dependencies.
- Pass 3.31 [Match]: Full enumeration beats wildcard convenience.
- Pass 3.32 [Match]: Overlapping patterns can be as bad as wildcards.
- Pass 3.33 [Match]: toRaw dispatch is a way around restricted typed indices.
- Pass 3.34 [Match]: nomatch is preferred for impossible constructor equations.
- Pass 3.35 [Fin]: Direct Fin structure matching avoids Fin.cases propext dependency.
- Pass 3.36 [Subst]: BHKM ladder supplies fusion laws in strict order.
- Pass 3.37 [Subst]: Allais simulation supplies paired-environment outer structure.
- Pass 3.38 [Cumul]: Cumulativity as syntax constructor breaks level-coherent substitution.
- Pass 3.39 [Cumul]: Use ConvCumulHomo plus viaUp shim or dispatch when heterogeneity is real.
- Pass 3.40 [Cumul]: Kripke validity belongs later in checker soundness, not immediate CUMUL subst.
- Pass 3.41 [Confluence]: Typed cd_lemma chain output forced cd-monotonicity strategy.
- Pass 3.42 [Confluence]: Eta needs separate opt-in treatment.
- Pass 3.43 [WHNF]: Raw WHNF soundness gives reachability, not completeness.
- Pass 3.44 [Parser]: EOF and progress checks are mandatory in recovery loops.
- Pass 3.45 [Parser]: Agent-generated malformed input is normal workload.
- Pass 3.46 [Surface]: String.toList and friends are axiom-leaking boundaries.
- Pass 3.47 [Surface]: String.ofList is useful for clean construction.
- Pass 3.48 [LegacyZ3]: z3-iprit tuning values are eager 10 and lazy 24.
- Pass 3.49 [LegacyZ3]: Prims WP combinator patterns caused severe instantiation blowup.
- Pass 3.50 [LegacyFStarX]: DefCache must account for non-fatal errors before storing pass entries.
- Pass 3.51 [LegacyFStarX]: WP phase1 uvar embedding can make phase2 unsound if stale.
- Pass 3.52 [Refs]: Check BiSikkel/Sikkel for modal type theory patterns.
- Pass 3.53 [Refs]: Check smpst-sr-smer for session type mechanization.
- Pass 3.54 [Refs]: Check CompCert for verified compiler simulation structure.
- Pass 3.55 [Refs]: Check Lean source for match compiler and Eq/HEq behavior.
- Pass 4.01 [Authority]: Use this digest as memory import, not as a replacement for current source.
- Pass 4.02 [Authority]: When a completion claim matters, rebuild or inspect the specific declaration.
- Pass 4.03 [StaleRule]: Mandatory root full-spec preflight is stale for Codex lean-fx behavior.
- Pass 4.04 [StaleRule]: Root specs remain valuable when task touches language design or parser spec alignment.
- Pass 4.05 [Workflow]: No worktrees, no background agents, no hidden parallel branches.
- Pass 4.06 [Workflow]: Prefer targeted implementation after enough context over repeated broad scans.
- Pass 4.07 [Git]: Never reset, checkout, or amend without explicit user direction.
- Pass 4.08 [Git]: Keep unrelated dirty worktree changes intact.
- Pass 4.09 [Style]: ASCII identifiers are mandatory for code.
- Pass 4.10 [Style]: Readable names carry semantic weight equal to types.
- Pass 4.11 [Style]: Predicate names should read like questions.
- Pass 4.12 [Style]: Do not put Q IDs, issue IDs, or task names in source comments.
- Pass 4.13 [FX]: FX is a graded dependent language with agentic LLM as primary user.
- Pass 4.14 [FX]: Proof automation and compiler retry loop are design center, not afterthought.
- Pass 4.15 [Bootstrap]: Lean 4 is the active host direction for kernel and compiler proofs.
- Pass 4.16 [Bootstrap]: Legacy F*/OCaml state should be isolated from Lean kernel decisions.
- Pass 4.17 [Intrinsic]: Correct-by-construction Term remains the kernel goal.
- Pass 4.18 [Intrinsic]: Extrinsic HasType can be studied but is ruled out for core FX path.
- Pass 4.19 [lean-fx]: Use zero-axiom audit as completion evidence.
- Pass 4.20 [lean-fx]: Use binder-form functions over indexed inductives.
- Pass 4.21 [lean-fx]: Use Nat-indexed scopes where Lean mutual signatures block textbook forms.
- Pass 4.22 [lean-fx]: Use function-typed substitutions and renamings.
- Pass 4.23 [lean-fx]: Do not use unweaken as a dependent eliminator substitute.
- Pass 4.24 [lean-fx-2]: Raw-aware Term index makes typed-to-raw bridge definitional.
- Pass 4.25 [lean-fx-2]: Unified Subst prevents singleton/dropNewest divergence.
- Pass 4.26 [lean-fx-2]: Conv as existential join makes congruence derived by mapStep.
- Pass 4.27 [lean-fx-2]: Subject reduction remains key for typed confluence consumers.
- Pass 4.28 [Audit]: propext, Quot.sound, and Classical.choice are audit failures in strict layers.
- Pass 4.29 [Audit]: Avoid funext; use pointwise compatibility.
- Pass 4.30 [Audit]: Avoid quotient machinery in kernel theorem dependencies.
- Pass 4.31 [Match]: Full enumeration beats wildcard convenience.
- Pass 4.32 [Match]: Overlapping patterns can be as bad as wildcards.
- Pass 4.33 [Match]: toRaw dispatch is a way around restricted typed indices.
- Pass 4.34 [Match]: nomatch is preferred for impossible constructor equations.
- Pass 4.35 [Fin]: Direct Fin structure matching avoids Fin.cases propext dependency.
- Pass 4.36 [Subst]: BHKM ladder supplies fusion laws in strict order.
- Pass 4.37 [Subst]: Allais simulation supplies paired-environment outer structure.
- Pass 4.38 [Cumul]: Cumulativity as syntax constructor breaks level-coherent substitution.
- Pass 4.39 [Cumul]: Use ConvCumulHomo plus viaUp shim or dispatch when heterogeneity is real.
- Pass 4.40 [Cumul]: Kripke validity belongs later in checker soundness, not immediate CUMUL subst.
- Pass 4.41 [Confluence]: Typed cd_lemma chain output forced cd-monotonicity strategy.
- Pass 4.42 [Confluence]: Eta needs separate opt-in treatment.
- Pass 4.43 [WHNF]: Raw WHNF soundness gives reachability, not completeness.
- Pass 4.44 [Parser]: EOF and progress checks are mandatory in recovery loops.
- Pass 4.45 [Parser]: Agent-generated malformed input is normal workload.
- Pass 4.46 [Surface]: String.toList and friends are axiom-leaking boundaries.
- Pass 4.47 [Surface]: String.ofList is useful for clean construction.
- Pass 4.48 [LegacyZ3]: z3-iprit tuning values are eager 10 and lazy 24.
- Pass 4.49 [LegacyZ3]: Prims WP combinator patterns caused severe instantiation blowup.
- Pass 4.50 [LegacyFStarX]: DefCache must account for non-fatal errors before storing pass entries.
- Pass 4.51 [LegacyFStarX]: WP phase1 uvar embedding can make phase2 unsound if stale.
- Pass 4.52 [Refs]: Check BiSikkel/Sikkel for modal type theory patterns.
- Pass 4.53 [Refs]: Check smpst-sr-smer for session type mechanization.
- Pass 4.54 [Refs]: Check CompCert for verified compiler simulation structure.
- Pass 4.55 [Refs]: Check Lean source for match compiler and Eq/HEq behavior.
- Pass 5.01 [Authority]: Use this digest as memory import, not as a replacement for current source.
- Pass 5.02 [Authority]: When a completion claim matters, rebuild or inspect the specific declaration.
- Pass 5.03 [StaleRule]: Mandatory root full-spec preflight is stale for Codex lean-fx behavior.
- Pass 5.04 [StaleRule]: Root specs remain valuable when task touches language design or parser spec alignment.
- Pass 5.05 [Workflow]: No worktrees, no background agents, no hidden parallel branches.
- Pass 5.06 [Workflow]: Prefer targeted implementation after enough context over repeated broad scans.
- Pass 5.07 [Git]: Never reset, checkout, or amend without explicit user direction.
- Pass 5.08 [Git]: Keep unrelated dirty worktree changes intact.
- Pass 5.09 [Style]: ASCII identifiers are mandatory for code.
- Pass 5.10 [Style]: Readable names carry semantic weight equal to types.
- Pass 5.11 [Style]: Predicate names should read like questions.
- Pass 5.12 [Style]: Do not put Q IDs, issue IDs, or task names in source comments.
- Pass 5.13 [FX]: FX is a graded dependent language with agentic LLM as primary user.
- Pass 5.14 [FX]: Proof automation and compiler retry loop are design center, not afterthought.
- Pass 5.15 [Bootstrap]: Lean 4 is the active host direction for kernel and compiler proofs.
- Pass 5.16 [Bootstrap]: Legacy F*/OCaml state should be isolated from Lean kernel decisions.
- Pass 5.17 [Intrinsic]: Correct-by-construction Term remains the kernel goal.
- Pass 5.18 [Intrinsic]: Extrinsic HasType can be studied but is ruled out for core FX path.
- Pass 5.19 [lean-fx]: Use zero-axiom audit as completion evidence.
- Pass 5.20 [lean-fx]: Use binder-form functions over indexed inductives.
- Pass 5.21 [lean-fx]: Use Nat-indexed scopes where Lean mutual signatures block textbook forms.
- Pass 5.22 [lean-fx]: Use function-typed substitutions and renamings.
- Pass 5.23 [lean-fx]: Do not use unweaken as a dependent eliminator substitute.
- Pass 5.24 [lean-fx-2]: Raw-aware Term index makes typed-to-raw bridge definitional.
- Pass 5.25 [lean-fx-2]: Unified Subst prevents singleton/dropNewest divergence.
- Pass 5.26 [lean-fx-2]: Conv as existential join makes congruence derived by mapStep.
- Pass 5.27 [lean-fx-2]: Subject reduction remains key for typed confluence consumers.
- Pass 5.28 [Audit]: propext, Quot.sound, and Classical.choice are audit failures in strict layers.
- Pass 5.29 [Audit]: Avoid funext; use pointwise compatibility.
- Pass 5.30 [Audit]: Avoid quotient machinery in kernel theorem dependencies.
- Pass 5.31 [Match]: Full enumeration beats wildcard convenience.
- Pass 5.32 [Match]: Overlapping patterns can be as bad as wildcards.
- Pass 5.33 [Match]: toRaw dispatch is a way around restricted typed indices.
- Pass 5.34 [Match]: nomatch is preferred for impossible constructor equations.
- Pass 5.35 [Fin]: Direct Fin structure matching avoids Fin.cases propext dependency.
- Pass 5.36 [Subst]: BHKM ladder supplies fusion laws in strict order.
- Pass 5.37 [Subst]: Allais simulation supplies paired-environment outer structure.
- Pass 5.38 [Cumul]: Cumulativity as syntax constructor breaks level-coherent substitution.
- Pass 5.39 [Cumul]: Use ConvCumulHomo plus viaUp shim or dispatch when heterogeneity is real.
- Pass 5.40 [Cumul]: Kripke validity belongs later in checker soundness, not immediate CUMUL subst.
- Pass 5.41 [Confluence]: Typed cd_lemma chain output forced cd-monotonicity strategy.
- Pass 5.42 [Confluence]: Eta needs separate opt-in treatment.
- Pass 5.43 [WHNF]: Raw WHNF soundness gives reachability, not completeness.
- Pass 5.44 [Parser]: EOF and progress checks are mandatory in recovery loops.
- Pass 5.45 [Parser]: Agent-generated malformed input is normal workload.
- Pass 5.46 [Surface]: String.toList and friends are axiom-leaking boundaries.
- Pass 5.47 [Surface]: String.ofList is useful for clean construction.
- Pass 5.48 [LegacyZ3]: z3-iprit tuning values are eager 10 and lazy 24.
- Pass 5.49 [LegacyZ3]: Prims WP combinator patterns caused severe instantiation blowup.
- Pass 5.50 [LegacyFStarX]: DefCache must account for non-fatal errors before storing pass entries.
- Pass 5.51 [LegacyFStarX]: WP phase1 uvar embedding can make phase2 unsound if stale.
- Pass 5.52 [Refs]: Check BiSikkel/Sikkel for modal type theory patterns.
- Pass 5.53 [Refs]: Check smpst-sr-smer for session type mechanization.
- Pass 5.54 [Refs]: Check CompCert for verified compiler simulation structure.
- Pass 5.55 [Refs]: Check Lean source for match compiler and Eq/HEq behavior.
- Pass 6.01 [Authority]: Use this digest as memory import, not as a replacement for current source.
- Pass 6.02 [Authority]: When a completion claim matters, rebuild or inspect the specific declaration.
- Pass 6.03 [StaleRule]: Mandatory root full-spec preflight is stale for Codex lean-fx behavior.
- Pass 6.04 [StaleRule]: Root specs remain valuable when task touches language design or parser spec alignment.
- Pass 6.05 [Workflow]: No worktrees, no background agents, no hidden parallel branches.
- Pass 6.06 [Workflow]: Prefer targeted implementation after enough context over repeated broad scans.
- Pass 6.07 [Git]: Never reset, checkout, or amend without explicit user direction.
- Pass 6.08 [Git]: Keep unrelated dirty worktree changes intact.
- Pass 6.09 [Style]: ASCII identifiers are mandatory for code.
- Pass 6.10 [Style]: Readable names carry semantic weight equal to types.
- Pass 6.11 [Style]: Predicate names should read like questions.
- Pass 6.12 [Style]: Do not put Q IDs, issue IDs, or task names in source comments.
- Pass 6.13 [FX]: FX is a graded dependent language with agentic LLM as primary user.
- Pass 6.14 [FX]: Proof automation and compiler retry loop are design center, not afterthought.
- Pass 6.15 [Bootstrap]: Lean 4 is the active host direction for kernel and compiler proofs.
- Pass 6.16 [Bootstrap]: Legacy F*/OCaml state should be isolated from Lean kernel decisions.
- Pass 6.17 [Intrinsic]: Correct-by-construction Term remains the kernel goal.
- Pass 6.18 [Intrinsic]: Extrinsic HasType can be studied but is ruled out for core FX path.
- Pass 6.19 [lean-fx]: Use zero-axiom audit as completion evidence.
- Pass 6.20 [lean-fx]: Use binder-form functions over indexed inductives.
- Pass 6.21 [lean-fx]: Use Nat-indexed scopes where Lean mutual signatures block textbook forms.
- Pass 6.22 [lean-fx]: Use function-typed substitutions and renamings.
- Pass 6.23 [lean-fx]: Do not use unweaken as a dependent eliminator substitute.
- Pass 6.24 [lean-fx-2]: Raw-aware Term index makes typed-to-raw bridge definitional.
- Pass 6.25 [lean-fx-2]: Unified Subst prevents singleton/dropNewest divergence.
- Pass 6.26 [lean-fx-2]: Conv as existential join makes congruence derived by mapStep.
- Pass 6.27 [lean-fx-2]: Subject reduction remains key for typed confluence consumers.
- Pass 6.28 [Audit]: propext, Quot.sound, and Classical.choice are audit failures in strict layers.
- Pass 6.29 [Audit]: Avoid funext; use pointwise compatibility.
- Pass 6.30 [Audit]: Avoid quotient machinery in kernel theorem dependencies.
- Pass 6.31 [Match]: Full enumeration beats wildcard convenience.
- Pass 6.32 [Match]: Overlapping patterns can be as bad as wildcards.
- Pass 6.33 [Match]: toRaw dispatch is a way around restricted typed indices.
- Pass 6.34 [Match]: nomatch is preferred for impossible constructor equations.
- Pass 6.35 [Fin]: Direct Fin structure matching avoids Fin.cases propext dependency.
- Pass 6.36 [Subst]: BHKM ladder supplies fusion laws in strict order.
- Pass 6.37 [Subst]: Allais simulation supplies paired-environment outer structure.
- Pass 6.38 [Cumul]: Cumulativity as syntax constructor breaks level-coherent substitution.
- Pass 6.39 [Cumul]: Use ConvCumulHomo plus viaUp shim or dispatch when heterogeneity is real.
- Pass 6.40 [Cumul]: Kripke validity belongs later in checker soundness, not immediate CUMUL subst.
- Pass 6.41 [Confluence]: Typed cd_lemma chain output forced cd-monotonicity strategy.
- Pass 6.42 [Confluence]: Eta needs separate opt-in treatment.
- Pass 6.43 [WHNF]: Raw WHNF soundness gives reachability, not completeness.
- Pass 6.44 [Parser]: EOF and progress checks are mandatory in recovery loops.
- Pass 6.45 [Parser]: Agent-generated malformed input is normal workload.
- Pass 6.46 [Surface]: String.toList and friends are axiom-leaking boundaries.
- Pass 6.47 [Surface]: String.ofList is useful for clean construction.
- Pass 6.48 [LegacyZ3]: z3-iprit tuning values are eager 10 and lazy 24.
- Pass 6.49 [LegacyZ3]: Prims WP combinator patterns caused severe instantiation blowup.
- Pass 6.50 [LegacyFStarX]: DefCache must account for non-fatal errors before storing pass entries.
- Pass 6.51 [LegacyFStarX]: WP phase1 uvar embedding can make phase2 unsound if stale.
- Pass 6.52 [Refs]: Check BiSikkel/Sikkel for modal type theory patterns.
- Pass 6.53 [Refs]: Check smpst-sr-smer for session type mechanization.
- Pass 6.54 [Refs]: Check CompCert for verified compiler simulation structure.
- Pass 6.55 [Refs]: Check Lean source for match compiler and Eq/HEq behavior.

## Import Decisions By File
01. `MEMORY.md` decision=import; note=Master Claude FX memory index; useful but contains stale full-spec rule.
02. `bug_pervasives_native_leak.md` decision=legacy-context; note=FStarX deferred Pervasives.Native bug from apostrophe type variables; legacy compiler note.
03. `feedback_ascii_only.md` decision=import; note=ASCII-only identifier rule; import as active project style.
04. `feedback_lean_binder_form.md` decision=import; note=Binder-form over indexed inductives; import as active Lean rule.
05. `feedback_lean_cd_dominates_unary_wrapper.md` decision=import; note=parWithBi workaround for opaque cd_dominates witnesses; import as proof pattern.
06. `feedback_lean_closed_type_sr.md` decision=import; note=Closed-type subject reduction pattern for nat/bool/unit; import as proof pattern.
07. `feedback_lean_cumul_subst_mismatch.md` decision=import; note=Ty.cumul constructor breaks substitution; import as architectural rule.
08. `feedback_lean_dispatch_sum_dependent_output.md` decision=import; note=Dispatch sum for heterogeneous Prop walls; import as proof/API pattern.
09. `feedback_lean_fin_cases_axiom.md` decision=import; note=Avoid Fin.cases; direct Fin structure matching; import as active Lean rule.
10. `feedback_lean_free_type_via_suffices.md` decision=import; note=Free type indices via suffices for strong uniqueness; import as proof pattern.
11. `feedback_lean_function_typed_subst.md` decision=import; note=Function-typed Subst avoids Nat arithmetic walls; import as design rule.
12. `feedback_lean_indexed_partial_match.md` decision=import; note=Indexed partial match leaks propext; import as active Lean rule.
13. `feedback_lean_mapStep_pattern.md` decision=import; note=mapStep lifters remove repetitive cong inductions; import as refactor pattern.
14. `feedback_lean_match_arity_axioms.md` decision=import; note=Hoist Nat indices out of pattern arity; import as active Lean rule.
15. `feedback_lean_match_propext_recipe.md` decision=import; note=Surface-layer match compiler recipes; import when working lexer/parser/schema.
16. `feedback_lean_match_witness_pattern.md` decision=import; note=match-with-witness and injection patterns; import as proof pattern.
17. `feedback_lean_mutual_index_rule.md` decision=negative-decision; note=Lean mutual index limitation; import facts, but extrinsic alternative is ruled out.
18. `feedback_lean_mutual_positivity.md` decision=import; note=Nat-indexed Allais-McBride encoding; import as Lean architecture note.
19. `feedback_lean_paired_predicate_pattern.md` decision=import; note=Use paired predicate for Step.par plus isBi; import as proof pattern.
20. `feedback_lean_pattern3_homogeneous_level.md` decision=import; note=Allais paired-env shipped homogeneous-level; import as cumul note.
21. `feedback_lean_propext_cons_index.md` decision=import; note=Avoid cons-specialized indexed matches; use Fin plus varType; import.
22. `feedback_lean_reducible_weaken.md` decision=import; note=@[reducible] on shape functions in ctor signatures; import.
23. `feedback_lean_subst_lemmas.md` decision=snapshot-verify-before-use; note=Term.subst infrastructure path; import as historical technique, verify current.
24. `feedback_lean_universe_constructor_block.md` decision=import; note=Level-constraining constructors need Eq witnesses; import.
25. `feedback_lean_unweaken_axiom_trap.md` decision=import; note=Ty.unweaken is axiom trap; use real substitution; import.
26. `feedback_lean_zero_axiom_match.md` decision=import; note=Zero-axiom match recipe; import as active Lean rule.
27. `feedback_no_task_ids_in_code.md` decision=import; note=No task IDs in source comments; import active style rule.
28. `feedback_prims_patterns.md` decision=legacy-context; note=Never add patterns to Prims WP combinators; legacy F* rule.
29. `feedback_read_full_specs.md` decision=stale-ignore-for-lean-fx; note=STALE for Codex lean-fx behavior; do not import mandatory preflight.
30. `feedback_readable_names.md` decision=import; note=Narrative names and question verbs; import active style rule.
31. `feedback_typed_inversion_breakthrough.md` decision=import; note=Term.toRaw plus HEq source inversion; import proof pattern.
32. `feedback_workflows.md` decision=import; note=No worktrees/background agents; action bias; import active workflow.
33. `project_build_state.md` decision=snapshot-verify-before-use; note=Old 2026-03-26 build state; snapshot only, verify before use.
34. `project_calc_chain_bug.md` decision=snapshot-verify-before-use; note=Legacy calc-chain incomplete quantifier bug; import as old F* caution.
35. `project_defcache_fix.md` decision=legacy-context; note=DefCache false-pass fix; import as legacy compiler caution.
36. `project_fx_agentic_design.md` decision=import; note=FX primary user agentic LLM; import project philosophy.
37. `project_lean_bootstrap.md` decision=import; note=Lean 4 bootstrap pivot; import as active direction.
38. `project_lean_fx_2_phase6_complete.md` decision=snapshot-verify-before-use; note=lean-fx-2 phase snapshot; import but verify source before relying.
39. `project_lean_fx_2_state.md` decision=snapshot-verify-before-use; note=lean-fx-2 architecture snapshot; import active architecture, verify state.
40. `project_lean_fx_confluence_strategy.md` decision=snapshot-verify-before-use; note=Typed confluence strategy; historical but useful proof map.
41. `project_lean_fx_state.md` decision=snapshot-verify-before-use; note=lean-fx intrinsic kernel snapshot; import architecture, verify current.
42. `project_lean_fx_v2_refactor.md` decision=snapshot-verify-before-use; note=lean-fx mega-refactor snapshot; historical, verify current.
43. `project_lean_fx_vs_lean_discipline.md` decision=import; note=What to reuse from Lean vs reimplement; import active discipline.
44. `project_parser_eof_trap.md` decision=import; note=Parser EOF/progress trap; import active parser rule.
45. `project_phase_c_blockers.md` decision=snapshot-verify-before-use; note=Bridge beta blockers; historical lean-fx map, verify current.
46. `project_seed_retry_bug.md` decision=legacy-context; note=Legacy seed retry bug; import as F* compiler caution.
47. `project_stage1_last_error.md` decision=snapshot-verify-before-use; note=Legacy stage1 bootstrap divergence; snapshot only.
48. `project_term_const.md` decision=import; note=Term.const global environment design; import architecture note.
49. `project_test_architecture.md` decision=legacy-context; note=Legacy 4-tier tests; import if working FStarX tests.
50. `project_ulib_verification.md` decision=snapshot-verify-before-use; note=Legacy ulib Z3 verification tactics; import as old F* note.
51. `project_w83_confluence_strategy.md` decision=snapshot-verify-before-use; note=W8.3 cd-monotonicity path; historical proof map.
52. `project_w83_subst_witnessed_blocker.md` decision=snapshot-verify-before-use; note=Witnessed subst dependency chain; historical proof map.
53. `project_w8_complete.md` decision=snapshot-verify-before-use; note=W8 completion snapshot; verify source before relying.
54. `project_wave9_status.md` decision=snapshot-verify-before-use; note=Wave 9 cascade obstruction; historical proof map.
55. `project_wp_encoding_bug.md` decision=legacy-context; note=Legacy WP else-branch bug; import caution.
56. `project_z3_tuning.md` decision=legacy-context; note=z3-iprit tuned thresholds; import legacy solver rule.
57. `reference_audit_axiom_semantics.md` decision=import; note=AXIOMS.md summary; import but treat AXIOMS.md as canonical.
58. `reference_brrr_project.md` decision=import; note=go-brrr reference overview; import context.
59. `reference_build_targets.md` decision=legacy-context; note=Legacy build/test targets; verify before use.
60. `reference_cumul_subst_pattern_decision.md` decision=import; note=Cumul-subst pattern matrix; import active architectural decision.
61. `reference_fx_refs_dir.md` decision=import; note=fx-refs directory map; import as reference lookup guide.
62. `reference_lean4_source_clone.md` decision=import; note=Lean source clone paths; import troubleshooting guide.
63. `reference_pattern_allais_simulation.md` decision=import; note=Allais paired-env pattern; import cumul architecture.
64. `reference_pattern_bhkm_ladder.md` decision=import; note=BHKM ladder; import subst architecture.
65. `reference_pattern_cwf_semantic.md` decision=import; note=CwF semantic pattern; import future modal architecture.
66. `reference_pattern_extrinsic_wellscoped.md` decision=negative-decision; note=Extrinsic pattern ruled out; keep as non-choice.
67. `reference_pattern_kripke_validity.md` decision=import; note=Kripke validity for Day 8 soundness, not CUMUL-1.7.
68. `reference_rm_alias_trap.md` decision=import; note=rm alias trap; import caution, still require approval for deletion.
69. `reference_z3_binary.md` decision=legacy-context; note=Custom Z3 and OCaml environment; legacy reference.
70. `user_profile.md` decision=import; note=User profile; import communication/project preferences.

## Final Checklist
- When asked to continue lean-fx-2 sprint work, locate kernel-sprint.md and current task state first.
- When asked to mirror Claude tasks, use ~/.claude/tasks JSON records as source of truth.
- When asked to read lean-fx tree, prune .lake on first pass.
- When a proof leaks propext, inspect match shape before inventing large theory.
- When a theorem seems impossible, search imported proof patterns before escalating architecture.
- When a memory says complete, verify with lake build and audit target before repeating complete.
- When a memory says blocked, verify current source because later memories may have resolved it.
- When legacy FStarX notes appear, check whether task actually concerns old compiler or Lean path.
- When using reference codebases, cite which reference informed the implementation decision.
- When editing this file, preserve the stale-rule warning near the top.

