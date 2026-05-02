# Roadmap — lean-fx-2

Phasing from skeleton → working kernel → full engine.  Each phase is one elite-hunter-resolver agent run (~250–500 tool calls).

## Phase 0 — Skeleton (CURRENT)

* [x] Directory layout
* [x] Build configs (lakefile, lean-toolchain, .gitignore)
* [x] Documentation: AXIOMS.md, README.md, ARCHITECTURE.md, ROADMAP.md, MIGRATION.md
* [x] Stub files for all layers with substantial docstrings
* [x] Build green (empty namespace declarations + import wiring)

## Phase 1 — Foundation (Layer 0)

* [ ] `Foundation/Mode.lean` — port from `lean-fx/LeanFX/Mode/`
* [ ] `Foundation/RawTerm.lean` — port from lean-fx with cleanups
* [ ] `Foundation/RawSubst.lean` — port + simplify (no dropNewest)
* [ ] `Foundation/Ty.lean` — port + add Modal/Refine ctors as foundational
* [ ] `Foundation/Subst.lean` — port + UNIFY singleton (no termSingleton variant)
* [ ] `Foundation/Context.lean` — port

Acceptance: build green, AuditAll passes, smoke tests for raw substitution + type substitution work.

## Phase 2 — Term (Layer 1)

* [ ] `Term.lean` — raw-aware Term inductive (per `LeanFX/Sketch/Wave9.lean` blueprint)
* [ ] `Term/Rename.lean` — typed renaming with raw index propagation
* [ ] `Term/Subst.lean` — TermSubst + Term.subst + Term.subst0 (single-binder)
* [ ] `Term/Pointwise.lean` — pointwise lemmas
* [ ] `Term/ToRaw.lean` — projection (rfl)

Acceptance: `Term.toRaw_rename = rfl`, `Term.toRaw_subst = rfl` (where types align).  Smoke tests for typed reduction examples.

## Phase 3 — Reduction (Layer 2)

* [ ] `Reduction/Step.lean` — Step + cong + β/ι rules.  Source/target raw indices.
* [ ] `Reduction/StepStar.lean` — RT closure + mapStep
* [ ] `Reduction/Conv.lean` — **Conv as ∃-StepStar** (this is W10 design — bake in here)
* [ ] `Reduction/ParRed.lean` — Step.par (raw-aware β-rule's RHS uses Term.subst0 directly, no cast scaffolding)
* [ ] `Reduction/RawPar.lean` — port from lean-fx
* [ ] `Reduction/Compat.lean` — rename + subst + Step.par compat (NO RawConsistent threading)

Acceptance: rename/subst preserves Step, Step.par lifts to StepStar.

## Phase 4 — Confluence (Layer 3)

* [ ] `Confluence/Cd.lean` — Term.cd (~17 cases inline)
* [ ] `Confluence/CdLemma.lean` — Step.par.cd_lemma
* [ ] `Confluence/Diamond.lean` — diamond
* [ ] `Confluence/ChurchRosser.lean` — Step.parStar.confluence
* [ ] `Confluence/CanonicalForm.lean` — Conv.canonical_form

Acceptance: full Tait–Martin-Löf chain green, zero axioms, smoke tests pass.  This is W8 reproved cleaner (no resultEq scaffolding, smaller HEq cascade).

## Phase 5 — Bridge (Layer 4)

* [ ] `Bridge.lean` — typed→raw forward (`Step.par.toRawBridge`) closes via `RawStep.par.<ctor> witnesses` per case.  All 4 lean-fx bridge sorries dissolve here as `rfl + ctor`.

Acceptance: `Step.par.toRawBridge` total, no sorries.

## Phase 6 — HoTT (Layer 5)

* [ ] `HoTT/Identity.lean`, `HoTT/J.lean` — full dep motive J
* [ ] `HoTT/Path/{Composition,Inverse,Groupoid}.lean`
* [ ] `HoTT/Transport.lean`
* [ ] `HoTT/Equivalence.lean`, `HoTT/NTypes.lean`
* [ ] `HoTT/Univalence.lean` — postulate (long-term: derive via cubical)
* [ ] `HoTT/HIT/{Spec,Setoid,Eliminator,Examples}.lean`

Acceptance: J on refl reduces, transport laws hold, S¹ via setoid works without propext.

## Phase 7 — Modal (Layer 6)

* [ ] `Modal/Foundation.lean` — Ty.modal + Term.{modIntro,modElim,subsume} + computation rules
* [ ] `Modal/Later.lean`, `Modal/Clock.lean`
* [ ] `Modal/Bridge.lean`, `Modal/Cap.lean`, `Modal/Ghost.lean`
* [ ] `Modal/2LTT.lean`, `Modal/Adjunction.lean`

Acceptance: modal computation rules fire, free theorems extract, 2LTT layering works.

## Phase 8 — Graded (Layer 7)

* [ ] `Graded/Semiring.lean`, `Graded/GradeVector.lean`, `Graded/Ctx.lean`, `Graded/Rules.lean`
* [ ] `Graded/Instances/{Usage,Effect,Security}.lean`

Acceptance: Atkey-2018 witness term is rejected by lambda rule (Wood/Atkey 2022 corrected); canonical linear/affine examples typecheck.

## Phase 9 — Refine (Layer 8)

* [ ] `Refine/Ty.lean`, `Refine/Term.lean`, `Refine/Decidable.lean`
* [ ] `Refine/SMTCert.lean`, `Refine/SMTRecheck.lean`

Acceptance: refinement bounds-check at boundaries; SMT cert recheckable in Lean.

## Phase 10 — Algo (Layer 9)

* [ ] `Algo/WHNF.lean`, `Algo/DecConv.lean`
* [ ] `Algo/Infer.lean`, `Algo/Check.lean`, `Algo/Synth.lean`
* [ ] `Algo/Eval.lean`, `Algo/Soundness.lean`, `Algo/Completeness.lean`

Acceptance: bidirectional checker is sound and complete; fuel-bounded eval terminates on canonical examples.

## Phase 11 — Surface (Layer 10)

* [ ] `Surface/{Token,Lex,AST,Parse,Print,Roundtrip,Elab,ElabSoundness,ElabCompleteness}.lean`

Acceptance: lex/parse/print roundtrip theorem; elaboration sound + complete; smoke example fully roundtrips.

## Phase 12 — Pipeline (Layer 11)

* [ ] `Pipeline.lean` — end-to-end compose

Acceptance: end-to-end smoke from String input → typed Term → reduced value, all axiom-free.

## Phase 13 — Tools (Layer 12)

* [ ] `Tools/AuditGen.lean` — auto-generation tactic
* [ ] `Tools/AuditAll.lean` — generated gates
* [ ] `Tools/Tactics/{Cast,HEq,SimpStrip}.lean`

Acceptance: AuditAll gates auto-update; tactics simplify proofs across the kernel.

## Phase 14 — Smoke (cross-cutting)

* [ ] Per-layer `Smoke/<Layer>.lean` files with concrete examples

Acceptance: every layer has its own smoke file; failures isolated per layer.

## Phase 15 — Cutover (M+12 months estimated)

* [ ] Verify lean-fx-2 has feature parity with lean-fx
* [ ] Move `lean-fx/` → `lean-fx.deprecated/`
* [ ] Move `lean-fx-2/` → `lean-fx/`
* [ ] Update parent project imports (`/root/iprit/FX/CLAUDE.md`, frontend)

## Estimated agent budget

* Phase 0: this skeleton (in-progress)
* Phases 1–4: ~4 agents × 400 calls = 1600 calls (kernel core)
* Phases 5–7: ~3 agents × 500 calls = 1500 calls (HoTT/MTT)
* Phases 8–13: ~6 agents × 400 calls = 2400 calls (extensions + frontend)
* Phase 14–15: ~2 agents × 300 calls = 600 calls
* **Total: ~6100 tool calls / ~12 agents / 8–10 sessions**

This is comparable to the lean-fx Wave 8 confluence project's effort (~25 commits) but delivers a *complete* engine instead of just the typed Church-Rosser chain.
