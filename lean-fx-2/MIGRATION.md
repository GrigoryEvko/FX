# Migration — lean-fx → lean-fx-2

## Strategy: coexist then cutover

lean-fx and lean-fx-2 develop in parallel.  When lean-fx-2 reaches feature parity (Phases 1–11 of `ROADMAP.md` complete), cutover.  Until then both build independently; `parent/CLAUDE.md` continues to reference lean-fx as the active kernel.

## What carries over from lean-fx

The following lean-fx artifacts are copied or referenced verbatim:

* **`LeanFX/Sketch/Wave9.lean`** — copy to `LeanFX2/Sketch/Wave9.lean` as the architectural prototype reference.  Already ships in this skeleton.
* **`LeanFX/Mode/`** — port to `Foundation/Mode.lean` (consolidated single file).  Mode 2-category infrastructure is sound; no architectural changes needed.
* **`LeanFX/Syntax/RawTerm.lean`** — port to `Foundation/RawTerm.lean`.  Raw-side semantics unchanged.
* **`LeanFX/Syntax/RawSubst.lean`** — port to `Foundation/RawSubst.lean`.  Drop `RawTermSubst.dropNewest` (singleton-of-unit suffices).
* **`LeanFX/Syntax/Reduction/RawPar.lean`** + raw confluence chain — port verbatim (`Reduction/RawPar.lean`).  Raw side is correct; bridge changes are kernel-side.

## What gets *deleted* during cutover

These exist in lean-fx as scaffolding for the inline-edit migration that didn't compose.  lean-fx-2 doesn't need them:

* `Term.toRaw_cast`, `Term.toRaw_rename`, `Term.toRaw_subst`, `Term.toRaw_subst0`, `Term.toRaw_subst0_term` — all collapse to `rfl` (raw is the index)
* `Term.subst0_term_subst_HEq` — no `RawConsistent` issue
* `TermSubst.RawConsistent`, `TermSubst.lift_RawConsistent`, `TermSubst.termSingleton_RawConsistent` — definitionally satisfied
* `Subst.singleton` vs `Subst.termSingleton` distinction — unified to single `Subst.singleton`
* `Subst.singleton_equiv_termSingleton_unit`, `Ty.subst0_eq_termSingleton_unit` — vacuous after unification
* W9.B1.1 `Term.appPi` `resultEq` parameter — type index supersedes
* W9.B1.2 `Term.snd` `resultEq` parameter — type index supersedes
* `Reduction/CdLemmaStarWithBi.lean`, `Reduction/ParStarWithBi.lean`, `Reduction/ParCompatibleIsBi.lean`, `Reduction/ParSubstWitnessed.lean`, `Reduction/ParSubstPointwise.lean` — paired-predicate workarounds for lean-fx's typed inversion gap; raw-aware Term sidesteps them
* `Reduction/ParToRawBridge.lean`'s 4 sorries — close as `rfl + RawStep.par.<ctor>` cases
* `LeanFX/Stash/` — no quarantined files in lean-fx-2
* `Subst.singleton_forTy_eq_termSingleton`, `Ty.subst_termSingleton_subst_commute`, `Subst.termSingleton_optionalRenamingSquare` — Wave 9 prep helpers, no longer needed
* W14 mapStep refactors at Conv level — Conv is now ∃-StepStar; cong rules become 1-line corollaries.  mapStep stays for StepStar.

## What gets *reworked* (not just ported)

These lean-fx artifacts contain correct math but need re-architecting:

* **W8 confluence chain** (`cd_lemma`, `diamond`, `parStar.confluence`, `Conv.canonical_form`) — reprove in Layer 3.  Expect ~30% smaller because:
  * No HEq cast threading through `Subst.singleton`/`Subst.termSingleton` distinctions
  * No paired-predicate `parStarWithBi` workaround for typed inversions
  * Bridge cases are `rfl + ctor`
* **AuditAll** — replace lean-fx's manually-maintained 660 `#assert_no_axioms` lines with auto-generated `Tools/AuditGen.lean` tactic
* **Conv** (the relation) — switch from inductive form (with 13 cong rules + mapStep refactor) to ∃-StepStar (uniform, decidable conversion much cleaner).  This is W10 design baked in
* **η-reduction** — isolate to opt-in `Step.eta` namespace (lean-fx mixed η into Step.par.isBi exclusion gates)
* **Cumulativity** — Conv rule, not Ty constructor (lean-fx v1.29 revert had the right diagnosis)

## What gets *deferred* (not in lean-fx-2 yet)

* Frontend decimal arithmetic (fx_design.md §3.1) — postponed to post-Phase-13
* Hardware/synthesis layer (fx_design.md §18) — separate project
* Distribution / package manager (fx_design.md §25) — far future

## Status check (2026-05-07)

Items already shipped (verifiable via `lake build LeanFX2`):

* ✅ Phase 0 (skeleton), 1 (Foundation), 2 (Term), 4 (Confluence raw),
  5 (Bridge), 6 (HoTT incl. real-theorem Univalence + funext), 8
  (Graded), 13 (Tools)
* ✅ Phase 3 D2.10 Compat — 28 of 28 typed cong rename+subst compat
  rules done at zero axioms (2026-05-07; budget ratcheted to 0)
* 🚧 Phase 9, 10, 11 partial
* ❌ Phase 7 (Modal D4.x) NOT STARTED
* ❌ Phase 12 (Pipeline) TODO
* ❌ Phase 15 cutover deferred

See ROADMAP.md "Critical-path summary" for the 7 load-bearing
remaining tasks.

## Cutover checklist (gated on critical path)

**Cutover MUST NOT fire** until ALL these v1.0 critical-path items
close (per ROADMAP.md):

* [x] D2.10 typed Step.par cong rename+subst compat — ✅ DONE
      2026-05-07 (28 of 28 shipped at zero axioms; tracker #1314)
* [ ] M06 Phase 7 subject reduction at arrow types (#1275; D2.10
      blocker cleared, ready to start)
* [ ] PHASE7-CONV-TRANS typed Conv.trans (#1504, blocked by M06)
* [ ] K07.1-8 dep-motive eliminator refactors (#1516-1523, 8 ctors)
* [ ] D2.5.1-2 typed cubical β rules transp/hcomp (#1527-1528;
      D2.5.3 #1529 ✅ verified — `Step.betaGlueElimIntro` IS the
      typed glueBeta)
* [ ] WEAK-FX2-03 retire 121 manufactured-witness wrappers (#1502)
* [ ] D4 modal layer (#1328-1336)
* [ ] D6.4-6.6 Surface Parse/Print/Roundtrip (#1354-1356)
* [ ] D6.7-6.9 Elab/ElabSoundness/ElabCompleteness (#1357-1359)
* [ ] D6.12 Pipeline.lean end-to-end (#1362)

When ALL of the above are closed, run the cutover sequence:

1. [ ] Verify `lake build LeanFX2` is green AND every phase shows
       ✅ in ROADMAP.md
2. [ ] Verify zero axioms via the strict harness:
       `lake build LeanFX2 2>&1 | grep -E "axiom audit (failed|FAILED)"`
       returns nothing
3. [ ] Verify zero sorries: `rg --type lean -n '\bsorry\b' LeanFX2/`
       returns NO matches in declaration bodies (docstring/keyword
       mentions are OK).  Univalence is NOT exempt — it is a real
       theorem with body `Conv.fromStep Step.eqType` per
       `HoTT/Univalence.lean`
4. [ ] Verify dashboard debt counts at zero or expected ratchet
       targets:
       - Compat coverage: 0/28 (all cong rules covered)
       - Conv cong: 75/75 covered
       - Bridge encoding: load-bearing ratio at expected level
       - Manufactured-witness wrappers: 0
5. [ ] Smoke test parity: every smoke test in
       `lean-fx/LeanFX/Syntax/Smoke.lean` has an analog in
       `lean-fx-2/LeanFX2/Smoke/`
6. [ ] W8 confluence chain delivers same theorems as
       `lean-fx/LeanFX/Syntax/Reduction/Confluence.lean`
7. [ ] Bridge sorries closed:
       `grep -c sorry lean-fx-2/LeanFX2/Bridge.lean` returns 0
8. [ ] `git mv lean-fx lean-fx.deprecated && git mv lean-fx-2 lean-fx`
9. [ ] Update `/root/iprit/FX/CLAUDE.md`'s lean-fx references
10. [ ] Update memory entries:
        `project_lean_fx_state.md` notes the cutover;
        `project_lean_fx_v2_refactor.md` archived
11. [ ] Tag the parent FX repo at the cutover commit
12. [ ] D7.11 v1.0 git tag + release manifest (#1374)

## What to keep from lean-fx forever

Even after cutover, `lean-fx.deprecated/` stays around as:

* Reference for design decisions (5+ versions of architectural evolution documented in commit history)
* Regression bench (compare lean-fx-2 confluence proofs against lean-fx's known-good versions)
* Memory archaeology for design analysis (gaps.json, design_analysis.json reference lean-fx version semantics)

Don't delete the deprecated tree.  It's a record.

## Memory note updates at cutover

Update these memory entries:

* `project_lean_fx_state.md` — update with lean-fx-2 cutover date + new architecture pointer
* `project_lean_fx_v2_refactor.md` — mark complete; superseded by lean-fx-2
* `project_wave9_status.md` — mark Wave 9 complete (delivered via lean-fx-2 from-scratch construction)
* New: `project_lean_fx_2_state.md` — lean-fx-2 architectural overview + active phase pointer
