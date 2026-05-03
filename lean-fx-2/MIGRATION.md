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

## Cutover checklist

When lean-fx-2 reaches Phase 11 (Surface complete):

1. [ ] Verify `lake build LeanFX2` is green with all phases 0–11
2. [ ] Verify zero axioms across kernel via AuditAll
3. [ ] Verify zero sorries: `rg --type lean -n '\bsorry\b' LeanFX2/` returns NO matches in declaration bodies (docstring/keyword mentions are OK).  Univalence is NOT exempt — it is a real theorem with body `Conv.fromStep Step.eqType` per `HoTT/Univalence.lean`
4. [ ] Smoke test parity: every smoke test in `lean-fx/LeanFX/Syntax/Smoke.lean` has an analog in `lean-fx-2/LeanFX2/Smoke/`
5. [ ] W8 confluence chain delivers same theorems as `lean-fx/LeanFX/Syntax/Reduction/Confluence.lean`
6. [ ] Bridge sorries closed (`grep -c sorry lean-fx-2/LeanFX2/Bridge.lean` returns 0)
7. [ ] `git mv lean-fx lean-fx.deprecated && git mv lean-fx-2 lean-fx`
8. [ ] Update `/root/iprit/FX/CLAUDE.md`'s lean-fx references
9. [ ] Update memory entries: `project_lean_fx_state.md` notes the cutover; `project_lean_fx_v2_refactor.md` archived
10. [ ] Tag the parent FX repo at the cutover commit

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
