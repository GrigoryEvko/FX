# CLAUDE.md — lean-fx-2 project-local instructions

When working in `lean-fx-2/` (this directory), apply the rules below
in addition to global `/root/iprit/FX/CLAUDE.md`.

## Required reading (in order, on every fresh context)

1. `AXIOMS.md` (this dir) — trust budget + per-axiom catastrophe analysis
2. `WORKING_RULES.md` (this dir) — 18 distilled kernel-discipline rules
3. `ARCHITECTURE.md` (this dir) — 13-layer dependency DAG
4. `ROADMAP.md` (this dir) — Layer-by-Layer phasing
5. `MIGRATION.md` (this dir) — lean-fx → lean-fx-2 cutover plan
6. `LeanFX2/Sketch/Wave9.lean` — raw-aware Term proof of concept

## Architectural commitments (DO NOT violate)

* **Term carries `RawTerm scope` as a type-level index.**
  `Term : Ctx mode level scope → Ty level scope → RawTerm scope → Type`.
  `Term.toRaw t = raw` is `rfl`.

* **Subst is unified.**  `Subst level src tgt = { forTy : Fin src → Ty level tgt, forRaw : RawTermSubst src tgt }`.
  ONE `Subst.singleton` operation; NO `dropNewest`, NO `termSingleton` variant.

* **Conv is `∃ commonReduct, StepStar t1 commonReduct ∧ StepStar t2 commonReduct`.**
  NOT inductive with 13 cong rules.  `Conv.trans` lives in Layer 3 (depends on Church-Rosser).

* **η is opt-in** (`Step.eta` namespace).  βι is the default.

* **Cumulativity is a Conv rule** (Layer 3+), not a Ty constructor.

* **Mode is at Ctx level only** (NOT a parameter on every Term ctor).
  Modal types are introduced via `Ty.modal modality inner` constructor at Layer 6.

* **Identity-type endpoints are RawTerm**, not typed Term.
  Sidesteps Lean 4's mutual-index rule.

## Zero-axiom commitment

Per `AXIOMS.md`:
* Layers K (Foundation) / M (Reduction, Confluence, Bridge) / E (Algo, Pipeline) are STRICT zero-axiom
* Layer 5 HoTT/Univalence is the ONLY documented exception (`@[univalence_postulate]` attribute)
* No `propext`, `Quot.sound`, `Classical.choice`, `funext`, `K`, `sorry` (durable) anywhere else

After every new theorem, verify:
```lean
#print axioms TheoremName  -- must report "does not depend on any axioms"
```

## Build verification

```bash
cd /root/iprit/FX/lean-fx-2 && lake build LeanFX2
```

Expected: green build.  AuditAll gates auto-fire during build.

## Naming + style discipline

Per `WORKING_RULES.md`:
* ASCII-only identifiers (no Greek, no Unicode in code)
* ≥4-character names (no `g`, `t`, `e`, `s`, `i`, `j`, `ty`, `fn`, etc.)
* Predicates use question verbs (`isLinear`, `hasRefinement`, `shouldInline`)
* Match-arity rule: hoist Nat indices before `:` for multi-indexed pattern theorems
* No wildcards in match (always full enumeration)
* `@[reducible]` on substitution-shape helpers
* Binder-form match for indexed inductives (verify with `#print axioms`)

## What to do when stuck

1. Re-read the relevant `WORKING_RULES.md` rule
2. Re-read the source memory in `/root/.claude/projects/-root-iprit-FX/memory/`
3. Check the lean-fx analog in `/root/iprit/FX/lean-fx/LeanFX/` for inspiration
4. Apply the paired-predicate pattern (Discipline #6) if tactic-mode opacity blocks you
5. Apply the toRaw-shape dispatch (Discipline #2 Rule 5) if dep-elim wall blocks you
6. Apply the mapStep abstraction (Discipline #7) if you're writing 4-line cong inductions

## What NOT to do

* Don't introduce `Subst.dropNewest` (the source of lean-fx's bridge sorries)
* Don't introduce `Subst.termSingleton` separate from `Subst.singleton` (the variant that motivated Wave 9)
* Don't introduce `Term.toRaw_subst0_term` or any "_term" suffix variant (collapse via raw-aware Term)
* Don't add `propext`, `Quot.sound`, `Classical.choice` to ANY kernel theorem
* Don't add `axiom` declarations except `Univalence` (and only inside `HoTT/Univalence.lean`)
* Don't bolt Mode onto Term inhabitants — keep at Ctx level
* Don't skip reading specs / memories on fresh context — those are the recovery mechanism
