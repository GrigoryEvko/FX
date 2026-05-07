# lean-fx-2

A zero-axiom, zero-sorry, full-HoTT, full-MTT, dependent-type-ready
engine for FX, written in Lean 4.

## Status (2026-05-07): kernel + confluence + HoTT shipped, surface + modal in progress

* **Build**: 467 jobs, 7780 declarations clean, 0 failed
* **Audit**: every shipped declaration is `#assert_no_axioms` gated
  inline via the strict harness; zero `propext` / `Quot.sound` /
  `Classical.choice` / FX-specific axioms anywhere in the kernel
* **Critical-path remaining**: 7 load-bearing tasks gating v1.0 (see
  ROADMAP.md "Critical-path summary"); D2.10 typed Compat at 13/28
  done as of 2026-05-07

```bash
cd /root/iprit/FX/lean-fx-2 && lake build LeanFX2
# expected: Build completed successfully (467 jobs)
# dashboard: SEMANTIC DEBT DASHBOARD banner reports debt counts
```

## Required reading

Before any kernel work, read in order:

1. `AXIOMS.md` — zero-axiom commitment + per-axiom catastrophe analysis
2. `WORKING_RULES.md` — 18 distilled kernel-discipline rules
3. `ARCHITECTURE.md` — 13-layer dependency DAG
4. `ROADMAP.md` — phase status + critical-path summary
5. `MIGRATION.md` — lean-fx → lean-fx-2 cutover plan
6. `LeanFX2/Sketch/Wave9.lean` — raw-aware Term proof of concept
7. `CLAUDE.md` — project-local instructions (zero-axiom commitment,
   forbidden declaration forms, mandatory verification gates)

## Why a new project (vs continuing lean-fx)

lean-fx accumulated architectural debt over 5+ kernel versions:

* `Term : Ctx → Ty → Type` with `Term.toRaw` as a structural-recursion
  function, requiring ~30 bridge lemmas
* Two parallel substitution flavors (`Subst.singleton` with
  `dropNewest` vs `Subst.termSingleton` with raw arg), with strangle
  equations between them
* `RawConsistent` threading through every `subst_compatible` chain
* W9.B1.1/B1.2 `resultEq` parameters as scaffolding for an inline
  migration that never composed (W9.B1.3a reverted at 343 tool calls)
* 4 unprovable bridge β sorries blocked on Phase C cascade

Inline editing through 30+ files at ~30% line-touch rate didn't
compose — agents kept reverting at the cascade wall.  lean-fx-2
builds the architecture-of-record from day 1:

* **Term carries `RawTerm scope` as a type index.**  `Term.toRaw t = raw`
  is `rfl` for all 75 ctors.
* **Subst is unified.**  No `dropNewest`; one singleton operation
  embedding `RawTermSubst.singleton arg.toRaw`.
* **Conv is ∃-StepStar.**  No 13 cong rules; uniform decidability.
* **η is opt-in** (separate `Step.eta` namespace) — βι confluence
  proof doesn't carry η weight.
* **Cumulativity is a Conv rule**, not a Ty constructor (lean-fx
  v1.29 revert had the diagnosis right).
* **Mode is at Ctx level only**, not parameter on every Term ctor.
* **Modal infrastructure foundational** (Mode 2-category is Layer 0,
  not bolted on).
* **Identity-type endpoints are RawTerm**, sidestepping Lean 4's
  mutual-index rule.
* **Smoke tests inline** — every theorem ships with `example`-style
  smoke gates in `Smoke/Audit*.lean` files.

## Engine commitments — verified zero-axiom

| | Status | What | Where |
|---|---|---|---|
| **0 axioms** | ✅ verified | No `propext`, `Quot.sound`, `Classical.choice`, no FX axioms | `AXIOMS.md`, enforced by `Tools/AuditAll/` |
| **0 sorry** | ✅ verified | Every shipped declaration has a body | enforced by build |
| **Full HoTT** | ✅ shipped | Identity types with full dep J, transport, equivalences, n-types, 7 HITs (Quot, PropTrunc, SetTrunc, S¹, Suspension, Pushout, Coequalizer), Univalence as REAL theorem `Conv.fromStep Step.eqType`, funext as REAL theorem `Conv.fromStep Step.eqArrow` | Layer 5 — `HoTT/` |
| **Full MTT** | 🚧 partial | 10-mode enum with 2 axes (runtime-layer + modal-fragment); D4.1-4.9 modal infrastructure pending | Layer 6 — `Modal/` |
| **Dependent type** | ✅ shipped | Π, Σ, Id, universes (cumulativity via Conv), inductive families, recursors at Term/Step/Conv layers | Layer 1 — `Term.lean` |
| **Engine** | 🚧 partial | Layer 9 (WHNF + bidirectional infer/check + decidable Conv) DONE; Layer 10 surface (Lex + Token + AST scaffold) PARTIAL; Layer 11 Pipeline pending | Layers 9-11 |

## Current artifact (multi-phase shipped)

* **467 build jobs** green
* **7780 declarations** in `LeanFX2.*` namespace, all axiom-clean per
  the strict harness
* **49 strict gates** for surface bridge/env/correspondence (#1531)
* **3 confluence gates** for raw Church-Rosser (#1508)
* **8 STRICT-N harness gates** (`STRICT-1` through `STRICT-8`)
  enforce: axioms-zero, raw/typed parity, naming discipline,
  hypothesis-as-postulate detection, sub-namespace coverage
* **30 cong rules** in `Step.par` with rename+subst compat: 13 of 28
  shipped (intervalOppCong + 12 batch); 15 still on the v1.0 path
* **Univalence + funext** as zero-axiom theorems via `Step.eqType` /
  `Step.eqArrow` reductions (NOT axioms)
* **5 docs**: AXIOMS.md, WORKING_RULES.md, README.md, ARCHITECTURE.md,
  ROADMAP.md, MIGRATION.md, CLAUDE.md

## Architecture

13 layers in dependency order — see `ARCHITECTURE.md` for the full
picture.

## Roadmap

See `ROADMAP.md` for HONEST per-phase status (Phase 0-2, 4 raw, 5,
6, 8, 13 DONE; Phase 3, 9-11, 14 PARTIAL; Phase 7 modal NOT STARTED;
Phase 15 cutover deferred until critical path closes).

## Migrating from lean-fx

See `MIGRATION.md` for the cutover plan.  Short version: lean-fx and
lean-fx-2 coexist until lean-fx-2 has full feature parity, then
lean-fx is retired (kept as `lean-fx.deprecated/` for historical
reference).  Cutover gating: D2.10 + M06 SR + PHASE7-CONV-TRANS +
K07.1-8 + D2.5.1-3 + WEAK-FX2-03 + D4 modal must close first.

## Layout

```
lean-fx-2/
├── LeanFX2.lean          umbrella import (all layers wired)
├── LeanFX2/
│   ├── Foundation/       Layer 0: untyped substrate (Mode, RawTerm, Ty, Subst, Context, Action)
│   ├── Term.lean         Layer 1: raw-aware Term inductive (75 ctors)
│   ├── Term/             Layer 1: rename, subst, subst0, toRaw, pointwise, SubjectReduction
│   ├── Reduction/        Layer 2: Step (105 ctors), StepStar, Conv, ParRed (109), RawPar, Compat
│   ├── Confluence/       Layer 3: Cd, Diamond, Church-Rosser (raw), CanonicalForm
│   ├── Bridge.lean       Layer 4: typed↔raw correspondence (Step.par.toRawBridge)
│   ├── Bridge/           Layer 4 cross-theory bridges (PathToId, IdToPath, etc.)
│   ├── HoTT/             Layer 5: Identity, J, Path, Transport, Equivalence, NTypes, Univalence, Funext, HIT/
│   ├── Cubical/          Layer 5: Path, Composition, Glue, Transport, Bridge
│   ├── Modal/            Layer 6: Modal foundation, Later, Bridge, Cap, Ghost, 2LTT (D4.x pending)
│   ├── Graded/           Layer 7: Semiring framework, GradeVector, 21 dimension instances
│   ├── Refine/           Layer 8: refinement types, decidable predicates, SMT cert (partial)
│   ├── Algo/             Layer 9: WHNF, decConv, infer, check, eval, soundness, completeness
│   ├── Surface/          Layer 10: Token, Lex, AST, KernelBridge, Semantics, Elab (scaffold)
│   ├── Pipeline.lean     Layer 11: end-to-end pipeline (TODO)
│   ├── FX1/              Lean 4 kernel mechanization (D8.1-D8.6 done; D8.7-D8.10 pending)
│   ├── FX1Bridge/        Term ↔ FX1 bridge (encodeTermSound_*)
│   ├── Tools/            Layer 12: AuditGen, AuditAll/, StrictHarness/, DependencyAudit
│   ├── Effects/, Sessions/, Codata/  Layer 5+ effect/session/codata infra
│   ├── Sketch/           Wave 9 raw-aware Term prototype
│   └── Smoke/            inline smoke tests per layer (~140 files)
├── lakefile.lean
├── lean-toolchain
├── AXIOMS.md             zero-axiom commitment + catastrophe analysis
├── WORKING_RULES.md      18 distilled kernel-discipline rules
├── ARCHITECTURE.md       13-layer dependency DAG
├── ROADMAP.md            phase status + critical-path summary
├── MIGRATION.md          lean-fx → lean-fx-2 cutover
├── CLAUDE.md             project-local agent instructions
└── README.md             this file
```

## Building

```bash
lake build LeanFX2
```

Expected output:
* `Build completed successfully (467 jobs).`
* Strict audit summary: `Total audited: 7780 / Clean: 7780 / Failed: 0`
* Semantic debt dashboard: load-bearing debt counts per category
  (lower = better; ratchets enforced inline)

If any gate fails, the build fails — there is NO advisory mode.

## Audit dashboard

The build prints a `lean-fx-2 SEMANTIC DEBT DASHBOARD` banner at the
end with current debt counts:

* Audited declarations (total / clean / failed)
* Schematic payload census
* Semantic signature debt (13 rows incl. dep eliminator motive,
  unit-typed proof placeholders, modal no-op, etc.)
* Coverage matrices (Bridge encoding, Step.par cong, Conv cong,
  toRaw projection, IsClosedTy parity)
* Inductive ctor-count snapshots (regression prevention)
* Refl-fragment dependency census (manufactured-rule wrapper count)
* Kernel decl-shape census (cast-operator deps, single-step Conv
  claims, etc.)
* Axiom-adjacent dependency census (HEq, decide, propext-adjacent)
* Lean-trust-escape census (OfNat, Eq.subst, Sigma, etc.)

Each row's count is enforced by an inline ratchet gate; new debt
fails the build immediately.
