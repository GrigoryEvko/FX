# lean-fx-2

A zero-axiom, zero-sorry, full-HoTT, full-MTT, dependent-type-ready
engine for FX, written in Lean 4.

## Status: Phase 0 (skeleton complete, build green at 90 jobs)

All 13 layers have stub files with substantial architectural
docstrings.  Build green from day 1 — every stub compiles, just
doesn't yet contain the full implementation.

```bash
cd /root/iprit/FX/lean-fx-2 && lake build LeanFX2
# expected: Build completed successfully (90 jobs)
```

## Required reading

Before any kernel work, read in order:

1. `AXIOMS.md` — trust budget + per-axiom catastrophe analysis
2. `WORKING_RULES.md` — 18 distilled kernel-discipline rules
3. `ARCHITECTURE.md` — 13-layer dependency DAG
4. `ROADMAP.md` — Layer-by-Layer phasing
5. `MIGRATION.md` — lean-fx → lean-fx-2 cutover plan
6. `LeanFX2/Sketch/Wave9.lean` — raw-aware Term proof of concept
7. `CLAUDE.md` — project-local instructions

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
  is `rfl`.
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
* **Smoke tests inline** — every theorem ships with `example` adjacent.

## Engine commitments

| | What | Where |
|---|---|---|
| **0 axioms** | No `propext`, `Quot.sound`, `Classical.choice`, `funext`, `K` | `AXIOMS.md`, enforced by `Tools/AuditAll.lean` |
| **0 sorry** | Every theorem proved | enforced by build |
| **Full HoTT** | Identity types with full dep J, transport, equivalences, n-types, HITs (Circle, Suspension, Quotient, PropTrunc), univalence (cubical-derived long-term, postulated short-term as **only** documented exception) | Layer 5 — `HoTT/` |
| **Full MTT** | BiSikkel-style: 2-category of modes, modalities (Later/Bridge/Cap/Ghost), 2LTT layering, modal computation rules | Layer 6 — `Modal/` |
| **Dependent type** | Π, Σ, Id, universes (cumulativity via Conv), inductive families, recursors | Layer 1 — `Term.lean` |
| **Ready engine** | lex → parse → elab → kernel; WHNF, decidable Conv, bidirectional infer/check, fuel-bounded eval; soundness + completeness | Layers 9–11 |

## Current artifact (Phase 0 skeleton)

* **90 Lean files** building green
* **5 docs**: AXIOMS.md (~400 lines), WORKING_RULES.md (18 rules),
  README.md, ARCHITECTURE.md, ROADMAP.md, MIGRATION.md, CLAUDE.md
* **1 Sketch** (`Sketch/Wave9.lean`) — raw-aware Term proof of concept
  ported verbatim from lean-fx
* **8 Smoke files** — placeholders for per-layer concrete examples
* **0 axioms, 0 sorries** (only stubs; no actual proofs to fail)

## Architecture

13 layers in dependency order — see `ARCHITECTURE.md` for the full
picture.

## Roadmap

See `ROADMAP.md` for the phasing from skeleton → working kernel →
full engine.

## Migrating from lean-fx

See `MIGRATION.md` for the cutover plan.  Short version: lean-fx and
lean-fx-2 coexist until lean-fx-2 has full feature parity, then lean-fx
is retired (kept as `lean-fx.deprecated/` for historical reference).

## Layout

```
lean-fx-2/
├── LeanFX2.lean          umbrella import (all layers wired)
├── LeanFX2/
│   ├── Foundation/       Layer 0: untyped substrate (Mode, RawTerm, Ty, Subst, Context)
│   ├── Term.lean         Layer 1: raw-aware Term inductive
│   ├── Term/             Layer 1: rename, subst, subst0, toRaw, pointwise
│   ├── Reduction/        Layer 2: Step, StepStar, Conv, ParRed, RawPar, Compat
│   ├── Confluence/       Layer 3: Cd, Diamond, Church-Rosser, canonical form
│   ├── Bridge.lean       Layer 4: typed↔raw correspondence
│   ├── HoTT/             Layer 5: Identity, J, Path, Transport, Equivalence, NTypes, Univalence, HIT
│   ├── Modal/            Layer 6: Modal foundation, Later, Bridge, Cap, Ghost, 2LTT
│   ├── Graded/           Layer 7: Semiring framework, GradeVector, dimension instances
│   ├── Refine/           Layer 8: refinement types, decidable predicates, SMT cert
│   ├── Algo/             Layer 9: WHNF, decConv, infer, check, eval
│   ├── Surface/          Layer 10: lex, AST, parse, print, elab
│   ├── Pipeline.lean     Layer 11: end-to-end pipeline
│   ├── Tools/            Layer 12: AuditAll, AuditGen, DependencyAudit, Tactics/
│   ├── Sketch/           Wave 9 raw-aware Term prototype
│   └── Smoke/            inline smoke tests per layer
├── lakefile.lean
├── lean-toolchain
├── AXIOMS.md             trust budget + catastrophe analysis
├── WORKING_RULES.md      18 distilled kernel-discipline rules
├── ARCHITECTURE.md       13-layer dependency DAG
├── ROADMAP.md            phasing
├── MIGRATION.md          lean-fx → lean-fx-2 cutover
├── CLAUDE.md             project-local agent instructions
└── README.md             this file
```

## Building

```bash
lake build LeanFX2
```

Skeleton phase: builds green at 90 jobs, contains stubs.  Working
kernel phase: replace stubs with implementations per `ROADMAP.md`.
