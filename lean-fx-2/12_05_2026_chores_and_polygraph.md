# Post-Metatheory Chores + Polygraph Centralization Plan

**Authored**: 2026-05-12
**Scope**: post-M-series stabilization + PolyTerm-canonical flip
**Status**: forward-looking plan; current sprint (Codex M04 close-out) continues uninterrupted

## Snapshot at 2026-05-12

* **M04** ~95% complete: compound CR3 shipped (15 arms), 75 fundamental_X
  cases shipped, ReducibleSubst.singleton/identity/consSingleton shipped,
  monotone (#1944) in flight via Codex.  Remaining: lift composition +
  fundamental_lam + M04 corollary.  ETA ~1-2 weeks.
* **M05/M06/M07/M10**: M06+M07 shipped (SR per-Ty including universe);
  M10 substantially shipped (15 `infer_complete_X` theorems).  M05
  progress at ~3% (1 ctor of 75 + headline-weak `value_or_cong_only`).
* **K11 polygraph layer**: 17/19 sub-tickets complete; **K11.10 + K11.11
  bijection completion is the single critical missing piece**.
* **K12-K20 main tracks**: blocked on dispatcher infrastructure not yet
  recognized as polygraph specializations.

This document is the post-M04 stabilization roadmap.  Three stages:
metatheory close-out → polygraph centralization → PolyTerm canonical
flip.

---

## Stage 0 — Close current metatheory tracks

### Decision required: minimal close vs full M-series

**Option A — Minimal close** (4-6 weeks)

Ship only M04 close + the residual classical proofs that have downstream
consumers:

* M04 K12.27 strong_normalization headline (1 atomic, 1-line corollary)
* K12.28 confluence via Newman (1 atomic, ~50 LoC corollary given M04 + diamond)
* K12.29 audit close + ROADMAP update
* K12.30 Atkey 2018 regression test
* M03 Term.eval termination (1-line via M04 SN witness, replacing fuel)

Defer M05 Progress and M08/M09 headStep work to v1.1.

**Option B — Full M-series close** (12-16 weeks)

Add to Option A:

* M05 ~75 per-ctor progress theorems + M05.D.2 headline
* M08 ~10 ι-rule extensions in `Term.headStep?`
* M09 `headStep?` completeness theorem

Full classical 4 rules shipped: SR + Progress + SN + Completeness.

### Recommendation

Option A is sufficient for "FX has a sound type theory" claim, since
SR + SN + Completeness ship together.  M05 Progress is a *separate*
classical property that strengthens the metatheory but isn't needed for
operational correctness (M03 Term.eval termination already implies
"every well-typed term has a step or is a value" via the eval algorithm).

**Default**: Option A.  Reassess after M04 lands whether M05 close is
worth the 8-12 weeks before pivoting to Stage 1.

---

## Stage 1 — Chores and stabilization

After Stage 0 ships, before any polygraph work begins.  Goal: leave the
kernel in a state where the polygraph pivot is mechanically safe.

### 1.1 Variable-block compaction (~1 week)

Hoist mode/level/scope/context binders into per-file `variable` blocks.
Cosmetic refactor with no semantic change.  Per-theorem signature
shrinks from ~15 lines to ~5 lines.  ~10K LoC visible compaction.

* Apply to `Reducibility.lean` (~12500 LoC, biggest yield)
* Apply to `Term/Subst.lean`, `Term/Rename.lean`, `Reduction/*.lean`
* Apply to FX1/Core/*.lean for consistency

Audit-pin preserving — no theorem names change.

### 1.2 Tactic-shape low-hanging wins (~3-5 days)

Per Agent 1's findings, ship the ~750 LoC of safe proof-body
simplifications:

* `step_or_eq_preserves` helper (collapses 39 sites)
* `subst_eqs` in HEqCongr (23 sites)
* `nomatch` inline pattern (26 sites)
* Inline disequality fun-closures (46 sites)
* Symmetric twin-body shared helpers (6 pairs)

Zero risk, low LoC, immediate readability improvement.

### 1.3 Audit-pin coverage extension (~30 minutes)

Extend `Smoke/AuditPhase6BInversion.lean` to cover all 73
`RawStep.par.<ctor>_inv` lemmas (currently 24/73).  Pure documentation
hygiene; the missing 49 are already audited via `#audit_namespace
LeanFX2` but not reviewer-facing.

### 1.4 Memory entry maintenance (~1 day)

Three documented patterns are now obsolete:

* `feedback_lean_zero_axiom_match.md` Rule 5 (toRaw-shape dispatch) —
  obsolete since `Term.toRaw t = raw` is `rfl` in lean-fx-2
* `feedback_lean_paired_predicate_pattern.md` — obsolete for the same
  architectural reason
* `feedback_lean_zero_axiom_match.md` Rule 1 ("wildcards always leak")
  — refuted by `Foundation/RawTermInjective.lean` (73 wildcard arms
  audit clean via `cases ... | _ => Foo.noConfusion ...`)

Update each entry with architecture-version stamp + obsolete marker.
Add new entry documenting the cases-with-noConfusion exception.

### 1.5 Three undocumented `Step.par` ctors (~5 minutes)

Per Agent 3 audit: `Step.par.equivApplyArgument`,
`Step.par.equivApplyEquiv`, `Step.par.uaToEquivProof` are typed-only
mirrors with no consumer and not in `isDocumentedTypedOnlyParity`.

Add to the parity exception list with one-line justification each.

### 1.6 Wave9 fate decision (~15 minutes)

`LeanFX2/Sketch/Wave9.lean` (491 LoC) is imported only from
`Smoke/ImportEverywhere.lean`.  CLAUDE.md cites it as "Required
reading #6".  Two options:

* **Archive**: move to `docs/legacy/Wave9.lean.txt`, drop import,
  update CLAUDE.md to point at the new location.  Saves audit-tax
  elaboration cost.
* **Keep live**: accept the elaboration cost; useful as live
  documentation.

Default: archive after CLAUDE.md update.

### 1.7 What NOT to do during Stage 1

* **Do NOT ship the dispatcher refactor as standalone abstractions**.
  The Action typeclass, HeadKind taxonomy, ReducibilityArm bundle —
  these are polygraph specializations.  Shipping them as standalone
  patterns now and re-routing through polygraphs later is double work.
* **Do NOT refactor K12 work into PolyTerm**.  Term stays as the
  classical-metatheory reference forever.
* **Do NOT delete any Term-side proofs**.  They're the legacy view per
  the 2026-05-11 pivot decision.

Stage 1 is purely additive cleanup.  Total: ~2 weeks of work.

---

## Stage 2 — Bijection landing

Single most critical milestone for everything that follows.  Until
the bijection ships, polygraph operations cannot transfer between
Term and PolyTerm.

### 2.1 K11.10 — Term.toPoly forward bijection (1-2 weeks)

`def Term.toPoly : Term ctx ty raw → PolyTerm ctx ty raw`

Critical requirements:

* Should be `rfl`-equal where possible (definitional bijection).  If
  forced to be propositional only, audit the cost of each call-site
  cast.
* Must commute with `Term.subst`, `Term.rename`, `Step` (these
  commutations are the polygraph operations everything else builds on).
* Per-ctor mechanical mapping.  ~75 cases, mostly 1-line each.

### 2.2 K11.11 — PolyTerm.toRawTerm/toTerm backward bijection (1 week)

`def PolyTerm.toTerm : PolyTerm ctx ty raw → Term ctx ty raw`
`def PolyTerm.toRawTerm : PolyTerm ctx ty raw → RawTerm scope`

The roundtrip theorems:
* `Term.toPoly.toTerm = id` (forward then backward)
* `PolyTerm.toTerm.toPoly = id` (backward then forward, on well-formed
  PolyTerm values — partial inverse on the polygraph image)

### 2.3 Bijection commute theorems (~1 week)

Prove the bijection respects the kernel operations:

* `(Term.subst σ t).toPoly = PolyTerm.subst σ.toPoly t.toPoly`
* `(Term.rename ρ t).toPoly = PolyTerm.rename ρ t.toPoly`
* `Step source target → PolyTerm.Step source.toPoly target.toPoly`
* `HasType ctx ty raw → PolyHasType ctx.toPoly ty.toPoly raw`

These are the LOAD-BEARING properties.  Without them, the polygraph
framework cannot consume Term-side proofs.

### 2.4 Stage 2 close-out

When K11.10 + K11.11 + bijection commutes ship:

* Mark #1752 (K11.10), #1748 (K11.11) complete
* Update memory entry `project_polyterm_daily_driver.md` to reflect
  bijection availability
* Add `STRICT-bijection-rfl` audit gate if bijection is definitional —
  catches any future regression that breaks the rfl property

Total Stage 2: ~3-4 weeks, ~1500 LoC.

---

## Stage 3 — PolyTerm pivot pilot (K13 NbE)

Validate the polygraph framework on one concrete K-task before
committing to full migration.  K13 NbE is the natural pilot because
it's greenfield (no existing Term-side proofs to migrate) and NbE is
mathematically a polygraph catamorphism.

### 3.1 Pilot design (~3-5 days)

Before writing any code, design:

* `ValueTerm` as a polygraph at dim 0 (closures, neutrals, env structure)
* `Term.eval : Term → ValueTerm` as a polygraph catamorphism
* `quote : ValueTerm → Term` as the reverse polygraph functor
* `nbe := quote ∘ eval` soundness via polygraph naturality

Output: one-page RFC.

### 3.2 Pilot execution (~2-3 weeks)

Ship the design.  ~1500 LoC total.  Replaces the ~3500 LoC that K13.1-
K13.20 would have cost via per-ctor work.

### 3.3 Decision gate

After pilot:

* **Pilot validates framework** → proceed to Stage 4 (full
  polygraph rewiring).  Polygraph becomes FX's strategic asset.
* **Pilot stalls on Lean elaboration walls** → document the walls,
  revert to per-ctor K13 work.  PolyTerm sits alongside Term for
  parallel-checking use cases (GPU pipeline) but isn't the primary
  representation.

The pilot has a clean revert path either way.

---

## Stage 4 — Full polygraph rewiring (if Stage 3 validates)

Conditional on Stage 3 pilot success.  Migrate remaining major K-tasks
to polygraph-native.

### 4.1 K14 EGraph as quotient polygraph (~2-3 weeks)

* `ECId` opaque identifier = polygraph cell identity
* `ENode` = polygraph 0-cell with children indexed by ECId
* `EGraph` = quotient polygraph by congruence-generated equivalence
* Saturation = computing the Dim0 homology of the quotient

Most K14.1-K14.15 sub-tickets collapse to polygraph operations.

### 4.2 K15 ReflTerm as reflective endomorphism (~2-3 weeks)

* ReflTerm = polygraph self-description (cells as data)
* reify = polygraph functor PolyTerm → ReflTerm
* elaborate = reverse functor (partial inverse)
* roundtrip = reflexive endomorphism diagonal

### 4.3 K16 Tactic monad as Dim3 strategy framework (~2-3 weeks)

* Strategy = Dim3 cell in the polygraph (per K11.19)
* Tactic state = polygraph context
* Tactic combinators = strategy composition via Mac Lane pentagon

### 4.4 K17-K20 reflection tower as polygraph functor chain (~6-8 weeks)

* K17 FX1/Core = the minimal polygraph admitting dependent function types
* K18 FX1/LeanKernel = polygraph extension (12 ctors)
* K19 encoders = polygraph functors between layers
* K20 FX-in-FX = polygraph reflexive endomorphism

Each layer transition is one Action typeclass instance + naturality
proof at generators.

### 4.5 Action typeclass completion subsumes dispatcher refactor

The dispatcher patterns identified earlier (Action, HeadKind,
ReducibilityArm, ClosedTyForm) all become specializations of
polygraph operations.  Don't ship them as standalone — they fall out
of polygraph machinery for free.

* Action typeclass = operadic action on the polygraph
* HeadKind taxonomy = polygraph stratification
* ReducibilityArm = colored polygraph fibration
* ClosedTyForm = polygraph subobject classifier

Total Stage 4: ~12-16 weeks.  ~5000 LoC of K-task work that would
otherwise be ~12000-15000 LoC of per-ctor work.

---

## Stage 5 — PolyTerm-canonical flip

The strategic positioning step.  Make PolyTerm the canonical
representation; Term retained as the classical-metatheory reference.

### 5.1 Policy update (~1 day, no code)

* Update `CLAUDE.md`: PolyTerm is the daily-driver for new operations;
  Term retained as classical-metatheory reference
* Update `ARCHITECTURE.md`: PolyTerm/PolyTy diagrams as the primary
  representation; Term/Ty as classical view
* Update `README.md`: positioning statement (see Stage 7)
* Update `ROADMAP.md`: phases align with polygraph-native execution

### 5.2 New-work convention (~ongoing)

All new K-task work after Stage 5 targets PolyTerm directly.  Bijection
cites Term-side classical metatheory where needed.

### 5.3 What stays in Term/Ty forever

Five "classical preserve" surfaces:

1. The 4 classical metatheorems (SR, Progress, SN, Completeness) —
   stated about Term, prove the textbook results
2. The operational semantics statement (Step, HasType) — Term-native
3. The trust-anchor bridge to FX1/Core — Term-anchored
4. The surface elaboration target (Surface/Lex → Surface/Parse →
   Surface/Elab → Term) — until Stage 6 lets surface elaborate to
   PolyTerm directly
5. The "what is FX?" documentation surface (`fx_design.md` describes
   the kernel in Term terms)

No retroactive refactor of K12-M-series Term work, ever.

---

## Stage 6 — Compilation pipeline foundation

If Stage 5 establishes polygraph as canonical, Stage 6 builds the
verified-compilation framework on top.

### 6.1 Polygraph functor chain for compilation (~4-6 weeks)

Define the architecture:

```
SourceFX (polygraph)
   │  pass₁ (polygraph functor — naturality proves correctness)
   ▼
IR₁ (polygraph)
   │  pass₂
   ▼
...
   ▼
Target (polygraph)
```

Each pass:
* A polygraph functor F: SourcePolygraph → TargetPolygraph
* A naturality proof showing F commutes with the semantic
  interpretation
* Composes functorially with adjacent passes

### 6.2 Worked-example passes (~4-6 weeks)

Ship 3-5 example passes to validate the framework:

* **Inlining**: Dim1 cell composition expansion
* **Constant folding**: Dim1 cell evaluation via ι rule application
* **Dead-code elimination**: subgraph quotient by reachability
* **Common-subexpression elimination**: quotient polygraph (reuses K14)
* **Loop fusion**: Dim2 cell coherence between rewrite paths

Each pass ~300-500 LoC including correctness proof.

### 6.3 Compilation correctness composition theorem (~1 week)

The headline:

```
theorem compilation.correctness
    {pass_chain : List CompilationPass}
    (each_pass_correct : ∀ p ∈ pass_chain, IsPolygraphFunctor p) :
    IsPolygraphFunctor (foldr compose identity pass_chain)
```

Functorial composition gives correctness composition for free.

### 6.4 Stage 6 close-out

* New tracker tickets for compilation pipeline (CMP1-CMPn)
* `fx_compile.md` doc describing the polygraph-functor framework

Total Stage 6: ~8-12 weeks.

---

## Stage 7 — v1.0 release positioning

The selling-point capture step.  v1.0 ships with both views and the
compilation framework.

### 7.1 The six-point story

1. **FX is a real type theory** — classical metatheory in Term proves
   the textbook 4 properties
2. **FX is mechanized end-to-end** — zero-axiom Lean proofs, every
   theorem `#print axioms`-clean
3. **FX has the most complete metatheory of any production type
   theory** — 21 dimensions handled uniformly; §6.8 collision catalogue
4. **FX's metatheory generalizes to compilation correctness** —
   every compiler pass = polygraph functor; correctness composes
   functorially
5. **FX's typechecker is natively parallelizable** — polygraph cell-set
   decomposition; GPU-cluster checking
6. **FX is self-hosting and self-checking** — K20 reflection tower;
   FX-in-FX bootstrap

Points 1-3 are the type theory.  Points 4-6 are what the polygraph
flip unlocks.  The combination is what no other production type theory
has.

### 7.2 Release artifacts

* Git tag v1.0
* Release notes referencing each of the six points
* Updated `README.md` with positioning
* Reference implementations (`fx-chip` for RISC-V, `fx-driver` for
  Linux kernel driver, etc.) demonstrating compilation correctness
* Academic paper (optional) on "graded modal dependent types with
  built-in compilation correctness"

---

## Risk register

### Risk 1: K11.10/K11.11 bijection isn't definitional

**Impact**: every Term ↔ PolyTerm transfer pays a propositional cast
cost.  Slows elaboration; some refactors become impractical.

**Mitigation**: aim for definitional bijection in K11.10 design.  If
infeasible, accept casts and benchmark elaboration impact.  Revert path:
keep Term as primary, use PolyTerm only for specific GPU-parallel use
cases.

### Risk 2: PolyTerm elaboration overhead

**Impact**: PolyTerm's polygraph structure adds type-level machinery.
Per-decl elaboration may slow by 1.5-3×.

**Mitigation**: benchmark in Stage 3 pilot.  If slow, optimize
PolyCell representation; consider erased proofs where possible.

### Risk 3: K13 NbE pilot stalls on Lean elaboration walls

**Impact**: pilot proves the framework isn't viable for some K-tasks.
Stage 4 doesn't materialize.

**Mitigation**: pilot has clean revert path.  Even partial success
means K13 NbE ships in polygraph form for the parts that work.
Per-ctor work resumes for the parts that don't.

### Risk 4: Polygraph framework is research-grade

**Impact**: novel ground for production type theory.  Could hit
unforeseen formal gaps in mechanization.

**Mitigation**: K11 already proved basic polygraph machinery ships
zero-axiom.  Specializations are incremental research-engineering.
Frequent pilots with revert paths.

### Risk 5: Strategic positioning fails to land

**Impact**: v1.0 ships with great metatheory and compilation framework
but doesn't differentiate FX in the type-theory landscape.

**Mitigation**: independent of execution success — the technical
content carries regardless of positioning.  Worst case: FX is a
"more dimensional Lean" in marketing while having the framework
internally.

---

## Decision log

| Decision | Status | Source |
|---|---|---|
| Term retained as legacy view | DECIDED 2026-05-11 | `project_polyterm_daily_driver.md` |
| PolyTerm becomes canonical for new work | DECIDED 2026-05-11 | same |
| Polygraph framework as strategic asset | OPEN | this document, pending Stage 3 pilot |
| Option A (minimal close) vs Option B (full M-series) | OPEN | this document, decision after M04 lands |
| Wave9 archive vs keep | OPEN | this document, Stage 1.6 |
| Variable-block compaction at Stage 1 | RECOMMENDED | this document |
| Don't ship dispatcher refactor standalone | RECOMMENDED | this document, falls out of polygraph |

---

## Timeline summary

| Stage | Duration | Cumulative |
|---|---|---|
| Stage 0 (metatheory close, Option A) | 4-6 weeks | 4-6 weeks |
| Stage 1 (chores + stabilization) | 2 weeks | 6-8 weeks |
| Stage 2 (K11.10/K11.11 bijection) | 3-4 weeks | 9-12 weeks |
| Stage 3 (K13 pilot) | 3 weeks | 12-15 weeks |
| Stage 4 (full polygraph rewiring) | 12-16 weeks | 24-31 weeks |
| Stage 5 (PolyTerm-canonical flip) | 1 week | 25-32 weeks |
| Stage 6 (compilation framework) | 8-12 weeks | 33-44 weeks |
| Stage 7 (v1.0 release) | 4 weeks | 37-48 weeks |

**Total to v1.0 with full polygraph framework**: ~9-12 months from
2026-05-12.  Most of the timeline is Stage 4 (polygraph rewiring) and
Stage 6 (compilation framework).  Stages 0-3 are the bridge from
current state to "polygraph framework validated."

**Total to v1.0 minimal** (skip Stage 6 compilation framework,
ship reflection tower only): ~6-8 months.

---

## Single critical decision now

Not "should we pivot to polygraph" — that was decided May 11.

The decision is: **after Codex closes M04, prioritize K11.10 + K11.11
(Stage 2) before K13 or any other major K-task starts**.  Schedule it
explicitly.  Everything downstream flows from that one priority.

Codex's current cron-tick cadence on M04 continues uninterrupted.  When
M04 lands and audit gate is 554/554 green, the next priority is the
bijection — not K13.1 or any other K-task ID.
