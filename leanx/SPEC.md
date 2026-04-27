# leanx — Lean 4 Reference Interpreter for FX

This document specifies the design of `leanx`, the canonical reference
implementation of FX semantics, written in Lean 4.  It complements
`../fx_design.md` (the language specification), `../fx_grammar.md` (the
formal grammar), and `../fx_lexer.md` (the lexer specification).

Status: design document for the leanx project.  Phase 2.2 in
progress (per §7).  Kernel covers dependent Pi/Sigma + 13 Term
forms (incl. Term.const + refl/J + Quot.mk/lift stubs), with
12 of 21 grade dimensions instantiated; bidirectional
infer/check threads a GlobalEnv for cross-decl resolution;
reduction handles β on closures and ι on concrete inductives.
Elaborator covers fn decls (one-liner + block), let, if/else
via Ind-elim, match via Ind-elim with method synthesis, type
parameters as ghost Pi binders, and two-pass checkFile for
self-reference + forward references.  Evaluator walks the 11
Value constructors with a globalEnv-threaded mutual block.
CLI: `fxi tokenize|parse|check|run` all work end-to-end; Bool
+ Nat programs run.  Metatheory theorems (Preservation,
Progress, Consistency, StrongNormalization) are stated as
concrete `Prop` defs in `FX/Metatheory/**` with proofs
deferred to Phase 8.  502 runtime test checks + compile-time
by-decide tests pass; `scripts/axiom-audit.sh` green (zero
sorry in Kernel / Metatheory, zero axioms outside
`AXIOMS.md`).  See §7 for the phase plan,
`docs/error-codes.md` for the diagnostic registry, and
`docs/MetatheoryCorpus.md` for the layer-1
unsoundness-corpus index.

---

## 1. Purpose and scope

`leanx` serves four roles.

**(1) Definitional semantics.**  The question "what should this FX
program do" has exactly one authoritative answer: whatever `leanx`
computes.  `fx_design.md` is the informal prose specification; `leanx`
is the executable specification.  Disagreements between the two are
resolved by updating one of them — either the prose has a bug, or
`leanx` has a bug, but they must converge.

**(2) Trust root.**  The production FX compiler (`fxc`, written in FX)
is tested or proven to refine `leanx`'s semantics.  `leanx` is the only
component for which verification coverage is tracked.  Everything else
is derived — its correctness argument routes through `leanx`.

**(3) Bootstrap host.**  `leanx` can run an FX program directly,
including the FX compiler source.  This gives a from-scratch build path
that does not require a prebuilt `fxc` binary.  After the first
`fxc` binary exists, `leanx` remains available for cross-validation
and for rebuilding from source in isolated environments.

**(4) Metatheory home.**  The four core theorems (Preservation,
Progress, Consistency, Strong Normalization — see `fx_design.md`
§27.4) are stated and proved in Lean 4 against the kernel definitions
in `FX/Kernel/**`.

### What `leanx` is not

* Not a production compiler.  It is a tree-walking interpreter.  It is
  intentionally slow.  Performance-critical work runs under `fxc`.
* Not a replacement for `fxc`.  Users run `fxc` for real work; `leanx`
  is for semantics, verification, bootstrap, and cross-checking.
* Not a general-purpose Lean library.  It is specific to FX.

### Relationship to the main project

`leanx/` lives at the repository root alongside the language spec
(`fx_design.md` etc.) and the production compiler source tree (to be
added as `compiler/` in FX).  The compiler depends on the spec; `leanx`
depends on the spec; the compiler does *not* depend on `leanx` at
build time.  A user building `fxc` from scratch uses `leanx` as a
one-time bootstrap or uses a prebuilt seed binary.

`fstarx/` is legacy from a prior F*/OCaml bootstrap attempt and is
retained only for history.  It is not referenced by `leanx`.

---

## 2. Trust model

Every component of `leanx` lives in one of three trust layers.

### Layer 0 — Lean 4 kernel

Lean 4's C++ kernel (~10k LOC) is the irreducible trust root.  The
Lean4Lean project (Mario Carneiro et al.) is verifying it in Lean 4
itself.  `leanx` does not add anything to this layer.

### Layer 1 — `leanx` kernel (trusted)

Approximately 10–15k lines of Lean 4 across `FX/Kernel/**` plus the
metatheory proofs in `FX/Metatheory/**`.  This layer is subject to the
**zero-sorry invariant** and the **33-axiom allowlist** (§4).  A bug
here is an FX soundness bug.

### Layer 2 — SMT oracle

Refinement predicates (`pre`, `post`, `{ x | pred }`) and some type
equalities are discharged by Z3 via subprocess.  Z3's answers are
trusted — if Z3 says SAT/UNSAT, `leanx` accepts.  All Z3 queries are
cached in `audit.smtq` and reproducible.  A Z3 bug is an FX soundness
bug, same severity as a Lean kernel bug; mitigation is running the same
query against CVC5 as cross-check on demand.

### Untrusted (elaborator, evaluator wrapper, IO primitives)

Components outside the three trust layers can have bugs.  These bugs
can produce:

* Rejection of valid programs (false negatives — inconvenient).
* Acceptance of syntactically wrong programs (caught at elaboration or
  Layer 1 check).

They cannot produce silently accepted ill-typed outputs, because
Layer 1 re-checks every kernel term the elaborator produces.

---

## 3. Architecture

`leanx` has seven layers, each depending only on the layers below.

```
┌────────────────────────────────────────────────────────────┐
│  Cli        user-facing: fxi check, fxi run, fxi repl      │
├────────────────────────────────────────────────────────────┤
│  Io         primitive operations (stdout, fs, clock, …)    │  trusted
├────────────────────────────────────────────────────────────┤
│  Derived    §3–§26 surface constructs → kernel terms       │  untrusted
├────────────────────────────────────────────────────────────┤
│  Eval       tree-walking interpreter                       │  untrusted
├────────────────────────────────────────────────────────────┤
│  Elab       surface FX → kernel terms                      │  untrusted
├────────────────────────────────────────────────────────────┤
│  Smt        Z3 oracle for refinements                      │  trusted
├────────────────────────────────────────────────────────────┤
│  Kernel     axioms, typing rules, Check, Reduce            │  TRUSTED
│  Metatheory Preservation, Progress, SN, Consistency        │  PROVED
└────────────────────────────────────────────────────────────┘
```

Only `Kernel`/`Metatheory` and `Smt` are in the trust base.  Bugs
elsewhere produce rejection, not unsoundness.

### Representation choices (non-negotiable)

* **De Bruijn indices** for bound variables, **De Bruijn levels** for
  free variables (locally nameless).  Eliminates α-equivalence from
  proofs.  Elaborator is the only layer that sees names.
* **Typing judgment in `Prop`.**  `inductive HasType : Ctx → Term → Ty
  → Prop`.  Proof-irrelevant.
* **Check function in `Bool`.**  `def check : Ctx → Term → Ty → Bool`.
  Theorem `check_iff : check Γ e T = true ↔ HasType Γ e T`.
* **Reduction as relation + fuel-bounded function.**  `inductive
  Reduces : Term → Term → Prop` and `def step : Term → Option Term`.
  Theorem `step_sound : step e = some e' → Reduces e e'`.
* **Dependencies: `std4` only, not Mathlib.**  Mathlib is large and
  unstable; we need `Nat`, `List`, `String`, decidability — all in
  `std`.

---

## 4. Trust policies

### Zero-sorry invariant

`sorry` is **forbidden** in the following trees:

* `FX/Kernel/**`
* `FX/Metatheory/**`

CI enforces via `scripts/axiom-audit.sh`.  A PR introducing `sorry` in
these paths is rejected automatically.

`sorry` is **tolerated** (tracked, not fatal) in:

* `FX/Elab/**` during feature development.
* `FX/Derived/**` when a feature is partially implemented.
* `FX/Eval/**` for primitives that don't yet have verified
  implementations.

Every open `sorry` is tracked in `SORRY.md` with owner, reason, and
removal target date.  The count is reported per release; the invariant
is that it **never increases** between releases.

### Axiom allowlist (33 axioms)

`AXIOMS.md` contains the canonical list of axioms, one-to-one with
Appendix H of `fx_design.md`.  Axioms are declared in `FX/Kernel/**`
as `axiom` declarations.

The list is closed.  Adding a 34th axiom requires:

1. A PR updating `AXIOMS.md`.
2. An RFC in `docs/rfcs/` justifying: what feature requires the axiom,
   why it cannot be derived, what published precedent supports it.
3. Cross-reference addition to `fx_design.md` Appendix H.
4. Re-run of the full metatheory proof suite.
5. Addition to the `test/Kernel/Axioms/` regression tests.
6. Approval by two reviewers.

`scripts/axiom-audit.sh` parses `FX/Kernel/**/*.lean` for `axiom`
declarations and compares against `AXIOMS.md`.  Any discrepancy fails
CI.

### Coverage metric

Every PR reports two numbers:

* `implemented_features` — the subset of FX currently supported by
  `leanx` (rough count via tagged conformance tests).
* `verified_features` — the subset with Preservation + Progress
  proved.

The invariant `verified / implemented = 1` must hold.  Features cannot
be merged ahead of their proofs.  This is the discipline that prevents
F*-style verification drift.

---

## 5. Directory structure

```
leanx/
├── README.md                    quick orientation
├── SPEC.md                      this document
├── BOOTSTRAP.md                 how to build fxc via leanx
├── AXIOMS.md                    canonical 33-axiom allowlist
├── SORRY.md                     open sorry tracker (one table row each)
├── lakefile.lean                Lake build configuration
├── lean-toolchain               Lean version pin
├── .gitignore                   local build artifacts
├── scripts/
│   ├── axiom-audit.sh           enforce axiom allowlist + zero-sorry
│   └── coverage.sh              compute verified/implemented ratio
├── docs/
│   └── rfcs/                    proposals that change the trust base
├── FX/
│   ├── Core.lean                top-level entry, re-exports
│   ├── Util/
│   │   ├── Basic.lean           common utilities
│   │   └── Pretty.lean          pretty-printing for errors
│   ├── Kernel/                  [TRUSTED — zero sorry]
│   │   ├── Level.lean           universe levels    (U-wf, U-hier, U-cumul, U-level, U-poly)
│   │   ├── Grade.lean           21-dim grade vector, tier system
│   │   │                          (Grade-semiring-laws, Grade-subsumption,
│   │   │                           Grade-division, Grade-zero, Grade-lattice)
│   │   ├── Term.lean            ten kernel term forms (§31.2)
│   │   ├── Context.lean         typing contexts
│   │   ├── Typing.lean          inductive typing judgment
│   │   │                          (Pi-form, Pi-intro, Pi-elim,
│   │   │                           Σ-form, Σ-intro, Σ-elim,
│   │   │                           Ind-form, Ind-intro, Ind-elim, Ind-ι,
│   │   │                           Coind-form, Coind-intro, Coind-elim, Coind-ν,
│   │   │                           Id-form, Id-refl, Id-J,
│   │   │                           Quot-form, Quot-mk, Quot-lift)
│   │   ├── Reduction.lean       β / ι / ν / η
│   │   ├── Conversion.lean      definitional equality   (T-conv)
│   │   ├── Subtyping.lean       cumulativity + grade subsumption  (T-sub)
│   │   ├── Check.lean           decidable checker
│   │   │                          theorem check_iff  : check Γ e T = true ↔ HasType Γ e T
│   │   │                          theorem check_dec  : Decidable (HasType Γ e T)
│   │   └── Emit.lean            U-emit axiom for atomic operations
│   ├── Metatheory/              [PROVED — zero sorry]
│   │   ├── Preservation.lean    HasType ∧ Reduces → HasType
│   │   ├── Progress.lean        closed ∧ HasType → value ∨ ∃ step
│   │   ├── Normalization.lean   strong normalization (phased — see §7)
│   │   └── Consistency.lean     ¬ ∃ e, HasType ∅ e (Π (P : Type<0>), P)
│   ├── Smt/
│   │   ├── LibTerm.lean         SMT-LIB2 abstract syntax
│   │   ├── Encode.lean          kernel terms → SMT-LIB2 subset
│   │   └── Oracle.lean          Z3 subprocess, query cache in audit.smtq
│   ├── Elab/
│   │   ├── Syntax.lean          surface AST (matches fx_grammar.md)
│   │   ├── Parser.lean          hand-written recursive descent
│   │   ├── Desugar.lean         dot shorthand, pipe, elif, trailing comma, f-string
│   │   ├── Names.lean           name resolution, open/include/use
│   │   ├── Bidir.lean           bidirectional elaboration
│   │   ├── Unify.lean           unification for implicit type arguments
│   │   └── Elaborate.lean       main entry: String → Kernel.Term
│   ├── Eval/
│   │   ├── Value.lean           runtime values (WHNF canonical forms)
│   │   ├── Env.lean             evaluation environment
│   │   └── Interp.lean          tree-walking evaluator; uses step repeatedly
│   ├── CodeGen/                 Phase 7+ stubs per §20.3 / §20.5
│   │   ├── FXCore.lean          §20.2–§20.3 first IR below surface FX
│   │   ├── FXLow.lean           §20.3 flat, type-erased IR
│   │   ├── FXAsm.lean           umbrella re-export of the four arch files
│   │   └── FXAsm/
│   │       ├── X86_64.lean      §20.5 emit table (x86-TSO) — stub
│   │       ├── Arm64.lean       §20.5 emit table (ARM Flat) — stub
│   │       ├── Rv64.lean        §20.5 emit table (RVWMO) — stub
│   │       └── Mips64.lean      §20.5 emit table (MIPS64 RC) — stub
│   ├── Derived/                 kernel translations for §3.3–§26 features
│   │   ├── Adt.lean             §3.3 algebraic data types → Ind
│   │   ├── Record.lean          §3.4 records → single-ctor Ind
│   │   ├── Codata.lean          §3.5 codata → Coind (sized)
│   │   ├── Effect.lean          §9 effects → graded monads
│   │   ├── Session.lean         §11 sessions → linear Coind
│   │   ├── Machine.lean         §13 state machines → Ind(states) × Π(transitions)
│   │   ├── Contract.lean        §14 contracts → Σ(data, version) + migration π
│   │   └── Atomic.lean          §11.10, §20.5 atomics → Ind + U-emit
│   ├── Io/                      [trusted boundary]
│   │   ├── Prims.lean           print, read_file, time, randomness
│   │   └── Effects.lean         IO effect handlers dispatched via Lean IO
│   └── Cli/
│       └── Main.lean            fxi binary: check | run | repl | test
└── test/
    ├── Conformance/             canonical test suite; shared with fxc
    │   ├── kernel/              kernel-level programs
    │   ├── surface/             parses + elaborates + runs
    │   └── full/                end-to-end examples (hello world, …)
    ├── Kernel/                  unit tests for Kernel/
    ├── Metatheory/              regression tests from §27.2 known-unsoundness
    │                              corpus; every entry must be rejected
    └── Smoke/                   cross-cutting smoke tests
```

Size target by file group:

| Tree                 | Lines of Lean  | Trust level   |
|----------------------|----------------|---------------|
| `FX/Kernel/`         | ~3000 def + 5000 proof | trusted  |
| `FX/Metatheory/`     | ~5000–30000 proof      | proved   |
| `FX/Smt/`            | ~1500                  | trusted  |
| `FX/Elab/`           | ~7000                  | untrusted |
| `FX/Eval/`           | ~2500                  | untrusted |
| `FX/Derived/`        | ~5000                  | untrusted |
| `FX/Io/`             | ~500                   | trusted  |
| `FX/Cli/`            | ~500                   | untrusted |
| Tests                | ~3000                  | —        |

Total trusted+proved ≈ 14k–40k lines (range = SN proof variance).
Total untrusted ≈ 15k lines.

---

## 6. Kernel layer

The kernel encodes `fx_design.md` §31 exactly.  Ten term forms, 33
axioms, five judgment forms.

### 6.1 Term (`FX/Kernel/Term.lean`)

```
inductive Term : Type where
  | var    (i : Nat)                                    -- De Bruijn
  | app    (f : Term) (a : Term)
  | lam    (g : Grade) (t : Term) (b : Term)           -- graded binder
  | pi     (g : Grade) (t : Term) (b : Term)
  | sigma  (g : Grade) (t : Term) (b : Term)
  | type   (u : Level)
  | ind    (spec : IndSpec)
  | coind  (spec : CoindSpec)
  | id     (t : Term) (a : Term) (b : Term)
  | quot   (t : Term) (r : Term)
```

No other constructors.  Every surface feature in `fx_design.md` §3–§26
reduces to one of these via `FX/Derived/`.

### 6.2 Grade (`FX/Kernel/Grade.lean`)

```
structure Grade where
  usage        : Usage         -- Tier S, {0, 1, ω}
  effect       : EffectRow     -- Tier S, set of labels
  security     : Security      -- Tier S, {public, classified}
  lifetime     : Region        -- Tier S
  provenance   : Provenance    -- Tier S
  trust        : Trust         -- Tier S
  repr         : Representation -- Tier L
  observ       : Observability -- Tier S
  clock        : ClockDomain   -- Tier L
  complexity   : Complexity    -- Tier S
  precision    : Precision     -- Tier S
  space        : Space         -- Tier S
  overflow     : Overflow      -- Tier S
  fpOrder      : FpOrder       -- Tier S
  mutation     : Mutation      -- Tier S
  reentrancy   : Reentrancy    -- Tier S
  size         : Size          -- Tier S
  version      : Version       -- Tier V
  -- 18 of 21 dims explicit; Type and Refinement are Tier F
  -- (handled by the foundational judgments), Protocol is Tier T
  -- (handled by session checks in Elab/Session.lean).
```

Each dimension's operations (`+`, `*`, `≤`, validity) are Lean
functions with decidable equality.  Semiring laws are stated and
proved per-dimension; `Grade-semiring-laws` is the conjunction.

**Phased:** dimensions arrive over Phases 1–5 (§7).  Until a dimension
is implemented, its field defaults to the most permissive value and
all operations on it are no-ops.

### 6.3 Typing judgment (`FX/Kernel/Typing.lean`)

```
inductive HasType : Ctx → Term → Ty → Prop where
  | var        : Γ.lookup i = some T → HasType Γ (Term.var i) T
  | piIntro    : … (Pi-intro rule, Wood-Atkey context division)
  | piElim     : … (Pi-elim rule, graded application)
  | sigmaIntro : …
  | sigmaElim  : …
  | indForm    : …
  | indIntro   : …
  | indElim    : …
  | coindForm  : …
  | coindIntro : …   -- guardedness check (Abel-Pientka)
  | coindElim  : …
  | idForm     : …
  | idRefl     : …
  | idJ        : …
  | quotForm   : …
  | quotMk     : …
  | quotLift   : …
  | conv       : HasType Γ e T → Conv Γ T T' → HasType Γ e T'
  | sub        : HasType Γ e T → Subtype Γ T T' → HasType Γ e T'
```

Each constructor corresponds to one kernel axiom from Appendix H.  The
one-to-one mapping is enforced by `scripts/axiom-audit.sh`.

### 6.4 Check (`FX/Kernel/Check.lean`)

```
def check : Ctx → Term → Ty → Bool

theorem check_sound    : check Γ e T = true → HasType Γ e T
theorem check_complete : HasType Γ e T → check Γ e T = true
theorem check_dec      : Decidable (HasType Γ e T)
```

`check` is the decision procedure.  Soundness and completeness make it
a genuine decision procedure for typing.  Together with Decidable
(derived), the kernel is a total, verified type checker.

### 6.5 U-emit axiom (`FX/Kernel/Emit.lean`)

For each supported architecture `A` ∈ {x86_64, arm64, rv64, mips64}
and each atomic operation `(op, ord, width)` in `fx_design.md` §20.5,
there is a semantic mapping from the source-level operation to an
instruction sequence under `A`'s formal memory model (Appendix G).

```
axiom Uemit (A : Arch) (op : AtomicOp) (ord : Ordering) (w : Width)
           (inst : InstrSeq A) :
  EmitTable.mapping A op ord w = inst →
  ∀ st, sourceSem op ord w st = observeSeq A inst st
```

The 120-lemma refinement proof (§20.5) is the obligation this axiom
stands for.  `leanx` itself does not emit — it simulates high-level
atomic semantics directly.  The axiom matters for `fxc` codegen
correctness; it lives here because it is part of FX's trusted base.

---

## 7. Phasing

Each phase is a complete, shippable, zero-sorry milestone.  Features
outside the current phase are not supported — running them yields a
clean "not yet implemented" error.

### Current status (snapshot)

  * **Phases 0 + 1** — complete.  `lake build` green, axiom audit
    green, `fxi run hello.fx` works end-to-end on Bool + Nat
    programs with the 13-term kernel.
  * **Phase 2 (dependent types + inductives)** — in progress.
    Done: Σ + Π with graded binders, universe `Type<level>`
    with basic cumulativity, `Ind` + `indRec` terms for Bool /
    Nat / Option / List / Unit / Empty / Pair, ι-reduction at
    both term and value layers, two-pass `checkFile` with
    Term.const for forward + self-recursion, elaborator support
    for fn / let / block / if/else / match / type-params.
    Pending: records (B8), ADT surface declaration (B9),
    for/while loops (B10), named + default args (B12), top-
    level const / val / impl / open / module (B13), full lambda
    destructuring + modes (B11).
  * **Phases 3–9** — not started.  Effects exist in Grade but
    aren't enforced; refinements don't elaborate; remaining
    9 grade dimensions are stubs; coinductive + quotient Terms
    are accepted but have no intro/elim; metatheory proofs are
    `Prop` statements without bodies; optimizer / LSP / REPL
    are not scaffolded.

Last updated as of the Q27 Diagnostic skeleton + Q26
coverage-audit commits.  For per-task tracking, see the
`TaskList` in the active session's memory; the milestone
tracking that shipped each phase is in the `M*` tasks.

### Phase 0 — Setup (weeks 1–2)

* Directory tree.
* `lakefile.lean`, `lean-toolchain`.
* CI pipeline: `lake build` + `scripts/axiom-audit.sh` + test runner.
* Empty kernel skeleton (modules exist, compile as trivial stubs).
* `test/Smoke/stub.lean` passes.

**Demo:** `lake build` succeeds.  No FX programs run yet.

### Phase 1 — STLC + Usage (months 1–3)

Minimal kernel: simply-typed lambda calculus with the Usage grade
dimension {0, 1, ω} and a single universe `Type<0>`.

* Implemented kernel terms: `var`, `app`, `lam`, `pi`, `type`.
* Typing rules: `Pi-form`, `Pi-intro`, `Pi-elim`, `Grade-*`, `T-conv`,
  `T-sub`.
* Reduction: β, η.
* Check function + soundness + completeness.
* Evaluator: tree-walking step function + soundness.
* **Metatheory:**
  * `Preservation` (proved, ~1500 lines).
  * `Progress` (proved, ~800 lines).

**Elaborator:** recursive-descent parser for a minimal subset: `fn`,
`let`, `if`/`else`, literals, function application.  ~1500 lines.

**Evaluator:** tree-walking interpreter, primitive `print` via
`FX.Io.Prims`.  ~800 lines.

**Demo:**
```fx
fn id(x: i64) : i64 = x;
fn main() : unit with IO = begin fn
  print(id(42));
  return ();
end fn;
```
`fxi run hello.fx` prints `42`.

**Exit gate:** zero sorry in `Kernel/` and `Metatheory/`; conformance
test `test/Conformance/full/hello.fx` passes.

### Phase 2 — Dependent types and inductives (months 4–6)

* Add `sigma` term form.  Σ-form, Σ-intro, Σ-elim.
* Add universe polymorphism.  U-poly, cumulativity (T-sub extended).
* Add `ind` term form.  Ind-form, Ind-intro, Ind-elim, Ind-ι.
* Derived: `FX/Derived/Adt.lean` (ADTs → Ind),
  `FX/Derived/Record.lean` (records → single-ctor Ind).
* Pattern matching compilation in elaborator.
* Preservation / Progress extended.

**Demo:** `option(i64)`, `list(i64)`, `match` on ADTs, recursive sum.

### Phase 3 — Effects and linearity (months 7–9)

* Activate Effect grade dimension (rows of labels).
* Activate full Usage semantics (linear/affine, `drop`, `defer`).
* Effect subsumption, effect lattice joins.
* Preservation extended to carry effect row.

**Demo:** `fn print(s: string) : unit with IO`, linear file handle
lifecycle.

### Phase 4 — Refinements and SMT (months 10–12)

* Add refinement types `T { pred }` at elaboration.
* `FX/Smt/LibTerm.lean`, `Encode.lean`, `Oracle.lean` — Z3 subprocess
  + query cache in `audit.smtq`.
* `pre`, `post`, `decreases` clause elaboration.
* No preservation/progress changes (refinements are erasable).

**Demo:** verified `head(xs) pre length(xs) > 0`.

### Phase 5 — Remaining grade dimensions (year 2, one per ~3 weeks)

Security, Lifetime, Provenance, Trust, Representation, Observability,
Clock, Complexity, Precision, Space, Overflow, FP order, Mutation,
Reentrancy, Size, Version.  Each: add dimension to `Grade`, extend
typing rules, prove non-interference with existing dimensions.

### Phase 6 — Coinductive and quotient types (year 2)

* Add `coind`, `quot` term forms.
* Coind-form, Coind-intro, Coind-elim, Coind-ν (guardedness check).
* Quot-form, Quot-mk, Quot-lift.
* Derived: `FX/Derived/Codata.lean`, `FX/Derived/Session.lean`.

### Phase 7 — Derived surface features (year 2–3)

Effect handlers, state machines, contracts, hardware atomics (U-emit
active).  Each file in `FX/Derived/` goes from stub to
feature-complete.

### Phase 8 — Strong Normalization (year 3)

The big proof.  Budget: 10–30k Lean lines.  Risk: precedents
(MetaCoq's CIC SN) exist but FX's combination (graded modalities +
coinductives with size + universe cumulativity) is novel.
Consistency follows from SN in ~200 lines.

### Phase 9+ — Performance, tooling, IDE (year 3+)

Optimizer passes (themselves verified), caching, LSP, REPL.  All
optional — Phases 1–8 deliver full spec coverage; Phase 9 polishes.

---

## 8. Conformance suite

`test/Conformance/` is the executable specification.  It is shared
with `fxc` (once that exists) — both implementations must pass every
test.

### Format

Each test is one of:

* `foo.fx` + `foo.expected` — program compiles, runs, and prints
  exactly `foo.expected` (byte-equal).
* `foo.fx` + `foo.typecheck` — program type-checks (no runtime).
* `foo.fx` + `foo.rejected` — program is rejected with exactly the
  error code in `foo.rejected` (e.g. `T045`, `M001`).

Tests carry tags in comments:
```
// @section 3.3
// @phase 2
// @dimensions usage, effect
```

`scripts/coverage.sh` uses tags to compute coverage by spec section.

### Growth

Phase N adds tests for the features Phase N implements.  Tests never
leave the suite — they become regression tests.  The suite grows
monotonically.

### Cross-checking

When `fxc` exists, the CI pipeline runs every conformance test under
both `leanx` and `fxc`.  Mismatch is a CI failure.  This is the
differential-testing discipline described in `fx_design.md` §29.

---

## 9. Interface with the main project

### Inputs to `leanx`

`leanx` reads:

* The specification.  `fx_design.md`, `fx_grammar.md`, `fx_lexer.md`
  are authoritative for syntax and intended semantics.
* Appendix H of `fx_design.md` is authoritative for the axiom list;
  `AXIOMS.md` is `leanx`'s machine-readable projection.

### Outputs of `leanx`

* The `fxi` binary (`FX/Cli/Main.lean` → `build/bin/fxi`):

  ```
  fxi check FILE.fx        # type-check only
  fxi run FILE.fx          # elaborate + evaluate
  fxi repl                 # interactive
  fxi test DIR             # run conformance suite
  fxi dump --kernel FILE.fx  # emit kernel terms for inspection
  ```

* The conformance test runner (used by CI).

* Artifacts of the metatheory proof: `.olean` files for each theorem,
  which downstream tooling (`fxc`, documentation generators) can
  reference.

### Bootstrap path

To build `fxc` from scratch on a machine with no prior FX binary:

```
# One-time: install Lean 4 matching lean-toolchain.
cd leanx
lake build                                     # builds fxi binary
./build/bin/fxi run ../compiler/main.fx        # SLOW: interprets fxc source
   → writes fxc-seed binary                    #   produces a native fxc
./fxc-seed build ../compiler/                  # fast native rebuild
```

After the one-time bootstrap, `leanx` is no longer on the critical
path for users; the prebuilt `fxc` binary is distributed.

See `BOOTSTRAP.md` for detailed instructions including the fixpoint
check.

---

## 10. Build and test

### Build

```
cd leanx
lake build                          # compiles everything
lake build FX.Kernel                # specific target
```

### Test

```
lake exe fxi test test/Conformance  # conformance suite
lake test                           # unit + conformance + metatheory
scripts/axiom-audit.sh              # axiom allowlist + zero-sorry
scripts/coverage.sh                 # verified/implemented ratio
```

### Lean version

Pinned in `lean-toolchain`.  Upgrades happen once per quarter, with
all tests passing on both old and new versions for one release cycle.

### Dependencies

`std4` only.  No Mathlib.  Rationale: `std` has everything the kernel
needs (Nat, List, String, decidability, well-founded recursion);
Mathlib is large, changes often, and its algebraic structures are not
what we need (our semirings live in `FX/Kernel/Grade.lean` with exact
instance shapes).

---

## 11. Policies

### PR requirements

Every PR:

* `lake build` must succeed.
* `lake test` must pass.
* `scripts/axiom-audit.sh` must exit zero.
* Coverage ratio (verified/implemented) must not decrease.
* If adding to `Kernel/` or `Metatheory/`: zero new `sorry`.
* If adding to `Elab/`, `Eval/`, `Derived/`: any new `sorry` must be
  entered into `SORRY.md` with owner and target removal date.

### Adding a new axiom

Blocked.  Requires an RFC under `docs/rfcs/`, update to `AXIOMS.md`
and `fx_design.md` Appendix H, two maintainer approvals, and a
regression test in `test/Kernel/Axioms/`.  Expected frequency: ~never
post-1.0.

### Removing a sorry

Replace `sorry` with a proof.  Single-maintainer approval.  `SORRY.md`
updated to move the entry to the closed section.

### Breaking kernel changes

Kernel changes are semantic.  They require:

1. An RFC.
2. Re-run of the full metatheory proof suite (all four theorems).
3. Bump of the `leanx` minor version.
4. Update to `fxc`'s conformance tests.
5. Three-maintainer approval.

### Release cadence

* Patch: any time.  Bug fixes in `Elab/`, `Eval/`, `Derived/`.
* Minor: ~quarterly.  New phase milestones.
* Major: only at kernel-breaking changes or FX language version bumps.

---

## 12. Open risks

### Risk 1 — Strong Normalization proof

SN for a graded modal dependent type theory with coinductives and
universe cumulativity has not been mechanized at FX's scope.
Precedents (MetaCoq for CIC, Abel-Pientka-Danielsson for sized
guardedness, Granule for three-dimension graded) each cover subsets.

**Impact if it blows up:** Phase 8 slips from "year 3" to "year 5,"
does not affect Phases 1–7 which ship incrementally.

**Mitigation:** Start Phase 8 exploratory work during Phase 5
(18-month lead time).  Collaborate with proof-assistant researchers.
Budget 30k lines (3x nominal).

### Risk 2 — Graded dimension interactions

21 dimensions produce `C(21,2) = 210` pairwise interactions.  §6.8
catalogs 10 soundness collisions; the remaining 200 require
non-interference lemmas.

**Impact if it blows up:** Phase 5 slips.

**Mitigation:** Tier classification (S/L/T/F/V) isolates interactions
by shape.  Non-interference within a tier follows from tier axioms.
Cross-tier interactions are <50 cases, addressable in ~2 months.

### Risk 3 — SMT incompleteness

Z3 can time out or answer UNKNOWN on obligations that should discharge.
This is a Z3 issue, not a `leanx` issue, but manifests as `leanx`
rejecting valid programs.

**Mitigation:** Query cache + timeout escalation.  For critical cases,
cross-check against CVC5.  Document the decidable fragment (§10.16)
explicitly so users know what is guaranteed.

### Risk 4 — Lean 4 ABI / Lake changes

Lean 4 evolves; occasional breaking changes in Lake or the standard
library.

**Mitigation:** Pin version in `lean-toolchain`.  Upgrade deliberately,
not automatically.  One release cycle of "both versions pass" before
switching.

### Risk 5 — Parser / elaborator bugs affecting users

The elaborator is untrusted but user-facing.  Bugs produce wrong error
messages or rejection of valid code.  Not a soundness risk but an
adoption risk.

**Mitigation:** Large conformance suite, fuzzing from Phase 4 onward,
`fxi repl` for interactive testing.

---

## 13. Design decisions explicitly rejected

The following were considered and rejected.  Documented here so they
don't come back.

**Option: make leanx a separate GitHub repo outside `fx/`.**
Rejected.  leanx is the canonical semantics of FX; it belongs in the
main repo.  The clean trust story is "the language is defined by
`leanx/`" — requiring a cross-repo jump weakens that.

**Option: dual interpreter (Lean-in-Lean and FX-in-FX both in core).**
Rejected.  Full duplication is the F* trap.  A cross-verification
interpreter in FX exists but as a separate project
(`fx-self-interp/`), not as core.

**Option: skip Phase 1's metatheory, catch up later.**  Rejected.
This is exactly what F* did, and "later" never came.  The zero-sorry
invariant must be total from Phase 1.

**Option: depend on Mathlib for algebraic structure substrate.**
Rejected.  Mathlib changes frequently; our semirings are small enough
to build in `FX/Kernel/Grade.lean` directly; Mathlib's categorical
abstractions don't match our tier system.

**Option: native Lean 4 tactic mode for elaboration.**  Rejected.  The
elaborator must be a function we can reason about.  Lean tactic mode
is for proofs about `leanx`, not for `leanx`'s own elaboration.

**Option: use Lean 4 macros to embed FX as an EDSL.**  Rejected.  FX
has its own grammar; treating it as an EDSL conflates two languages
and makes error messages opaque.

**Option: skip the Smt layer and prove refinements in Lean.**
Tempting but rejected.  SMT gives users a reasonable discharge
experience; requiring Lean proofs for every refinement obligation
makes the language unusable for non-expert users.  We accept Z3 as a
trusted oracle with audit-log discipline.

---

## 14. First deliverable — Phase 0 exit

The immediate next work produces the following, verifiable by `lake
build` + `lake test` + `scripts/axiom-audit.sh`:

* `leanx/lakefile.lean` — library target `FX`, exe target `fxi`.
* `leanx/lean-toolchain` — pinned Lean version.
* `leanx/FX/Core.lean` — empty entry point.
* `leanx/FX/Util/Basic.lean` — common utilities (error type, pretty
  print stub).
* `leanx/FX/Kernel/Term.lean` — type declaration stub (ten
  constructors, bodies `sorry` → TODO replaced with unit).
* `leanx/FX/Kernel/Typing.lean` — empty relation.
* `leanx/FX/Cli/Main.lean` — "fxi: not yet implemented" stub.
* `leanx/scripts/axiom-audit.sh` — functional, passes on empty state.
* `leanx/AXIOMS.md` — the 33-axiom list.
* `leanx/SORRY.md` — empty (no sorries yet).

**Exit criterion:** `lake build` succeeds, `scripts/axiom-audit.sh`
passes, `./build/bin/fxi --version` prints something.

Timeline: 1 week once the directory tree exists.

Phase 1 follows immediately with the STLC-plus-usage milestone
described in §7.

---

## 15. References

* `../fx_design.md` §31 — The Kernel Calculus.
* `../fx_design.md` Appendix H — Complete Kernel Axiom List.
* `../fx_design.md` §27.4 — Core Meta-Theorems.
* `../fx_grammar.md` — Formal grammar (LALR(1)-compatible).
* `../fx_lexer.md` — Lexical structure.
* Carneiro, *Lean4Lean: Verifying Lean 4's typechecker in Lean 4*
  (2024), https://arxiv.org/abs/2403.14064.
* Sozeau et al., *The MetaCoq Project*, JAR 2020.
* Wood & Atkey, *A Framework for Substructural Type Systems*,
  ESOP 2022.
* Orchard, Liepelt, Eades, *Quantitative Program Reasoning with
  Graded Modal Types*, ICFP 2019.
* Abel & Pientka, *Copatterns: Programming infinite structures by
  observations*, POPL 2013.
