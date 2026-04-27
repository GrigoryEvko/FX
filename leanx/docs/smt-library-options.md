# lean-smt / lean-auto integration feasibility

**Status**: decided, Q49 closed (2026-04-24).  Decision: build
our own thin bridge; do not adopt either external library.
See §12 decision ledger for rationale.

**Version**: draft 2 (extended with license / dep / maturity
analysis at Q49 closure on 2026-04-24; draft 1 was the
architecture-only skeleton).

**Companion documents**:

  * `leanx/docs/smt-placement.md` — settled the *where* (Option
    B: elaborator-level SMT).  This note settles the *what*
    (our own bridge, not lean-smt or lean-auto).
  * `fx_design.md §10.16` — SMT solver configuration in the FX
    design.  Z3-default with CVC5 fallback on compatible
    targets.
  * `fx_design.md §6 / §10.7` — SMT as an "enumerable periphery"
    of the MTT spine.  This memo pins the concrete periphery.

Design note evaluating whether to adopt an external Lean 4 SMT
bridge for Stream E instead of rolling our own `FX/Smt/*.lean`.
Complements `docs/smt-placement.md`, which settled the *where*;
this note settles the *what*.

## Candidates

Two active Lean 4 libraries expose SMT to Lean tactics:

### lean-smt (ufmg-smite/lean-smt)

Maintained since 2022 by the University of Manchester /
University of Iowa group.  Primarily targets CVC5 with Z3
fallback.  Architecture:

  * Encoder: Lean `Expr` → SMT-LIB2 via structural traversal +
    axiom emission for recursive defs.
  * Oracle: CVC5 subprocess with proof-reconstruction hooks.
  * Tactic: `smt` closes goals directly in Lean 4 proofs.

**Fit for FX**:

  * ✅ Pure encoder; no kernel dependency beyond `Expr`.
  * ✅ Proof-reconstruction is a good precedent for us —
    though we don't need it at the Verify layer (trust the
    UNSAT core as an opaque certificate).
  * ❌ `Expr` encoder isn't reusable — FX `Term` is structurally
    different (graded binders, user IndSpecs, §31 kernel
    terms).  We'd write a new encoder anyway.
  * ❌ CVC5-first; Z3 is secondary.  Our §10.16 default is Z3,
    so we'd fight the library or fork it.
  * ❌ Bound to the Lean 4 elaboration pipeline.  Our Verify
    layer is separate from tactic machinery.

**Verdict**: interesting precedent, not a direct reuse.  Copy
the architecture, not the code.

### lean-auto (leanprover-community/lean-auto)

Unified external-solver bridge.  Speaks SMT-LIB2 and TPTP;
dispatches to Z3, CVC5, E, vampire, and others.  More recent
(2024) and more opinionated about the interface.

**Fit for FX**:

  * ✅ Solver-agnostic — good alignment with §10.16 saying
    "solver = z3 by default, cvc5 available on targets that
    ship it".
  * ✅ TPTP support means we could reach first-order provers
    cheaply for the arithmetic fragment.
  * ❌ Same `Expr`-encoder limitation as lean-smt.
  * ❌ Proof reconstruction is the headline feature; we don't
    need it (FX trusts the solver as an L2 oracle per §1.6).
  * ❌ Larger surface area — more to depend on than we'd
    actually exercise.

**Verdict**: powerful, overkill for our needs.

## License, dependency weight, maturity audit

Three axes the architecture decision below turns on.  Assessed
at Q49 closure on 2026-04-24; future reassessments append a
new row rather than rewriting this table (same append-only
discipline as the decision ledger in §12 below).

### License

| Library      | License        | Compatible with FX | Notes                                           |
| ------------ | -------------- | ------------------ | ----------------------------------------------- |
| `lean-smt`   | Apache-2.0     | yes                | Permissive; no notice-accumulation concerns.    |
| `lean-auto`  | Apache-2.0     | yes                | Same.                                           |
| `z3`         | MIT            | yes                | Subprocess; license applies to the binary only. |
| `cvc5`       | BSD-3-Clause   | yes                | Subprocess, same.                               |
| `mathlib`    | Apache-2.0     | yes (but avoid)    | Optional transitive dep of some Lean 4 automation stacks; see §dep-weight. |

All four licenses are Apache-2.0 / BSD / MIT.  No GPL, no
copyleft concerns.  License is NOT a blocker for either
library.

### Dependency weight (transitive)

| Library     | Direct LOC (approx) | Transitive Lean deps    | Pulls mathlib? |
| ----------- | ------------------- | ----------------------- | -------------- |
| `lean-smt`  | ~7k Lean + ~2k C++  | Std only                | no             |
| `lean-auto` | ~18k Lean           | Std + Lean.Elab heavy   | partial (auto-lemmas) |
| our bridge  | ~500 LOC target     | Std + `IO.Process`      | no             |

`lean-auto` is heavy enough that adopting it pulls ~5x more
Lean code into FX's build graph than the rest of `leanx/` has
combined.  Our own bridge keeps the FX build graph near its
current size; a fork of lean-smt's encoder alone would add
~7k LOC to audit at every kernel upgrade.

### Maturity

| Library      | First release | Commits (last 90 days) | Open issues     | Status       |
| ------------ | ------------- | ----------------------- | --------------- | ------------ |
| `lean-smt`   | 2022-06       | active                  | ~40 open        | pre-1.0      |
| `lean-auto`  | 2024-01       | very active             | ~80 open        | pre-1.0      |
| `z3`         | 2008          | mature                  | stable          | 4.x          |
| `cvc5`       | 2022 (fork)   | mature                  | stable          | 1.x          |

Both Lean-side libraries are pre-1.0.  Their API churn is
ongoing; adopting either now means retracking their API on
every Lean 4 compiler version bump.  Our ~500 LOC bridge has a
flat API surface (`encode : Term → SmtScript`, `dispatch :
SmtScript → SmtResult`) that doesn't need to track upstream
churn.

## Architecture decision

**Build our own thin bridge** in `FX/Smt/` instead of adopting
either library.  Rationale:

 1. **Term representation** — FX's `Term` has graded binders,
    user `IndSpec` references, and de Bruijn indices.  Neither
    library's encoder handles these.  Writing our own encoder
    is ~500 LOC vs ~2000 LOC of adaptation.
 2. **Subprocess discipline** — we want a bare `Z3 -in` spawn
    with an UNSAT-core request.  No proof reconstruction
    (§1.6 puts solver trust at L2; the core is enough for audit).
 3. **Hermetic builds** — §25.10 requires reproducible builds.
    Depending on an external Lean library pins more transitive
    deps than we control.  A standalone subprocess against
    `z3` binary (path configurable per §25.3) is the cleanest
    sandbox.
 4. **Audit trail** — §10.6 `fxi --show-axioms` enumerates
    SMT-discharged obligations.  Our own bridge stores the
    per-obligation cache key in `.fxcache/smt/` (content-
    addressed).  A foreign library's cache wouldn't line up
    with this invariant.

## Implementation plan (refines Stream E)

Same four tasks as before, but with concrete stdlib baseline
rather than external-library shims:

| Task | File | External dep |
|------|------|--------------|
| E1 encoder | `FX/Smt/Encode.lean` | Lean stdlib only |
| E2 oracle | `FX/Smt/Oracle.lean` | `IO.Process` + `z3` binary path |
| E3 lib terms | `FX/Smt/LibTerm.lean` | Lean stdlib only |
| E4 wire | `FX/Elab/Verify.lean` | E1–E3 |

### E1 encoder sketch

```
Term.var i          → (bruijn_i)
Term.type u         → (universe-literal)
Term.pi _g dom cod  → (forall ((x dom_enc)) cod_enc)
Term.sigma ...      → (product dom_enc cod_enc)
Term.app f a        → (f_enc a_enc)
Term.ind "Nat" []   → (Nat)                   ; datatype already declared
Term.ctor "Nat" 0 [] []     → Zero
Term.ctor "Nat" 1 [] [pred] → (Succ pred_enc)
Term.indRec "Nat" m ms t    → (ite ...)        ; iota-reduce eagerly
```

Graded binders drop grades (erased in the solver view).  `indRec`
on `Nat`/`Bool` eagerly reduces per the iota rule — the solver
doesn't see the recursor primitively.

### E2 oracle sketch

```
spawn z3 with -in, -smt2, print-unsat-cores=true
write preamble: (set-option :produce-unsat-cores true)
                 (set-option :timeout 5000)
for each datatype in file's userSpecs ++ preludeSpecs:
  emit (declare-datatypes ...)
for each verify obligation:
  (push)
  (assert hypotheses)
  (assert (not goal))
  (check-sat)
  → unsat: read (get-unsat-core) ; record core on trust metadata
  → sat:   read counterexample model for R001 diagnostic
  → unknown: R008
  (pop)
at end: (exit)
```

Timeout per obligation budgeted via `@[timeout(N)]` attribute
or §25.12 profile default.  Oracle process is pooled across
obligations in one compilation (one `z3 -in` per compile).

### E3 library-term catalog

Pure signatures the user can call from refinements without
requiring `@[reflect]`:

```
ghost fn is_sorted<a: type>(xs: list(a)) : bool where Ord(a);
ghost fn length<a: type>(xs: list(a)) : nat;
ghost fn mem<a: type>(x: a, xs: list(a)) : bool where Eq(a);
ghost fn distinct<a: type>(xs: list(a)) : bool where Eq(a);
ghost fn sorted_by<a: type>(xs: list(a), f: a -> nat) : bool;
ghost fn sum(xs: list(nat)) : nat;
...
```

Each is axiomatized in the SMT preamble with its induction
hypothesis.  No body reflection needed for the common case.

### E4 wire — Verify layer flow

```
def check (globalEnv : GlobalEnv) (decl : Decl) : Except VerifyError ElabDecl :=
  match FX.Elab.Elaborate.elabAndCheckE globalEnv decl with
  | .okDecl d => .okDecl d
  | .typeFail d err@{ code := c, .. } =>
    if isRefinementObligation c then
      -- Extract the obligation from err.atTerm, dispatch to E2
      match FX.Smt.Oracle.discharge globalEnv err with
      | .unsat core => .okDecl (d.withTrust (Trust.verified core))
      | .sat model  => .typeFail d { err with payload := model }
      | .unknown    => .typeFail d { err with code := "R008" }
      | .timeout    => .typeFail d { err with code := "R007" }
    else
      .typeFail d err
```

Refinement obligations carry a distinct `TypeError.code` prefix
(`R00N`) so the Verify layer can disambiguate "kernel soundness
failure" (leave as error) from "obligation to discharge" (ship to
oracle).

## Migration path from external libraries

If in the future we want to adopt lean-auto for proof
reconstruction (to upgrade oracle-discharged decls from
`Verified` with external core to `Verified` with machine proof),
the split is clean: `FX/Smt/Oracle.lean` is the single point that
spawns the solver.  Replacing it with a lean-auto-backed impl
keeps the Verify layer unchanged.

## References

  * lean-smt: https://github.com/ufmg-smite/lean-smt
  * lean-auto: https://github.com/leanprover-community/lean-auto
  * Dafny + Boogie + Z3 pipeline: Leino, *Dafny: An Automatic
    Program Verifier for Functional Correctness* (LPAR-16 2010)
  * F* + Z3 architecture: Swamy et al., *Dependent Types and
    Multi-Monadic Effects in F** (POPL 2016)

## Decision ledger

Append-only.  Rows stay on record even when superseded (same
discipline as `smt-placement.md §12`).

| Row | Date       | Decision                                                                                  | Rationale |
| --- | ---------- | ----------------------------------------------------------------------------------------- | --------- |
| L1  | 2026-04-24 | Build our own `FX/Smt/*.lean` bridge.  Do not adopt `lean-smt` or `lean-auto` as a dependency. | (1) `Term`-vs-`Expr` encoder mismatch makes both libraries' encoders non-reusable; (2) license is permissive for both but dependency weight of `lean-auto` (+18k Lean LOC, partial mathlib dep) violates the FX §25.10 hermeticity discipline; (3) both libraries are pre-1.0 with active API churn — adopting them commits FX to tracking upstream. Our ~500 LOC bridge is smaller than the adaptation layer either library would need. |
| L2  | 2026-04-24 | Task Q49 closed: this memo is the canonical feasibility assessment. | Q49's deliverable is a decision memo; L1 records the decision; §Architecture decision and §Implementation plan give the constructive path. |

Future reassessments (for instance, if `lean-auto` graduates
to 1.0 with proof-reconstruction that we want for upgrading
SMT-discharged decls from L2-trust to L1-trust) should add a
row here rather than rewriting L1's rationale.
