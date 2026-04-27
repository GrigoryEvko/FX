# Metatheory status

Snapshot of the four core soundness theorems per `fx_design.md`
§27.4 and their current state in `leanx`.  Companion to
`docs/MetatheoryCorpus.md` (layer 1 of §27.3 — known-witness
smoke tests) and `AXIOMS.md` (trust base allowlist).

This file is the project's layer-4 "self-verified metatheory"
tracker: it shows which theorems are stated, which are proved,
and what blocks each remaining proof.

## The four theorems

Per `fx_design.md` §27.4 all four are stated in Lean 4 at
`FX/Metatheory/{Preservation,Progress,Consistency,Normalization}
.lean`.  Each is a concrete `def X : Prop := ...`; running `lake
build` type-checks every statement but does not prove it.

| Theorem | File | Status | Blocked by |
|---|---|---|---|
| `Preservation` | `FX/Metatheory/Preservation.lean` | stated | Phase 8 |
| `Progress` | `FX/Metatheory/Progress.lean` | stated | Phase 8 |
| `Consistency` | `FX/Metatheory/Consistency.lean` | stated | SN |
| `StrongNormalization` | `FX/Metatheory/Normalization.lean` | stated | Phase 8+ |

`stated` means the `Prop` compiles — the theorem's type is
well-formed.  No `sorry` exists; the statement has no proof
body.  `scripts/axiom-audit.sh` tolerates this because the defs
produce `Prop` values, not `Prop`-typed terms we assume.

## Statements

### Preservation

```
∀ (context term reduct expectedType) (globalEnv),
  check context term expectedType globalEnv = .ok () →
  betaStep? term = some reduct →
  check context reduct expectedType globalEnv = .ok ()
```

Well-typed terms stay well-typed under one β or ι reduction
step.  Covers the two head rules in `Term.betaStep?`; η lands
when `Conversion.convEq` gains real content; ν lands when
coinductive reduction is implemented (Phase 6).

### Progress

```
∀ (term expectedType) (globalEnv),
  check [] term expectedType globalEnv = .ok () →
  isCanonical term ∨ (betaStep? term).isSome
```

Closed well-typed terms are either canonical head-values or
can take a step.  `isCanonical` is a syntactic predicate
covering the 8 head-value constructors (type, pi, sigma, lam,
ind, ctor, id, quot).  Open terms with free variables use a
variant that reduces to neutrals — not currently stated.

### Consistency

Currently stated as a `Prop` that holds iff no closed term has
type `Π (P : Type<0>). P`.  The kernel is consistent as a
logic: no proof of False exists.  Proved from SN for the pure
MLTT fragment (the emit-table axiom U-emit is non-reducing at
the kernel layer and doesn't threaten consistency).

### Strong Normalization

```
∀ (term expectedType) (globalEnv),
  check [] term expectedType globalEnv = .ok () →
  ∃ (normalForm fuel),
    normalize fuel term = normalForm ∧ betaStep? normalForm = none
```

Every well-typed term has a finite reduction path to a normal
form.  **Explicitly deferred to Phase 8+** per SPEC.md §7.  SN
proofs for MLTT-family calculi run 10–30 kLOC of proof work;
FX's graded-modal-with-coinductives-and-universes kernel is a
novel combination whose SN argument is a multi-person-month
project on its own.

## Current correctness argument

Without SN, the interpreter's day-to-day correctness rests on:

  1. **Fuel-bounded `normalize`** — `FX.Kernel.Reduction.normalize`
     takes explicit `Nat` fuel; runaway reduction surfaces as
     `R_fuel` rather than a hang.  `defaultFuel = 4096` is the
     one kernel-trusted constant; it's documented at the
     `whnf` call site in `Reduction.lean`.
  2. **Layer-1 unsoundness corpus** (`docs/MetatheoryCorpus.md`)
     — every cataloged type-theory bug from the literature is a
     permanent rejection test.  The kernel currently rejects
     entries #1 (Atkey-2018 Lam) and parts of the corpus
     reachable through the Phase-2.2 surface (#2 session aliasing
     lands when sessions do; #4-#6 land when universes + Ind +
     Coind gain their full content).
  3. **Kernel axiom audit** — `scripts/axiom-audit.sh` keeps the
     allowlist at 0 declared axioms (33 entries in AXIOMS.md,
     12 realized as `partial def`, 4 proved, 17 pending).

## Proof-roadmap notes

### Preservation + Progress

Both proofs follow the standard pattern — structural induction
on the typing derivation, case analysis on head reductions.
Budget estimate (precedent: Lean 4 kernel verification):
  * Preservation: ~2,000 lines including grade preservation.
  * Progress: ~800 lines.

Blocked on Phase 8 because the mechanization depends on:
  * a proper `HasType` inductive relation (currently typing is
    a partial-def decision procedure that reduces on demand);
  * stability under substitution lemmas for `shift` / `subst`
    across every term constructor (partially realized in
    `FX/Kernel/Substitution.lean`'s `shift_zero` but needs
    more);
  * completeness of `openWith` for substitution into dependent
    codomain types.

### Consistency

Proof-sketch: closed term of type `Π (P : Type<0>). P` would
normalize (by SN) to a canonical form.  The only canonical
`Π` is `lam`, whose body would need type `P` for an arbitrary
`P` in a context with one binder — impossible without another
term of the required type, giving infinite regress.  Cleans up
in ~200 lines once SN is in hand.

### Strong Normalization

Three standard approaches:

  * **Girard's candidates of reducibility** — semantic argument
    assigning each type a reducibility candidate set.  Standard
    for pure MLTT; graded extension via Atkey's indexed-
    reducibility (ICFP 2018) but not yet mechanized at scale.
  * **Tait's saturated sets** — similar structure, sometimes
    easier for the Ind / Coind cases.
  * **Structural / big-step approach** — MetaCoq's current
    strategy.  Recent (2020s) and still the subject of active
    research for graded MLTT variants.

Expected cost: 10–30 kLOC, 6–24 person-months.  Cited precedents
in AXIOMS.md §H.9 commentary.

## Addition discipline

Adding a new theorem statement:

  1. State as `def X : Prop := ...` in a new file under
     `FX/Metatheory/`.
  2. Add a row to the table at the top of this file.
  3. Document the blocking dependency (kernel extension, SN,
     etc.) and cite the planned phase in SPEC.md §7.
  4. If mechanizing a proof, keep the statement unchanged and
     add the proof body; update the table from `stated` →
     `proved`.

Removing a theorem requires an RFC — the four core statements
in particular are load-bearing for the trust model described
in fx_design.md §1.2 and §27.
