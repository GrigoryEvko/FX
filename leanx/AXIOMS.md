# leanx — Canonical Axiom Allowlist

This file is the single source of truth for the axiom allowlist enforced
by `scripts/axiom-audit.sh`.  Every `axiom` declaration in `FX/Kernel/**`
must correspond to exactly one entry here.

The list is one-to-one with `../fx_design.md` Appendix H.  Changes to
this file require coordinated updates to Appendix H, an RFC under
`docs/rfcs/`, and two maintainer approvals.

**Total: 33 entries.  The count is load-bearing.**

## Current state (Phase 2.2)

**0 of 33 entries declared as `axiom` in Lean.**  Many entries are
now **realized** — a partial-def function in `FX/Kernel/Typing.lean`
or `FX/Kernel/Reduction.lean` implements the rule directly, and no
axiom declaration is needed.  Others remain **pending** as their
term forms and kernel rules ship in Phase 2.3+.

The `scripts/axiom-audit.sh` gate passes at every commit because no
`axiom` is declared in `FX/Kernel/**` yet — every rule in scope for
Phase 2.2 is either a `partial def` (realized as computable code
that termination-checks under Lean's kernel via fuel or
`partial def`) or a `by decide` theorem over a finite carrier
(Grade semiring laws on `Usage` / `Security` / etc.).

Whenever possible we prefer to realize an Appendix-H entry as a
**proved theorem** or a **realized `partial def`** over the
relevant finite structure.  Only the genuinely axiomatic rules —
principally the `U-emit` hardware-memory-model refinement (§H.10)
and the strong-normalization meta-theorems (Phase 8) — will be
declared as `axiom` when their content lands.

The status column below distinguishes:

* **realized** — implemented as a computable `def` / `partial def`
  in `FX/Kernel/**` whose body IS the rule.  No axiom declared;
  kernel executes the rule directly.
* **pending** — slated to be declared as `axiom` when the kernel term
  forms land; currently neither declared nor proved.
* **stated** — stated as a theorem (`Prop` def); Lean proof in
  progress.
* **proved** — proved in Lean 4 without an `axiom`.  Listed here for
  provenance; `scripts/axiom-audit.sh` tolerates the row but does not
  require a matching `axiom` declaration.
* **removed** — no longer needed; requires an RFC under `docs/rfcs/`.

`scripts/axiom-audit.sh` checks that every declared `axiom` in
`FX/Kernel/**` corresponds to a row here, and that no `axiom` is
declared outside `FX/Kernel/**`.  It does NOT require that every row
here correspond to a declared `axiom` — many entries will be discharged
as theorems rather than postulated.  This is deliberate:  the trusted
base is whichever subset of entries is declared `axiom` at any given
time, and that subset only ever shrinks.

---

## H.1 — Universes (5)

| Name      | Status  | Lean file                 | Reference                           |
|-----------|---------|---------------------------|-------------------------------------|
| `U-wf`    | pending | `FX/Kernel/Level.lean`    | `fx_design.md` Appendix H.1, §31.4  |
| `U-hier`  | pending | `FX/Kernel/Level.lean`    | Appendix H.1                        |
| `U-cumul` | pending | `FX/Kernel/Level.lean`    | Appendix H.1                        |
| `U-level` | pending | `FX/Kernel/Level.lean`    | Appendix H.1                        |
| `U-poly`  | pending | `FX/Kernel/Level.lean`    | Appendix H.1                        |

Precedents: Lean 4 `Sort`, Coq Polymorphic universes (Sozeau-Tabareau
ECOOP 2019), Agda `Set` levels.

---

## H.2 — Pi (dependent function) (3)

| Name       | Status  | Lean file                  | Reference       |
|------------|---------|----------------------------|-----------------|
| `Pi-form`  | realized | `FX/Kernel/Typing.lean` (infer on `.pi`)    | Appendix H.2    |
| `Pi-intro` | realized | `FX/Kernel/Typing.lean` (infer on `.lam`)   | Appendix H.2, Wood-Atkey LICS 2022 |
| `Pi-elim`  | realized | `FX/Kernel/Typing.lean` (infer on `.app`)   | Appendix H.2    |

Precedent: Martin-Löf type theory (1984).  `Pi-intro` adopts the
**Wood-Atkey 2022 corrected Lam rule** with context division — the
Atkey 2018 rule is unsound (see §H.8 commentary and
`docs/MetatheoryCorpus.md` entry #1).  Phase 1 realizes the
division operator in `FX/Kernel/Grade/Usage.lean::div`; when the
Pi typing rule lands in `FX/Kernel/Typing.lean` it will use that
operator in the premise.

---

## H.3 — Sigma (dependent pair) (3)

| Name       | Status  | Lean file                  | Reference       |
|------------|---------|----------------------------|-----------------|
| `Σ-form`   | realized | `FX/Kernel/Typing.lean` (infer on `.sigma`)    | Appendix H.3    |
| `Σ-intro`  | pending  | `FX/Kernel/Typing.lean` (no pair term yet)     | Appendix H.3    |
| `Σ-elim`   | pending  | `FX/Kernel/Typing.lean` (no `split` term yet)  | Appendix H.3    |

---

## H.4 — Inductive (4)

| Name         | Status  | Lean file                 | Reference       |
|--------------|---------|---------------------------|-----------------|
| `Ind-form`   | realized | `FX/Kernel/Typing.lean` (infer on `.ind`)     | Appendix H.4    |
| `Ind-intro`  | realized | `FX/Kernel/Typing.lean` (infer on `.ctor`)    | Appendix H.4    |
| `Ind-elim`   | realized | `FX/Kernel/Typing.lean` (infer on `.indRec`)  | Appendix H.4; method-type check T116 pending |
| `Ind-ι`      | realized | `FX/Kernel/Reduction.lean` + `FX/Eval/Interp.lean` | Appendix H.4    |

Precedent: CIC, Coq / Lean 4 inductive families.  Strict positivity
required; enforced by `FX/Kernel/Term.lean`'s well-formedness check
on `IndSpec`.

---

## H.5 — Coinductive (4)

| Name          | Status  | Lean file                 | Reference                       |
|---------------|---------|---------------------------|---------------------------------|
| `Coind-form`  | pending | `FX/Kernel/Typing.lean`   | Appendix H.5                    |
| `Coind-intro` | pending | `FX/Kernel/Typing.lean`   | Appendix H.5                    |
| `Coind-elim`  | pending | `FX/Kernel/Typing.lean`   | Appendix H.5                    |
| `Coind-ν`     | pending | `FX/Kernel/Reduction.lean`| Abel-Pientka POPL 2013, H.5     |

The guardedness check is Abel-Pientka copatterns; decidable by the
checker in `FX/Kernel/Check.lean`.

---

## H.6 — Identity (3)

| Name       | Status  | Lean file                  | Reference     |
|------------|---------|----------------------------|---------------|
| `Id-form`  | realized | `FX/Kernel/Typing.lean` (infer on `.id`)       | Appendix H.6  |
| `Id-refl`  | pending  | `FX/Kernel/Typing.lean` (no refl term yet)     | Appendix H.6  |
| `Id-J`     | pending  | `FX/Kernel/Typing.lean` (no J eliminator yet)  | Appendix H.6  |

Strict propositional equality with J eliminator.  Extensionality is
not admitted — users who need function extensionality can opt into it
as a declared `axiom` under `fx_design.md` §1.6's per-definition
escape-hatch discipline (not in `leanx`'s kernel).

---

## H.7 — Quotient (3)

| Name         | Status  | Lean file                 | Reference                         |
|--------------|---------|---------------------------|-----------------------------------|
| `Quot-form`  | realized | `FX/Kernel/Typing.lean` (infer on `.quot`)     | Appendix H.7, §3.7                |
| `Quot-mk`    | pending  | `FX/Kernel/Typing.lean` (no quotMk term yet)   | Appendix H.7                      |
| `Quot-lift`  | pending  | `FX/Kernel/Typing.lean` (no quotLift term yet) | Appendix H.7 (Lean 4 `Quot.lift`) |

Set quotients (not HIT).  `Quot.lift` is the sole eliminator —
pattern-matching to a representative is not admitted.

---

## H.8 — Grade algebra (5)

| Name                    | Status  | Lean file                           | Reference       |
|-------------------------|---------|-------------------------------------|-----------------|
| `Grade-semiring-laws`   | proved  | `FX/Kernel/Grade/Usage.lean` et al. | Appendix H.8    |
| `Grade-subsumption`     | pending | `FX/Kernel/Typing.lean` (future)    | Appendix H.8    |
| `Grade-division`        | proved  | `FX/Kernel/Grade/Usage.lean`        | Wood-Atkey LICS 2022 |
| `Grade-zero`            | proved  | `FX/Kernel/Grade/Usage.lean`        | Abel-Danielsson-Eriksson ICFP 2023 |
| `Grade-lattice`         | proved  | `FX/Kernel/Grade/*.lean`            | Appendix H.8    |

`Grade-semiring-laws` is the conjunction of the semiring axioms for
each Tier S dimension.  Proved per-dimension in the files under
`FX/Kernel/Grade/` (one file per dimension, all laws discharged by
`decide` or by small case-analysis).  Because each dimension is
finite (or a finite quotient), the laws are all decidable and no
`axiom` declaration is needed — the `proved` status reflects this.

`Grade-division` is the context-division operator underpinning the
corrected `Pi-intro` rule.  Wood & Atkey, *A Framework for
Substructural Type Systems*, LICS/ESOP 2022.  Implemented as
`FX.Kernel.Usage.div` with universal-property theorems proved in
`FX/Kernel/Grade/Usage.lean` (search for `div_spec`).

**Cross-reference — the Atkey 2018 Lam bug.**  Atkey's 2018
*Syntax and Semantics of Quantitative Type Theory* used the rule
`Γ, x :_r A ⊢_s b : B  ⟹  Γ ⊢_s λx.b : (x :_r A) → B`, which
silently allowed a linear variable to be captured in a replicable
closure — see `fx_design.md` §27.1 and §27.2 for the witness term.
Wood-Atkey 2022 fixes this by dividing the outer context:

```
Γ/s, x :_r A ⊢_1 b : B  ⟹  Γ ⊢_s λx.b : (x :_r A) → B.
```

The `/` operator is the context-division morphism whose universal
property is `r / s = max { d | d * s ≤ r }` on each grade.  For
Usage, `1 / ω = 0`:  a linear variable is erased from a closure
being built at grade ω, which means the closure cannot actually
use it — exactly the soundness we want.  This rule is realized in
`FX/Kernel/Grade/Usage.lean` and keyed to §27.1.  Its rejection
of the Atkey 2018 witness is the first entry in the unsoundness
corpus (see `docs/MetatheoryCorpus.md`).

`Grade-zero` is the erasure theorem: values at grade 0 have no
runtime representation.  Abel-Danielsson-Eriksson ICFP 2023 give
the soundness of erasure under graded modal dependent type theory.
Realized in `FX/Kernel/Grade/Usage.lean` via the `Usage.zero`
annihilator law.

---

## H.9 — Subsumption and conversion (2)

| Name       | Status  | Lean file                     | Reference      |
|------------|---------|-------------------------------|----------------|
| `T-conv`   | realized | `FX/Kernel/Conversion.lean` + `FX/Kernel/Reduction.lean` | Appendix H.9   |
| `T-sub`    | realized | `FX/Kernel/Subtyping.lean` (`subOrConv`)  | Appendix H.9   |

`T-conv` covers β, ι, ν, η definitional equality.  `T-sub` composes
universe cumulativity + grade subsumption + refinement weakening +
effect row inclusion into one rule.

---

## H.10 — Emit-table (1)

| Name      | Status  | Lean file                 | Reference                     |
|-----------|---------|---------------------------|-------------------------------|
| `U-emit`  | pending | `FX/Kernel/Emit.lean`     | Appendix H.10, §20.5, App. G  |

The single non-pure-MLTT axiom.  For each supported architecture ∈
{x86_64, arm64, rv64, mips64} and each atomic operation `(op, ord,
width)`, the source-level semantics refines against the instruction
sequence defined in §20.5, interpreted under the arch's formal memory
model (Appendix G).

Proof obligation: ~120 lemmas (30 per arch × 4 arches).  Each lemma
is a refinement argument: `observe(emit(A, op, ord, w)) ⊆
sourceSem(op, ord, w)` under `M_A`.

Status today: axiom, pending mechanization.  `leanx` itself does not
emit — it simulates the source-level atomic semantics directly.  The
axiom is present because it is part of FX's trusted base for `fxc`
codegen correctness.

---

## 11. Totals

| Category               | Total | `axiom` | `proved` | `realized` | `pending` |
|------------------------|-------|---------|----------|------------|-----------|
| H.1 Universes          |  5    |  0      |  0       |  0         |  5        |
| H.2 Pi                 |  3    |  0      |  0       |  3         |  0        |
| H.3 Sigma              |  3    |  0      |  0       |  1         |  2        |
| H.4 Inductive          |  4    |  0      |  0       |  4         |  0        |
| H.5 Coinductive        |  4    |  0      |  0       |  0         |  4        |
| H.6 Identity           |  3    |  0      |  0       |  1         |  2        |
| H.7 Quotient           |  3    |  0      |  0       |  1         |  2        |
| H.8 Grade algebra      |  5    |  0      |  4       |  0         |  1        |
| H.9 Subsumption/conv.  |  2    |  0      |  0       |  2         |  0        |
| H.10 Emit-table        |  1    |  0      |  0       |  0         |  1        |
| **Total**              | **33**| **0**   | **4**    | **12**     | **17**    |

Phase 2.2 snapshot: 0 declared axioms; 4 Grade-algebra laws
proved via `by decide` on finite carriers; 12 typing /
reduction rules realized as computable `partial def` code in
`FX/Kernel/**`; 17 entries pending their term forms (Universes
not explicitly propagated yet; Sigma intro/elim pending
`split` / pair terms; Coind/Id intro-elim pending; Quot mk/
lift pending; U-emit pending atomics).

The load-bearing invariant is:  *declared `axiom` never grows
past the current Appendix-H list.*  The `realized` status
counts rules whose body IS the rule (computable `partial def`
in `FX/Kernel/**`); it is strictly stronger than `axiom`
(realized rules execute; axiomatic rules are trusted).
Migrations `pending → realized → proved` (good) or
`pending → axiom` (acceptable; requires row status flip).
The reverse direction is forbidden without an RFC.

---

## 12. Status legend

* **pending** — slated to become an `axiom` or theorem when the
  relevant kernel term form / typing rule lands.  Currently neither
  declared as `axiom` in Lean nor proved as theorem.  NOT in the
  trusted base.
* **stated** — stated as a theorem in Lean with a Lean proof in
  progress.  Not yet in the trusted base.
* **axiom** — declared as an `axiom` in `FX/Kernel/**`.  In the
  trusted base.  Every row with this status must correspond to
  exactly one `axiom` declaration (enforced by `scripts/axiom-audit.sh`).
* **proved** — discharged as a Lean theorem, no `axiom` required.
  Retained here for provenance; `scripts/axiom-audit.sh` tolerates the
  row but does not require a matching `axiom`.
* **removed** — no longer needed.  Explain in `docs/rfcs/`.

The trusted base is exactly the set of entries with status `axiom`.
It can only shrink (via `axiom → proved` or `axiom → removed`) once
it has been populated.  An entry cannot silently disappear — every
transition requires a PR, and `axiom → removed` requires an RFC.

The migration direction is **pending → stated → axiom** (if genuinely
axiomatic) or **pending → stated → proved** (if mechanizable).  The
reverse direction (proved → pending, etc.) is forbidden.

Phase 1 status (cross-reference the table in §11): zero entries are
declared `axiom`; four entries are `proved` (the Tier-S grade semiring
laws for the finite dimensions that have landed); twenty-nine entries
are `pending`.  The trusted base is empty at the Lean level; the
`U-emit` axiom in §14 of `fx_design.md` is a future obligation, not a
current declaration.

---

## 13. Non-axioms (derived)

Every surface feature in `fx_design.md` §3–§26 is **derived** from the
33 entries above (whether declared as `axiom` or proved as theorem),
not axiomatic in its own right.  The derivations live in
`FX/Derived/`:

* `FX/Derived/Adt.lean`       §3.3 algebraic data types
* `FX/Derived/Record.lean`    §3.4 records
* `FX/Derived/Codata.lean`    §3.5 codata
* `FX/Derived/Effect.lean`    §9 effects
* `FX/Derived/Session.lean`   §11 sessions
* `FX/Derived/Machine.lean`   §13 state machines
* `FX/Derived/Contract.lean`  §14 contracts
* `FX/Derived/Atomic.lean`    §11.10, §20.5 atomics

If a derivation requires a 34th axiom, that axiom must be added to
this list via the RFC process, with a positive test (accepted program),
a negative test (rejected program), and a metatheory re-proof run.

If a proposed derivation cannot be written without adding an axiom
and the axiom cannot be justified, the feature needs redesign — FX
does not grow its trusted base to support any particular surface
convenience.
