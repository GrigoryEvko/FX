# Known-unsoundness Corpus

`fx_design.md` §27.2 mandates that every cataloged type-theory bug
from the literature becomes a permanent `test_theory` case
(`fx_design.md` §23.6).  This document is `leanx`'s projection of
that corpus:  a row per known bug, cited to its source paper, with
a pointer to the Lean-level regression test that witnesses the
leanx kernel rejecting it.

The corpus **grows, never shrinks**.  When a paper reveals a new
bug, we add a row.  Rows do not leave the corpus even after the
soundness proof is accepted — they become regression tests, and
if a future kernel change accidentally re-admits a cataloged bug,
the test fires and the kernel change is rejected.

References:
  * fx_design.md §27   — Metatheory
  * fx_design.md §27.1 — Corrected Lam rule
  * fx_design.md §27.2 — Known unsoundness corpus
  * fx_design.md §27.3 — The five-layer defense
  * fx_design.md §23.6 — Type theory tests

---

## Five-layer defense (§27.3) and this file

The corpus implements **layer 1**: known-witness smoke tests.  The
other four layers live elsewhere:

| Layer | Name                                    | Home in leanx                                      |
|-------|-----------------------------------------|----------------------------------------------------|
|   1   | Known-witness smoke tests               | `tests/Tests/Metatheory/UnsoundnessCorpusTests.lean` (this file indexes) |
|   2   | Property-based metatheory fuzzing       | `tests/Tests/Metatheory/Fuzz.lean` (Phase 2+)     |
|   3   | Cross-ref published mechanized proofs   | AXIOMS.md row references, SPEC.md §15              |
|   4   | Self-verified metatheory                | `FX/Metatheory/{Preservation,Progress,…}.lean`     |
|   5   | Formal review                           | `docs/rfcs/` + AXIOMS.md RFC discipline            |

---

## Corpus entries

Each row: **ID**, short title, cite, rejecting Lean feature, status
(`realized` = the kernel as-of Phase 1 already rejects it;
`deferred` = the rejection depends on kernel relations that land in
a later phase), regression-test name in
`tests/Tests/Metatheory/UnsoundnessCorpusTests.lean`.

### Category A — Grade and linearity

| # | Witness                                       | Source                                                  | Rejector (Lean)                                       | Status   | Test                           |
|---|-----------------------------------------------|---------------------------------------------------------|-------------------------------------------------------|----------|--------------------------------|
| 1 | Atkey 2018 Lam, linear var in closure         | Atkey, *Syntax and Semantics of QTT*, LICS 2018         | `Usage.div` (`FX/Kernel/Grade/Usage.lean`)            | realized | `atkey2018LamRule_rejected`    |
| 2 | Session endpoint aliased (double-use)         | Honda-Yoshida-Carbone, *MPST*, POPL 2008 (negative)     | Usage `1 + 1 = ω` rule (`Usage.add`)                  | realized | `sessionEndpointAliased_rejected` |
| 3 | ML value restriction — polymorphism under ref | Wright, *Simple Imperative Polymorphism*, LISP-SC 1995  | Usage+Mutation product grade (future Phase 3)         | deferred | `mlValueRestriction_rejected`  |

### Category B — Dependent / higher-order

| # | Witness                                       | Source                                                         | Rejector (Lean)                    | Status   | Test                           |
|---|-----------------------------------------------|----------------------------------------------------------------|------------------------------------|----------|--------------------------------|
| 4 | `Type : Type` (Girard's paradox)              | Girard, *Interprétation fonctionnelle*, 1972; Coquand 1986     | Universe hierarchy (Level layer)   | deferred | `girardParadox_rejected`       |
| 5 | Unfounded inductive (negative occurrence)     | Coq manual, `Inductive` strict-positivity requirement          | `IndSpec` WF check in `Term.lean`  | deferred | `negativeInductive_rejected`   |
| 6 | Coinductive without guardedness               | Coquand, *Infinite objects in type theory*, TLCA 1993         | Abel-Pientka copattern check       | deferred | `unguardedCoinductive_rejected` |

### Category C — Information flow

| # | Witness                                                | Source                                                    | Rejector (Lean)                   | Status   | Test                         |
|---|--------------------------------------------------------|-----------------------------------------------------------|-----------------------------------|----------|------------------------------|
| 7 | Implicit flow via branch on secret → public result     | Volpano-Smith-Irvine, *Sound Type System for Secure Flow*, JCS 1996 | Security grade on `if` (Phase 5) | deferred | `implicitFlowBranch_rejected` |
| 8 | CT violation: secret-indexed memory read               | Almeida et al., *Verifying CT-code by Compilation*, 2016  | Observability grade on array ops  | deferred | `ctIndexLeak_rejected`       |

### Category D — Concurrency / permissions

| # | Witness                                          | Source                                                       | Rejector (Lean)                     | Status   | Test                              |
|---|--------------------------------------------------|--------------------------------------------------------------|-------------------------------------|----------|-----------------------------------|
| 9 | Fractional permission over-allocation (> 1)      | Boyland, *Checking Interference with Fractional Perms*, SAS 2003 | `Usage.add` closure of `omega`       | realized | `fractionalOverAllocation_rejected` |
|10 | Mutex aliased across closures                     | O'Hearn, *Resources, Concurrency, and Local Reasoning*, 2004 | Exclusive `ref mut` via Usage+Mutation (Phase 3) | deferred | `mutexAliased_rejected`      |

### Category E — Effects / handlers

| # | Witness                                        | Source                                                    | Rejector (Lean)                   | Status   | Test                         |
|---|------------------------------------------------|-----------------------------------------------------------|-----------------------------------|----------|------------------------------|
|11 | Effect row escape via untyped handler          | Leijen, *Koka: Programming with Row-Polymorphic Effects*, 2014 | Effect grade row inclusion        | deferred | `effectEscape_rejected`      |
|12 | Multishot continuation with linear capture     | Hillerström-Lindley, *Shallow Effect Handlers*, ICFP 2018 | Usage × effect multi-shot rule    | deferred | `multishotLinearCapture_rejected` |

---

## Addition discipline

Adding a new corpus entry is a docs-only PR:

  1. Append a row here with cite and ID.
  2. Add a `-- TODO(§27.2, entry #N, paper): <witness>` comment
     or, better, a failing test case to
     `tests/Tests/Metatheory/UnsoundnessCorpusTests.lean`.
  3. If the rejector relies on a kernel feature that is not yet
     realized, mark status `deferred` and cite the phase from
     `SPEC.md` §7 at which it activates.

Removing a row is not allowed without an RFC.  The corpus is
append-only — this is the whole point of a "never shrinks"
regression set.
