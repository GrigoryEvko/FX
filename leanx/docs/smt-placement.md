# SMT placement — kernel vs elaborator

Design note tracking the load-bearing question for Stream E
(SMT integration): **which layer consults the oracle?**

`fx_design.md` §10.16 settles the high-level answer — SMT is
the discharge mechanism for refinement predicates,
`pre`/`post`/`decreases`, and `assert` statements.  The open
question is *where in the pipeline* the oracle fires.  Three
plausible architectures, each with concrete tradeoffs.

## Option A — kernel-level SMT (rejected)

The kernel's typing judgement consults Z3 directly when
checking refinement types.  Every `check` call that encounters a
refinement obligation emits an SMT query before returning.

| Pros | Cons |
|------|------|
| Uniform rule-by-rule integration | Kernel no longer closed-form |
| No separate proof tree | Oracle becomes trusted component |
| Reduction + typing share one discharge mechanism | Forever ties trust base to Z3's soundness |
| | Self-verification of the kernel becomes much harder |
| | Every stage-2 build needs Z3 installed |

**Rejection reason**: §1.2's "finite kernel, enumerable trust"
commitment forbids making the kernel depend on a 500k-LOC
external solver.  The kernel must stay checkable by a
300-line verifier (Metamath-style, §31.1 discipline).

## Option B — elaborator-level SMT (chosen)

A new `FX/Elab/Verify.lean` layer wraps `FX.Kernel.Typing.check`.
Refinement obligations bubble up from kernel check-failures (as
`TypeError`s with a specific code, e.g. `R001 pre not proved`).
The Verify layer catches those, emits SMT-LIB2 (§E1), dispatches
to the oracle (§E2), and either returns `.ok` or re-raises the
error with an UNSAT-core-annotated `TypeError`.

| Pros | Cons |
|------|------|
| Kernel stays pure | Two-phase discharge complicates error location |
| SMT is L2 untrusted (§1.6 escape-hatch tier) | Need to carry obligations across the layer boundary |
| `--show-axioms` walker (F5/Q44) can enumerate every SMT-discharged fact | Some refinements that need body reflection (`@[reflect]`) have to duplicate the body on the SMT side |
| Z3 replaceable with CVC5 / other oracle without kernel touch | |
| Matches Dafny / Viper / F* architecture | |

**Chosen**.  `Verify.lean` becomes the integration point.  The
kernel's `check` returns `R001`..`R006` codes that the elaborator
layer reinterprets as "discharge via SMT"; on success the Verify
layer reports `.ok` to callers and records the UNSAT-core on the
decl's trust metadata (for audit via `fxi --show-axioms`).

## Option C — external proof agent (deferred)

A separate `fxc verify` binary reads elaborated-but-unchecked
`.fxc` files and dispatches refinements independently.  Decouples
verify time from compile time entirely.

Pro: parallelism on a CI fleet, independent rebuilds.  Con: two
artifacts to reason about, race conditions if verify runs
before elab completes.  Deferred to M8 (`fxi verify` as a CLI
mode once `Verify.lean` stabilizes).

## Corollaries for Stream E tasks

| Task | Placement | Notes |
|------|-----------|-------|
| **E1** encode `Term → SMT-LIB2 string` | `FX/Smt/Encode.lean` | Pure syntactic emitter.  No kernel dependency beyond `Term` / `Grade`. |
| **E2** Z3 subprocess oracle | `FX/Smt/Oracle.lean` | Spawn + pipe + parse.  Result cache in `.fxcache/smt/`. |
| **E3** library term (`is_sorted`, `length`, `mem`) | `FX/Smt/LibTerm.lean` | Axiomatized predicates callers can reuse.  Kept separate from the emitter so the emitter stays schema-free. |
| **E4** wire into Typing | **`FX/Elab/Verify.lean`** | Note: *NOT* `FX/Kernel/Typing.lean` directly.  Verify wraps kernel check; kernel stays oracle-free. |

The E1–E4 placement above pins the files.  The
build-vs-adopt question — do we write our own encoder or adopt
`lean-smt` / `lean-auto`? — is settled separately in
`docs/smt-library-options.md` (Q49 closure ledger row L1): our
own ~500 LOC bridge wins on hermeticity, dependency weight, and
on `Term`-vs-Lean-`Expr` encoder fit.

## Implications for the axiom audit

The audit script (`scripts/axiom-audit.sh`) enforces no axioms
outside `FX/Kernel/**`.  The Verify layer MAY declare axioms
(e.g., `Smt.trust_oracle` for each solver-released obligation),
but these live OUTSIDE the kernel allowlist per §1.6 tier
discipline.  Release builds need an explicit `--accept-smt`
flag (or the published-package signer's attestation, §25.9)
before oracle-discharged obligations graduate to `Verified`
trust.

A build without the flag running against oracle-only proofs
compiles but reports trust `Sorry` on every such decl.  This
keeps L1 kernel soundness separable from L2 oracle soundness —
a bug in Z3 can't silently compromise the kernel's published
guarantees.

## Error-code allocation

Per `docs/error-codes.md` and the existing `R0xx` space:

  * `R001` — precondition not satisfied (existing)
  * `R002` — postcondition not satisfied (existing)
  * `R003` — decreases doesn't strictly decrease (existing)
  * `R004` — assert not proved (existing)
  * `R005` — literal violates type refinement (existing)
  * `R006` — unreachable reached (existing)
  * **`R007`** — SMT oracle timeout (reserved for E2)
  * **`R008`** — SMT oracle unknown (reserved for E2)
  * **`R009`** — SMT oracle unavailable (env misconfig, reserved)

The R0xx codes carry an optional UNSAT-core field in their
diagnostic payload so the Verify layer can attribute failures to
specific kernel rule applications.

## Precedent

This placement mirrors:

  * **F*** — Z3 consulted by the typechecker, kernel stays pure.
    F*'s `--lax` flag (§22 sketch-mode equivalent) skips SMT
    entirely.
  * **Dafny** — Boogie between source and SMT; Z3 is the oracle
    layer, Dafny's verifier wraps kernel lowering.
  * **Lean 4 Mathlib** — `decide`/`omega`/`polyrith` are tactics
    layered on top of the kernel; the kernel itself contains no
    oracle calls.

FX follows this discipline.  Tasks E1–E4 slot into the Verify
layer architecture without touching kernel soundness.

## Under the theoretical reframe (forward-looking)

FX's in-progress theoretical direction (tracked in
`docs/fx_reframing.md` once that artifact lands per Phase R0)
commits to a slightly-heterogeneous unified algebra: one
Multimodal Dependent Type Theory (MTT) spine plus a small,
enumerable set of peripheries.  Under that framing, SMT
placement ceases to be a local architectural decision —
it becomes the canonical first example of what counts as a
periphery.

**SMT dispatch does not admit a modality.**  A proposition `P`
at the MTT level is a type; its inhabitants are proof terms.
SMT theorems are first-order formulae over decidable theories
(QF_UFLIA, QF_BV, QF_NRA, QF_FP per §10.16) with no intrinsic
proof-term structure.  A `sat` / `unsat` / `unknown` response
from the solver is not a proof term — it is an external
judgement relative to the solver's own consistency.  No 2-cell
of any mode theory can represent this cleanly because the
oracle's semantics is not compositional with type-theoretic
elaboration.

**Consequence for the mode theory.**  The Ghost mode carries
proof-level obligations.  Refinement types land in Ghost mode
via the `erase` adjunction.  Obligations inside Ghost mode
either discharge internally (structural proof, `by decide`,
HITs for quotient reasoning, bridge types for free theorems)
or dispatch outward to the SMT periphery.  The dispatch is
explicit at the obligation site — the same way `sorry` and
`axiom` are explicit today.

| Mode theory position | Discharge mechanism | Trust level |
|----------------------|---------------------|-------------|
| Ghost, structural proof | internal MTT rule | Verified |
| Ghost, parametricity | bridge modality | Verified |
| Ghost, HIT construction | HIT eliminator | Verified |
| Ghost, external SMT | Verify layer dispatch | Oracle (≤ Verified) |
| Ghost, `sorry` | dev-only stub | Sorry |
| Ghost, `axiom` | declared assumption | Assumed |

The Oracle row is the canonical periphery.  Its trust level
is bounded above by the solver's own soundness guarantee; the
kernel's soundness does not depend on the solver being correct.

**This settles a question the kernel-layer option left open.**
An earlier draft of this document considered whether the mode
theory could absorb SMT as a "decidability modality" (any
proposition decidable by QF_UFLIA becomes a modality-elim).
That framing was not chosen.  SMT stays peripheral.  The
boundary is the MTT ↔ SMT interface (the Verify layer).
Everything inside the MTT spine stays machine-checkable by a
finite kernel verifier; SMT-discharged facts are annotated
specifically so release gating can treat them separately.

## Composition pattern — SMT as the canonical periphery

Under the reframe's periphery discipline, SMT is the first and
cleanest example of what belongs outside the spine:

**Why SMT is peripheral, concretely:**

  1. Its semantics are first-order, not dependently typed.
  2. Its proof terms are unsat cores — opaque to the mode
     theory's elimination rules.
  3. Its correctness depends on the solver, a 500kLOC C++
     codebase not in FX's trust base.
  4. It is swappable — Z3 today, CVC5 tomorrow, Bitwuzla for
     QF_BV-heavy code, without spine changes.
  5. It is network-dispatchable — Phase E2 can parallelize
     across a solver pool without kernel entanglement.

**Why SMT is still part of FX's trust story, enumerably:**

`fxi --show-axioms SYMBOL` (per F5 and §1.2) prints the
transitive kernel-axiom closure plus every SMT-discharged fact
transitively.  The SMT-discharged subset is distinguishable
from the kernel-axiom subset, so release-mode gating can
weight them separately:

  * Kernel axioms ≤ 33 (Appendix H allowlist) — always
    trusted.
  * SMT discharges ≤ N per build — trusted per `--accept-smt`
    or per the published-package signer's attestation per
    §25.9.

This is the mechanization of the slightly-heterogeneous
commitment: kernel axioms compose into a single coherence
theorem, SMT discharges compose into a separate enumerable
trust layer, and the two layers meet at the Verify interface.

## Agent-protocol integration

The §24 REST daemon (F2/F5) consumes the Verify layer, not the
kernel directly.  Agents interacting with FX see:

  * `POST /check` returns kernel errors (T, M, E, S, I codes —
    structural).
  * `POST /check` returns Verify errors (R0xx codes — SMT-
    related).
  * `GET /proof-state` returns the MTT-level Known / Goal /
    Suggestion structure.
  * `GET /check/{id}/unsat-core` returns the SMT-level unsat
    core when available.
  * `GET /axioms/SYMBOL` returns the separated kernel + SMT
    trust lists.

An agent writing FX code can therefore distinguish "the kernel
cannot type-check this" from "the kernel accepts this but SMT
could not discharge its refinement" — the two failure modes
require different remedies.  The Verify layer's role is
exactly this separation: it preserves the kernel's
compositional error structure while adding a well-typed SMT
failure channel.

## Summary decision ledger

Load-bearing decisions, each with a cited rationale:

| Decision | Rationale | Citation |
|----------|-----------|----------|
| SMT discharge at elaborator layer, not kernel | Kernel stays closed-form and auditably simple | §1.2; this doc §2 Option A rejection |
| Verify layer wraps `Typing.check` | Refinements are kernel-typed, discharge is external | This doc §3 Option B choice |
| R007 / R008 / R009 reserved for SMT outcomes | Separate from structural R0xx codes | This doc §6 |
| Oracle trust ≤ Verified without `--accept-smt` | Keep L1 kernel trust separate from L2 oracle trust | This doc §5 axiom-audit coupling |
| Verify layer owns UNSAT-core reporting | Kernel has no concept of unsat cores | This doc §3, §6 |
| SMT is the canonical periphery under the reframe | First concrete example of the §5 periphery discipline in `fx_reframing.md` | This doc §7, §8 |
| Agents see Verify errors and kernel errors separately | Different remediation modes | This doc §9 |
| `fxi --show-axioms` surfaces kernel + SMT layers separately | Enumerable trust per §1.2 | This doc §8 |

This ledger is the acceptance artifact for the placement
question (Q50).  When a future kernel change forces a revisit,
update the ledger with a new row rather than rewriting the
sections above — the prior rationale stays on record for
audit.
