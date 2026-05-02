# AXIOMS.md — trust budget for lean-fx-2

This document is the canonical reasoning about what lean-fx-2 trusts,
what catastrophes are possible, and how the project disciplines itself
against them.  Adapted from `lean-fx/AXIOMS.md` with lean-fx-2-specific
commitments.

## The four layers of trust

A lean-fx-2 theorem stands on:

1. **Lean 4's C++ kernel** — typechecker + CIC reduction rules
   (β, η, ι, δ, ζ).  ~6 KLoC.  Out of scope for policy.
2. **Lean's three core axioms** — `propext`, `Quot.sound`,
   `Classical.choice`.  Inheritable when any stdlib import happens.
   We *can* avoid using them; we cannot remove them from the
   environment without forking Lean.
3. **lean-fx-2-specific axioms** — postulates we add for FX-foundational
   reasons.  Currently: ZERO declared.  Reserved future ceiling:
   `Univalence` (in `HoTT/Univalence.lean`, scoped via
   `@[univalence_postulate]` attribute) + the four `lean-fx`-style
   slots (`ua_wire`, `ua_ghost`, `fix_productivity`, `hit_path_intro`)
   reserved as design warnings.
4. **lean-fx-2's definitions** — every `def`, `theorem`, `inductive`,
   `structure`.  These don't add logical strength but expand the
   surface that the Lean kernel must check correctly.

## Layered policy

| Layer | Scope                                                    | Stdlib axioms | FX axioms |
| ----- | -------------------------------------------------------- | ------------- | --------- |
| 1     | Lean 4 C++ kernel                                         | n/a (meta)    | n/a       |
| K     | Kernel: `Foundation/`, `Term*`, `Reduction/`              | FORBIDDEN     | FORBIDDEN |
| M     | Metatheory: `Confluence/`, `Bridge`, `HoTT/` (non-univ)  | FORBIDDEN     | FORBIDDEN |
| E     | Algorithmic: `Algo/`, `Pipeline`, `Surface/`              | FORBIDDEN     | FORBIDDEN |
| U     | HoTT/Univalence: `HoTT/Univalence.lean`                   | discouraged   | 1 allowed |
| S     | Surface user reasoning (`verify`, `assert` blocks)        | discouraged   | allowed   |
| F     | FX-specific axioms (future: ua_wire, etc.)                | n/a           | ceiling 5 |

Goal: push zero-axiom property as far as it will go.  A theorem only
falls back to an axiom once a credible zero-axiom encoding has been
attempted and shown impossible at the current state of lean-fx-2; the
fallback is a documented design exception, not a default.

## Univalence — the documented exception

In standard MLTT, univalence is not provable.  HoTT-style theories
admit it as either:
1. A primitive axiom (loses 0-axiom status)
2. A theorem in cubical type theory (huge implementation cost)
3. A truth-by-construction in models (meta-theoretic, not internal)

lean-fx-2's stance:
* **Short term**: postulate via `axiom Univalence` + `@[univalence_postulate]`
  attribute, scoped to `HoTT/Univalence.lean`.  Downstream theorems
  that depend on it carry the attribute (propagation tracked by
  `#assert_no_axioms_except_univalence` gate).
* **Long term**: derive via cubical layer (deferred to v3.x).

This is **one** documented exception, not a license for axiom slippage.

## Per-axiom catastrophe analysis

### `propext` — propositional extensionality

```lean
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
```

**Failure mode P-1: Silent collapse of distinguishable propositions.**
Two propositions that are logically equivalent become equal as types.
Audit trails / verified certificates that depend on telling them
apart silently lose information.

**Failure mode P-2: Erased decidability.**  `Decidable P` instances
that depend on propext can produce values whose computational content
is degenerate.

**Failure mode P-3: HoTT-incompatibility shockwave.**  When future
modal univalence (`ua_wire`, `ua_ghost`) lands, propext + ua produces
paradoxical inhabitants if any FX modal type that we *think* is
proof-irrelevant turns out not to be.

### `Quot.sound` — quotient soundness

**Failure mode Q-1: Quotient by a non-equivalence.**  Quot.sound
accepts ANY relation; Quot identifies more elements than specified
when the relation isn't an equivalence.

**Failure mode Q-2: Respect-proof loophole.**  `Quot.lift f h`
accepts type-correct but semantically-wrong respect proofs.

**Failure mode Q-3: Computational deadlock.**  Pattern matches that
depend on Quot.sound-derived equality don't reduce at runtime.

### `Classical.choice` — global choice

**Failure mode C-1: The noncomputable cascade.**  Once Choice enters
a definition, every transitive caller is noncomputable.  A "verified
compiler" using Choice somewhere cannot actually compile.

**Failure mode C-2: Silent excluded-middle injection.**  Choice +
propext = `Classical.em : ∀ p, p ∨ ¬p`.

**Failure mode C-3: Hilbert epsilon nondeterminism.**  Two proofs
invoking Choice may pick different witnesses; extraction can drift.

## Combination catastrophes

### `propext + Quot.sound` ⇒ function extensionality

**Failure mode F-1: Implementation collapse.**  An optimized `compile`
and a naive one are funext-equal whenever they agree on inputs.
Performance bugs become unprovable as bugs.

### `propext + Classical.choice` ⇒ classical first-order logic

**Failure mode FC-1: Total verification failure.**  A typechecker
proof "this program halts" might use `Classical.em`; the proof goes
through; the artifact gives no algorithm.

### All three (Lean's default classical foundation)

**Failure mode VAPOR-1: Verified vapor.**  Decidable instances may
be opaque; definitions noncomputable; equalities may not reflect
operational distinctions.  You can have a "verified compiler" that
doesn't compile anything.

## FX-specific catastrophes

### FX-Cat-1: Modal collapse via propext

```
⟨ghost⟩ Bool  ↔  Bool   ⇒  ⟨ghost⟩ Bool = Bool
```

If modal types collapse via propext, **erasure discipline breaks**.
Compiler emits ghost values into runtime; arbitrary memory corruption.

### FX-Cat-2: Session protocol skip

A session type `send(x); recv(y); end` is a *protocol*.  Two sessions
with the same termination state can be propext-equivalent.  Kernel
believes a session that skipped `send` is the same as one that did
it.  Verified networking code corrupts wire state.

### FX-Cat-3: Hardware-mode determinism failure via Choice

A `synth` modality function compiled to Verilog.  Choice picks
representative.  Two compilations produce different Verilog.  Both
pass bisimulation theorem.  Engineers can't tell them apart.

### FX-Cat-4: The combination disaster

All three axioms + modal univalence + HIT primitive (Phase 3-4 of
the foundation plan): a verified contract migration that
propext-collapses two distinct contracts, then HIT-quotients them,
then Choice-extracts a "representative."  Result type-checks; running
on real data silently drops fields.  **Data loss in production with
a verified-correct certificate attesting it didn't happen.**

## Reserved future-axiom slots

These are design warnings, not declarations.  Each requires a
separate RFC if added.

### `ua_wire` — modal univalence at Wire mode

Failure modes UW-1 (contract identity collapse), UW-2 (parser/
serializer mismatch becomes definitional), UW-3 (wire equality
crosses trust boundary).

Mitigation: scope to narrow `WireEquiv` record with explicit
encode/decode + losslessness proofs + version labels + external-
format citations.

### `ua_ghost` — modal univalence at Ghost mode

Failure modes UG-1 (erasure leak through equality transport),
UG-2 (proof irrelevance applied to computational evidence),
UG-3 (static inconsistency becomes operational by reflection).

Mitigation: make Ghost/Dynamic boundary a theorem, not a convention.

### `fix_productivity` — guarded fixed point for Later

Failure modes FP-1 (unguarded recursion smuggled through Later),
FP-2 (productivity proof checks wrong clock), FP-3 (space leak
certified as productive).

Mitigation: axiom must mention clocks + guarded contexts explicitly.
Pair with separate space discipline.

### `hit_path_intro` — computing paths for HITs

Failure modes HP-1 (path constructor missing coherence law),
HP-2 (bad quotient relation becomes equality with computation),
HP-3 (nontermination through recursive HIT eliminators).

Mitigation: start with named, specific HITs, not general schema.

### Combined future-axiom catastrophe

The dangerous case is the chain `ua_wire + ua_ghost + fix_productivity
+ hit_path_intro` combined with the three Lean core axioms.  Each
must have a separate RFC; ceiling is 5 FX-specific axioms ever.

## Common axiom-injection sources to avoid (Layer K critical)

* **`simp`/`split` on a function whose match has a wildcard** —
  match compiler emits propext.  Fix: full enumeration; for
  restricted-index scrutinees use toRaw-shape dispatch
  (see `WORKING_RULES.md` Discipline #2).
* **`funext` and `congr` steps that funext-extend** — replace with
  pointwise-equivalence predicates.
* **`Quot.sound` via `Quot.lift`/`Quot.mk`** — avoid quotient types
  in kernel; use setoid-flavored predicates.
* **`Classical.choice` via `Classical.byContradiction`,
  `Classical.em`, `Decidable.decide` on undecidable props,
  `Nonempty.intro`+`Classical.choice`** — replace with constructive
  proofs.
* **`Eq.mpr`/`Eq.mp` cascades** chained through term-level Eq → Prop
  coercions can drag in propext.
* **`cases`/`rcases` on multi-Nat-indexed inductive in goal whose
  target uses scrutinee through a function** — fix per
  `feedback_lean_match_arity_axioms` (hoist implicits before `:`)
  or `feedback_lean_universe_constructor_block` (propositional-
  equation pattern).

## Diagnosing

```lean
#print axioms TheoremName
-- shows precise axiom dependencies; expected: "does not depend on
-- any axioms"
```

For per-decl audit:
```
LeanFX2.Tools.DependencyAudit.computeStats env name (includeStdlib := true)
```

## When fixing is structural

If a kernel construct intrinsically requires a wildcard, `funext`,
or a multi-arity dependent match that triggers propext: refactor.
Split the function into per-shape helpers each with full enumeration;
replace function equality with pointwise predicate; restructure the
match scrutinee via paired predicate.  Do NOT downgrade Layer K work
to Layer M just to evade the gate — that hides axiom dependencies
behind a layer label.

## Verifying the bar

```bash
# Strict zero-axiom check across the kernel:
grep -rn "propext\|Quot.sound\|Classical.choice\|funext\|sorry" LeanFX2/ \
  --include="*.lean" \
  | grep -v "Univalence.lean\|axiom_policy\|comment\|AXIOMS.md\|WORKING_RULES.md"
# Should return nothing.

# Per-decl axiom check (run by AuditAll.lean during build):
lake build LeanFX2 2>&1 | grep "axiom audit failed"
# Should return nothing.
```

## The definition gap — beyond axioms

A wrong definition is just as harmful as a wrong axiom in practice.
A `compile` function with a subtly wrong definition can produce a
"verified-correct" artifact that misbehaves in ways the proof can't
detect because the proof is *against* the wrong definition.

Mitigations: cite vendor specifications at every external-reality
definition (x86 ISA → Intel SDM, ARM → ARMv8-A reference, RISC-V →
unprivileged spec).  Multiple-presentation discipline (operational +
denotational + algebraic).  Differential testing against trusted
oracles.  Use validated Sail-derived ISA specs where they exist.

This is a separate category of risk from axiom-induced unsoundness
but no less critical.

## Eight-axiom ceiling

The project's standing commitment: total axiom budget = 3 Lean core +
5 FX-specific.  Hitting the ceiling without dropping an existing axiom
forces a project-policy review before the 9th lands.

Currently used: 0 Lean core (all kernel theorems strictly axiom-free);
0 FX-specific.  Reserved: 1 (`Univalence` in HoTT/Univalence.lean).
Future budget: 4 (ua_wire, ua_ghost, fix_productivity, hit_path_intro).

## Living document

Update when:
* A new axiom is added to Layer F — append per-axiom catastrophe
  analysis + combinations
* A new layer of trust discipline is identified — append a layer
* A near-miss or actual failure occurs — append to historical section
* A new external-reality definition is added (hardware, ISA,
  encoding, protocol) — extend definition-gap section
