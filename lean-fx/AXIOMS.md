# AXIOMS.md — the trust-budget policy for lean-fx

This document is the canonical reasoning about what lean-fx trusts,
what catastrophes are possible, and how the project disciplines itself
against them.  It complements the empirical audit machinery in
`LeanFX/Tools/DependencyAudit.lean` and any future CI scripts.

## The four layers of trust

A lean-fx theorem stands on:

1. **Lean 4's C++ kernel** — typechecker + CIC reduction rules
   (β, η, ι, δ, ζ).  ~6 KLoC.  The kernel itself is not declared
   anywhere in source; it is the meta-language.  Out of scope for
   policy.
2. **Lean's three core axioms** — `propext`, `Quot.sound`,
   `Classical.choice`, declared in Lean's stdlib (`Init.Core`,
   `Init.Classical`).  Inheritable when any stdlib import happens.
   We *can* avoid using them; we cannot remove them from the
   environment without forking Lean.
3. **lean-fx-specific axioms** — postulates we add for FX-foundational
   reasons (modal univalence, Nakano fix, HIT path constructors).
   Currently: ZERO declared.  Planned future ceiling: FIVE.
4. **lean-fx's definitions** — every `def`, `theorem`, `inductive`,
   `structure`.  These don't add logical strength but expand the
   surface that the Lean kernel must check correctly.  Verified per-
   theorem with `LeanFX.Tools.DependencyAudit.#audit_dependencies`.

Audit shorthand: `#print axioms FOO` covers layer 2-3; the dependency-
audit tool covers layer 4.  Layer 1 is the immutable bottom of the
trust base.

## Current state

```
Layer 2 (Lean core axioms)              : 3 inherited, 0 used by any kernel theorem
Layer 3 (lean-fx-specific axioms)       : 0 declared, 0 used
Layer 4 (definitions, transitive count)  : ~120-280 per kernel theorem
                                          (varies with theorem complexity)
```

The kernel theorems through v2.2 are **strictly axiom-free** in the
sense that `#print axioms theorem_name` reports no dependency on any
axiom.  This is the strongest claim available short of forking Lean.

## Why this document exists

A "verified" system can fail in many ways short of being inconsistent.
The catastrophes below are not "Lean would derive False" — they are
**realistic failure modes where the formal artifact is correct but
the engineering goal is missed**.  The discipline below is designed
to keep these failure modes rare and visible.

---

## Per-axiom catastrophe analysis

### `propext` — propositional extensionality

```lean
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
```

Two propositions that are logically equivalent become equal as types.
Implies proof-irrelevance for `Prop` and underwrites function
extensionality (when combined with `Quot.sound`).

**Failure mode P-1: Silent collapse of distinguishable propositions.**
If two propositions happen to be biconditional but mean different
things at the *intent* level, propext makes them the same
*formally*.  Audit trails, verified certificates, or proof-carrying
artifacts that depend on telling them apart silently lose information.

> Concrete: `IsTrue` and `IsValidUnderPolicy` happen to coincide for a
> particular kernel.  An audit trace says "this witness validates
> policy."  The witness was just trivially `True`; nobody checked
> policy.  The kernel doesn't lie — but the *shape* of the proof
> stops carrying the engineering distinction we wanted preserved.

**Failure mode P-2: Erased decidability.**  `Decidable P` instances
that depend on propext can produce values whose computational content
is degenerate.  `decide` returns the right answer; extracting the
algorithm yields an opaque wrapper around `True`/`False`.

> Concrete: a `decide`-driven typechecker passes verification.
> Compiled and run, it cannot produce typing certificates — the
> "decision" was never algorithmic.

**Failure mode P-3: HoTT-incompatibility shockwave.**  When future
modal univalence (`ua_wire`, `ua_ghost`) lands, propext interacts
with it.  In Lean today, `Prop` is genuinely (-1)-typed by kernel
construction, so propext is consistent with HoTT-flavored
extensions.  But if any FX modal type that we *think* is
proof-irrelevant turns out not to be, the combination
**propext + ua_wire** produces paradoxical inhabitants —
`True ≃ False` indirectly, then `True = False`, then `False`.

> Concrete: a contract-migration "proof" reduces to `rfl` because
> Wire-mode propositions collapsed.  Looks verified; actually
> vacuous.  Production deploys broken contracts with a passing
> test suite.

### `Quot.sound` — quotient soundness

```lean
axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
                     r a b → Quot.mk r a = Quot.mk r b
```

If two elements are r-related, their quotient classes are equal.
Without this, `Quot` would be a useless type former.  With it, plus
`Quot.lift`, you get computational quotient types.

**Failure mode Q-1: Quotient by a non-equivalence.**  Quot.sound
accepts ANY relation.  If `r` is not symmetric or transitive, the
resulting Quot still admits Quot.sound but `=` (which IS reflexive,
symmetric, transitive) generates a *larger* equivalence than `r`.
The Quot identifies more elements than you specified.

> Concrete: a quotient meant to identify "definitionally equal terms"
> via `Conv` instead identifies terms equal up to *some larger*
> equivalence (e.g., extensional equality you didn't want).
> Theorems about your Quot now prove things about the larger
> equivalence; downstream safety arguments shift meaning silently.

**Failure mode Q-2: The Quot.lift respect-proof loophole.**
`Quot.lift f h` accepts any `h : ∀ a b, r a b → f a = f b`.  If the
respect-proof is *type-correct but not what you meant* (e.g., uses
classical reasoning that defeats r-respecting intent), the lifted
function is well-typed but doesn't respect r in the way you
documented.

> This is the "intent gap" surfacing: `h` typechecks, but its
> structure may not encode the property your code review thought it
> did.

**Failure mode Q-3: Computational deadlock.**  `Quot.mk r x = Quot.mk
r y` is propositional.  Programs that pattern-match on the
underlying class and depend on this equality reducing get stuck at
runtime.

> Concrete: an FX evaluator that calls `Quot.mk` somewhere, then
> matches on the result.  If the matching depends on a Quot.sound-
> derived equality, the match doesn't reduce; evaluator hangs on
> certain inputs.

### `Classical.choice` — global choice

```lean
axiom Classical.choice : ∀ {α : Sort u}, Nonempty α → α
```

Given a proof that something exists, extract a witness.  Implies
classical excluded middle when combined with propext.

**Failure mode C-1: The noncomputable cascade — biggest realistic
risk.**  Once Choice enters a definition, it terminally infects every
transitive caller as noncomputable.

> Concrete:
> ```
> def find_witness (...) := Classical.choice ...
> def my_kernel_function (...) := ... find_witness ...
> def my_compiler_pass (...) := ... my_kernel_function ...
> def compile (prog) := ... my_compiler_pass ...
> ```
> `compile` typechecks.  Running `compile` on input produces nothing
> — the proof says it's correct, the artifact can't be executed.
> For an FX backend, this means a "verified compiler" that cannot
> actually compile.

**Failure mode C-2: Silent excluded-middle injection.**
Choice + propext = `Classical.em : ∀ p, p ∨ ¬p`.  Even when you
think you're doing constructive reasoning, auto-derived instances
may use LEM.  Proofs port to constructive systems with hidden
classical dependencies.

**Failure mode C-3: Hilbert's epsilon — nondeterministic spec.**
Two proofs invoking Choice may pick different witnesses for the same
proposition.  At the spec level, this is allowed; in practice
Lean chooses consistently, but extraction to a different system or
re-elaboration can pick differently.

> Concrete: an FX optimization that is verified per-spec.  Two builds
> of the same FX program produce different gate-level Verilog.  Both
> pass the bisimulation theorem.  Bug reports come in: "the compiler
> gave different output yesterday."  Nothing is wrong per the proof.

---

## Combination catastrophes

The axioms compose, and combinations introduce hazards none has alone.

### `propext` + `Quot.sound` ⇒ function extensionality

Standard derivation: `Function.funext` uses both.  Side effect:
*all behaviorally equivalent functions become equal*.

**Failure mode F-1: Implementation collapse.**  An optimized `compile`
and a naive `compile` are funext-equal whenever they agree on inputs.
A theorem "the optimized compile is correct" reduces by funext to
"the naive compile is correct" — the optimization's *content* becomes
invisible to the formal system.  Performance-related bugs (the
optimized version is slow, or panics on a corner case the naive one
handles differently) are unprovable to be bugs because the formal
system thinks the two are the same function.

### `propext` + `Classical.choice` ⇒ classical first-order logic

Plus the noncomputable cascade.

**Failure mode FC-1: Total verification failure mode.**  A
typechecker proof "this program halts" might use `Classical.em` to
case-split on `does it halt or not`.  The proof goes through; the
artifact gives no algorithm.  You've "verified" halting via classical
reasoning that has no operational content.

> Concrete: a "verified" optimization pass that's actually halting-
> undecidable in the case it tries to handle.  Proof says it's
> correct; runtime says it loops.

### `Quot.sound` + `Classical.choice` ⇒ representative extraction

Choose a representative from each equivalence class.

**Failure mode QC-1: The Banach-Tarski-style fallout.**  In a
foundational sense, you can prove the existence of objects that
cannot be constructed.  For FX: theorems can assert "there exists a
verified program with property P" without yielding any actual
program.  You're proving emptiness has structure.

### All three (Lean's default classical foundation)

Approximately ZFC-strength.  Known consistent.

**Failure mode VAPOR-1: Verified vapor.**  Every theorem in your
stdlib is potentially built on classical reasoning + nonconstructive
Choice + extensional collapse.  The whole tower is consistent, but:

  * Decidable instances may be opaque (no algorithm).
  * Definitions may be noncomputable.
  * Equalities may not reflect operational distinctions.
  * Quotients may not respect intended equivalences.

You can have a "verified compiler" that doesn't compile anything,
"verified optimizations" that have no operational content, "verified
safety" that's trivially true because Decidable collapsed via
propext.

This is the realistic worst case: the formal system says everything
is fine.  The artifacts produce nothing.  **You shipped a proof, not
a program.**

---

## FX-specific catastrophes

These are tied to the multi-modal FX foundation.

### FX-Cat-1: Modal collapse via propext

```
⟨ghost⟩ Bool   ↔   Bool       (ghost is erased; propositionally equivalent)
propext        ⇒   ⟨ghost⟩ Bool = Bool
```

If our modal types collapse via propext, **erasure discipline
breaks**.  Kernel can't tell ghost-mode from runtime.  Compiler emits
ghost values into runtime; runtime reads them as live data; arbitrary
memory corruption.

### FX-Cat-2: Session protocol skip

A session type `send(x); recv(y); end` is a *protocol*.  Two sessions
that "happen to have the same termination state" can be propext-
equivalent (both are `(termination outcome) iff (termination
outcome)`).  The kernel believes a session that skipped `send` is the
same as one that did it.

> Result: protocol violations look like valid traces.  Verified
> networking code corrupts state at the wire.

### FX-Cat-3: Hardware-mode determinism failure via Choice

A `synth` modality function compiled to Verilog.  The Lean side uses
Choice somewhere to pick a representative.  Two compilations of the
same FX hardware module produce different gate-level Verilog.  Both
pass the bisimulation theorem.  Neither is what the engineer
intended, and the system cannot tell them apart.

### FX-Cat-4: The combination disaster

All three axioms + modal univalence + HIT primitive (Phase 3-4 of the
foundation plan):

  * `propext` + `ua_wire` ⇒ Wire-mode propositional equivalences
    become universal equalities.
  * `Quot.sound` + HITs ⇒ HIT equivalences propagate via Quot
    machinery.
  * `Choice` + modal types ⇒ noncomputable modal projections.

Worst-case path: a verified contract migration that propext-collapses
two distinct contracts into one, then HIT-quotients them, then
Choice-extracts a "representative."  The result type-checks.
Running it on real data: the migration silently drops fields, never
throws an error, never logs anything.

> **Data loss in production with a verified-correct certificate
> attesting it didn't happen.**

---

## Reserved FX-specific axiom catastrophes

The current foundation declares **zero** FX-specific axioms.  The
following names are reserved slots only: they describe where the
axiom pressure is expected to appear if the project later chooses to
cross from axiom-free encodings into kernel-level computation rules.

Each slot below is therefore a design warning, not a declaration.

### `ua_wire` — modal univalence at Wire mode

Intended role: equivalent Wire-mode contract types may be treated as
equal, so verified migrations, serialization formats, and protocol
adapters can transport values across equivalent wire descriptions.

What it would buy: contract migration by equivalence instead of by
hand-written adapter chains.  A proof that two wire contracts are
equivalent could become enough to move data between them.

**Failure mode UW-1: Contract identity collapse.**  If the chosen
notion of Wire equivalence is too coarse, distinct wire contracts
become equal.  A contract that preserves all fields and a contract
that silently drops an optional field can be treated as the same type
if the equivalence relation forgot to model that field.

> Concrete: `UserV1` and `UserV2` are proven equivalent because both
> can serialize to a common JSON object after dropping unknown keys.
> `ua_wire` turns that equivalence into type equality.  A migration
> proof now transports values across the equality and silently loses
> `UserV2.email_verified`.  The proof is correct against the
> equivalence; the equivalence was not what the product meant.

**Failure mode UW-2: Parser/serializer mismatch becomes definitional.**
Wire equivalence is usually observational: encode then decode
round-trips on accepted values.  If the parser accepts more than the
serializer emits, or the serializer normalizes in a lossy way,
`ua_wire` can promote a partial compatibility result into full type
identity.

> Concrete: a parser accepts both canonical and legacy decimal
> encodings, but the serializer always emits canonical decimal.  A
> proof of round-trip on canonical values is accidentally used as a
> proof of full contract equivalence.  `ua_wire` makes legacy and
> canonical payload types equal; old payloads accepted at the boundary
> cannot be reconstructed.

**Failure mode UW-3: Wire equality crosses a trust boundary.**  Wire
mode is exactly where external reality enters: bytes, protocols,
schemas, and peers outside the proof assistant.  If `ua_wire` is used
without a citation-backed external model, a local proof about a model
can become global equality about the world.

Mitigation if this axiom ever lands: scope it to a narrow
`WireEquiv` record with explicit encode/decode functions, losslessness
proofs in both directions, version labels, and external-format
citations.  Never allow arbitrary `Equiv` to feed `ua_wire`.

### `ua_ghost` — modal univalence at Ghost mode

Intended role: proof-only types in Ghost mode may identify equivalent
specifications without affecting runtime.  This is useful for proof
refactoring, theorem reuse, and high-level mathematical reasoning.

What it would buy: stronger proof transport in erased code while
leaving Software/Hardware/Wire computation untouched.

**Failure mode UG-1: Erasure leak through equality transport.**  Ghost
content is erased, but equality transports can still rearrange the
types of dynamic terms if the mode boundary is porous.  A Ghost-mode
univalence proof that is allowed to rewrite Software types collapses
the static/dynamic separation.

> Concrete: a Ghost proof establishes an equivalence between a refined
> dynamic type and its unrefined carrier.  If `ua_ghost` transport is
> permitted to rewrite Software terms, a runtime value can lose the
> refinement proof that was supposed to guard an array index.

**Failure mode UG-2: Proof irrelevance applied to computational
evidence.**  Ghost mode invites classical proof convenience.  If a
type classified as Ghost actually carries computational evidence
needed later (for example, a certificate that selects a verified
adapter), univalence can erase the difference between certificates.

> Concrete: two certificates both prove "schema migration valid."  One
> certifies a field-preserving adapter; the other certifies a lossy
> adapter under a weaker policy.  `ua_ghost` lets proof code treat the
> certificates as interchangeable.  Later extraction forgets which
> adapter was justified.

**Failure mode UG-3: Static inconsistency becomes operational by
reflection.**  The intended rule is "Ghost may be classical because it
does not run."  If the frontend later adds reflection from proofs into
diagnostics, optimization hints, or generated adapters, Ghost
equalities can influence runtime artifacts indirectly.

Mitigation if this axiom ever lands: make the Ghost/Dynamic boundary a
theorem, not a convention.  Any theorem using `ua_ghost` must be
unable to appear in the transitive dependency graph of evaluator,
normalizer, CoreIR, or backend definitions.

### `fix_productivity` — guarded fixed point for Later

Intended role: a Nakano-style guarded recursion principle for the
Later modality:

```lean
fix_productivity : ((Later A) -> A) -> A
```

or an equivalent typed rule.  This unlocks productive streams and
corecursive definitions where each recursive call is delayed by one
tick.

What it would buy: real guarded corecursion instead of only bounded
or manually unrolled delayed structures.

**Failure mode FP-1: Unguarded recursion smuggled through Later.**  If
the type system can forge `Later A -> A`, or if `modElim` for Later is
too permissive, `fix_productivity` degenerates into a general fixed
point combinator.  Strong normalization and total evaluation are gone.

> Concrete: a helper proves `force : Later A -> A` by a mode/coercion
> loophole.  Then `fix_productivity (fun delayed => force delayed)` is
> an inhabitant of any recursive equation.  The kernel still
> typechecks; the evaluator loops on terms that were certified total.

**Failure mode FP-2: Productivity proof checks the wrong clock.**  In
clocked guarded recursion, "later" must be later on the same clock
that the recursive definition consumes.  If clocks are labels without
strict scoping, a recursive call delayed on clock `k1` can be consumed
as if delayed on clock `k2`.

> Concrete: a stream producer delays recursive tail production on an
> internal proof clock, then exposes the stream on a hardware clock.
> The Verilog backend believes every cycle has a value; generated
> hardware reads an uninitialized register on cycle 0.

**Failure mode FP-3: Space leak certified as productive.**  Guarded
recursion proves that observations eventually produce values.  It does
not automatically prove bounded memory.  A careless `fix_productivity`
API can certify a stream as productive while each tick retains the
entire history.

> Concrete: a verified "constant space" stream transducer is
> productive but accumulates a thunk chain.  Software mode leaks
> memory; hardware mode synthesizes an unbounded register structure
> that cannot exist.

Mitigation if this axiom ever lands: the axiom must mention clocks and
guarded contexts explicitly.  It must not expose a general
`Later A -> A`.  Pair it with a separate space/size discipline before
using it for backend claims.

### `hit_path_intro` — computing paths for HITs

Intended role: higher inductive types with path constructors whose
eliminators compute over both point constructors and path
constructors.  This is the step from "HITs as setoid encodings" to
"HITs with kernel-level path computation."

What it would buy: quotient types, circles, truncations, and other
HoTT structures with usable computation principles rather than manual
respect proofs everywhere.

**Failure mode HP-1: Path constructor missing a coherence law.**  HITs
are not just point constructors plus path constructors.  Higher paths
and coherences matter.  If the axiom accepts an underspecified HIT,
the eliminator can compute in ways that violate the intended higher
structure.

> Concrete: a quotient HIT identifies terms by a relation but forgets
> the coherence that the relation is compatible with substitution.
> The eliminator proves a function respects the quotient, but
> substitution later observes different representatives and breaks
> subject reduction.

**Failure mode HP-2: Bad quotient relation becomes equality with
computation.**  `Quot.sound` already risks quotienting by the wrong
relation.  `hit_path_intro` makes the risk sharper: the wrong relation
does not merely prove equalities; it gets computation behavior through
the eliminator.

> Concrete: a HIT quotient identifies effect rows modulo a relation
> that forgot ordering constraints for handlers.  The path constructor
> computes through the handler eliminator, so two programs with
> different handler order become definitionally interchangeable.
> Runtime behavior changes while proofs still reduce.

**Failure mode HP-3: Nontermination through recursive HIT eliminators.**
If HIT eliminators are allowed to compute under path constructors
without a strict positivity and termination discipline, they can hide
recursive calls that Lean's ordinary inductive checker would reject.

> Concrete: an eliminator for a syntax quotient recursively normalizes
> under an equality path.  The path computation re-enters the same
> quotient proof.  The normalizer is "verified" but loops on a term
> whose equality proof was supposed to be irrelevant.

Mitigation if this axiom ever lands: start with named, specific HITs
whose eliminators are hand-audited, not a general HIT schema.  Require
strict positivity, explicit coherence fields, and a per-HIT
catastrophe note before allowing it into Layer K.

### Combined future-axiom catastrophe

The dangerous case is not any one future axiom.  It is the chain:

```text
ua_wire + ua_ghost + fix_productivity + hit_path_intro
```

combined with the three Lean core axioms already available in the
environment.

**Failure mode FUTURE-1: Verified self-rewriting protocol.**  A wire
contract equivalence becomes equality by `ua_wire`; proof-only
certificates become interchangeable by `ua_ghost`; a recursive stream
adapter is accepted by `fix_productivity`; a quotient over protocol
states computes by `hit_path_intro`.

If any one of the four specifications is too broad, the system can
derive a transport from one live protocol state to another, run it
forever productively, and erase the proof distinctions that would have
shown which adapter was selected.

> Concrete: a streaming migration between two wire protocols is
> verified.  On malformed legacy input, it repeatedly transports
> through an equality that drops a state transition, uses the guarded
> fixpoint to continue producing output, and hides the lossy adapter
> behind Ghost equality.  The service stays up, emits well-typed
> bytes, and silently corrupts every migrated stream.

**Failure mode FUTURE-2: Backend/model mismatch becomes unobservable.**
`hit_path_intro` can quotient backend states, `ua_wire` can identify
serialized observations, and `fix_productivity` can certify infinite
traces.  If the hardware model is wrong, the proof can make the wrong
model internally coherent enough that differential symptoms disappear
inside the formal layer.

> Concrete: an x86 flag model mishandles overflow on one instruction.
> A HIT quotient identifies traces modulo an observational relation
> that forgets that flag.  Wire univalence transports serialized trace
> certificates across the quotient.  The generated binary is verified
> against a model that can no longer state the bug.

Policy consequence: these future axioms must never be added as a
bundle.  Each one needs a separate RFC, a narrow scope, a model of its
failure modes, and an audit showing exactly which definitions and
theorems become dependent on it.

---

## Historical near-misses

Examples of these failure modes hitting other systems:

  * **Coq's proof-irrelevance + kernel bug (2017)**: Coq accepted a
    small definition that combined with `proof_irrelevance` (close
    cousin of propext) to derive `False`.  Bug was in the kernel's
    universe-checking logic.  **Implication**: Lean kernel bugs of
    similar shape would propagate to lean-fx via stdlib's propext.
  * **Agda's --without-K violation**: pre-cubical equality + a
    specific match could derive K, which is incompatible with HoTT-
    style univalence.  **Implication**: when we add modal univalence
    at Wire mode, K-violating patterns must be ruled out.
  * **Lean 3 `Classical.choice` extraction issue**: Some Lean 3 proofs
    using Choice extracted to runtime errors.  Not a soundness issue,
    but the extracted code panicked because the witness didn't exist
    at runtime.  **Implication**: any FX kernel function using Choice
    transitively cannot be extracted to runnable FX code.
  * **Early HoTT funext + universe paradox**: function extensionality
    + universe polymorphism + a specific encoding gave Type:Type-like
    collapse.  Patched by careful universe handling.
    **Implication**: as we add MTT modes + universes + funext (via
    propext + Quot.sound), each new dimension is a potential paradox
    surface.

---

## The layered discipline

To keep the catastrophes rare and visible, lean-fx adopts a graduated
trust model.  Each layer of the project has different rules.

### Layer K — Kernel (`LeanFX/Syntax/`, `LeanFX/Mode/`)

**Rule: zero axiom dependencies.**

  * No use of any of the three Lean core axioms, transitively.
  * No `partial def`.
  * No `sorry`.
  * No `unsafe`, `nativeReduce`, `nativeDecide`, `opaque def`.
  * Every theorem passes `#print axioms` with zero output.

Verified by CI when the audit script lands.  Currently verified
manually per-theorem.

### Layer M — Metatheory (future, post-MLTT-completion)

Theorems *about* the kernel — confluence, normalization, subject
reduction.

**Rule: `propext` and `Quot.sound` allowed; `Classical.choice`
discouraged and audited.**

Reasoning: confluence and SR proofs commonly use proof-irrelevance
reasoning that propext underwrites.  Choice can leak in via
`Decidable` instances; flag and review.

Each metatheory theorem must pass `#print axioms` and have its
output explicitly justified in the theorem's docstring.

### Layer E — Evaluator and code-generators

Future Phase 6 onward: the evaluator, normalizer, IR passes, codegen.

**Rule: zero `Classical.choice` use, period.**

Reasoning: Choice produces noncomputable values.  Any function
transitively using Choice cannot be extracted to a runnable form.
For FX's bootstrap goal (eventually self-host the compiler in FX),
the evaluator must be fully computable.

`propext` and `Quot.sound` allowed if needed but discouraged.

### Layer S — Surface-level user reasoning (FX program proofs)

User-level FX code with `verify` blocks, `assert` constructs,
property-based tests.

**Rule: all three axioms available with explicit acknowledgment.**

User-code reasoning may use full classical mathematics.  Trade-off
documented per-program: if a user-level proof uses Choice, the
verified property may not extract to runtime checks.

### Layer F — FX-specific axioms (future)

When we add `ua_wire`, `fix_productivity`, `hit_path_intro`, etc.,
each gets:

  * A documented signature in this file.
  * A scope restriction (e.g., `ua_wire` valid only at Wire mode).
  * An RFC explaining the kernel-level rule it stands in for.
  * A justification for why it cannot be derived.
  * An audit incantation showing which theorems depend on it.

Ceiling: 5 FX-specific axioms ever.  Combined with 3 Lean core, total
8.  Hitting the ceiling without dropping an existing axiom forces a
project-policy review before the 9th lands.

---

## The definition gap — beyond axioms

Axioms are not the only commitments lean-fx makes.  Definitions are
not axioms in the logical sense (they're conservative extensions),
but each `def` is a name the Lean kernel must check correctly, and
each one creates a *semantic commitment* — "this is what we mean by
X."

A wrong definition is just as harmful as a wrong axiom in
practice.  A `compile` function with a subtly wrong definition can
produce a "verified-correct" artifact that misbehaves in ways the
proof can't detect because the proof is *against* the wrong
definition.

This matters acutely for hardware, ISA modeling, encoding, and
serialization.  When we eventually need to write:

```lean
def x86.decode (bytes : ByteSequence) : Option Instruction := ...
def x86.execute (state : MachineState) (insn : Instruction) : MachineState := ...
def x86.eflags_after_add (a b : UInt64) : Flags := ...
```

we are committing to: **"the real x86-64 silicon behaves like this
Lean model."**  If the model deviates from the silicon (silicon bug,
undocumented behavior, microcode update, manufacturer-specific
extension), our verified compiler is verified against the model and
not against the actual hardware.

This is a different category of risk from axiom-induced unsoundness.
The proof is still correct; it just refers to the wrong external
reality.

### Mitigations for the definition gap

In order of strength:

  1. **Cite vendor specifications** at every definition.  If we model
     `x86 ADD`, the docstring must point to Intel SDM Vol. 2A or
     equivalent.  Reviewers can check the model against the cited
     source.
  2. **Multiple-presentation discipline**.  When practical, define a
     concept three ways (operational, denotational, algebraic) and
     prove pairwise equivalence.  A bug in one is caught by the
     others.
  3. **Differential testing** against trusted oracles.  Run our model
     against an existing emulator (QEMU for x86, IceStorm for
     iCE40 FPGAs) on randomly-generated inputs.  Disagreements
     indicate the model is wrong.
  4. **Use validated specs where they exist**.  Sail-derived ISA specs
     for x86, ARM, RISC-V are cross-validated against vendor docs by
     the Sail team.  Importing those instead of writing our own
     reduces independent error.
  5. **Test against actual hardware** for critical claims.  An FX
     program compiled to x86 should be tested on real silicon, not
     just our model.  Discrepancies point to model bugs.

### What this implies for the project plan

When we hit Phase 7 (Lean x86 backend) or Phase 8 (Verilog/Wire
backends), the documentation burden grows substantially:

  * Every modeled instruction needs a vendor-spec citation.
  * Every modeled state-transition needs a multi-presentation
    discipline.
  * A differential-testing harness needs to live alongside the
    formalization.

These are not "axioms" in the formal sense, but they are commitments
that affect what "verified" means in practice.  This file is the
right place to track that growth.

---

## Audit incantations

### Per-theorem axiom dependency

```lean
import LeanFX.Syntax.Term

#print axioms LeanFX.Syntax.Ty.subst_id
-- Expected: 'LeanFX.Syntax.Ty.subst_id' does not depend on any axioms
```

Any output mentioning `propext`, `Quot.sound`, `Classical.choice`,
`sorryAx`, or anything not enumerated in this document is a policy
violation.

### Per-theorem definition footprint

```lean
import LeanFX.Tools.DependencyAudit
import LeanFX.Syntax.Term

#audit_dependencies LeanFX.Syntax.Ty.subst_id
-- Reports: axioms / theorems / definitions / inductives / constructors /
--          recursors / quotients / opaques counts.
```

Use this to track the trust footprint over time.  Sudden growth in
definition count (e.g., a previously-100-dep theorem becomes a 1000-
dep theorem) indicates either substantial new dependencies or a
regression.

### Whole-project audit (when the script lands)

```bash
bash scripts/axiom-audit.sh
# Walks every public theorem in LeanFX.*, runs #print axioms,
# rejects build if any output is off-allowlist.
```

### Definition-gap audit for hardware (when Phase 7 lands)

```bash
bash scripts/spec-citation-audit.sh
# Walks every def in LeanFX.Backend.X86.*, checks that each has a
# vendor-spec citation in its docstring.
```

---

## Living document

This file evolves with the project.  Updates required when:

  * A new axiom is added to Layer F — append per-axiom catastrophe
    analysis and combinations with existing axioms.
  * A new layer of trust discipline is identified — append a layer
    section.
  * A near-miss or actual failure occurs — append to historical
    section as a permanent corpus entry.
  * A new external-reality definition is added (hardware, ISA,
    encoding, protocol) — extend the definition-gap section with the
    relevant model and its sources.

The eight-axiom ceiling is the project's standing commitment.  Any
proposal to exceed it requires a documented redesign discussion, not
a budget bump.
