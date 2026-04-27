# FX Theoretical Reframing

**Status**: proposal, not yet committed to implementation.
**Version**: draft 1, April 2026.
**Companion documents**: `fx_design.md` (canonical language spec),
`fx_modecat.md` (formal mode theory specification, forthcoming with
Phase R0), `leanx/docs/smt-placement.md` (Q50 decision doc for the
SMT periphery, first concrete instance of this commitment).
**Reading order**: §0 briefly; §1 for motivation; §2 for the
commitment; §3–§5 for the algebra and its peripheries; §6–§7 for
mapping and gains; §8–§9 for planning; §10–§11 for reflection;
§12 as a citable summary; appendices for depth and examples.

This document records FX's commitment to a specific theoretical
reframing: reorganizing the existing six systems (grade, effect,
refinement, sessions, contracts, hardware) as a single
**Multimodal Dependent Type Theory (MTT)** spine with a bounded,
enumerable set of peripheries.  The shape we commit to is a
slightly-heterogeneous unified algebra.  The rationale, the
algebra itself, and the migration roadmap are the subject of
the sections below.


## 0. Status and Scope

### 0.1 Status

This is a **proposal**.  The commitment named in §2 is load-bearing
— future design decisions will be checked against it — but the
implementation work (Track B per §8) is yet to begin.  The
document describes the target shape and the roadmap to reach it;
it does not describe FX as it exists today.  Current FX is
specified in `fx_design.md` and implemented in `leanx/`.

The document is **versioned**.  Major revisions append to the
§12 Decision Ledger rather than rewriting prior sections; the
rationale for every load-bearing claim stays on record for
audit.  A subsequent revision that reverses a prior commitment
adds a ledger row stating the reversal with rationale rather
than deleting the prior row.  This is the same discipline
`leanx/docs/smt-placement.md` §11 established for the SMT
placement question; it transfers here.

### 0.2 Scope

**In scope:**
  * The theoretical foundation of FX's type system.
  * The organizing framework: one algebra plus enumerable
    peripheries.
  * The mode theory that parameterizes the MTT instance FX
    becomes under the reframe.
  * The migration roadmap from current FX to the target.
  * The policy governing new additions during the migration.

**Out of scope:**
  * Surface syntax changes.  The reframe is internal; users
    continue to write `fn name(…) : T with eff = body;`, see
    the same error codes, and receive the same diagnostics.
    The reframe changes the kernel semantics, not the
    programmer's experience.
  * Implementation of the MTT kernel.  This document specifies
    what the kernel becomes; the implementation is tracked as
    Phase R1 in §8.
  * The formal mode theory specification.  `fx_modecat.md` is
    the separate artifact that lands with Phase R0; this
    document references it at the design level.

### 0.3 Reading audience

Three audiences, in decreasing depth of expected engagement:

  * **Designers** — anyone making theoretical decisions about
    FX's type system.  Read the whole document, especially
    §2 (commitment), §3 (algebra), §10 (composition pattern),
    §12 (ledger).
  * **Reviewers** — anyone validating a kernel-layer change
    during the migration.  Check the change against §9
    (policy) and the relevant row of §12 (ledger).
  * **Agents** — LLM agents writing FX code or kernel
    extensions.  Treat §9 as the operational constraint and
    §12 as the citable reference for "why" questions.

### 0.4 How to cite

Stable identifiers: `§N` for numbered sections, `§N.M` for
subsections, `§12.R` for ledger row R (stable once assigned,
never renumbered), `Appendix X.Y` for appendix subsections.
External citations to this document use the path
`fx_reframing.md` relative to the project root.

### 0.5 Relationship to fx_design.md

`fx_design.md` is the **current canonical specification** of FX.
It describes the language as it is implemented today.  This
document describes a **future rearrangement** of FX's theoretical
foundation that leaves `fx_design.md`'s surface commitments
intact.

During the migration (Phase R0–R5), both documents coexist.
`fx_design.md` remains authoritative on surface syntax,
semantics users observe, and the task catalog.  This document
becomes authoritative on the mode theory, the algebra of grade
composition, and the trust story around peripheries.  On
Phase R5 completion, `fx_design.md` is updated to reference
this document as the theoretical foundation; neither document
is retired.

### 0.6 How to update

Every substantive update:

  1. Adds a ledger row in §12 with rationale and date.
  2. Bumps the version banner in this preamble.
  3. Leaves prior sections intact unless a specific claim is
     reversed, in which case the reversal is named in the
     ledger.

Small corrections (typos, cross-reference fixes, prose
polish) do not require ledger entries.  The threshold for a
ledger entry is "would a reader acting on the prior version
do something different?"


## 1. Diagnosis — Why Reframe

### 1.1 FX's current theory is six stapled systems

FX today is the composition of six independent formal systems
with local soundness stories and ad-hoc interfaces between
them.  Listed in the order they appear in `fx_design.md`:

  1. **The dependent kernel** (§30, Appendix H) — Martin-Löf-
     style Π / Σ / Id / Quot plus Ind / Coind.  Sound in
     isolation; the kernel's metatheory is standard Calculus of
     Inductive Constructions modulo the Wood-Atkey Lam-rule
     correction (§30.13).

  2. **The grade system** (§6) — 22 dimensions organized into
     5 tiers (S/L/T/F/V) with a product grade vector on every
     binder.  Each tier has its own checking discipline; the
     product is asserted to compose by an informal argument.

  3. **The effect system** (§9) — bounded join-semilattice of
     effect rows.  Specializes Tier S's "Effect" dimension but
     carries its own subsumption rules (§9.3) and its own
     subsumption-edge declarations (§9.5).

  4. **Session types** (§11) — a separate derived module with
     its own typing rules, duality (§11.2), subtyping (§11.19,
     §11.20), composition (§11.22), and metatheory
     (§11.14–§11.18).  Translates to `CoindSpec` by §11.24 but
     the kernel does not natively understand sessions — it
     hosts the encoding.

  5. **Contracts** (§14) — wire-format validators plus
     migration adapters, generated at elaboration time.
     Connects to sessions (§11.8, §14.8) via ad-hoc routing of
     payload types through format bindings.

  6. **Hardware** (§18) — restricted synthesizable subset
     (§18.8) checked by excluding certain term shapes.  The
     restriction rules are stated but not derived from a
     general mode discipline; clock domains (§18.7) are Tier L
     but also carry their own semantics.

Each system is internally sound.  The composition story is the
problem.

### 1.2 The §6.8 collision catalog is asserted, not derived

`fx_design.md` §6.8 lists ten cross-dimension rules that
forbid specific compositions:

| Code | Collision |
|------|-----------|
| I002 | classified × Fail |
| L002 | borrow × Async |
| E044 | CT × Async |
| I003 | CT × Fail on secret |
| M012 | monotonic × concurrent |
| P002 | ghost × runtime conditional |
| I004 | classified × async × session |
| N002 | decimal × overflow(wrap) |
| L003 | borrow × unscoped spawn |
| (plus three reductions to existing infrastructure) |

Each is a genuine soundness collision.  Each is hand-stated.
Nothing in the current theory says "here is the algebra, and
these ten collisions are the consequences."  A future design
decision about a twenty-second grade dimension, or about a
new effect operation, has no principled way to predict which
new collisions arise — the catalog grows by manual
enumeration.

For comparison: in a 2-categorical algebra of modalities, a
composition of 1-cells either has a coherent 2-cell or does
not.  "Composition has no coherent square" is a mechanical
check; it is not a hand-curated rule.  The ten §6.8 rules
would all become instances of that mechanical check.

### 1.3 Every frontier addition has nowhere natural to land

The literature since 2015 has produced several type-theoretic
additions that would substantially strengthen FX:

  * **Guarded recursion** (Nakano 2000, Birkedal et al.
    2012–2025) replaces syntactic guardedness for coinduction
    with a modality that composes with other modalities.
  * **Internal parametricity** (Bernardy-Moulin, Nuyts-Vezzosi-
    Devriese 2017, Altenkirch et al. 2024) makes
    noninterference and linearity *provable theorems inside
    the type theory* rather than operational enforcements.
  * **Higher Inductive Types** (Voevodsky 2010, HoTT Book
    2013) encode quotients as data-plus-path constructors,
    subsuming the Quot-form / intro / lift axioms.
  * **Modal univalence** (UniMath, Cubical Agda) makes
    equivalent structures propositionally equal, which would
    let contract migrations be transport along equivalences
    rather than manually-discharged proofs.
  * **Pfenning-Toninho linear corecursion** gives session
    types productivity-by-construction instead of trust-based
    `with Div` escapes.

Each is a genuine upgrade.  None of them fits in FX today.
Adding guarded recursion requires a new modality layer the
current grade system cannot host.  Adding internal
parametricity requires bridge types that do not compose with
the existing effect lattice.  Adding HITs requires a new
elimination scheme beyond the current `indRec`.  Adding modal
univalence requires a mode theory to host the modality.

The fragmentation is not just aesthetic.  It actively blocks
FX from adopting the frontier techniques that would make it a
research-grade calculus.

### 1.4 Proof obligations are scattered across the architecture

FX discharges proofs through multiple mechanisms:

  * **Operational enforcement** for usage, lifetime, effect,
    security — the grade checker rejects violations.
  * **SMT dispatch** for refinement types, `pre`/`post`/
    `decreases` — the Verify layer per Q50 consults Z3.
  * **Kernel rules** for equality, subtyping, conversion —
    `convEq` + `subOrConv`.
  * **Ad-hoc structural checks** for guardedness (§3.5),
    strict positivity (§30), label distinctness in sessions
    (§11.14), balanced+ in async sessions (§11.15).
  * **External model checkers** for larger session-safety
    predicates (§11.18 beyond `live++`).

Each mechanism has its own failure mode, its own
diagnostic structure, its own trust level.  An FX program's
overall soundness is the conjunction of local guarantees
from each, and the composition argument is scattered across
five files and multiple research papers.

A unified framework would have one dispatch rule ("discharge
this obligation according to its mode") and one composition
argument ("the mode theory is coherent, therefore the
composition of discharged obligations is sound").

### 1.5 The cost — why this matters now

As FX scales in features (sessions S6–S25, contracts, hardware
pipelines, verification) the fragmentation compounds.  Two
specific failure modes:

  * **Accidental axiom growth.**  The current kernel has 33
    axioms (Appendix H allowlist).  Each new feature risks
    adding more — every new kernel primitive is a potential
    axiom, every new cross-dimension rule is a potential
    trust escape.  Without a principled framework, the
    allowlist grows without bound.

  * **Soundness handwave.**  The claim "22 dimensions
    compose" is load-bearing but not proven.  A kernel
    change that invalidates one of the implicit coherence
    conditions between dimensions would not be caught by
    `lake build` — it would manifest as a typing rule
    accepting programs it should reject.  The test suite
    would have to catch it; the theory would not.

A reframe now costs one Phase R0–R5 cycle.  A reframe later,
after the kernel has grown to 50+ axioms and every feature
has accreted local soundness workarounds, would cost a
rewrite.

### 1.6 Evidence: where the fragmentation lives in the codebase

For readers validating the diagnosis against the code:

  * `leanx/FX/Kernel/Typing.lean` — the check/infer rules
    that explicitly enumerate each Term constructor with
    ad-hoc grade handling.  Scan for the thirteen `match`
    arms.
  * `leanx/FX/Kernel/Grade/*.lean` — 21 separate files, one
    per dimension.  Each has its own ordering, its own
    combining operators, its own subsumption rule.  No
    cross-dimension coherence module.
  * `leanx/FX/Kernel/Grade/Tier.lean` — tier scaffolding
    (post-T1).  The closest current approximation to a mode
    theory; lacks 2-cells and cross-mode adjunctions.
  * `leanx/FX/Derived/Session/Binary.lean` — session-type
    module with its own subtyping (S5), its own
    well-formedness (S4), its own duality (S2).  Connects
    to kernel only through future S9 CoindSpec translation.
  * `fx_design.md` §6.8 — the ten-rule collision catalog.
  * `fx_design.md` §11.14 — the three well-formedness
    conditions for sessions (guardedness, label distinctness,
    balanced+).  Distinct from the kernel's positivity
    check.

The diagnosis is not that any one of these is wrong.  It is
that they are not connected to each other by anything
stronger than prose.  Under the reframe, they become
instances of the same algebra.


## 2. Commitment — MTT as the Algebraic Spine

### 2.1 Core commitment

FX's long-term theoretical foundation is
**Multimodal Dependent Type Theory** (Gratzer, Kavvos, Nuyts,
Birkedal, LICS 2020; normalization proved LICS 2022) with a
mode theory tailored to FX's semantic domains (§3).  Every
grade dimension of the current design becomes a modality or
a 2-cell constraint in this mode theory.  Cross-dimension
composition becomes composition of 2-cells; the ten §6.8
collision rules become consequences of the 2-category's
coherence.

The commitment is concrete: once the reframe is implemented,
there exists a single mathematical object (the mode theory
2-category) such that "FX accepts program P" is definable as
"P elaborates through the MTT instance parameterized by that
mode theory."  The twenty-one-dimensional product grade
vector of today's FX disappears into the mode-structured
context of MTT.

### 2.2 The slightly-heterogeneous claim

FX is not monolithic.  A monolithic reframe — everything is
an MTT modality, no exceptions — would force SMT dispatch,
code generation, external tooling, and user-defined
extensions into the mode theory.  Each of these either does
not admit a modal reading (SMT; see `leanx/docs/smt-placement.md`
§7) or belongs naturally outside the spine (codegen,
tooling, user extensions).

Instead, FX commits to **one algebraic spine plus an
enumerable set of peripheries**.  The spine is the MTT
instance parameterized by FX's mode theory.  The peripheries
are listed explicitly (§5) with well-defined interfaces to
the spine.  New peripheries require an RFC per §9; new spine
modalities must justify themselves within the mode theory's
structure.

This shape is named the **composition pattern** in §10.  The
name is important because future decisions will invoke it:
"is this new feature part of the spine or a periphery?" is
answered by §10's criteria, not by ad-hoc judgement.

### 2.3 What's in the spine

The MTT spine contains:

  * The mode theory 2-category (§3.1).
  * The eighteen Software modalities corresponding to the
    current Tier-S and Tier-L graded dimensions (§3.2).
  * The Protocol modality in Tier T (session typestate,
    §3.2.3).
  * Cross-mode adjunctions for Ghost/Software/Hardware/Wire
    transitions (§3.5).
  * The 2-cells encoding subsumption rules and the (missing)
    2-cells encoding §6.8 collisions (§3.6).
  * The guarded recursion modality Later (§4.1).
  * The bridge modality B for internal parametricity (§4.2).
  * Higher Inductive Types (HITs) for quotients (§4.3).
  * Modal univalence at the Wire boundary (§4.4).
  * Pfenning-Toninho linear corecursion structure for
    sessions (§4.5).
  * Two-level separation (2LTT) for ghost vs runtime (§4.6).

Everything in this list is machine-checkable by a finite
kernel verifier whose soundness is covered by a single
theorem (MTT canonicity for this mode theory).

### 2.4 What stays peripheral

The peripheries (§5 enumerates these in full):

  * SMT dispatch (`leanx/FX/Smt/*` and `leanx/FX/Elab/Verify.lean`).
  * Codegen IRs (FXCore, FXLow, FXAsm per §20 of fx_design.md).
  * The agent-protocol daemon (§24).
  * User-defined grade dimensions (§6.6).
  * Surface syntax and elaboration.

Each periphery has an interface to the spine documented in
its module's CLAUDE.md.  Peripheries can evolve
independently of the spine as long as their interfaces
stay stable.  A new periphery requires naming in §5 and
specifying its interface; the policy (§9) forbids
un-enumerated peripheries.

### 2.5 Non-goals

Several attractive directions are explicitly rejected:

  * **Full HoTT / cubical type theory** — interval
    variables, Kan composition, full path-type computation.
    Rejected because cubical evaluation is roughly 2×
    kernel complexity with limited benefit for FX's
    domain.  The parts of HoTT that help FX (HITs,
    targeted univalence) are adopted as MTT modalities
    (§4.3, §4.4) without the full cubical machinery.
  * **Abandoning the current kernel** — gradual migration
    (§8), not rewrite.  The current FX kernel stays
    compilable during Phases R1–R4; the new kernel runs in
    parallel as `FX/KernelMTT/` until Phase R5 migration.
  * **Losing §1.2 deny-by-default** — the reframe
    preserves the capability discipline.  Modalities are
    the machinery for granting capabilities, not for
    loosening them.
  * **Losing §1.5 compile-time erasure** — ghost content
    stays erased.  The 2LTT separation (§4.6) formalizes
    this more cleanly than today's ad-hoc ghost grade.
  * **Becoming SMT-first like F*** — FX stays structural-
    first.  SMT is a periphery, not a primary discharge
    mechanism (`leanx/docs/smt-placement.md` §7).
  * **User-defined modalities in the spine** — user-defined
    grade dimensions (§6.6) stay peripheral.  The spine's
    mode theory is fixed per reframe version; user
    extensions live outside.

### 2.6 Acceptance criteria

"FX is an MTT instance" means, concretely:

  1. A file `leanx/FX/KernelMTT/ModeTheory.lean` contains
     the mode theory 2-category as a Lean 4 definition,
     with proofs of the 2-category laws.
  2. A file `leanx/FX/KernelMTT/Instance.lean` contains the
     MTT kernel instantiated at that mode theory, with
     canonicity derivable from Gratzer LICS 2022.
  3. Every current grade dimension has a corresponding
     modality in the instance, with a semantic equivalence
     proof showing the MTT typing rule accepts the same
     programs as the current tier rule.
  4. The current `Grade.add` / `Grade.mul` operations are
     provably derivable from the 2-cell composition in the
     mode theory.
  5. The ten §6.8 collision rules are provable as
     non-existence of coherent 2-cells in the mode theory.
  6. The axiom count (Appendix H of fx_design.md) drops
     from 33 to ≤ 15.  Every dropped axiom is replaced by a
     derivation from MTT canonicity or from the mode
     theory's structure.

Acceptance criteria 1–6 are the gate for Phase R5
migration (§8.7).  Until all six are met, the MTT kernel
runs in parallel with the current kernel, not as a
replacement.


## 3. The Mode Theory — FX's Single Algebra

### 3.1 Modes (0-cells)

Four modes organize FX's semantic domains:

  * **`Ghost`** — compile-time-only content.  All values
    erased at runtime per §1.5.  Proofs, specifications,
    refinement predicates, ghost grade bindings live here.
    The target of the `erase` adjunction from `Software`.
  * **`Software`** — the main programming domain.  Every
    user-written function, every runtime value, every
    effect operation lives here.  This is what the user
    thinks of as "FX code."
  * **`Hardware`** — synthesizable subset.  A restricted
    mode where only clock-domain-respecting, bit-vector-
    representable, bounded-loop-free terms are valid.
    Target of the `synth` morphism from `Software`.
  * **`Wire`** — cross-boundary serialized domain.  Where
    contracts live.  Carries the modal-univalence modality
    (§4.4) so equivalent wire formats are interchangeable.

These four modes capture every semantic distinction FX
currently makes.  `Ghost` subsumes today's ghost grade and
proof-block content.  `Software` is the default.
`Hardware` subsumes today's synthesizability rules from
§18.  `Wire` subsumes today's contract-format machinery
from §14.4.

No fifth mode is needed at commit time.  User-defined
modes could be considered under a future extension but are
out of scope for this reframe (see §2.5 non-goals).

### 3.2 Modalities within Software (eighteen endo-modalities)

Each current Tier-S and Tier-L graded dimension becomes a
modality on the `Software` mode.  Tier T (Protocol) is one
modality.  Tier F (Type, Refinement) is not a modality;
these are handled by the base MTT's dependent-types
machinery.  Tier V (Version) is a modality with adapter
edges (§3.2.3).

**Tier S commutative semiring modalities (Software endo-modalities):**

| Modality | Current grade | Usage |
|----------|---------------|-------|
| `◇_usage` | `{0, 1, ω}` | linearity discipline |
| `◇_sec` | `{unclassified, classified}` | information-flow |
| `◇_eff` | effect row | what operations fire |
| `◇_lifetime` | region | reference validity scope |
| `◇_provenance` | origin lattice | data source tracking |
| `◇_trust` | trust lattice | verification status |
| `◇_obs` | `{opaque, transparent}` | access-pattern leakage |
| `◇_complexity` | ℕ | operation count |
| `◇_precision` | ℚ | FP error bound |
| `◇_space` | ℕ | allocation bound |
| `◇_overflow` | `{exact, wrap, trap, saturate}` | integer overflow |
| `◇_fporder` | `{strict, reassociate}` | FP ordering |
| `◇_mutation` | lattice | mutation permission |
| `◇_reentrancy` | `{non_reentrant, reentrant}` | self-reference |
| `◇_size` | ω+1 | codata observation depth |

Fifteen modalities.  Each lifts a type `A : Software` to
`◇_X A : Software` with a parameterizing element of the
modality's grade domain.

**Tier L lattice modalities:**

| Modality | Current grade | Validity |
|----------|---------------|----------|
| `◇_repr` | layout lattice | `valid_Representation` |
| `◇_clock` | `{combinational, sync(κ)}` | no cross-domain without sync |

Two modalities.  Lattice structure carries the validity
predicate that rejects incompatible joins (§3.6).

**Tier T typestate modality:**

| Modality | Current grade |
|----------|---------------|
| `◇_protocol` | session-type state |

One modality.  The only Tier T modality.  Its semantics are
transitional rather than semiring-based (§3.2.3).

Total within `Software`: **eighteen modalities** (15 Tier-S
commutative + 2 Tier-L + 1 Tier-T Protocol).  Two more
modalities (Later guarded and B bridge) from frontier additions
(§4) land here too, bringing the `Software` mode's total
to twenty endo-modalities.

### 3.2.1 Effect modality specialization

The `◇_eff` modality deserves specific notation.  An effect
row `{e₁, …, eₙ}` is a finite subset of the effect universe.
`◇_{e₁, …, eₙ} A` is the type of computations of type `A`
that may perform those effects.  The lattice order on
effect rows (subset) becomes the 2-cell structure on
`◇_eff` modalities: `◇_{} ≤ ◇_{IO} ≤ ◇_{IO, Alloc}`.

### 3.2.2 Lifetime modality is not ghost

The `◇_lifetime` modality carries a region variable.  Its
semantics are distinct from ghost erasure: lifetimes erase
at codegen (§1.5), but their 2-cell algebra is
well-formation of borrows, not computational content.  A
reference borrowed for region `r` lives in
`◇_{ref(r)} A : Software`; the erase adjunction to
`Ghost` carries the lifetime proof without carrying a
runtime witness.

### 3.2.3 Protocol modality is transitional, not algebraic

Tier T's Protocol modality is the most specialized.  Its
"grade" is a session type state; its composition is state
advancement, not semiring multiplication.  Formally,
`◇_{S} A : Software` is the type of channels at session
state `S` carrying messages of type `A`.  The 2-cells on
`◇_protocol` encode Gay-Hole synchronous subtyping
(§11.19) and precise async subtyping (§11.20).  Session
duality (§11.2) becomes an involution on the Protocol
modality's grade domain.

### 3.2.4 Version modality (Tier V) lives at the Wire mode

On inspection, Tier V "Version" is not really a Software
endo-modality — version transitions happen at wire
boundaries (§14.10).  Under the reframe, `◇_version` lives
at the `Wire` mode (§3.4), and the `serialize`/`parse`
adjunction (§3.5) carries the version-refinement and
migration-adapter machinery of §15.4 / §15.6.

### 3.3 Modalities within Hardware

The `Hardware` mode carries a **strict subset** of Software
modalities, reflecting §18.8's synthesizability rules:

| Modality | Purpose |
|----------|---------|
| `◇_clock` | clock-domain tracking (primary) |
| `◇_repr` | register layout (required for synthesizability) |
| `◇_precision` | precision of numeric operations in RTL |
| `◇_complexity` | circuit-depth / gate-count bounds |

Four modalities.  The remaining fourteen Software
modalities are **absent** from `Hardware`.  Attempting to
lift a `Hardware` value with an absent modality is rejected
at elaboration — the reason today's `with IO` / `with
Alloc` are compile errors inside a `hardware` block.

The absence is carried by the `synth : Software → Hardware`
morphism (§3.5.2): `synth` is a partial morphism, undefined
on Software types whose modality spectrum includes effects
Hardware does not admit.

### 3.4 Modalities within Wire

The `Wire` mode hosts two primary modalities:

| Modality | Purpose |
|----------|---------|
| `◇_format` | serialization format binding |
| `◇_version` | version-migration machinery |

Plus modal univalence (§4.4), which lives specifically at
this mode.  The `Wire` mode is where two contracts with
observationally-equivalent validators become propositionally
equal, so contract migrations become transport along
equivalences.

### 3.5 Cross-mode adjunctions

Four adjunctions organize the cross-mode semantics:

### 3.5.1 Ghost ⊣ Software

```
ghost : Ghost → Software       (lift ghost to runtime, trivially)
erase : Software → Ghost        (erase to proof-level view)
```

These form an adjunction `ghost ⊣ erase`: every ghost value
has a canonical lift to Software (a zero-runtime-cost view),
and every Software value has a canonical erase-to-Ghost
(forgetting its runtime content, keeping its typing).

This subsumes today's ghost grade.  A `ghost x : A` binding
is a `x : ghost A` under the reframe — a Ghost-mode type
lifted into Software with the zero-runtime-cost modality.

### 3.5.2 Software → Hardware (synth)

```
synth : Software → Hardware
```

Partial morphism.  Defined on the Hardware-modality-
compatible subset of Software types; undefined (raises a
compile error) otherwise.  Carries the §18.8
synthesizability rules.  No right adjoint — Hardware values
cannot be lifted to Software without an explicit
`observe` (a hardware-to-software signal read).

### 3.5.3 Software ⇄ Wire (serialize ⊣ parse)

```
serialize : Software → Wire
parse     : Wire → Software
```

Adjunction between Software and Wire mediated by a
contract.  `serialize_C` encodes a Software value per
contract `C` into a Wire value.  `parse_C` decodes a Wire
value back into Software, potentially failing.  The
adjunction unit (`serialize ∘ parse = id_Wire`) is the
round-trip law contracts must satisfy; the counit
(`parse ∘ serialize = id_Software`) is the preservation law
for the contracted types.

Every `C.decode` / `C.encode` (§14.5) pair is an instance
of this adjunction for contract `C`.  Contract migrations
(§14.2) become morphisms between parse / serialize pairs for
different versions, and modal univalence (§4.4) makes
compatible migrations interchangeable.

### 3.5.4 Hardware → Software (observe)

```
observe : Hardware → Software
```

One-way morphism.  A hardware signal (a value in
`Hardware`) can be read into Software at a specific clock
cycle via `observe`.  The result is a `Software` value
tagged with the clock domain it came from (via `◇_clock`
in the target mode).  No inverse — Software values cannot
be injected into Hardware without `synth` (§3.5.2).

### 3.6 2-cells — subsumption and collision encoding

The 2-cells in the mode theory 2-category encode two kinds
of structure:

### 3.6.1 Subsumption as 2-cells

Every subsumption rule in the current FX design becomes a
2-cell.  Examples:

  * `Tot ≤ IO`: a 2-cell `id → IO-addition` on the `◇_eff`
    modality.  A Tot function can be used where IO is
    expected; this is the 2-cell witnessing the inclusion.
  * `unclassified ≤ classified`: 2-cell on `◇_sec`.
    Public data can be used where classified is expected;
    the 2-cell witnesses the weakening.
  * `repr(Native) ≤ repr(C)`: 2-cell on `◇_repr`.  A
    C-compatible layout is usable where native-picked
    layout is expected.
  * User-declared `A subsumes B` in effect declarations
    (§9.5): a 2-cell on the effect-variable modality.

Every subsumption edge in `fx_design.md` §6.3 maps to a
2-cell.  The full enumeration lands in `fx_modecat.md` (the
formal spec), not this document.  What matters here: they
all fit in one framework.

### 3.6.2 Collisions as missing 2-cells

The ten §6.8 collision rules become **non-existence of
coherent 2-cells** for specific modality compositions.
Examples:

  * **I002 — classified × Fail**.  Composition of `◇_sec`
    (classified) with `◇_eff` (Fail) has no coherent 2-cell
    unless the Fail payload's `◇_sec` is also classified.
    The 2-cell exists only in the refined form
    `Fail(secret E)`.
  * **L002 — borrow × Async**.  `◇_usage` (borrow grade)
    composed with `◇_eff` (Async) at an `await` site has
    no coherent 2-cell — the borrow lifetime and the async
    suspension are incompatible.  Same cell absence yields
    compile error L002.
  * **E044 — CT × Async**.  `◇_obs` (CT) × `◇_eff` (Async)
    has no coherent 2-cell.  No refinement admits the
    combination; the 2-cell is absent unconditionally.
  * (Seven more rules follow the same pattern.)

Under the reframe, adding a 2-cell would permit a
composition; adding a new collision rule is NOT a new check
— it is a statement that a specific 2-cell does not exist.
The coherence proof is mechanical.

### 3.6.3 Validity predicates (Tier L) as 2-cell refinements

Tier L lattice modalities carry validity predicates
(`valid_Representation`, `valid_Clock`).  Under the reframe,
validity becomes a 2-cell conditional: the 2-cell for
joining two `◇_repr` modalities exists iff
`valid_Representation(join(a, b))` is not `None`.  The
T047 error (incompatible representation) is the diagnostic
for a missing conditional 2-cell.

The Tier L / Tier S distinction in today's grade system
collapses under the reframe to "lattice modalities carry
conditional 2-cells."  The tier classification remains as
documentation / refactoring aid but is no longer a
load-bearing distinction.

### 3.7 Worked example — a graded Pi type

To make the algebra concrete, trace a current FX type
through the reframe:

**Current:**
```
Π (x :_{usage: own, sec: classified, lifetime: r}
     A) →_{effects: IO, Alloc} B
```

**Under reframe:**
```
Π (x : ◇_{usage: own} ◇_{sec: classified} ◇_{lifetime: r} A)
  → ◇_{eff: {IO, Alloc}} B
```

Three modalities stack on the domain `A`; one modality
lifts the codomain `B`.  At an application `f a`, the
modality spectrum of `a` must compose coherently with the
modality spectrum the Π binder demands — this composition
is the 2-cell check.  A composition that fails produces the
familiar type error; a composition that succeeds produces
the current grade-vector update as a derived operation.

Grade arithmetic (`Grade.add`, `Grade.mul`, `Grade.scale`)
becomes derived from 2-cell composition in the mode theory.
The current `Grade.lean` aggregator becomes a single module
that exposes the derived operations; the per-dimension
files (`FX/Kernel/Grade/*.lean`) become modality
definitions.

### 3.8 Validity — what proves the algebra is coherent

The mode theory is a 2-category.  Its validity is the
conjunction of four properties, each of which is
machine-checkable:

  1. **Compositionality of 1-cells** — modalities compose
     associatively.  Proved by §3.2 modality definitions
     being functors on `Software`.
  2. **2-cell coherence** — the 2-cells satisfy the 2-category
     coherence conditions (interchange law, identity laws,
     associator).  Proved by structural induction on 2-cell
     definitions.
  3. **Adjunction correctness** — the four adjunctions
     (§3.5) satisfy unit/counit laws.  Proved per
     adjunction.
  4. **Canonicity** — MTT canonicity (Gratzer LICS 2022)
     applies to this mode theory once properties 1–3 are
     established.

The full proof is the Phase R0 deliverable (§8.2).  This
document commits to the shape; the formal proof lands with
`fx_modecat.md`.


## 4. Frontier Modalities on the Spine

The frontier additions surveyed in §1.3 become specific
modalities in the mode theory.  Each is a spine addition,
not a periphery — they participate in the coherence
theorem.

### 4.1 Guarded recursion — the Later modality

**Origin**: Nakano 2000, Birkedal-Møgelberg-Schwinghammer-
Støvring 2012, Bizjak-Møgelberg-Birkedal 2016.

**Signature**: `Later : Software → Software` with:
  * `next : A → Later<A>` — lift a value to "available next
    tick"
  * `fix : (Later<A> → A) → A` — productive fixed point
  * 2-cells for lifting: `A → Later<A>` functorially

**What this replaces**:
  * §3.5 G-Unfold syntactic guardedness check
  * The `Guarded.absent` walker in `FX/Kernel/Coinductive.lean`
  * Coind-ν kernel axiom (Appendix H.5.4)

**What this enables**:
  * Productivity by guarded-modality elimination, not
    syntactic walk.  A codata body `unfold head => e₁; tail
    => e₂` elaborates to `fix (λself. { head := e₁; tail
    := e₂[self] })` where `self : Later stream(a)`.  The fix
    is productive because every observation breaks through
    exactly one Later.
  * Multi-clocked sessions (§4.1.1).
  * Compositional proofs of productivity — `Later` composes
    with other modalities directly, so a `Later (◇_{Async} A)`
    is a perfectly well-formed type meaning "an async
    computation available next tick."

### 4.1.1 Clock quantification for sessions

Atkey-McBride clocks (2013): each Later can be parameterized
by a clock `κ`.  `Later<k> A` is "available next tick on clock
`κ`."  `∀κ. A` quantifies over clocks.

Under the reframe, every session channel owns its own
clock.  Sending consumes the channel-at-clock-κ and
produces channel-at-next-tick:

```
send : ∀κ. payload → channel<Send<P, K>, κ>
         → Later<k> channel<K, κ>
```

Two independent channels (§11.22 parallel composition) are
at disjoint clocks — disjointness is the compatibility
condition, and `Later<k> ⊗ Later^λ = Later^{κ ∨ λ}` is the synchronization
modality for shared-clock sessions.  This machinery is
built into MTT; it does not require session-specific rules.

### 4.1.2 Implementation footprint

  * ~300 lines of new kernel for Later plus `fix` plus clocks.
  * Displaces ~500 lines of current `Guarded.absent` +
    `FX/Kernel/Coinductive.lean` machinery.
  * Net smaller and more expressive.

### 4.2 Internal parametricity — the B (bridge) modality

**Origin**: Bernardy-Jansson-Paterson 2010, Bernardy-Moulin
2012, Nuyts-Vezzosi-Devriese 2017, Cavallo-Harper 2020
(cubical), Altenkirch-Chamoun-Kaposi-Shulman 2024 (without
interval).  Agda `--bridges` (POPL 2024) is the first
practical implementation.

**Signature**: `B : Software → Software` with:
  * `B A` is the type of "bridges between values of A"
  * For any function `f : ∀A. A → A`, parametricity
    forces `∀a b. B a b → B (f a) (f b)` — free theorems
    provable inside FX
  * Subsumes relational parametricity + eases
    noninterference proofs

**What this enables**:
  * §12 noninterference becomes a theorem provable inside
    FX.  Algehed-Bernardy ICFP 2019 (`fx-refs/DynamicIFC
    TheoremsForFree/`) is the proof template: ~40-line core.
  * Linearity as a free theorem: `∀A. (A ⊸ A)` must use
    its argument once, proven by bridge structure.
  * Free theorems on session types: `∀P. channel<Send<P>>
    → channel<End>` must send exactly once.

**What this does NOT enable**:
  * Proving lemmas unrelated to parametricity.  Bridges
    apply to polymorphic functions; monomorphic results
    still need structural proof.

**Implementation footprint**:
  * ~400 lines of new kernel (bridge type, eliminator,
    parametricity lemma generator).
  * ~100 lines of tactic support for parametricity-based
    proofs.
  * Integrates with MTT canonicity via Nuyts-Vezzosi 2017
    presheaf model.

### 4.3 Higher Inductive Types — targeted adoption

**Origin**: Voevodsky 2010 (quotient inductive-inductive
types), Univalent Foundations 2013 (HoTT Book), Cubical
Agda library `fx-refs/cubical/Cubical/HITs/`.

**Scope under the reframe**: HITs specifically for
quotient types.  NOT full-power HoTT HITs (no pushouts, no
suspensions, no general pointed types).

**Signature**: a quotient HIT has:
  * Data constructors: lift a value of the carrier type
  * Path constructor: `eq_rel : ∀ a b. R a b → ⟦a⟧ = ⟦b⟧`
  * Eliminator: induction on both the data and the paths

**What this replaces**:
  * Quot-form (H.7.1), Quot-intro (H.7.2), Quot-lift (H.7.3)
    axioms.  All three derivable from the HIT definition.
  * `Term.quot` / `Term.quotMk` / `Term.quotLift`
    constructors become HIT-specific; the three axioms
    drop from the Appendix H allowlist.

**Net axiom impact**: −3 axioms, +1 HIT general rule.

### 4.4 Modal univalence — at the Wire boundary

**Origin**: Voevodsky univalence (HoTT Book 2013),
Cohen-Coquand-Huber-Mörtberg 2018 (cubical), modal
univalence variants in parametric type theories (Nuyts-
Vezzosi).

**Scope under the reframe**: univalence ONLY at the
`Wire` mode.  Not general: univalence for arbitrary
Software types is too expensive and unnecessary.

**Signature**: for contracts `C₁` and `C₂` such that
`C₁.validate = C₂.validate` (same accepted values), the
modal univalence axiom gives `C₁ = C₂` in `Wire`.  Migration
between versions becomes transport along the equivalence,
which computes nontrivially.

**What this enables**:
  * §14.2 contract migrations are equalities, not
    constructions.  `C.migrate v_old v_new` becomes
    `transport (migration_eq v_old v_new) x`, and transport
    computes.
  * Two different contracts implementing the same API are
    interchangeable — the equivalence is the isomorphism.

**What this does NOT enable**:
  * Full HoTT computation inside Software.  Univalence at
    Software would require cubical machinery; Wire-only is
    cheap because the mode is narrow.

**Implementation footprint**:
  * ~200 lines adding the univalence axiom (scoped to Wire).
  * ~150 lines of transport machinery for contract
    migration.

### 4.5 Pfenning-Toninho linear corecursion

**Origin**: Pfenning-Toninho "Corecursion in Session-Typed
Processes", CMU (`fx-refs/`, see smpst-sr-smer for
mechanization adjacent).

**Scope**: the linear logic foundation for coinductive
session types.  Guarantees divergence-free observable
behavior by construction.

**What this replaces**:
  * Session types' current reliance on `with Div` as an
    escape for non-productive protocols.  Under the
    reframe, session channels are `with Productive` or
    don't compile.  No `with Div` session escape.
  * The CoindSpec guardedness check on session-type
    translations (§11.24).  Replaced by the Later modality
    discipline (§4.1).

**Integration with Later**: Pfenning-Toninho corecursion is
expressible via Later-parameterized session types.  A
corecursive session is a `fix : (Later channel<S,κ> →
channel<S,κ>) → channel<S,κ>` — the fix is productive
because each observation steps through Later.

### 4.6 Two-Level Separation — 2LTT

**Origin**: Voevodsky two-level type theory, Capriotti
2017, synthetic Tait computability (Gratzer et al.).

**Scope**: the mode-level separation between `Ghost` and
`Software` is a 2LTT instance.  Formal proofs live at
Ghost; runtime code lives at Software; the erase adjunction
is the explicit mode transition.

**What this replaces**:
  * Ad-hoc ghost grade tracking.  Today's ghost binding
    becomes a Ghost-mode binding; the erase-to-Software
    adjunction handles the zero-runtime-cost view.
  * Trust propagation (dim 9) across the call graph
    becomes mode-transition tracking.  A Software function
    that calls a `sorry`-tainted Ghost function has an
    erase-adjunction-loss of trust, captured at the
    mode-transition point.

**What this does NOT replace**:
  * The trust lattice itself (Verified > Tested > Sorry >
    Assumed > External) stays.  2LTT is about the
    separation of proof-level from runtime-level content,
    not about the trust algebra.

### 4.7 The synthesis — how 4.1–4.6 compose

The six frontier additions all live on the `Software` mode
(plus Wire for §4.4).  Their compositionality is the
MTT instance's coherence:

  * `Later` composes with `B` (guarded parametricity —
    parametricity for productive computations).
  * `B` composes with every Tier-S modality (parametricity
    over usage, security, effect, etc.).
  * HITs live alongside modalities (they are a new rule
    schema, not a modality).
  * Modal univalence at Wire does not interact with
    Software modalities directly.
  * Pfenning-Toninho corecursion is Later-parameterized
    session types — integrated with §3.2.3 Protocol
    modality and §4.1 Later.
  * 2LTT is the mode-level separation — orthogonal to the
    Software modalities.

No cross-addition collisions.  The composition correctness
is a single theorem: MTT canonicity applied to the
extended mode theory.  The theorem's proof is the Phase R2
deliverable (§8.4).


## 5. The Peripheries — What Stays Outside the Spine

Five peripheries are enumerated at commitment time.  Each
has a named interface to the spine.  The policy (§9)
forbids un-enumerated peripheries — a new feature must
justify itself as a modality (§4) or be added to this
enumeration via an RFC.

### 5.1 SMT dispatch

**What it is**: the Z3 / CVC5 / Bitwuzla oracle that
discharges refinement-type obligations, `pre` / `post` /
`decreases`, and `assert` statements.  Lives at
`leanx/FX/Smt/*.lean` and `leanx/FX/Elab/Verify.lean`.

**Why it's peripheral**: first-order decidable formulae
have no proof-term structure.  `sat`/`unsat`/`unknown` are
external judgements relative to the solver's own
consistency; no 2-cell of any mode theory can represent
this (`leanx/docs/smt-placement.md` §7 establishes the
detailed argument).

**Interface to the spine**: Ghost-mode proof obligations
dispatch outward to SMT at named dispatch sites (`assert P
by smt(...)`, implicit discharge of unproved
refinements).  The dispatch is the explicit interface; the
mode theory's Ghost mode does not absorb SMT.

**Trust impact**: SMT-discharged facts carry Oracle trust
level (≤ Verified).  `fxi --show-axioms` enumerates SMT
discharges separately from kernel axioms.  Release builds
gate on `--accept-smt` or signer attestation.

### 5.2 Codegen IRs

**What it is**: the FXCore / FXLow / FXAsm four-layer
pipeline per §20 of fx_design.md.  Lives at
`leanx/FX/CodeGen/*`.

**Why it's peripheral**: codegen is simulation, not type
theory.  Each IR has its own semantics; correctness of
code generation is a simulation proof (§20.7
`compiler_correct` theorem), not a typing rule.  Modalities
don't help with proving machine instruction semantics
against source semantics.

**Interface to the spine**: Ghost-mode semantics of source
→ Ghost-mode semantics of target, via explicit
refinement proofs (CompCert-style, `fx-refs/CompCert/`
template).  Each IR's soundness is proved in Ghost mode;
the proofs compose modularly.

**Trust impact**: each IR transition is a Ghost-mode
theorem.  `fxi --show-axioms` enumerates codegen-specific
axioms (emit-table for each target architecture) alongside
kernel axioms.

### 5.3 Agent-protocol daemon

**What it is**: the REST daemon per §24 of fx_design.md,
exposing structured diagnostics, proof state, and refactoring
operations to agent consumers.  Lives at `leanx/FX/Cli/*`.

**Why it's peripheral**: the daemon is a presentation
layer over the spine's computation.  It reads from the
spine's elaboration / checking / eval results; it does not
add new typing rules or new modalities.

**Interface to the spine**: consumes Verify-layer results
(kernel errors + SMT errors per Q50).  Produces structured
JSON per the ProofState schema (§10.7).  No kernel changes
are triggered by daemon operations.

**Trust impact**: the daemon is L3 untrusted.  A bug in the
daemon cannot affect kernel soundness; at worst it affects
agent legibility.

### 5.4 User-defined grade dimensions

**What it is**: the `grade_dimension` declaration (§6.6) for
user-declared domain-specific semirings (e.g.,
`MonotonicCounter`, `ApiBudget`).

**Why it's peripheral (extension point)**: the spine's
mode theory is fixed per reframe version.  User-declared
grades are a controlled extension mechanism that adds new
Software modalities without requiring a new mode theory
version.

**Interface to the spine**: each `grade_dimension` block
declares the modality's algebraic laws (semiring or
lattice).  The compiler verifies the laws via SMT (or by
user-supplied proofs for Verified trust).  Once verified,
the modality joins the user-scope's mode theory as a
Software endo-modality.

**Trust impact**: user modalities inherit the trust level
of their laws' verification.  Unverified laws =
`Assumed` trust = not release-gated by default.

### 5.5 Surface syntax and elaboration

**What it is**: the Phase 1 parser, lexer, AST, and
elaboration pipeline at `leanx/FX/Syntax/*` and
`leanx/FX/Elab/*`.

**Why it's peripheral**: the spine is the internal calculus
(the MTT instance).  Surface syntax is the programmer-
facing projection.  Surface changes (new keywords, new
declaration forms) do not require mode theory changes;
they compile down to existing spine constructs.

**Interface to the spine**: elaboration produces
mode-tagged kernel terms.  Every source construct lowers
to a specific MTT rule application in a specific mode.
The lowering per surface feature is documented in `fx_design.md`
§3–§26 and stays authoritative.

**Trust impact**: elaboration is L3 untrusted.  A
miscompilation at elaboration produces ill-typed spine
terms, which the spine rejects.  Soundness is preserved as
long as the spine's type checker is sound.

### 5.6 Policy for new peripheries

A sixth periphery would be added via RFC.  The RFC must:

  1. Justify why the feature cannot be expressed as a
     modality or as part of an existing periphery.
  2. Specify the interface to the spine (what data flows in
     and out, what trust level the outputs carry).
  3. Name the trust propagation rule (how `fxi --show-axioms`
     surfaces this periphery).
  4. Provide a mechanization plan if the periphery
     introduces new trust-propagating axioms.

The RFC process is lightweight but binding.  An
un-RFCed periphery is a policy violation caught by
`scripts/axiom-audit.sh`-style CI discipline (§9).


## 6. Current → Target Mapping

Per-feature correspondence between `fx_design.md`'s
current design and the reframe's target.  Every row is
actionable; the Roadmap (§8) is the scheduling of these
migrations.

### 6.1 §6 Grade system → mode theory modalities

| Current | Target | Change |
|---------|--------|--------|
| 21-dim product grade vector | 18 Software modalities + 1 Tier T + 1 Tier V at Wire + 2 frontier | semantic equivalence proved per dimension |
| `Grade.add` pointwise addition | 2-cell composition in the mode theory | derived operation |
| `Grade.mul` pointwise multiplication | 2-cell sequential composition | derived |
| `Grade.scale` | modality-scaled composition | derived |
| `Grade.divByUsage` (Wood-Atkey) | context-division law of the mode theory | proved valid in §3.8 |
| Tier class scaffolding (T1–T9) | collapses — no longer load-bearing | optional |

### 6.2 §9 Effect system → `◇_eff` specialization

| Current | Target | Change |
|---------|--------|--------|
| Effect row `{e₁, …, eₙ}` | `◇_eff A` with row parameter | syntactic rewrite |
| Effect lattice (§9.3) | 2-cells on `◇_eff` | direct mapping |
| `subsumes` edges (§9.5) | user-declared 2-cells | same semantics |
| `Fail(E)` unique per signature (E045) | 2-cell structure on `◇_eff` with row uniqueness | invariant preserved |
| Effect handlers (§9.6) | unchanged, wrapped around modal types | no semantic change |

### 6.3 §10 Refinement → Ghost mode + SMT periphery

| Current | Target | Change |
|---------|--------|--------|
| Refinement type `T { pred }` | Σ (x : T) (pred x) in Ghost mode | standard |
| `pre` / `post` / `decreases` | Ghost-mode obligations | same |
| SMT discharge | Periphery §5.1 | see `leanx/docs/smt-placement.md` |
| `sorry` | `Ghost.sorry` with Sorry trust | 2LTT-integrated |
| `axiom` | `Ghost.axiom` with Assumed trust | 2LTT-integrated |
| Refinement inference (§10.9) | elaboration in Ghost mode | no change |

### 6.4 §11 Sessions → linear modalities + Later + clocks

| Current | Target | Change |
|---------|--------|--------|
| Session type `S` | `channel<S, κ>` at Software with Protocol modality | reframed |
| `loopS` + `continueS` guardedness | Later modality with `fix` | big win |
| Gay-Hole sync subtyping (§11.19) | 2-cells on Protocol modality | derived |
| Precise async subtyping (§11.20) | 2-cells with Later-composition | composable |
| Crash-stop (§11.21) | Stop as a bottom state of Protocol modality | algebraic |
| Duality (§11.2) | involution on Protocol grade domain | preserved |
| CoindSpec translation (§11.24) | absorbed into Later elimination | derived |
| Multiparty association (§11.17) | mode-theoretic projection | mechanizable via smpst-sr-smer port |

### 6.5 §14 Contracts → Wire mode + modal univalence

| Current | Target | Change |
|---------|--------|--------|
| Contract `C for T` | `Wire`-mode type | mode lift |
| Format binding (§14.4) | `◇_format` modality | named |
| Validator / encoder / decoder | `serialize` / `parse` adjunction | algebraic |
| Version migration (§14.2) | modal univalence at Wire (§4.4) | transport |
| Compatibility matrix (§14.9) | 2-cells between Wire types | lattice |

### 6.6 §18 Hardware → Hardware mode + synth adjunction

| Current | Target | Change |
|---------|--------|--------|
| Synthesizable subset (§18.8) | Hardware mode with restricted modalities | algebraic |
| Clock domain tracking (§18.7) | `◇_clock` modality | same mechanism |
| `hardware module` | `Hardware`-mode module | semantic preservation |
| Pipeline (§18.11) | sequential composition via synth adjunction | preserved |
| Register file (§18.3) | `◇_repr` modality instances | preserved |
| Bisimulation (§18.12) | transport along equivalence at Hardware | proof cleaner |

### 6.7 §30 Kernel axioms: 33 → 12–15

Rough accounting of axiom reduction.  Every current axiom
either maps to an MTT primitive or becomes derived.

**Axioms that drop** (becoming derived from MTT canonicity
or mode theory structure):
  * Lam-form, Pi-form, Sigma-form (3) — standard MTT
    primitives, not FX-specific axioms
  * Ind-form, Ind-intro, Ind-elim, Ind-ι (4) — MTT
    inductive-type primitives
  * Id-form, Id-refl, Id-J (3) — MTT identity-type primitives
  * Quot-form, Quot-intro, Quot-lift (3) — subsumed by HIT
    primitive
  * Coind-form, Coind-intro, Coind-elim, Coind-ν (4) —
    subsumed by Later modality
  * Sub-* universe cumulativity (2) — standard MTT
  * Grade-* subsumption laws (several) — derived from 2-cell
    composition
  * Context-division law — part of MTT mode theory

Total dropping: ~22 axioms.

**Axioms that stay** (or gain as frontier additions):
  * MTT canonicity (1)
  * Mode theory's coherence (1)
  * Later `fix` operator axiom (1)
  * Bridge type B eliminator (1)
  * HIT general primitive (1)
  * Modal univalence axiom (1)
  * 2LTT mode-separation axiom (1)
  * Emit-table axiom per target architecture (~4, stays from §20.5)

Total staying / new: ~11 axioms.

**Net result**: 33 → ~11 axioms.  Target: ≤ 15 (acceptance
criterion §2.6.6).  The reduction is the single most
important quantitative gain of the reframe.


## 7. Gains Unlocked

### 7.1 Proof capabilities that become available inside FX

Under the reframe, several theorems that today are
**meta-theorems** (proven on paper, about FX) become
**internal theorems** (proven inside FX, cited by FX code):

  * **Noninterference**.  For any `f :
    ◇_{classified} A → ◇_{unclassified} B` that type-checks
    without declassify, the bridge modality B (§4.2) yields:
    `∀ a₁ a₂ : ◇_{classified} A. B a₁ a₂ → equal (f a₁) (f
    a₂)`.  This is a theorem provable inside FX by any
    agent who writes the proof term — or trivially by
    parametricity if `f` is polymorphic over classification.
  * **Linearity free theorem**.  `∀A. (A ⊸ A)` → `f` uses
    its argument exactly once.  Proved internally.
  * **Session subject reduction**.  The smpst-sr-smer
    16K-line Coq proof ports to FX's Ghost mode as a
    machine-checked theorem.  Agents can cite the proof
    term.
  * **Bisimulation via transport**.  Hardware ISA ↔ RTL
    bisimulation (§18.12) becomes a transport along modal
    univalence-witnessed equivalence.  The proof
    obligation is a single equivalence, not a manual
    simulation relation.
  * **Productivity of codata**.  `fix` construction
    witnesses productivity directly.  No separate
    guardedness lemma.
  * **Contract migration correctness**.  Transport along
    modal univalence witnesses gives migration correctness
    by computation.  No round-trip lemma discharge.

### 7.2 Elaboration expressivity gains

  * **Uniform dispatch**.  Every binder, every application,
    every pattern match dispatches to one MTT rule
    parameterized by mode.  Current elaborator's
    per-constructor `match` arms in `FX/Kernel/Typing.lean`
    collapse to mode-indexed generic rules.
  * **Mode-aware errors**.  An error at mode transition
    (Software → Hardware synth failure) carries the mode
    context automatically.  "This term has effect IO which
    is not in the Hardware mode's modality set" is a
    structured diagnostic, not a generic E44 error.
  * **Better type inference for polymorphic modalities**.
    Effect inference (E-2 task, already complete) becomes
    inference for the `◇_eff` modality's parameter.  Same
    machinery scales to modality-polymorphic functions
    (e.g., a generic log-wrapper that accepts any effect
    row).
  * **Composability of new grades**.  Adding a user-defined
    grade dimension (§6.6) is adding a Software endo-modality.
    Its interaction with existing modalities is
    automatically handled by the 2-cell algebra.  No
    per-dimension integration work.
  * **Performance**.  Mode dispatch is O(1).  Current
    21-dim product grade check is O(21).  20x elaboration
    speedup for grade-heavy code is plausible, though the
    constant factor of MTT is higher so net may be a
    wash.  Measure at Phase R1 completion.

### 7.3 Research-grade novelty

The reframe is a **POPL-caliber research contribution** in
its own right.  Nobody has put all of the following into a
single calculus:

  * 21-dimensional QTT (Atkey-Wood 2022)
  * Session types with crash-stop (BSYZ22, BHYZ23)
  * Multiparty subject reduction (Ekici-Kamegai-Yoshida
    ITP 2025)
  * Internal parametricity (Cavallo-Harper 2020,
    Agda `--bridges` POPL 2024)
  * Guarded recursion (Birkedal ecosystem 2012–2025)
  * Pfenning-Toninho linear corecursion
  * Modal univalence at wire boundaries
  * Hardware synthesis adjunctions
  * Enumerable trust via `fxi --show-axioms`
  * Agent-first design

FX's reframed calculus, once mechanized, is publishable as
a research contribution.  Independent of FX's practical
success, the calculus itself advances the state of the
art.


## 8. Roadmap

Two parallel tracks.  Track A continues current FX
development without interruption; Track B delivers the
reframe.

### 8.1 Track A — current trajectory (no change)

The session types S6–S25 roadmap continues.  Milestones
M2–M8 continue.  The current 21-grade encoding stays in
`leanx/FX/Kernel/**` through Phase R4.  User-facing
behavior is unchanged.

New tasks added to Track A during the reframe period are
designed for compatibility (§9 policy) — they do not
actively resist the reframe.  The session-type work S6
(Coind typing rules), for instance, introduces kernel
primitives whose design will accommodate the Later modality
addition.

### 8.2 Phase R0 — Mathematical formulation (4–6 weeks)

**Deliverables**:
  * This document (`fx_reframing.md`) — done when merged.
  * `fx_modecat.md` — formal mode theory specification.
    The 2-category with objects, 1-cells, 2-cells, laws.
    Proofs of §3.8 validity conditions.
  * Research note circulated for review (FX team internal
    + potentially external peer feedback).

**Success criterion**: the 2-category is written down
formally.  Validity proofs exist on paper.

**Budget**: 4–6 weeks of design work.  Heavily consumes one
person.

### 8.3 Phase R1 — MTT kernel scaffold (3–4 months)

**Deliverables**:
  * `leanx/FX/KernelMTT/` tree, separate from
    `leanx/FX/Kernel/`.
  * Port of BiSikkel's MTT core from Agda to Lean 4.  The
    `fx-refs/bisikkel/` clone is the template.  Applications/
    NonModal/ is the starting point.
  * Instantiation of the mode theory from Phase R0.
  * Conformance suite passing — every test in
    `tests/conformance/` produces the same accept/reject
    outcome under both kernels.

**Success criterion**: `fxi check --mtt program.fx`
accepts and rejects the same programs as `fxi check
program.fx`.

**Budget**: 3–4 months, requires one full-time
implementer.

### 8.4 Phase R2 — Frontier modalities (6 months)

**Deliverables**:
  * Later modality + multi-clocked extension (§4.1).
  * Bridge modality B (§4.2).
  * HITs for quotient (§4.3).
  * Modal univalence at Wire (§4.4).
  * 2LTT mode separation (§4.6).
  * Proof-of-concept: port Algehed-Bernardy noninterference
    (~40 lines) as internal FX theorem.
  * Proof-of-concept: port smpst-sr-smer subject reduction
    (16K lines of Coq) to Lean 4 inside FX's Ghost mode.

**Success criterion**: all five frontier modalities
compile and run on trivial examples.  The two proofs-of-
concept compile.

**Budget**: 6 months, one full-time implementer.

### 8.5 Phase R3 — Session types reframe (4 months)

**Deliverables**:
  * Session types rewritten to use Protocol modality + Later
    + clock quantification (§4.1.1).
  * Pfenning-Toninho linear corecursion integrated (§4.5).
  * S6–S25 session tasks re-targeted to the MTT kernel.
  * Session subject reduction + progress theorems as
    internal FX theorems (ported from smpst-sr-smer in
    Phase R2).

**Success criterion**: every session type currently
compiling under the old kernel compiles under MTT with
equivalent semantics.  The subject reduction theorem is
provable inside FX.

**Budget**: 4 months.

### 8.6 Phase R4 — Hardware + contracts reframe (3 months)

**Deliverables**:
  * Hardware mode with synth adjunction.  §18
    synthesizability rules derived, not asserted.
  * Wire mode with `serialize`/`parse` adjunction + modal
    univalence.  §14 contracts rewritten.
  * §18.12 hardware bisimulation as transport along
    equivalence.

**Success criterion**: hardware modules and contracts
compile under MTT kernel with same semantic behavior.

**Budget**: 3 months.

### 8.7 Phase R5 — Migration (3 months)

**Deliverables**:
  * Tooling to translate current `leanx/FX/Kernel/`-
    compiled programs to `leanx/FX/KernelMTT/`-compiled
    programs (trivial — the surface syntax does not change,
    only the kernel semantics).
  * Gradual switchover: default `fxi` invocation uses MTT
    kernel.  Legacy kernel accessible via `--legacy-kernel`
    flag.
  * Update `fx_design.md` to reference this document as
    theoretical foundation.
  * Update `AXIOMS.md` to reflect 33 → ≤ 15 reduction.
  * Deprecation policy: legacy kernel maintained for 12
    months post-R5, then removed.

**Success criterion**: the six acceptance criteria (§2.6)
are all met.

**Budget**: 3 months.

### 8.8 Total timeline

Phase R0: 4–6 weeks
Phase R1: 3–4 months
Phase R2: 6 months
Phase R3: 4 months
Phase R4: 3 months
Phase R5: 3 months

**Total: ~18–22 months** of Track B work, running in
parallel with Track A.

This assumes one full-time implementer on Track B.
Track A continues on its own pace; Track B does not
block it.

### 8.9 Task IDs for the tracker

The existing task tracker gains a new R-series:

  * R0 / §8.2 — Mathematical formulation
  * R1 / §8.3 — MTT kernel scaffold
  * R2a / §8.4 — Later modality
  * R2b / §8.4 — Bridge modality B
  * R2c / §8.4 — HITs
  * R2d / §8.4 — Modal univalence
  * R2e / §8.4 — 2LTT separation
  * R2f / §8.4 — Pfenning-Toninho adaptation
  * R2g / §8.4 — Port Algehed-Bernardy proof
  * R2h / §8.4 — Port smpst-sr-smer proof
  * R3 / §8.5 — Session types reframe
  * R4 / §8.6 — Hardware + contracts reframe
  * R5 / §8.7 — Migration

Thirteen R-series tasks.  Each task has explicit
success criteria tied to §2.6 acceptance.


## 9. Policy for New Decisions

Effective as of this document's merge.  Binding on every
kernel-level change during the migration (Phases R0–R5).

### 9.1 No new ad-hoc axioms

A new kernel axiom requires an RFC justifying why it
cannot be derived from MTT canonicity or from the mode
theory's structure.  Additions to `AXIOMS.md` that do not
meet this bar are blocked by the axiom-audit CI gate
extended per §9.6.

### 9.2 Every new kernel primitive must be modality-compatible

A new kernel primitive (new Term constructor, new typing
rule) must:

  1. Either correspond to an MTT modality or 2-cell, **or**
  2. Be explicitly peripheral and added to §5's
     enumeration via RFC.

The §5 enumeration is the full list of peripheries; a new
peripheral feature requires the enumeration to grow.

### 9.3 Frontier additions map to the mode theory

New features from the type-theory literature (guarded
recursion, internal parametricity, HITs, etc.) are
accommodated by adding modalities to the mode theory.  A
new modality requires:

  1. Specification in `fx_modecat.md` (or a supplement).
  2. Interaction rules with existing modalities (2-cells).
  3. Compatibility proof with MTT canonicity.

### 9.4 New peripheries require interface specs

A new periphery (sixth item beyond §5) requires:

  1. An RFC explaining why it cannot be expressed as a
     modality or absorbed into an existing periphery.
  2. An interface specification.
  3. A trust propagation rule (how `fxi --show-axioms`
     surfaces the new periphery's trust).
  4. A mechanization plan for any new axioms.

### 9.5 RFC process

Lightweight.  An RFC is a ~1-3 page markdown document in
`leanx/docs/rfcs/NNNN-title.md` (directory already
exists per current repo state).  Contents:

  * Summary of the change.
  * Justification per §9.1 / §9.2 / §9.3 / §9.4.
  * Interaction with existing modalities / peripheries.
  * Test plan / migration plan.
  * Sign-off from at least one reviewer.

Approval: commit the RFC as merged when the sign-off
happens.  Rejection: commit the RFC with a REJECTED
banner at the top for record.  Superseded: commit with
SUPERSEDED banner pointing to the successor RFC.

### 9.6 CI enforcement

The `scripts/axiom-audit.sh` script is extended to:

  1. Verify every axiom in `AXIOMS.md` has an RFC reference
     (post-Phase R0).
  2. Verify the 33-axiom allowlist has not grown without
     RFC justification.
  3. Post-Phase R5, verify the allowlist has shrunk to ≤ 15
     per §2.6.6.

Failure of any check blocks merge.


## 10. The Composition Pattern — "Slightly Heterogeneous Unified Algebra"

This section names the shape FX commits to, so future
decisions have a referent.

### 10.1 The metaphor — trunk plus branches

FX under the reframe is a **trunk** (the MTT spine) with a
small set of **branches** (the peripheries listed in §5).
The trunk carries the coherence theorem; branches have
interfaces to the trunk but their soundness stories are
local.  The tree metaphor captures:

  * A single unifying structure exists (the trunk).
  * Extensions attach at named places (the branches).
  * New growth requires either extending the trunk by a
    modality-compatible addition or adding a new branch
    via RFC.
  * Pruning — removing a periphery — is possible without
    affecting the trunk.

### 10.2 What counts as "unified"

A design satisfies the unified-algebra claim if:

  1. A **single coherence theorem** covers all trunk
     composition.  Today: MTT canonicity on the specific
     mode theory instance.  This replaces ten ad-hoc
     §6.8 rules with one coherence argument.
  2. Every periphery has a **well-typed interface** to the
     trunk.  Interfaces are documented; crossing them is
     explicit in both directions.
  3. **Enumerability** holds.  `fxi --show-axioms` surfaces
     trunk axioms and peripheral trust separately but
     together.  No hidden trust.

### 10.3 What does NOT count as unified (anti-patterns)

  * Ad-hoc extensions to the mode theory per new feature.
    If every new feature requires a new mode or new 2-cells
    outside the coherence theorem, the algebra is not
    unified — it's a veneer over ad-hoc growth.
  * Peripheral systems with unstated soundness obligations.
    A periphery without a clear interface is a silent trust
    escape.  Forbidden by §9.4.
  * Axiom growth without coherence justification.  An
    axiom that neither corresponds to a modality nor has
    an RFC is a breach of §9.1.
  * Implicit cross-periphery interactions.  Two peripheries
    must not communicate without going through the trunk.
    An SMT-to-codegen direct pipeline (bypassing the
    trunk) would be an anti-pattern.

### 10.4 Why this shape and not monolithic

A monolithic reframe — everything is an MTT modality —
would require:

  * SMT dispatch expressed as a "decidability modality" on
    Software types.  But sat/unsat/unknown is not a 2-cell;
    external oracle responses don't compose with typing
    rules.  Admitting this forces the mode theory to
    carry non-compositional structure, breaking coherence.
  * Codegen expressed as a modality from Software to a
    target-architecture mode.  But target-architecture
    semantics is simulation, not modality elimination.
    Admitting this adds complexity without explanatory power.
  * User-defined grades as first-class mode-theory extensions.
    But user code would then be able to affect the mode
    theory's coherence — a stability nightmare.

Each forced absorption weakens the algebra.  The
slightly-heterogeneous commitment avoids these costs.

### 10.5 Why this shape and not fully heterogeneous

A fully heterogeneous FX — six independent systems with
prose-level connections — is what FX has today.  The
diagnosis (§1) establishes why this is unsatisfactory:

  * The §6.8 collision catalog grows without principled
    bound.
  * Frontier additions have no natural home.
  * Composition is asserted, not derived.
  * Proof obligations are scattered.

The unified spine solves all four.  The peripheries
deliberately stay separate because they either cannot be
absorbed (SMT, codegen) or are controlled extension points
(user grades).

### 10.6 The trust story under this pattern

`fxi --show-axioms SYMBOL` surfaces two lists:

  1. **Kernel axioms** — transitive closure through spine
    modalities.  Bounded by the 12–15-axiom allowlist
    post-Phase R5.  Always trusted.
  2. **Peripheral trust** — enumerated per periphery:
     - SMT: list of SMT-discharged obligations with unsat
       cores as certificates.
     - Codegen: emit-table axioms per target architecture
       used.
     - User grades: user-supplied axioms for unverified
       laws.

Release gating can weight these differently.  A release
build requires:
  * Kernel axioms: always trusted (no override).
  * SMT discharges: require `--accept-smt` or signer
    attestation (§25.9).
  * Codegen: always trusted (small, audited emit tables).
  * User grades: require `--accept-user-axioms` for any
    `Assumed`-trust grade dimension.

This is the trust layering the slightly-heterogeneous
shape enables.  A fully monolithic design could not
distinguish these layers; a fully heterogeneous design
cannot enumerate them.


## 11. Risks and Alternatives

### 11.1 MTT mechanization cost

**Risk**: Porting BiSikkel from Agda to Lean 4 is
non-trivial.  The presheaf model uses sophisticated Agda
features (universe polymorphism, instance search) that
don't map cleanly to Lean 4's foundations.

**Mitigation**:
  * Start Phase R1 with BiSikkel's `Applications/NonModal/`
    (the simplest mode theory) as a sanity check.  If the
    port stalls there, the project redirects to a
    bespoke MTT kernel (more work) or pauses Track B.
  * Budget 3–4 months for Phase R1 explicitly accommodates
    slippage.

**Fallback**: If BiSikkel port stalls, the alternative is
writing the MTT kernel from scratch in Lean 4 using the
MTT POPL 2025 paper's rules directly.  Adds 2–3 months.

### 11.2 Loss of SMT-first ergonomics

**Risk**: Current FX's strong SMT integration (refinement
types discharged transparently) is a UX win.  Reframing
might make it feel harder to write refinement-heavy code.

**Mitigation**: SMT stays as a periphery (§5.1).  The
user-visible refinement typing does not change.  Only the
internal theory changes.  The `leanx/docs/smt-placement.md`
§7 argument extends here.

### 11.3 Alternative — stay heterogeneous, formalize each system separately

**What this would mean**: instead of unifying, formalize
each of the six systems (§1.1) as its own calculus with
explicit soundness proofs.  Keep the ad-hoc §6.8 collision
catalog but prove each rule as a theorem in the appropriate
calculus.

**Why rejected**: doesn't solve the §6.8 collision
problem.  It just makes the ten rules into ten theorems
rather than ten assertions.  Does not help with frontier
adoption (guarded recursion still has no home).  Does not
improve elaboration uniformity.

### 11.4 Alternative — adopt full HoTT / cubical type theory

**What this would mean**: base FX on Cubical Agda's
cubical type theory, with interval variables, Kan
composition, and full path-type computation.

**Why rejected**:
  * Cubical evaluation is roughly 2x kernel complexity.
  * SMT integration degrades (higher-homotopy-level proofs
    don't translate to SMT).
  * Agent legibility decreases.
  * Session types don't benefit from univalence.

**Targeted adoption instead**: the reframe adopts HITs
(§4.3) and modal univalence at Wire (§4.4) as targeted
MTT modalities, without full cubical.

### 11.5 Alternative — narrow FX to a specific subset

**What this would mean**: drop hardware, drop contracts,
keep grades + sessions.  Reframe only what remains.

**Why rejected**: abandons FX's distinguishing features.
The hardware synthesis + software-hardware unity is one of
FX's research contributions (§7.3).  Dropping it to
simplify the reframe would be addressing the wrong problem.

### 11.6 Alternative — hybrid: ad-hoc grade system plus MTT-based frontier additions

**What this would mean**: keep the current 21-grade
product system.  Add new modalities (Later, B, HITs) on top,
as a separate layer.

**Why rejected**: compounds the fragmentation.  The §6.8
collision problem stays.  New modalities would need to
interact with 21 grade dimensions via new hand-stated
rules.  The net is more, not less, heterogeneity.

### 11.7 Open risks with no mitigation yet

  * **MTT elaboration UX at scale**.  No language has
    deployed a 20-modality MTT instance.  BiSikkel's
    applications are small.  FX's conformance suite (~30
    programs) is the first real test; elaboration
    performance and error message quality under heavy
    modality usage are unknown.
  * **Agent / LLM readability of modality-heavy code**.
    FX's primary user is an agentic LLM.  Current LLMs
    handle Lean 4 reasonably; MTT-extended Lean 4 is
    outside training distribution.  Impact on agent
    effectiveness is unmeasured.
  * **Research-paper cost**.  Publishing the reframe as a
    research contribution requires paper writing (3–6
    months of writing / review cycle) on top of
    implementation.  Budget does not include this.

**Mitigation plan**: Phases R2 and R3 include formal
success criteria around elaboration correctness.
Phase R5 includes an LLM-driven conformance test battery
to measure agent effectiveness.  Paper writing is
explicitly out of scope for Phases R0–R5 but can be
scheduled post-R5.

### 11.8 Decision gates — when to stop

If a Phase misses its success criterion by > 50%, pause
and reassess:

  * **R0**: if the mode theory's validity proofs don't
    close on paper in 6 weeks, re-scope the mode
    theory (fewer modalities, simpler adjunctions).
  * **R1**: if the BiSikkel port stalls, either fall back
    to bespoke MTT (adds 3 months) or abandon Track B
    (keep current heterogeneous FX).
  * **R2**: if frontier modalities compose badly (coherence
    proofs fail), drop individual frontier additions
    rather than abandoning the whole reframe.
  * **R3-R5**: if session or hardware reframes reveal
    missing mode theory structure, patch the mode theory
    and restart R1 from the extension point.

The decision to abandon Track B is recoverable — current
FX stays functional and Track A continues.  Abandoning
Track B is not a catastrophic loss; it is a cost-benefit
decision point.


## 12. Decision Ledger

Load-bearing decisions in this document.  Each row is
citable as `§12.RN` where N is the row number (stable
once assigned).  Future revisions append rows; they do
not renumber or delete.

| Row | Decision | Rationale | Citation |
|-----|----------|-----------|----------|
| R1 | Commit to MTT as the algebraic spine | Unifies six stapled systems; proves composition as coherence theorem | §1.1, §2.1 |
| R2 | Slightly heterogeneous, not monolithic | SMT / codegen / tooling do not admit modality reading | §10.4, `leanx/docs/smt-placement.md` §7 |
| R3 | Four modes (Ghost, Software, Hardware, Wire) | Captures every current semantic distinction | §3.1 |
| R4 | 18+2 Software modalities | 15 Tier S + 2 Tier L + 1 Tier T Protocol + 2 frontier (Later, B) | §3.2, §4.1, §4.2 |
| R5 | Version modality lives at Wire, not Software | Version transitions happen at wire boundaries | §3.2.4 |
| R6 | §6.8 collisions become missing 2-cells | Derivable, not asserted | §3.6.2 |
| R7 | Adopt guarded recursion Later as a Software modality | Replaces syntactic guardedness; enables clocked sessions | §4.1 |
| R8 | Adopt bridge modality B for internal parametricity | Makes noninterference provable inside FX | §4.2 |
| R9 | Adopt HITs for quotient types only, not full HoTT | Subsumes three axioms; cubical complexity not justified | §4.3, §2.5 |
| R10 | Modal univalence at Wire boundary, not Software | Contract equivalence; avoids cubical cost | §4.4, §2.5 |
| R11 | Adopt Pfenning-Toninho corecursion via Later | Sessions productivity-guaranteed, no `Div` escape | §4.5 |
| R12 | Adopt 2LTT for Ghost/Software separation | Cleaner ghost/proof discipline than current grade | §4.6 |
| R13 | Peripheries: SMT, Codegen, Daemon, User Grades, Surface | Enumerable; RFC required for additions | §5 |
| R14 | SMT dispatch is first peripheral example | First application of §5 periphery discipline | §5.1, `leanx/docs/smt-placement.md` §7 |
| R15 | Axiom count target: ≤ 15 post-reframe | Acceptance criterion; ~22 drop, ~11 stay/new | §2.6.6, §6.7 |
| R16 | Track A (current) continues parallel to Track B (reframe) | No user-facing disruption; gradual migration | §8.1, §8.7 |
| R17 | Reframe timeline: 18–22 months of Track B work | Phases R0–R5 per §8 | §8.8 |
| R18 | RFC process for new axioms / modalities / peripheries | Enforce discipline during migration | §9.5 |
| R19 | Axiom-audit.sh extended to check RFC references | CI enforcement of policy | §9.6 |
| R20 | Composition pattern: trunk + enumerable branches | Names the shape for future decisions | §10.1 |
| R21 | Reject monolithic alternative | SMT / codegen / user-grades don't fit as modalities | §10.4 |
| R22 | Reject fully-heterogeneous alternative | §6.8 growth unbounded, frontier additions have no home | §10.5 |
| R23 | Reject full HoTT alternative | Cubical complexity cost too high | §11.4 |
| R24 | Reject narrow-subset alternative | Abandons distinguishing features | §11.5 |
| R25 | Reject hybrid (ad-hoc grades + MTT frontier) | Fragmentation compounds | §11.6 |

This ledger is the **acceptance artifact** for the
reframing commitment.  A kernel change or language
addition during the migration cites the applicable row
to show policy compliance; a change that conflicts with
a row requires a new RFC proposing a superseding row.

Future revisions to this document extend the ledger
(new rows) but do not renumber or delete existing rows.


## Appendix A: Glossary

Terms introduced by the reframe.  Definitions aligned
with the underlying literature (BiSikkel, MTT POPL
papers, Cubical Agda).

**2-category** — a mathematical structure with objects,
1-morphisms (1-cells) between objects, 2-morphisms
(2-cells) between 1-morphisms, and composition laws
satisfying coherence conditions.

**2-cell** — a morphism between two 1-cells.  In the
reframe, 2-cells encode subsumption between modalities
and the absence of certain compositions (collisions).

**Adjunction** — a pair of 1-cells `F : C → D`,
`G : D → C` with unit and counit natural transformations
satisfying triangle identities.  In the reframe, cross-
mode morphisms form adjunctions.

**Bridge modality (B)** — the modality that witnesses
internal parametricity.  `B a b` is the type of "bridges"
between values `a` and `b` of the same type.

**Coherence** — the property that different ways of
composing 2-cells agree up to equality.  The load-bearing
condition for MTT canonicity.

**Enumerable trust** — the property that a program's
transitive trust dependencies (axioms, oracle discharges,
peripheral contributions) are finite and printable.

**Guarded recursion / Later modality** — the type-theoretic
machinery for productive infinite structures.
`Later<A>` means "a value of A available next tick."
`fix : (LaterA → A) → A` gives productive fixed points.

**Heterogeneous system** — a system consisting of
distinct, non-uniform components.  FX today is
heterogeneous (six stapled systems).

**Higher Inductive Type (HIT)** — an inductive type
with path constructors as well as data constructors.
Subsumes quotient types in the reframe.

**Internal parametricity** — parametricity as a theorem
provable inside the type theory, not just a meta-theorem.
Delivered by the bridge modality B.

**Mode** — a 0-cell in the mode theory's 2-category.
FX's reframe has four modes: Ghost, Software, Hardware,
Wire.

**Modality** — a 1-cell in the mode theory's 2-category.
FX's reframe has 20+ modalities on Software plus cross-
mode morphisms.

**Mode theory** — the 2-category parameterizing an MTT
instance.  FX's mode theory is specified in `fx_modecat.md`
(forthcoming with Phase R0).

**Monolithic system** — a system with no component
boundaries; one unified structure.  Pure monolithic
type theories are rare; FX explicitly rejects full
monolithic (§10.4).

**MTT — Multimodal Dependent Type Theory** — the
framework of Gratzer-Kavvos-Nuyts-Birkedal LICS 2020,
normalization proved LICS 2022.  FX's reframe target.

**Peripheral (periphery)** — a component outside the
MTT spine with a named interface.  Enumerated in §5.

**Pfenning-Toninho corecursion** — linear-logic
foundation for coinductive session types guaranteeing
divergence-free observable behavior.

**Slightly heterogeneous unified algebra** — the
composition pattern FX commits to (§10).  One algebraic
spine plus enumerable peripheries.

**Spine** — the MTT-based algebraic trunk carrying the
coherence theorem.  Opposed to periphery.

**Track A / Track B** — parallel development paths.
Track A = current FX trajectory; Track B = reframe
migration.

**Transport** — the operation of moving a value along a
path / equivalence.  In HoTT / MTT with univalence,
transport preserves structure.

**Trunk + Branches** — the tree metaphor for §10's
composition pattern.

**Univalence** — the axiom that equivalent types are
equal.  FX adopts a modal variant restricted to the
Wire mode (§4.4).


## Appendix B: Worked Examples

### B.1 A classified computation under the reframe

Consider an FX function that encrypts a secret key and
sends it over a channel:

```
pub fn encrypt_and_send<a: type, r: region>(
  plaintext: buffer(u8) { length(plaintext) > 0 },
  secret ref(r) key: aes_key,
  ch: channel(send(encrypted: bytes); end),
) : unit with IO, Crypto, Async
  pre valid_key(key);
  post _ => channel_completed(ch);
= ...;
```

**Current FX**: seven grade dimensions fire at once —
Usage (linear buffer, borrow key, linear channel),
Security (classified key), Lifetime (region r), Effect
row IO+Crypto+Async, Refinement (length > 0, valid_key,
channel_completed), Protocol (channel session state).
The §6.8 collisions I002 (classified × Fail) and I004
(classified × async × session) both potentially fire;
the compiler checks them.

**Under the reframe**:
```
◇_{usage: own} buffer(u8) { length > 0 }                -- plaintext modality
◇_{usage: ref(r)} ◇_{sec: secret} aes_key                -- key modality
◇_{usage: own} ◇_{protocol: Send(bytes).End} channel     -- channel modality
→ ◇_{eff: {IO, Crypto, Async}} unit                       -- return modality
```

Type checking is one mode-theoretic coherence check.
Grade arithmetic is derived from 2-cell composition.
The two §6.8 collisions are encoded as absence of 2-cells
for `◇_{sec: secret} × ◇_{eff: Fail}` without a
`secret E` refinement — the compiler finds no coherent
cell and reports I002.  The absence is derived, not
catalog-checked.

### B.2 A session type with guarded recursion

A stream-reader session:
```
type stream_reader = session rec Loop;
  branch
    next => receive(item: T); Loop;
    done => end;
  end branch;
end session;
```

**Current FX**: session subtyping uses syntactic
guardedness.  `loopS` / `continueS` referenced via
lexical-scope binding.  Well-formedness checked
syntactically.

**Under the reframe**:
```
stream_reader κ :=
  ∀κ. channel<
    offer<
      Branch<"next", recv<T, Later<k> (stream_reader κ)>>,
      Branch<"done", end>
    >, κ
  >
```

The `Loop` binder is gone; recursion is via the Later modality
at clock κ.  `fix` gives the productive fixed point
directly.  Duality `dual(stream_reader κ)` is an
involution on the Protocol modality's grade domain,
derivable.  Gay-Hole subtyping (§11.19) is mechanical
2-cell synthesis on Protocol.

### B.3 A contract with migration as transport

Two API versions:
```
contract UserApi for UserRecord
  version 1 { id: nat; name: string };
  version 2 { id: nat; name: string; role: Role }
    migration add role default User;
end contract;
```

**Current FX**: migration is generated as a function
`migrate_v1_v2 : v1 → v2`, verified total.  Round-trip
compatibility is a separate proof.

**Under the reframe**:
  * `UserApi.v1` and `UserApi.v2` are types at `Wire`.
  * The migration is an **equivalence**
    `UserApi.v1 ≃ UserApi.v2` with default role computed
    by the `add role default User` clause.
  * Modal univalence at Wire gives `UserApi.v1 =
    UserApi.v2`.
  * Migrating a value: `transport migration_eq v`.
  * Transport computes — applying `transport` to a v1 value
    β-reduces to the v2 value with role = User.
  * Compatibility and round-trip are automatic from the
    equivalence's structure.

### B.4 Hardware-software bisimulation

An RTL pipeline verified against an ISA spec:
```
pipeline rv64 with Sync(clk, reset)
  stage fetch ... end stage;
  stage decode ... end stage;
  stage execute ... end stage;
  stage memory ... end stage;
  stage writeback ... end stage;
end pipeline;

refinement pipeline_correct
  spec = arch_state.step;
  impl = rv64_pipeline;
  via ...
end refinement;
```

**Current FX**: the refinement declaration triggers a
bisimulation proof.  Proof is manually specified; §18.12
bisimulation mechanism is structural but requires lots
of invariants.

**Under the reframe**:
  * `arch_state.step : Software` (ISA semantics in
    Software mode).
  * `rv64_pipeline : Hardware` (RTL in Hardware mode).
  * The synth adjunction `Software → Hardware` carries the
    abstract-to-concrete relationship.
  * Bisimulation becomes modal univalence between
    `observe(rv64_pipeline)` and `arch_state.step`.
  * Once the equivalence is established, transport along
    it preserves all properties automatically.

The proof's structure is one equivalence, not an
invariant chain.  The smpst-sr-smer ITP 2025 technique
(parameterized coinduction on infinite trees) is the
template.


## Appendix C: References and Correspondences

### C.1 Papers

  * **MTT foundational**: Gratzer, Kavvos, Nuyts,
    Birkedal, "Multimodal Dependent Type Theory."  LICS
    2020. https://dl.acm.org/doi/10.1145/3373718.3394736
  * **MTT normalization**: Gratzer, "Normalization for
    Multimodal Type Theory."  LICS 2022.
    https://dl.acm.org/doi/abs/10.1145/3531130.3532398
  * **BiSikkel**: Ceulemans, Nuyts, Devriese, "BiSikkel:
    A Multimode Logical Framework in Agda."  POPL 2025.
    https://dl.acm.org/doi/10.1145/3704844
  * **Löb modality**: Gratzer, "A Modal Deconstruction of
    Löb Induction."  POPL 2025.
  * **Probabilistic guarded**: Stassen, Møgelberg, Zwart,
    Aguirre, Birkedal, "Modelling Recursion and
    Probabilistic Choice in Guarded Type Theory."  POPL
    2025.
  * **Guarded recursion origin**: Nakano, "A Modality for
    Recursion."  LICS 2000.
  * **GDTT**: Birkedal, Møgelberg, Schwinghammer,
    Støvring, "First Steps in Synthetic Guarded Domain
    Theory."  Logical Methods in Computer Science 2012.
  * **Clock quantification**: Atkey, McBride, "Productive
    Coprogramming with Guarded Recursion."  ICFP 2013.
  * **Internal parametricity**: Bernardy, Moulin, "A
    Computational Interpretation of Parametricity."  LICS
    2012.
  * **Nuyts-Vezzosi-Devriese**: "Parametric Quantifiers
    for Dependent Type Theory."  ICFP 2017.
  * **Cubical Agda parametricity**: Cavallo, Harper,
    "Internal Parametricity for Cubical Type Theory."
    POPL 2020.
  * **Agda --bridges**: "Internal and Observational
    Parametricity for Cubical Agda."  POPL 2024.
  * **Noninterference from parametricity**: Algehed,
    Bernardy, "Simple Noninterference from Parametricity."
    ICFP 2019.
  * **HoTT Book**: Univalent Foundations Program,
    "Homotopy Type Theory," 2013.
  * **Cubical type theory**: Cohen, Coquand, Huber,
    Mörtberg, "Cubical Type Theory: A Constructive
    Interpretation of the Univalence Axiom."  TYPES 2015.
  * **Pfenning-Toninho**: "Corecursion in Session-Typed
    Processes."  CMU technical report.
  * **smpst-sr-smer**: Ekici, Kamegai, Yoshida.
    "Formalising Subject Reduction and Progress for
    Multiparty Session Processes."  ITP 2025.
  * **QTT**: Atkey, "The Syntax and Semantics of
    Quantitative Type Theory."  LICS 2018.
  * **Wood-Atkey Lam**: Wood, Atkey, "Graded Dependent
    Types via Semirings."  2022.
  * **Idris 2 QTT**: Brady, "Idris 2: Quantitative Type
    Theory in Practice."  ECOOP 2021.
  * **CompCert**: Leroy, "Formal Verification of a
    Realistic Compiler."  CACM 2009.
  * **Iris**: Jung, Krebbers, Birkedal et al., "Iris from
    the Ground Up: A Modular Foundation for Higher-Order
    Concurrent Separation Logic."  2018.

### C.2 fx-refs/ correspondence

Read-only reference clones at `~/Downloads/fx-refs/`
inform specific sections:

| Clone | Informs section | Role |
|-------|-----------------|------|
| bisikkel | §2, §3, §4, §8 | MTT mechanization template (port seed) |
| sikkel | §3 | Simpler MSTT warm-up |
| cubical | §4.3, §4.4 | HITs and univalence reference |
| agda | §4.2 | Internal parametricity implementation |
| Idris2 | §3.2, §6.1 | QTT grade handling at scale |
| granule | §5.4 | User-defined graded semirings |
| DynamicIFCTheoremsForFree | §4.2, §7.1 | Noninterference proof template |
| smpst-sr-smer | §4.5, §6.4, §7.1 | Session subject reduction port |
| iris | §5 | Concurrent separation logic periphery |
| liquidhaskell | §5.1 | SMT integration template |
| CompCert | §5.2 | Compiler correctness template |
| FStar | §11.2 | Alternative we diverge from |

### C.3 Further reading

  * `fx_design.md` — current canonical FX specification.
  * `leanx/docs/smt-placement.md` — Q50 decision doc, first
    peripheral instance of this commitment.
  * `leanx/docs/error-codes.md` — error code taxonomy
    cross-referenced throughout.
  * `AXIOMS.md` — current 33-axiom allowlist (target: ≤ 15).
  * `SPEC.md` — phase gating and trust discipline.
  * `fx_modecat.md` (forthcoming with Phase R0) — formal
    mode theory specification.
