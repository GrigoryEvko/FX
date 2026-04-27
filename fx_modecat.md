# FX Mode Category — Formal Specification

**Status**: skeleton landed at task R0.1 (2026-04-24).  Sections
1–8 are load-bearing and in force; §9 enumerates R2 frontier
additions that land progressively as R2a–R2h tasks close.  The
content in §1–§8 is AUTHORITATIVE for the R0 scaffold — this
document and the Lean files in `leanx/FX/KernelMTT/*.lean` must
stay in lockstep; conflicts are bugs.

**Version**: draft 1, reframe-version `R0.8` (tracks the last
completed R0 task).  Bump the version and append to the Decision
Ledger (§10) when the mode theory changes.

**Companion documents**:
  * `fx_design.md` — canonical language spec.  §6 (mode theory
    and modalities), §27 (kernel canonicity / metatheory), §30
    (kernel discipline) and Appendix H (axiom allowlist) are
    the conceptual precursor to this document; they fold in
    the content of the now-deleted `fx_reframing.md`
    (commit 4a5697ca).
  * `fx_grammar.md` — surface syntax (LALR(1) EBNF).
  * `fx_lexer.md` — tokenization.
  * `leanx/FX/KernelMTT/*.lean` — MECHANIZED definitions.  When
    the doc and the Lean code disagree, the Lean code wins and
    this doc needs a fix.

**Reading order**: §1 for status and discipline; §2–§6 as the
core mode-theory specification; §7 for the coherence laws the
Lean checker discharges; §8 for unit/counit 2-cell structure
(R0.8 delta); §9 for the R2 roadmap; §10 for the decision
ledger.

---

## 1. Status and Scope

### 1.1 What this document specifies

The FX **mode theory**: the finite 2-category whose 0-cells are
modes, 1-cells are modalities and cross-mode morphisms, and
2-cells are subsumption/coercion relationships.  Every decision
in the FX type system that was previously stated as an
independent convention (effect lattice, usage semiring, security
labels, trust propagation, clock domains, hardware
synthesizability, wire-format contracts) reduces to data in
this mode theory — either as a modality, a 2-cell, or a
missing 2-cell.

Per `fx_design.md §6` (which now folds in the reframing
content from the deleted `fx_reframing.md`), FX's type system is
an MTT instance parameterized at this mode theory.  The mode
theory is **fixed per reframe version**; extending it requires
an RFC and a version bump.

### 1.2 What this document does NOT specify

  * The MTT kernel's type-formation rules (see `fx_design.md`
    §6 / Appendix H).
  * User-level grade dimensions declared via `grade_dimension`
    (per `fx_design.md §6.6`) — these are peripheries that
    extend the modality namespace at user scope, but do NOT
    modify this document's enumeration.
  * The R2 frontier additions (Later, B, HITs, Wire univalence,
    2LTT) — those land progressively in `§9` as their R2a–R2h
    tasks close.

### 1.3 Authority

The Lean 4 modules in `leanx/FX/KernelMTT/*.lean` are the
MECHANIZED source of truth.  Every structural claim in §2–§8 has
a corresponding `theorem ... := by decide` (or a per-record
pinning lemma) in those files.  A drift between this doc and
the Lean code fails `lake build` at one of the coherence
theorems in `FX/KernelMTT/Coherence.lean`.

### 1.4 Trust layer

`FX/KernelMTT/**` is currently **UNTRUSTED scaffold** per
`leanx/FX/KernelMTT/CLAUDE.md`.  It runs in parallel with the
trusted `FX/Kernel/**` path until the Phase R1 acceptance gate
(task R1.14) closes.  After R5 migration (task R5.2), the MTT
tree becomes TRUSTED and the legacy kernel deprecates for 12
months before removal (per the kernel-discipline commitments
in `fx_design.md` §30).

### 1.5 How to update this document

Changes to the mode theory REQUIRE:

  1. An RFC for changes to the 4-mode enum or the 20-modality
     count (per the kernel-discipline / axiom-allowlist regime
     in `fx_design.md` §30 / Appendix H).
  2. A decision-ledger row (§10 below) stating the change and
     its rationale.
  3. Synchronized edits in the corresponding Lean files, with
     `lake build` and `lake build Tests` green.
  4. A reframe-version bump.

Ledger rows append only; prior rows stay on record even when
reversed.

---

## 2. Modes (0-cells)

**Count**: 4.  **Lean authority**: `FX/KernelMTT/Mode.lean`.

The 2-category's 0-cells are the four modes of FX.  A value's
mode answers the question "where does this value live at
runtime?" and determines which modalities apply.

| Mode       | Meaning                                              | Per-mode modalities |
| ---------- | ---------------------------------------------------- | ------------------- |
| `Ghost`    | Compile-time only; erased at runtime                 | 0                   |
| `Software` | General-purpose runtime values (heap, stack, CPU)    | 18                  |
| `Hardware` | Synthesizable circuit signals (combinational / sync) | 4                   |
| `Wire`     | Contract-encoded bytes on the wire                   | 2                   |

The per-mode modality count totals 24 entries across the
enumeration of 20 distinct `Modality` constructors (per R0.3):
the 4 Hardware modalities are a subset of the 18 Software
modalities (complexity, precision, repr, clock — same semantic
content, applicable at either mode), not independent entries.

Modes are pairwise DISTINCT.  Self-loops are forbidden at the
1-cell layer: every cross-mode morphism crosses modes (see §4).
Pinned in `Mode.lean` via `Mode.all.length = 4` and
`decEq : DecidableEq Mode`.

### 2.1 Mode config

Each mode carries a `ModeConfig` record of per-mode data:
admitted modality names, outgoing cross-mode morphism edges.
Pinned in `Mode.lean` via `Mode.config : Mode → ModeConfig`.

### 2.2 Cross-references

  * `fx_design.md §6` — conceptual introduction (folds in the
    former `fx_reframing.md §3.1`).
  * `fx_design.md §1.1` — the 21-dimension framing these modes
    partition.
  * `leanx/FX/KernelMTT/Mode.lean` — Lean definition + 10
    pinning theorems.

---

## 3. Modalities (endo-1-cells per mode)

**Count**: 20 distinct constructors; 24 per-mode admissions.
**Lean authority**: `FX/KernelMTT/Modality.lean`.

Modalities are mode-indexed endo-functors: a modality at mode
`M` takes a type at `M` and returns a type at `M` annotated
with additional structure (a grade, a state, a validity
predicate).  The 20 modalities partition into four `ModalityKind`
categories (per `fx_design.md §6.3` / former
`fx_reframing.md §3.2`):

  * **commutativeSemiring** — grade algebras closed under
    `+` and `*` (Atkey 2018 / Wood-Atkey 2022).
  * **latticeWithValidity** — preorders with optional
    refinement predicates (Tier L).
  * **typestate** — protocol-state machines (Tier T).
  * **wirePrimitive** — Wire-mode-only protocol encoding and
    versioning (Tier W).

### 3.1 Software modalities (18)

Pinned in `Modality.softwareModalityNames`:

| # | Name          | Kind                  | Source spec      |
| - | ------------- | --------------------- | ---------------- |
| 1 | `usage`       | commutativeSemiring   | §6.3 dim 3       |
| 2 | `eff`         | commutativeSemiring   | §6.3 dim 4       |
| 3 | `sec`         | commutativeSemiring   | §6.3 dim 5       |
| 4 | `lifetime`    | latticeWithValidity   | §6.3 dim 7       |
| 5 | `provenance`  | latticeWithValidity   | §6.3 dim 8       |
| 6 | `trust`       | commutativeSemiring   | §6.3 dim 9       |
| 7 | `repr`        | latticeWithValidity   | §6.3 dim 10      |
| 8 | `obs`         | commutativeSemiring   | §6.3 dim 11      |
| 9 | `clock`       | latticeWithValidity   | §6.3 dim 12      |
|10 | `complexity`  | commutativeSemiring   | §6.3 dim 13      |
|11 | `precision`   | commutativeSemiring   | §6.3 dim 14      |
|12 | `space`       | commutativeSemiring   | §6.3 dim 15      |
|13 | `overflow`    | commutativeSemiring   | §6.3 dim 16      |
|14 | `fporder`     | commutativeSemiring   | §6.3 dim 17      |
|15 | `mutation`    | commutativeSemiring   | §6.3 dim 18      |
|16 | `reentrancy`  | commutativeSemiring   | §6.3 dim 19      |
|17 | `size`        | commutativeSemiring   | §6.3 Size        |
|18 | `refinement`  | latticeWithValidity   | §6.3 dim 2       |

### 3.2 Hardware modalities (4)

The Hardware mode inherits a strict subset of Software
modalities — `clock`, `repr`, `precision`, `complexity` — in
the canonical filter order (not in spec-prose order).  Pinned
in `Mode.hardwareModalityNames` with a documented reorder
explaining the drift from the spec prose (per `fx_design.md`
§18.7 / former `fx_reframing.md §3.3`) to the canonical
filter order.

### 3.3 Wire modalities (2)

Wire-only modalities (per `fx_design.md §14` / former
`fx_reframing.md §3.4`):

  * `protocol` — typestate for session-type encoding
    (Tier T).
  * `format` — version modality for contract evolution
    (Tier V).
  * `version` — explicit version label (also Tier V).

The third entry (`version` distinct from `format`) lifts the
§6.3 Version dimension into a Wire-mode-only modality; the
count in `Modality.wireModalityNames` is 3 per R0.3 but
§3.4's prose only enumerates 2 primary Wire modalities plus
`version` as a derived tag.  Pinned with a per-name agreement
theorem in `Modality.wire_names_agree`.

### 3.4 Ghost modality count

`Ghost` admits **zero** modalities — every ghost value is
erased at runtime and carries no runtime structure.  Pinned
in `Mode.ghostModalityNames = []`.  The zero-count discipline
makes `Ghost` the terminal object in the mode-theory's
admissibility lattice.

### 3.5 Cross-references

  * `fx_design.md §6.3` — the 21-dimension semantics each
    modality lifts from (folds in the former
    `fx_reframing.md §3.2–§3.4` per-mode modality catalog).
  * `leanx/FX/KernelMTT/Modality.lean` — Lean definition + 12
    pinning theorems including agreement with `Mode.lean`.

---

## 4. Cross-mode adjunctions (1-cells across modes)

**Count**: 4 records, 6 directed edges.  **Lean authority**:
`FX/KernelMTT/Adjunction.lean`.

Per `fx_design.md §6` (formerly `fx_reframing.md §3.5`), four
adjunction records organize the cross-mode semantics.  Two are
PROPER (carry backward morphism + unit/counit 2-cells); two are
one-way or partial.

| §    | Record               | Left      | Right     | Forward     | Backward  | Proper |
| ---- | -------------------- | --------- | --------- | ----------- | --------- | ------ |
| 3.5.1 | `ghostSoftware`     | Ghost     | Software  | `ghost`     | `erase`   | yes    |
| 3.5.2 | `softwareHardware`  | Software  | Hardware  | `synth`     | —         | no     |
| 3.5.3 | `softwareWire`      | Software  | Wire      | `serialize` | `parse`   | yes    |
| 3.5.4 | `hardwareSoftware`  | Hardware  | Software  | `observe`   | —         | no     |

### 4.1 `ghost ⊣ erase` (§3.5.1)

Canonical 2LTT separation (per `fx_design.md §6` / former
`fx_reframing.md §4.6`).  Every
ghost value lifts to a zero-runtime-cost Software view (the
left-adjoint `ghost : Ghost → Software`); every Software value
has a canonical erase-to-Ghost view (the right-adjoint
`erase : Software → Ghost`).  Both total.

Unit: `eta_ghost : 1_Ghost → erase ∘ ghost`.
Counit: `epsilon_ghost : ghost ∘ erase → 1_Software`.

Triangle-identity shape (R0.8, mechanized at the endpoint
level):

  * Unit triangle endpoints: `(Ghost, Software, Ghost)`.
  * Counit triangle endpoints: `(Software, Ghost, Software)`.

### 4.2 `synth : Software → Hardware` (§3.5.2)

Partial morphism.  Defined on the Hardware-modality-compatible
subset of Software types (per §3.2 admissibility); undefined
(compile error) otherwise.  Carries `fx_design.md §18.8`
synthesizability rules.

**No right adjoint.**  Hardware values cannot be lifted into
Software without `observe` (§4.4), which is a separate one-way
morphism — NOT a backward half of `synth`.  No unit/counit.

### 4.3 `serialize ⊣ parse` (§3.5.3)

Adjunction mediated by a contract.  `serialize_C : Software →
Wire` encodes per contract `C`; `parse_C : Wire → Software`
decodes, potentially failing.

Unit: `eta_serialize : 1_Software → parse ∘ serialize`.
Counit: `epsilon_serialize : serialize ∘ parse → 1_Wire`.

The spec's §3.5.3 prose phrases the laws as "unit: serialize∘
parse = id_Wire" and "counit: parse∘serialize = id_Software".
Categorically the direction is reversed from standard
convention; we read the prose as a TRIANGLE-IDENTITY citation
and use standard unit/counit naming in the mechanization.
`fx_design.md §14.5`'s `C.decode` / `C.encode` pair instantiates
this adjunction per contract `C`.

Triangle-identity shape (R0.8):

  * Unit triangle endpoints: `(Software, Wire, Software)`.
  * Counit triangle endpoints: `(Wire, Software, Wire)`.

### 4.4 `observe : Hardware → Software` (§3.5.4)

One-way morphism.  A hardware signal reads into Software at a
specific clock cycle, producing a Software value tagged with
its clock domain via the `clock` modality.

**No inverse.**  Software cannot be injected into Hardware
without `synth`.  Not an adjunction with `synth` because
`synth` is partial.  No unit/counit.

### 4.5 Coherence commitments

Per `Adjunction.lean` (R0.4 + R0.8):

  * `total_count : all.length = 4`
  * `edge_count : allEdges.length = 6`
  * `proper_adj_has_backward` — isProperAdj iff backwardName
    is `some _`.
  * `proper_adj_has_unit_name` / `has_counit_name` — iff
    with isProperAdj.
  * `proper_adj_unit_triangle_shape` /
    `counit_triangle_shape` — triangle endpoints equal the
    expected round-trip triples.
  * `all_names_pinned` — 10 morphism + 2-cell names match a
    literal list in record order.

### 4.6 Cross-references

  * `fx_design.md §6` — conceptual introduction (folds in the
    former `fx_reframing.md §3.5`).
  * `fx_design.md §14.5` — contract `decode`/`encode`.
  * `fx_design.md §18.8` — synthesizability rules.
  * `leanx/FX/KernelMTT/Adjunction.lean` — Lean definition +
    30+ pinning theorems (including R0.8 unit/counit
    structure).

---

## 5. Subsumption 2-cells

**Count**: 27 cells across 11 modalities.  **Lean authority**:
`FX/KernelMTT/TwoCells.lean`.

Every subsumption rule in the current FX design lifts to a
2-cell in the mode theory.  A 2-cell `alpha : f ⇒ g` witnesses
that a value typeable under modality-grade `f` is also usable
where modality-grade `g` is expected.  At the enumerated-data
layer, a cell is a triple `(modality, fromGrade, toGrade)`.

### 5.1 Per-modality subsumption orders

Pinned in `SubsumptionCell.all`:

| Modality     | Cells | Example                                      |
| ------------ | ----- | -------------------------------------------- |
| `usage`      | 3     | `0 ≤ 1 ≤ w` (erased → linear → unrestricted) |
| `eff`        | 8     | `Tot ≤ Read ≤ Write`                         |
| `sec`        | 1     | `unclassified ≤ classified`                  |
| `obs`        | 1     | `opaque ≤ transparent`                       |
| `trust`      | 4     | `Verified ≤ Tested ≤ Sorry ≤ Assumed ≤ External` |
| `mutation`   | 3     | `immutable ≤ append_only ≤ monotonic ≤ read_write` |
| `overflow`   | 3     | `exact ≤ wrap`, `exact ≤ trap`, `exact ≤ saturate` |
| `fporder`    | 1     | `strict ≤ reassociate`                       |
| `reentrancy` | 1     | `non_reentrant ≤ reentrant`                  |
| `clock`      | 1     | `combinational ≤ sync(clk)`                  |
| `repr`       | 1     | `repr(Native) ≤ repr(C)`                     |

Every cell is WITHIN-MODALITY — no cross-modality 2-cells
exist in the enumeration.  See §6 for why this discipline
matters and how the §6.8 collision catalog interacts.

### 5.2 Reachability (transitive closure)

`SubsumptionCell.reachableFrom` implements fuel-bounded BFS
over the cell graph; `SubsumptionCell.subsumes m a b` returns
`true` iff there is a chain of cells at modality `m` from
grade `a` to grade `b`.  Reflexivity is immediate (the seed
inserts the source into `visited`); transitivity composes
through the BFS frontier.

Pinned by 21+ theorems in `TwoCells.lean`.

### 5.3 Overflow incomparability

Overflow's three non-exact grades — `wrap`, `trap`, `saturate`
— are PAIRWISE INCOMPARABLE (per `fx_design.md §6.3` dim 16).
Pinned in `Coherence.lean` as `overflow_wrap_trap_incomparable`
et al.: the reverse or sibling direction never `subsumes`.

### 5.4 Cross-references

  * `fx_design.md §6.2–§6.3` — dimension-by-dimension
    subsumption orders (folds in the former
    `fx_reframing.md §3.6.1` "subsumption as 2-cells" framing).
  * `leanx/FX/KernelMTT/TwoCells.lean` — Lean definition + 21
    pinning theorems.

---

## 6. Missing 2-cells (§6.8 collisions)

**Count**: 9 primary rules + 3 reductions.  **Lean authority**:
`FX/KernelMTT/Collisions.lean`.

Every `fx_design.md §6.8` collision rule (formerly framed in
`fx_reframing.md §3.6.2`) corresponds to the **non-existence**
of a coherent 2-cell
for a specific multi-modality composition.  Adding a 2-cell
admits the composition; adding a collision rule is a commitment
that the 2-cell does NOT exist.

### 6.1 Primary rules (9)

Pinned in `CollisionRule.all`:

| Code  | Name                          | Gap  | Refinement                          | Sources |
| ----- | ----------------------------- | ---- | ----------------------------------- | ------- |
| I002  | classified × Fail             | #102 | `declare 'Fail(secret E)'`          | 2       |
| L002  | borrow × Async                | #104 | (conditional refinement)            | 2       |
| E044  | CT × Async                    | #105 | UNCONDITIONAL                        | 2       |
| I003  | CT × Fail on secret           | #106 | (conditional)                       | 3       |
| M012  | monotonic × concurrent        | #108 | (conditional)                       | 3       |
| P002  | ghost × runtime conditional   | #109 | UNCONDITIONAL                        | 2       |
| I004  | classified × async × session  | #112 | (conditional)                       | 3       |
| N002  | decimal × overflow(wrap)      | #113 | (conditional)                       | 2       |
| L003  | borrow × unscoped spawn       | #114 | (conditional)                       | 2       |

Unconditional collisions (E044, P002) have `refinement = none`
— no refinement admits the composition.  Conditional
collisions (the other 7) have `refinement = some "..."` naming
the narrow admissibility refinement.

### 6.2 Reductions (3)

Per `fx_design.md §6.8` reductions are collisions that reduce
to combinations of primary rules; they don't carry independent
sources but are catalogued for diagnostic completeness.

| Gap  | Name                       |
| ---- | -------------------------- |
| #103 | session × Fail             |
| #111 | classified × linear × Fail |
| #110 | multiple Fail effects       |

### 6.3 Multi-modality framing

Every primary rule references 2 or 3 `sources` — the modality
grades whose simultaneous presence triggers the collision.
Pinned in `Coherence.collisions_have_multiple_sources` and
`Coherence.collisions_bounded_sources` (2 ≤ sources ≤ 3).

### 6.4 Cross-references

  * `fx_design.md §6.8` — primary collision catalog (folds in
    the former `fx_reframing.md §3.6.2` "collisions as missing
    2-cells" framing).
  * `leanx/FX/KernelMTT/Collisions.lean` — Lean definition + 14
    pinning theorems.

---

## 7. Coherence laws

**Lean authority**: `FX/KernelMTT/Coherence.lean`.

The mode theory's validity reduces to four machine-checkable
conditions (per `fx_design.md §27` / former
`fx_reframing.md §3.8`).  R0.7 discharges the
enumerated-data-layer obligations; R1's kernel scaffold picks
up the semantic obligations.

### 7.1 Enumeration closure

Every modality references only enumerated modes; every 2-cell
names an enumerated modality; every collision's error code
lives in the declared 9-entry primary list.  Pinned by
`modality_admissibility_closed`, `twocell_modalities_closed`,
`collision_codes_closed`.

### 7.2 2-cell invariants

**Within-modality**: every `SubsumptionCell` names a single
modality (`cells_are_within_modality`).

**Reflexivity**: every grade subsumes itself — the BFS seed
visits the source.

**Transitivity**: chains compose through `reachableFrom`.

**Anti-reflexivity on reverse chains**: for preorders that are
NOT total orders (e.g., effect preorder), the reverse direction
is absent.  Pinned per-modality in `Coherence.lean`.

**Overflow incomparability**: the three non-exact grades are
pairwise incomparable.

### 7.3 Adjunction correctness

Every adjunction crosses modes (`adjunctions_cross_modes`);
proper adjunctions carry backward names
(`proper_adj_implies_backward_some`); non-proper never do
(`non_proper_adj_implies_backward_none`); forward names are
pairwise distinct (`forward_names_distinct`); every adjunction
edge is in `Mode.config`'s morphism lists
(`adjunction_forwards_in_mode_config`).

### 7.4 Canonicity (deferred to R1)

Canonicity of the MTT instance follows from Gratzer LICS 2022
(per `fx_design.md §27` / former `fx_reframing.md §3.8.4`).
At R0 we only pin the
PRE-CONDITIONS (enumeration closure + within-modality
invariant); the actual canonicity theorem is an R1 obligation.

### 7.5 Aggregate witness

`Coherence.mode_theory_coherent` is a 9-conjunct witness
bundling the load-bearing coherence claims.  If any of
R0.2–R0.8's enumerated data drifts, this conjunction fails
`by decide` at `lake build FX.KernelMTT.Coherence`.

### 7.6 Cross-references

  * `fx_design.md §27` — validity of the mode theory (folds in
    the former `fx_reframing.md §3.8` framing).
  * `leanx/FX/KernelMTT/Coherence.lean` — Lean proofs + 40+
    theorems.

---

## 8. Unit/counit 2-cell structure (R0.8)

**Lean authority**: `FX/KernelMTT/Adjunction.lean` (R0.8 block)
and `FX/KernelMTT/Coherence.lean` (§R0.8 block).

Proper adjunctions carry two named 2-cells satisfying triangle
identities.  At R0 we can pin the NAMES and the mode-level
ENDPOINTS of each triangle on finite data; the triangle
EQUATIONS themselves are an R1+ obligation once kernel terms
exist.

### 8.1 For `ghost ⊣ erase`

  * Unit: `eta_ghost : 1_Ghost → erase ∘ ghost`.
  * Counit: `epsilon_ghost : ghost ∘ erase → 1_Software`.
  * Unit triangle endpoints: `(Ghost, Software, Ghost)`.
  * Counit triangle endpoints: `(Software, Ghost, Software)`.

Triangle identities (R1+):
  * `(epsilon_ghost · ghost) ∘ (ghost · eta_ghost) = 1_ghost`
  * `(erase · epsilon_ghost) ∘ (eta_ghost · erase) = 1_erase`

### 8.2 For `serialize ⊣ parse`

  * Unit: `eta_serialize : 1_Software → parse ∘ serialize`.
  * Counit: `epsilon_serialize : serialize ∘ parse → 1_Wire`.
  * Unit triangle endpoints: `(Software, Wire, Software)`.
  * Counit triangle endpoints: `(Wire, Software, Wire)`.

Triangle identities (R1+):
  * `(epsilon_serialize · serialize) ∘ (serialize · eta_serialize)
     = 1_serialize`
  * `(parse · epsilon_serialize) ∘ (eta_serialize · parse)
     = 1_parse`

### 8.3 Non-proper adjunctions

`synth` (§4.2) and `observe` (§4.4) carry NEITHER unit nor
counit.  `Adjunction.unitName` and `counitName` are both `none`;
`unitTriangleEndpoints?` and `counitTriangleEndpoints?` both
return `none`.  Pinned by `non_proper_has_no_unit` /
`non_proper_has_no_counit` / `non_proper_adj_no_triangles`.

### 8.4 Name uniqueness

The 6 mode-level morphism names (4 forward + 2 backward) and
the 4 unit/counit 2-cell names form a 10-element list pinned
as a literal equality in `Adjunction.all_names_pinned` and in
`Coherence.ten_name_shape`.

---

## 9. Frontier additions (R2 roadmap)

These modalities extend the mode theory in Phase R2.  They are
NOT part of the R0 scaffold.  Each bullet becomes its own
subsection once the corresponding R2a–R2h task closes.

### 9.1 `Later` Later modality (R2a)

Productive coinduction via guarded recursion (Nakano / Atkey-
McBride / Clouston).  `Later_κ A` = "an A available at the next
step of clock `κ`".  Replaces syntactic guardedness in
`Coind-ν` with typed elimination.

**Status**: skeletal.  Populates once R2a.1–R2a.6 close.

### 9.2 `B` Bridge modality (R2b)

Parametricity as a modality per Bernardy-Coquand-Moulin.
Enables free theorems: noninterference for classified data,
linearity for session types, send-once for channels.

**Status**: skeletal.  Populates once R2b.1–R2b.5 close.

### 9.3 Higher Inductive Types (R2c)

Drops the three Quot axioms (`Quot.mk`, `Quot.lift`, sound) by
expressing quotients as HITs with path constructors.

**Status**: skeletal.  Populates once R2c.1–R2c.4 close.

### 9.4 Modal univalence at Wire (R2d)

Wire-mode types with equivalent validators become
propositionally equal.  Contract migration becomes transport
along Wire equivalences.

**Status**: skeletal.  Populates once R2d.1–R2d.4 close.

### 9.5 2LTT mode-level separation (R2e)

Ghost ⊣ Software as a 2LTT separation rather than a grade
dimension.  Ghost erasure becomes a type-level reflection.

**Status**: skeletal.  Populates once R2e.1–R2e.4 close.

### 9.6 Linear corecursion (R2f)

Session types integrate with `Later` to drop the `with Div` escape
hatch.  Corecursion becomes productive-by-construction.

**Status**: skeletal.  Populates once R2f.1–R2f.3 close.

### 9.7 Noninterference via Bridge (R2g)

Algehed-Bernardy noninterference proof ported into FX applies
to the classified/unclassified separation.

**Status**: skeletal.  Populates once R2g.1–R2g.2 close.

### 9.8 Session subject reduction (R2h)

Coq → Lean 4 port of session subject reduction (smpst-sr-smer),
session progress, and association-invariant preservation
(HYK24 Thm 5.8).

**Status**: skeletal.  Populates once R2h.1–R2h.3 close.

---

## 10. Decision Ledger

Append-only record of mode-theory changes.  Rows stay on record
even when superseded (same discipline as
`leanx/docs/smt-placement.md §11`).

| Row | Date       | Change                                                                 | Reframe version | Rationale |
| --- | ---------- | ---------------------------------------------------------------------- | --------------- | --------- |
| L1  | 2026-04-24 | Initial R0 scaffold: 4 modes, 20 modalities, 4 adjunctions, 27 2-cells, 9+3 collisions, unit/counit 2-cells for 2 proper adjunctions. | R0.8            | Close Phase R0 (kernel-discipline commitments per `fx_design.md` §30 / Appendix H); baseline for R1 kernel work. |
| L2  | 2026-04-24 | R1.1 aggregator lands: `leanx/FX/KernelMTT.lean` re-exports the 6 scaffold submodules; `scaffoldVersion = "R1.1"` + 9-entry `closedRTasks` ledger.  Test module `Tests.KernelMTT.AggregatorTests` pins the version tag and the exact closed-task list. | R1.1            | Provide a single-import surface for R1.2+ downstream files.  Machine-checkable completion state via the Lean version tag means an agent inspecting the scaffold sees structural progress, not just file listings. |

Future rows append below.

---

## 11. Cross-reference index

### 11.1 Lean source files

| File                                    | Purpose                                     | R-task    |
| --------------------------------------- | ------------------------------------------- | --------- |
| `leanx/FX/KernelMTT/Mode.lean`          | 4 modes + per-mode config + morphism lists  | R0.2      |
| `leanx/FX/KernelMTT/Modality.lean`      | 20 modalities + admissibility               | R0.3      |
| `leanx/FX/KernelMTT/Adjunction.lean`    | 4 adjunction records + R0.8 unit/counit     | R0.4, R0.8 |
| `leanx/FX/KernelMTT/TwoCells.lean`      | 27 subsumption 2-cells + reachability       | R0.5      |
| `leanx/FX/KernelMTT/Collisions.lean`    | 9 primary rules + 3 reductions              | R0.6      |
| `leanx/FX/KernelMTT/Coherence.lean`     | 40+ coherence theorems                      | R0.7, R0.8 |
| `leanx/FX/KernelMTT/CLAUDE.md`          | Module-local trust-layer notes              | R0.2      |

### 11.2 Test files

| File                                                  | Purpose                   |
| ----------------------------------------------------- | ------------------------- |
| `leanx/tests/Tests/KernelMTT/ModeTests.lean`          | R0.2 compile-time tests   |
| `leanx/tests/Tests/KernelMTT/ModalityTests.lean`      | R0.3 compile-time tests   |
| `leanx/tests/Tests/KernelMTT/AdjunctionTests.lean`    | R0.4 + R0.8 tests         |
| `leanx/tests/Tests/KernelMTT/TwoCellsTests.lean`      | R0.5 compile-time tests   |
| `leanx/tests/Tests/KernelMTT/CollisionsTests.lean`    | R0.6 compile-time tests   |
| `leanx/tests/Tests/KernelMTT/CoherenceTests.lean`     | R0.7 + R0.8 tests         |

### 11.3 Companion spec sections

`fx_reframing.md` was deleted in commit 4a5697ca; its content
folded into `fx_design.md` (chiefly §6 / §27 / §30 / Appendix
H).  The mapping below records both the live `fx_design.md`
anchor and the legacy `fx_reframing.md` section (for readers
auditing pre-merge artifacts).

| Concern            | This doc | Legacy `fx_reframing.md` | `fx_design.md`    |
| ------------------ | -------- | ------------------------ | ----------------- |
| Modes              | §2       | §3.1                     | §1.1, §6          |
| Software modalities | §3.1    | §3.2                     | §6.3              |
| Hardware modalities | §3.2    | §3.3                     | §18.7             |
| Wire modalities    | §3.3     | §3.4                     | §14               |
| Adjunctions        | §4       | §3.5                     | §6, §14.5, §18.8  |
| Subsumption 2-cells | §5      | §3.6.1                   | §6.2–§6.3         |
| Collisions         | §6       | §3.6.2                   | §6.8              |
| Coherence          | §7       | §3.8                     | §27               |
| Unit/counit        | §8       | §3.5.1, §3.5.3           | §6                |
| R2 frontier        | §9       | §4, §8 roadmap           | §30 / Appendix H  |

---

*End of fx_modecat.md.*
