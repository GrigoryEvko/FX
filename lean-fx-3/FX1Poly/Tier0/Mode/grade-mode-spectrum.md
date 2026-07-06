# The Grade↔Mode Spectrum — a runged categorical design

> **TL;DR.** Every "grade," "mode," "stratification," "level," and "dimension"
> in the FX kernel is a *position on one categorification ladder*. This document
> defines that ladder, runs it down all four ω-axes (term / type / context /
> mode), pins where the fibrancy trinity (φ / δ / ℓ) actually sits, and shows the
> ladder **describes itself** (a grade is the decategorification of a mode). It
> settles three standing design questions: why fibrancy is *one mode property*
> (`Tier0/Mode/FibrancyMode`), not a standalone axis; why the mode axis is "the
> grade of grades"; and the φ→ℓ→δ build order.
>
> Home: this lives under `Tier0/Mode/` because the **mode axis is the classifier
> of all grading structures** — see §7. It is design prose, not a proof
> obligation; the Lean realizations it points at are tracked tasks (mapped in §7).

---

## 0. The one question this answers

Across the kernel we kept conflating *grade* (a usage/effect/cost quantity on a
binding) with *mode* (a place in a mode 2-category, à la MTT/MATT). They are
neither the same nor unrelated: **they are two heights on a single ladder, and
the rung is a measurable property of one structure 𝓜.** Naming the rungs is what
stops the confusion from recurring.

A grading is *a structure 𝓜 that the type theory is indexed / fibred over*; every
judgment carries a **position in 𝓜**. The single parameter sweeping the spectrum
is **the categorical richness of 𝓜**, which factors as
`(number of objects) × (algebra on 1-cells) × (categorical dimension)`.

---

## 1. The spectrum (the ladder)

```
┌──────┬────────────────────────────────────────────────────┬──────────────────────────────┬───────────────────────────────────────────┐
│ rung │                         𝓜                          │     what a "position" is     │                   name                    │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R1   │ a poset / join-lattice                             │ a point in an order          │ lattice grade (security, effect-join)     │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R2   │ one object, 1-cells = semiring (+,·)               │ an endo-1-cell "how much"    │ grade proper (usage, cost — QTT)          │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R3   │ one object, 1-cells = monoidal category (2-cells!) │ a graded modality !ᵣ         │ graded modality (bounded LL)              │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R4   │ many objects, 1-cells between them, sparse 2-cells │ a 0-cell "which place"       │ few-object mode (2LTT f/e, polarity, LNL) │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R5   │ many objects, rich 1- and 2-cells, adjoint strings │ a mode + its modalities      │ mode proper (MTT/MATT)                    │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R6   │ weak ω-category                                    │ a mode with higher coherence │ ω-mode (mode-21)                          │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R7   │ 𝓜 = the type theory itself                         │ self-indexing                │ doctrine / bootstrap (mode-17)            │
└──────┴────────────────────────────────────────────────────┴──────────────────────────────┴───────────────────────────────────────────┘
```

The grade/mode distinction is now a **theorem about 𝓜**, not a vibe:

- a **GRADE** is a *1-cell of a one-object 𝓜* (R1–R3) — "how much."
- a **MODE** is a *0-cell of a many-object 𝓜* (R4–R7) — "which place."
- the crossover is exactly **R3 → R4: one object becomes many.** That single
  step *is* grade → mode. Everything below it is quantity; everything above is
  place.

The increasing parameter, rung by rung: R1 orders the 1-cells; R2 gives them a
second binary op (a semiring); R3 adds genuine 2-cells (the grades become a
*category*); R4 splits the single object into many; R5 enriches the inter-object
1-/2-cells (adjoint strings); R6 climbs to ω; R7 lets 𝓜 *be* the theory it grades.

---

## 2. Two axes orthogonal to the rung

The rung is not the whole story. Two further dials run *perpendicular* to it, and
the kernel must track them independently.

### 2.1 beneath ↔ alongside (this is `mode-26`)

The same grading can be **presented** two ways:

- **beneath** — annotate the *judgment*: `x :ᵣ A`, grade-arithmetic in the rules.
  (FX's §6 grade vector / `HasGradeOver R`.)
- **alongside** — promote the grade to a *base* 𝓜 with locks `◐_μ`, and the
  graded modality `!ᵣ` becomes an MTT modality. (The mode axis / `ModalityPath`.)

A static semiring R **is** a one-object 2-category B_R, so for static grades the
two presentations coincide — this is precisely the `mode-26` "alongside-vs-beneath
boundary." FX currently runs *both at once*: the §6 grade vector (beneath) and the
mode axis (alongside). Unifying them is the goal of `FRONTIER-GRADED-EVERYTHING`
(#1872).

### 2.2 static ↔ value-dependent (the one genuine break)

A **value-dependent** grade — where the grade is a *term* (FX §6.7,
`take_n<a>(n, xs) pre n ≤ length(xs)`) — **cannot** be a static 𝓜: a mode theory's
1-cells are fixed, they cannot depend on a runtime value. So dependent grades are
**stuck beneath**, off the categorification ladder. This is the *only* place
`mode ≡ grade` fails for a reason deeper than presentation, and it is the one part
of the 4×7 grid (§3) that will **not** collapse under #1872.

Consequence for the cost dimension: cost `O(n)` is value-dependent, so the cost
grade MUST split into a static asymptotic-class shadow (modality-able; COPT-7 /
CLEX) and a value-dependent index (PolyBound, COST-7 — beneath forever). Any
"cost as a mode/fibration" construction (`BRIDGE-COST-FIBRATION` #1859) can only
fiber over the static shadow — fibering the full cost function is exactly the
category error this subsection rules out.

---

## 3. The 4×7 grid — the spectrum down each axis

Each of the four ω-axes carries the *whole* ladder. The kernel is a scatter of
filled cells across a `(4 axes) × (7 rungs)` grid; most cells are already shipped.

### TERM
- **R1** Böhm / definedness order (`term-13`); the cost order.
- **R2** usage / linearity (§6 vector); the **SN / proof-theoretic ordinal**
  (an ordinal semiring under max,+).
- **R3** `!ᵣ` bounded reuse (`mode-22`, `mode-26`).
- **R4** value/computation **polarity** (CBPV); strict vs fibrant term layers.
- **R5** FitchTT-**lock** terms — crisp/flat under `Γ/μ` (the A1 work).
- **R6** the **term polygraph itself** (`term-5`, `term-17`): terms as cells of
  the term ω-category.
- **R7** terms reflecting the kernel (the bootstrap).

### TYPE
- **R1** cumulativity / subtyping (`type-18`); the truncation order.
- **R2** universe level **ℓ** (max/succ); dimension **δ** as a number (truncation ℕ).
- **R3** the truncation modality `‖-‖ₙ`; Rijke–Shulman reflective subuniverses
  (`type-10`); cohesion (`type-11`).
- **R4** **fibrancy f/e** (2LTT, `type-22`); Prop/Type proof-relevance
  (`type-19`, `type-26`).
- **R5** cohesion / transpension type-formers `♭ ♯ ʃ`, Gel/Glue (`type-11`,
  `type-12`).
- **R6** the type ω-category (`type-21`).
- **R7** the universe reflecting itself.

### CONTEXT
- **R1** sub-context / weakening order.
- **R2** the graded context (QTT resource-vector).
- **R3** coeffect graded comonad.
- **R4** modal contexts at distinct modes (MTT).
- **R5** the **lock `Γ/μ`** (`context-4`; the A1 `lockCons`).
- **R6** the (∞,ω) context category (`context-36`).
- **R7** the context-of-contexts classifier (`context-38`).

### MODE — the special column
The mode axis is **where 𝓜 itself lives**; its own ladder is `mode-1 … mode-21`
(R5/R6) plus the `mode-17` 2-monad doctrine (R7). But its real role is *meta*: it
**classifies which rung any grading sits at** (the `mode-2`/`mode-12`
structure-class certificate). The mode axis is therefore not just a fourth column
— it is the **grade of grades** (see §7).

---

## 4. The sharpening: φ, δ, ℓ live at DIFFERENT rungs

The "trinity" `𝒰[ℓ, φ, δ]` is **not three peers at three addresses.** They sit at
three *different heights*:

| grade | rung | because |
|-------|------|---------|
| **ℓ** size / level | **R1–R2** | cumulativity is a lattice; level arithmetic (max/succ) is a semiring. Low. |
| **δ** depth | **R3** | the n-truncation `‖-‖ₙ` is a *graded modality*. Middle. |
| **φ** fibrancy | **R4** | f / e are genuine *many-object modes* (2LTT). High. |

This is *why* the architecture diverges by member: **ℓ** is just `LevelExpr`; **δ**
is the cell-number / truncation modality; **φ** is the one that has crossed R3 → R4
into mode-land, so it lives as a *mode property* (`Tier0/Mode/FibrancyMode`, §7).

---

## 5. The fibrancy column (R4) — the universal higher-cell classifier

φ at R4 is not type-specific. "Fibrancy" is the universal question *"what
structure do the ≥1-cells of an ω-category carry?"* — and the four answers run
identically down all four axes:

| φ-value     | TERM                 | TYPE                  | CONTEXT             | MODE              |
|-------------|----------------------|-----------------------|---------------------|-------------------|
| **strict**     | syntactic / α-eq     | UIP / exotype         | raw context         | strict 2-cat      |
| **groupoidal** | **Conv**             | **Path** (univalence) | univalent context   | modal equivalence |
| **directed**   | **Step**             | **Hom** (directed)    | directed context    | adjoint string    |
| **relational** | reducibility / LR    | **Bridge** (param.)   | sconing / gluing    | Galois / profunctor |

2LTT's f/e is just the *type-axis, strict-vs-groupoidal* shadow of this. The whole
kernel's SN/CR/decidable-Conv heart **is** the term column (Step ⟶ Conv ⟶
reducibility). Most cells are shipped (`type-7`, `type-9`, `context-11/30/31/34`,
`mode-1..27`); the conspicuous gap is the type-axis *directed* cell (`type-24`).

### The wider grade families
φ/δ/ℓ are three threads of a six-family frontier inventory, distinguished by what
the grading structure R *is*:

| family | R is… | members |
|--------|-------|---------|
| **Geometric** | a shape / site | φ, variance/polarity, arity (degrees-of-relatedness), multi-circle (path×bridge×directed×clock), motivic/chromatic |
| **Size** | an ordinal / cardinal | ℓ, κ-accessibility, large-cardinal/reflection, the proof-theoretic ordinal |
| **Depth** | ℕ∪{ω} / ℤ | δ, truncation, connectivity, suspension/stabilization |
| **Resource** | a semiring | usage, effect, cost, precision, space, security-flow, separation |
| **Modal** | a modality lattice | reflective subuniverses, cohesion ♭♯ʃ, localization, guarded/clock, phase, observability |
| **Epistemic** | a strength lattice | trust/provenance, proof-relevance (SProp/Prop/Type), decidability/arithmetic-hierarchy, realizability |

FX's 21 dimensions span **Resource + Modal + Epistemic** almost entirely; the φ/ℓ/δ
trinity adds the **Geometric + Size + Depth** *identity/coherence* grades the 21
lack. They are not redundant: the 21 grade *runtime/resource*; the trinity grades
*identity*.

### Worked cross-section: the quotient grade (2026-07-02)

"Quotient" is a position in a product of grades this document already names:
**(§2.1 beneath↔alongside) × (δ truncation) × (decidability, Epistemic family)**.
Setoid = the congruence carried *beneath* (judgment side-conditions); definable
quotient = promoted *alongside* with a computable section — the §2.1 static-
crossing condition instantiated at equality (decidable normal form); observational
quotient = `Id` computes to a prop (δ = −1 content); classifying type =
proof-relevant identifications (δ ≥ 1). The collapse **set quotient =
π₀(classifying quotient)** is the §6 seam (`grade = π₀(mode)`, CSHD-5) applied to
quotients — the quotient ladder *embeds in the R-ladder*. Along it, computation
and information run in opposite orders (a Pareto pair). Realization: EXT-2/3/6/7
rows + a QUOT admission table (deny-by-default; the tier rides as a grade).

### A Resource-family addendum: usage measures ambidexterity (conjecture X7)

Height-1 semiadditivity (norm maps invert over π-finite classifiers) holds
exactly where duplication is free — so the usage semiring `{0, 1, ω}` measures
the *failure of ambidexterity*, with linearity as the height-(−1) obstruction.
This gives the Resource family a Geometric-family shadow ("chromatic height of a
resource discipline") and ties the R2 usage row to the CSHD cardinality arc
(groupoid cardinality exists ⟺ 1-semiadditive over ℚ).

---

## 6. The self-application — the ladder describes itself

The spectrum is itself a structure, so we can ask its own rung.

1. The rungs are **ordered** (R1 ≤ … ≤ R7) — so the spectrum is *at least* a poset:
   **R1 of itself.**
2. But the rungs are connected by *functors*: **categorify** (free, up:
   semiring ↦ its one-object 2-category; mode theory ↦ its ω-completion) and
   **decategorify** (forgetful, down: a mode's 1-cells shadowed to a semiring;
   `π₀` of a category; the cardinality of a groupoid). These are **adjoint**:
   `categorify ⊣ decategorify`. Hence:

   > **A grade is the decategorification of a mode; a mode is the categorification
   > of a grade.** `grade = π₀(mode)`, `mode = the category whose shadow is the
   > grade`.

   This is exactly `CSHD-5` (#1483) — *"a number is the shadow of a category"* —
   now recognized as the structure of the grade↔mode seam itself.
3. With rungs as objects and `categorify ⊣ decategorify` as adjoint 1-cells, the
   spectrum is a **rich adjoint-string 2-category: R5 of itself.** Climbing it is
   the very operation that defines it.
4. **The fixpoint.** At R7, `𝓜 = the type theory`; the kernel's *own mode axis is a
   point on the spectrum*, while the kernel *as a whole is a point on the
   spectrum*. "Apply the spectrum to itself" has a self-consistent solution: the
   kernel grading itself by the ladder it lives on. That fixpoint is
   `THE-ONE-OBJECT` (#1591) / the reflective bootstrap `FRONTIER-SELF-FORMALIZE`
   (#1874), and `FRONTIER-GRADED-EVERYTHING` (#1872) is the statement that the 4×7
   grid collapses to *one* product-graded object whose grading structure is itself
   a grid-point. Sharpening (conjecture X3, 2026-07-02): the fixpoint is a
   *terminal coalgebra* of `categorify` — `𝓜∞ ≅ categorify(𝓜∞)` — and the
   reflective bootstrap (#1874) is coinduction on it; fib-13 becomes a universal
   property with a uniqueness obligation rather than a slogan.

---

## 7. Architectural consequences (what this settles)

1. **Naming, fixed.** Reserve **"grade"** for R1–R3 (beneath, semirings —
   `LevelExpr`, the §6 vector, the δ-truncation). Reserve **"mode"** for R4+ (the
   mode axis, φ/f-e, the locks). The seam between them is *decategorification*. Use
   the words this way in code and docs; it is the whole point of this file.

2. **Fibrancy is one mode property.** φ is a *mode* (R4) and lives in the mode axis
   as `Tier0/Mode/FibrancyMode.lean` (the 2LTT f/e presentation, the MATT predicate
   classes, the non-sharp ι; mode-13). It is **not** promoted to a standalone
   cross-axis classifier: the earlier `Tier0/Fibrancy/` proposal is dropped —
   fibrancy is just one property of the mode axis, not a separate folder every axis
   imports. Any per-axis reading of "what structure the ≥1-cells carry" reads the
   fibrancy kind off that mode property; "fibred over mode" is a Core/Fib gluing
   statement.

3. **The mode axis is the grade-of-grades.** There is **no fifth ω-category axis
   for grades.** Every grading structure — one-object semirings, multi-object
   stratifications, rich modalities — is a mode-2-category, and the mode axis (via
   `mode-2`/`mode-12`) classifies *which rung* each one occupies.
   Operational since 2026-07-02: the carrier (`ModeGraph`/`ModalityPath`/
   `ModeSignature`) lives in `Polygraph/Computad/Signature.lean` and the judgment
   is indexed by `ModalityPath` (fib-3d) — the mode theory is *swappable data*.
   Two instances already exist in-tree: the affine signature (the A1 arc) and
   `fibrancyModeSignature` (2LTT f/e). fib-3 at those two points = one fibration,
   two mode theories — the classifier role made executable.

4. **Build order φ → ℓ → δ, with a causal spine.** On every axis: the **strict
   (exo) φ** is the rigid/decidable *substrate* → **ℓ** (size/reflection strength)
   can only be *measured over* a strict reduction/identity → **δ** (full coherence)
   is the *telos*. Exo-strictness *causally enables* the reflecting tower
   (decidable syntactic equality before ordinal analysis; strict universe codes
   before reflecting operators; the strict 2-cat before the GLP modalities). So the
   2LTT (φ) work is the foundation; the ordinal/ω-level tower (ℓ) is built strictly
   over it; the (∞,ω) depth (δ) is the roof. *Do not bundle them* — they are
   sequenced because of this dependency, not merely to avoid churn.

5. **The dependency boundary survives everything.** Value-dependent grades stay
   beneath (§2.2); they are the one thing #1872 will not collapse.

### Roadmap map (this document organizes)
`mode-2`/`mode-12` (structure-class = the rung classifier) · `mode-26`
(alongside↔beneath) · `mode-17` (R7 doctrine) · `CSHD` #1478–#1484
(decategorification = the seam) · `FRONTIER-GRADED-EVERYTHING` #1872 (the grid collapses) ·
`THE-ONE-OBJECT` #1591 / `FRONTIER-SELF-FORMALIZE` #1874 (the fixpoint) ·
`GLP-UNIV-BRIDGE` #1449 (the ℓ-tower across axes = one ordinal) · `type-22` (2LTT) /
`type-24` (the missing directed type cell) · EXT-2/3/6/7 + the QUOT admission
table (the §5 quotient cross-section) · X3/X7 (the terminal-coalgebra and
ambidexterity sharpenings, §5–§6).

---

## 8. Honesty ledger

| claim | status |
|-------|--------|
| The per-axis grid cells (Conv/Step/LR; type-7/9; context-11/30/31/34; mode-1..27) | **SHIPPED** — the spectrum is a *reading* of existing structure, not new code. |
| grade = 1-cell of one-object 𝓜 / mode = 0-cell of many-object 𝓜; crossover at R3→R4 | **ESTABLISHED** (standard: B_R, MTT-over-a-mode-2-cat). |
| `categorify ⊣ decategorify`, grade = π₀(mode) | **ESTABLISHED math**; the *kernel realization* (CSHD #1483) is roadmap. |
| φ/δ/ℓ at rungs R4/R3/R1–2 | **DESIGN CLAIM** of this doc; load-bearing for placing φ as a mode property. |
| non-sharp ι ⟺ no `𝒰_ω : 𝒰_ω` as *one* obstruction | **CONJECTURE** — structural parallel ("no reflective collapse at the limit"), not yet a uniform theorem; a target for `O-OBSTRUCT` #1434 / `fib-10` #1588. |
| The 4×7 grid collapses to one product-graded object (#1872) | **ROADMAP-TARGET.** |
| The R7 fixpoint = the self-formalizing kernel (#1591/#1874) | **ROADMAP-TARGET / telos.** |
| chromatic / motivic geometric grades | **EXTERNAL / NASCENT** — not yet internalizable; the deepest open prize. |
| quotient = (beneath/alongside × δ × decidability) product position; set-quot = π₀(classifying) | **DESIGN CLAIM** (2026-07-02); realization = EXT-2/3/6/7 + the QUOT admission table. |
| usage `{0,1,ω}` measures failure of 1-semiadditivity (X7) | **CONJECTURE** — novel framing; falsifiable at the CSHD/cardinality instance. |
| R7 fixpoint = terminal coalgebra of `categorify` (X3) | **CONJECTURE** — fib-13 as a universal property. |
| the mode carrier is swappable data (`Polygraph/Computad/`); fib-3 at affine + fibrancy points | **SHIPPED carrier / ROADMAP instantiation** (2026-07-02 refactor + fib-3d). |

---

*Status: this document is the settled record of the grade↔mode design discussion.
Fibrancy is one mode property (`Tier0/Mode/FibrancyMode`, shipped); the earlier
proposal to extract a standalone `Tier0/Fibrancy/` classifier has been dropped.*
