# The Grade↔Mode Spectrum — a runged categorical design

> **TL;DR (2nd edition, 2026-07-16).** There are **two dials, not one ladder.**
>
> * **The seam.** A **grade** has `+` (addition — sharing, "how much"); its home is
>   a semiring. A **mode** has `∘` only (composition — position, "which place"); its
>   home is a (2-)category. **A 2-category has no `+`** — so the seam is the
>   ALGEBRA, and it cuts **across** every rung (§1.2).
> * **The ladder** (R1–R7) measures one real thing: how rich the mode theory 𝓜 is.
>   It is the *alongside* dial. It is **not** a grade/mode classifier and **not**
>   monotone (§2.3).
> * **Consequences:** beneath ≠ alongside even for static grades, because `B_R`
>   discards the `+` (§2.1); the lock and the count are **incomparable**, both
>   load-bearing (§2.2); and FX stands in the empty box that Shulman's MATT open
>   question **(vi)** names — answering it **NO** (§2.3).
>
> ⚠ **The first edition's central theorem — grade = one-object 𝓜, mode =
> many-object 𝓜, crossover at R3→R4 — is REFUTED** (§1.2), and it was marked
> ESTABLISHED here for a year while a use-position tag grew the name
> `affineDimensionModeGraph` around it. Five dependent claims fell with it. If you
> remember this file's "grade = π₀(mode)" slogan or its name-by-rung rule, both are
> corrected below (§6, §7.1).
>
> Home: this lives under `Axis/Mode/` because the mode axis classifies **mode
> theories** — not grades, which it cannot see (§7.3). Design prose, not a proof
> obligation; the Lean realizations are tracked tasks (mapped in §7). **Every
> ESTABLISHED row below carries a citation, a probe, or a re-runnable census —
> check a row's tag before you build on it.**

---

## 0. The one question this answers

Across the kernel we kept conflating *grade* (a usage/effect/cost quantity on a
binding) with *mode* (a place in a mode 2-category, à la MTT/MATT). They are
neither the same nor unrelated — but the first edition of this document got the
distinction **wrong**, and the wrong version was load-bearing for a year of A1
work. The correction is §1.2; read it before anything else here.

A grading is *a structure 𝓜 that the type theory is indexed / fibred over*; every
judgment carries a **position in 𝓜**. The spectrum sweeps **the categorical
richness of 𝓜**: `(number of objects) × (algebra on 1-cells) × (categorical
dimension)`.

★ **But richness is not the only dial, and it is not what separates grade from
mode.** There are **two independent parameters** (§2.3), and the grade/mode seam
is a fact about the **algebra**, not the rung (§1.2). The first edition claimed a
single ladder whose R3→R4 step *was* the grade→mode crossover; that claim is
refuted twice over, by Shulman's own examples and by FX's own kernel. Everything
that follows is written against the corrected version.

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
│ R4   │ many objects, 1-cells between them, sparse 2-cells │ a 0-cell "which place"       │ few-object mode (2LTT f/e, polarity)      │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R5   │ many objects, rich 1- and 2-cells, adjoint strings │ a mode + its modalities      │ mode proper (MTT/MATT)                    │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R6   │ weak ω-category                                    │ a mode with higher coherence │ ω-mode (mode-21)                          │
├──────┼────────────────────────────────────────────────────┼──────────────────────────────┼───────────────────────────────────────────┤
│ R7   │ 𝓜 = the type theory itself                         │ self-indexing                │ doctrine / bootstrap (mode-17)            │
└──────┴────────────────────────────────────────────────────┴──────────────────────────────┴───────────────────────────────────────────┘
```

The increasing parameter, rung by rung: R1 orders the 1-cells; R2 gives them a
second binary op (a semiring); R3 adds genuine 2-cells (the grades become a
*category*); R4 splits the single object into many; R5 enriches the inter-object
1-/2-cells (adjoint strings); R6 climbs to ω; R7 lets 𝓜 *be* the theory it grades.

**The ladder is a real measure of one thing: how rich 𝓜 is.** It is *not* a
classifier of grade-vs-mode (§1.2), and it is *not* monotone (§2.3). Read it as
the "alongside" dial and nothing more.

★ **LNL was removed from the R4 cell** (first edition listed it there). Shulman's
LNL polycategories have **many objects and ZERO 2-cells** —
*"without 2-cells in the 'mode theory' |D|"* (`papers/shulman-lnl-…:1603`) — so
they have *more* objects and *fewer* 2-cells than R3 and cannot sit on a monotone
rung at all. LNL is a **point off this ladder**, on axis 2 (§2.3). Related: LNL
also **cannot express affine** — its indexing condition is *"if `|σ⁻¹(j)| ≠ 1`
then `K_j` is negative and nonlinear"* (`:847`), which bundles weakening and
contraction under one clause; no sort admits `|σ⁻¹(j)| ≤ 1`. LNL realizes exactly
`{1, ω}`; **affine is the element it is missing** (`rg -c -i 'affine|graded'` over
1821 lines: zero hits).

---

## 1.2 ★★ THE CORRECTION — the seam is the ALGEBRA, not the object count

> **The first edition asserted, and marked ESTABLISHED:** *"a GRADE is a 1-cell of a
> one-object 𝓜 (R1–R3); a MODE is a 0-cell of a many-object 𝓜 (R4–R7); the
> crossover is exactly R3 → R4: one object becomes many."*
>
> **That is false.** Object count is a *presentation choice*, not the invariant.

**Refutation 1 — Shulman deletes a mode and keeps the mathematics.** MATT Example
6.11 (`papers/shulman-matt-2303.02572.md:603`, verbatim): *"We can simplify the
mode theory of Example 6.10 by **removing the mode** corresponding to the base
topos. Then L has **one mode** p and a single idempotent comonad μ : p → p"* —
and it still carries crisp type theory. Table 1 (`:568-577`) has **four
one-object rows**: idempotent monad → Parametric TT; idempotent comonad → Spatial
TT; meet-semilattice → Crisp TT; idempotent bimonad → commuting cohesions. This
document files cohesion at **R5** (§3, TYPE). Shulman realizes it at **one
object**.

**Refutation 2 — FX's own kernel is a counterexample to FX's own theorem.**
`dimensionUsePositionModeGraph` (`Typed/Fib/ModeLockPath.lean`; named
`affineDimensionModeGraph` until 2026-07-16 — see §7.1) has `Mode := Unit` — one
object — and carries genuine *modal* content: a use-**position** test, which is
this document's own definition of a mode. Machine-checked, zero-axiom: the same
variable, in the same context, with the same occurrence count, is **rejected** at
`.fibrant` and **accepted** at `.dimensional`. Only the position changed.

### The invariant that actually separates them

- a **GRADE** is a structure with **addition**. `+` is what fires when **one
  binding is shared by two parallel subterms** — the App rule's `p1 + r·p2`, the
  children fold, `1 + 1 = ω`. A grade answers **"how much / how shared."**
  Its home is a **semiring**.
- a **MODE** is a structure with **composition only**. `∘` is what fires when a
  term sits **under another lock** — `Γ/μ/ν = Γ/(μ∘ν)`. A mode answers
  **"which place."** Its home is a **(2-)category**.

**A 2-category carries composition and 2-cells. It has no `+`.** That is not an
omission to be repaired; it is what a 2-category *is*. So:

> ★★ **The grade/mode seam is the presence of addition. It cuts ACROSS the
> ladder, at every rung.** One object with `+` is a grade (R2's semiring). One
> object without `+` is a mode (Shulman's crisp TT). Many objects with `+` would
> be a graded mode theory — **the empty box of §2.3.**

This is why `B_R` cannot rescue the identification (§2.1), why the two mechanisms
are provably **incomparable** (§2.2), and why *"the lock replaces the count"* was
never a late deliverable but a **category error**.

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

★★ **The first edition claimed these COINCIDE for static grades** — *"a static
semiring R **is** a one-object 2-category B_R, so for static grades the two
presentations coincide"* — **and concluded that unifying them is the goal of
`FRONTIER-GRADED-EVERYTHING` (#1872). Both halves are wrong.**

**`B_R` is not `R`. It is `R`'s MULTIPLICATIVE reduct.** Delooping a semiring
`(R, +, ·, 0, 1, ≤)` yields the one-object 2-category whose 1-cells are `R` under
`·`, whose 2-cells are `≤`. **The `+` is thrown away.** It is not 2-categorical
data — there is nowhere for it to live. A 2-category has objects, 1-cells,
2-cells, and composition; addition is not among them.

So the alongside presentation **cannot express a grade**, ever — not "not yet,"
not "pending #1872." The mode theory's entire lock algebra is
`Γ/μ/ν = Γ/(μ∘ν)` and `Γ/1 = Γ` (MATT `:123`; exhaustive check of Figs 2–6
finds nothing that sums, joins, or splits an annotation). And `+` is precisely
what a grade is *for* — `1 + 1 = ω` is the statement that one binding was used by
two subterms.

> ★★★ **Corollary — `#1872` is refuted AS POSED.** "Unify beneath and alongside"
> cannot be done, because alongside has no `+`. **The correct target is the
> opposite result:** the *impossibility* theorem (they cannot be unified) plus the
> *coexistence* theorem (the pair is sound as two orthogonal axes). See §2.2.

FX runs both at once, and **that is correct** — not a redundancy awaiting
collapse. It is two axes that were mislabelled as one.

### 2.2 ★★ The incomparability theorem (machine-checked, zero-axiom)

The two presentations are not merely distinct — they are **incomparable**, and
FX's own kernel proves it. Two separators, running in **opposite** directions:

| separator | witness | lock | count |
|---|---|---|---|
| **the diagonal** | `λ⟨i⟩. p i i` — two *dimensional* uses | **accepts** (every obligation, `rfl`) | **rejects** (`rfl`) |
| **the single fibrant use** | one `.fibrant` use of the dimension | **rejects** (`rfl`) | **accepts** |

Neither refines the other. The reason is structural, and it is the content of the
theorem:

- **the count is `g(term)`** — `appScaledDimensionGrade` takes **no context
  argument**. It is blind to the lock. (`control_countIsContextBlind`, zero-axiom.)
- **the lock is `f(context, position)`** — the *same* variable, *same* context,
  *same* occurrence count is rejected at `.fibrant` and accepted at
  `.dimensional`. Only the position moved. It is blind to multiplicity.

**Disjoint inputs ⟹ incomparable ⟹ neither is redundant.** The diagonal
separator was not a discovery about FX's lock; given §2.1's no-`+` theorem it
**could not have failed to exist**.

★ **Naming consequence — ACTED ON 2026-07-16.** The carrier was called
`affineDimensionModeGraph`, and it is **not affine**: it rejects a *single* fibrant
use, so it has nothing to do with duplication. It is a use-**position** tag, which
the kernel already said where it mattered — `ElimRuleTable.lean:66`, *"The
USE-POSITION MODALITY."* The whole `affineDimension*` family is now
`dimensionUsePosition*`. The name was not merely an overclaim: it **collided with a
genuine concept it is not** — `MultiplierStructureClass.affine` is one of Nuyts'
four real structure classes (affine / cartesian / dedekind / deMorgan) and stays.
`dimensionUsePositionLockMultiplier` is in fact the mode-12 **void** multiplier, and
its own docstring said so ("NOT the mode-2 pointed affine class") while the name
said the opposite. The docstrings calling the lock a "count-free replacement" for
the grade are refuted by the table above and were repaired in the same pass. The
richer honest carrier still exists unwired: `fibrancyModeSignature` (two modes,
"MATT Example 2.5").

### 2.3 ★★ The second dial — the ladder is not the whole story

The first edition read the rungs as *the* parameter. They are **one of two**, and
the rungs are **not even monotone**:

> **Counterexample (LNL).** Shulman's LNL polycategories have **many objects** and
> **ZERO 2-cells** — *"a 'fibrational' calculus … **without 2-cells in the 'mode
> theory' |D|**"* (`papers/shulman-lnl-…:1603`). This document files LNL at **R4**
> = "many objects, sparse 2-cells", and claims R4 *extends* R3's 2-cells. LNL has
> **more** objects and **fewer** 2-cells than R3. No linear order survives this.

The honest structure is **two independent dials**:

| dial | what it varies | who sweeps it |
|---|---|---|
| **axis 1 — alongside** | the mode theory's shape: objects × 1-cells × 2-cells | **MATT sweeps the whole line** (Table 1: one object to many, sparse to adjoint strings) |
| **axis 2 — beneath** | the judgment's structural discipline: **cartesian / affine / linear / graded** | **MATT pins this at CARTESIAN and never varies it.** LSR/LNL vary it but are simply-typed or 2-cell-free |

The R1–R7 ladder measures **axis 1**. The grade/mode seam (§1.2) is the presence
of `+`, which is **axis 2**. Conflating them is the first edition's error, and it
is what hid the following:

> ★★★ **THE EMPTY BOX: axis-1 rich × axis-2 graded × DEPENDENT.**
>
> Nobody has filled it. MATT is rich × cartesian × dependent. Bounded LL / LNL are
> graded × simply-typed. **Shulman names the gap himself** — MATT §7, open question
> **(vi)**, verbatim: *"In [27], simple modal type theories were unified with
> substructural ones. **Is there a context-lock approach to substructurality? Can
> it be unified with modal dependent type theory?**"*
>
> **FX is standing in that box.** `IntroRuleTable.lean:154-167` carries a lock
> premise (MATT-shaped) and a graded premise (QTT-shaped) **on one dependent
> rule** — the exact configuration (vi) asks about. They are stapled, not unified.
>
> **And FX's kernel already answers (vi) — NEGATIVELY.** §2.2's two separators
> prove a context-lock **cannot** be made to count: the lock word never sees a
> binding (`locks(Γ, x:^μ A) = locks(Γ)`), and a 2-category has no `+`. Not "has
> not yet been" — *cannot*. **That impossibility theorem is the beyond-MATT
> result, and it is already proven; it needs writing up, not discovering.**

### 2.4 static ↔ value-dependent (the one genuine break)

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
into mode-land, so it lives as a *mode property* (`Axis/Mode/FibrancyMode`, §7).

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
   **decategorify** (forgetful, down: a mode's 1-cells shadowed to a monoid;
   `π₀` of a category; the cardinality of a groupoid). These are **adjoint**:
   `categorify ⊣ decategorify`. Hence:

   > **A grade is the decategorification of a mode; a mode is the categorification
   > of a grade.** `grade = π₀(mode)`, `mode = the category whose shadow is the
   > grade`.

   ★★ **CORRECTED — this holds only where there is something to decategorify INTO
   `+`.** The first edition stated it unconditionally, and it carries §1.2's error
   in a second disguise. `π₀` of a bare category is its 1-cells up to iso **under
   composition** — a **monoid**, not a semiring. The `+` is not recovered, because
   `categorify(R) = B_R` never carried it (§2.1): the round trip
   `R ↦ B_R ↦ π₀(B_R)` returns `(R, ·, 1)` and **loses the addition**. So
   `categorify ⊣ decategorify` is an adjunction **between mode theories and
   monoids**, and `grade = π₀(mode)` is **false in general**.
   **Where it IS true:** when the categorified object carries an *additive*
   structure to shadow — **coproducts**. `π₀` of a groupoid-with-coproducts gives
   cardinality, and cardinality genuinely has `+` (disjoint union) and `×`
   (product). That is exactly CSHD's setting (#1478–#1484), and it is why CSHD-5
   is a real theorem while the general slogan is not.
   ⟹ **The honest statement:** *a grade is the decategorification of a mode
   theory **with coproducts**; a bare mode 2-category decategorifies only to the
   multiplicative reduct.* The seam is `+`, all the way down (§1.2).

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

1. **Naming, fixed — CORRECTED.** The first edition said: *"Reserve 'grade' for
   R1–R3, 'mode' for R4+"* — i.e. name by **rung**. That rule is built on the
   refuted object-count theorem and it is **what put the wrong name on the
   kernel's lock**: a one-object carrier got called a mode-graph *and* called
   affine, and both are false (§2.2).
   **Name by ALGEBRA, not by rung:**
   - **"grade"** ⟺ the structure has **`+`** (sharing / how-much). `LevelExpr`,
     the §6 usage vector, δ-truncation, cost. Lives **beneath**.
   - **"mode"** ⟺ the structure has **`∘` only** (position / which-place). The
     locks, φ/f-e, cohesion. Lives **alongside**.
   - This cuts **across** every rung. A one-object carrier can be either
     (§1.2). The rung tells you how rich the mode theory is; it does not tell you
     whether you are looking at a grade.
   ★ **Consequence in the tree — DONE 2026-07-16:** `affineDimensionModeGraph` was
   misnamed twice — not affine (it rejects a single use), and its content is a *mode*
   (position) on a carrier the old rung-rule called a grade. The family is now
   `dimensionUsePosition*` (150 sites, 13 files, build green). The richer honest
   carrier `fibrancyModeSignature` still exists unwired.

2. **Fibrancy is one mode property.** φ is a *mode* (R4) and lives in the mode axis
   as `Axis/Mode/FibrancyMode.lean` (the 2LTT f/e presentation, the MATT predicate
   classes, the non-sharp ι; mode-13). It is **not** promoted to a standalone
   cross-axis classifier: the earlier `Axis/Fibrancy/` proposal is dropped —
   fibrancy is just one property of the mode axis, not a separate folder every axis
   imports. Any per-axis reading of "what structure the ≥1-cells carry" reads the
   fibrancy kind off that mode property; "fibred over mode" is a Core/Fib gluing
   statement.

3. **The mode axis classifies mode theories — NOT grades (corrected).** The first
   edition claimed *"Every grading structure — one-object semirings, multi-object
   stratifications, rich modalities — **is** a mode-2-category"*, and called the
   mode axis "the grade-of-grades." **The first clause is false**: a semiring is
   **not** a 2-category; delooping it discards the `+` (§2.1). What the mode axis
   classifies is the **axis-1** shape of a *mode* theory — genuinely, and that role
   is real. It cannot classify a grade's additive structure, because it cannot see
   it. There is still **no fifth ω-axis for grades**; grades live **beneath**, in
   the §6 vector, and that is their permanent home (§2.2, §2.4).
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
   beneath (§2.4) — a mode theory's 1-cells are fixed and cannot depend on a
   runtime value. The first edition called this "the one thing #1872 will not
   collapse"; the correction (§2.1) is stronger — **#1872 collapses nothing**, so
   value-dependence is no longer the *exception* but the second, independent
   reason the two presentations stay apart. Static grades are already separated by
   the missing `+`; value-dependent grades are separated *again* by dependency.

6. **What replaces #1872 (new).** The goal is not unification; it is the **pair of
   theorems** the kernel already witnesses: **(a) impossibility** — no context-lock
   can carry a grade (§2.1's no-`+` theorem + §2.2's separators), which answers
   Shulman's open question (vi) negatively; and **(b) coexistence** — the lock and
   the grade are *sound together* as two orthogonal premises on one dependent rule,
   because they read disjoint inputs. (b) is what makes `IntroRuleTable.lean:154-167`
   correct rather than redundant. Retarget #1872 accordingly.

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
| ~~grade = 1-cell of one-object 𝓜 / mode = 0-cell of many-object 𝓜; crossover at R3→R4~~ | ★★ **REFUTED** (2026-07-16). Was marked ESTABLISHED here for a year and was **load-bearing for the A1 arc's naming**. Killed twice: **(1)** Shulman MATT Ex 6.11 (`:603`) **deletes a mode** and keeps crisp TT; Table 1 (`:568-577`) has four **one-object** rows carrying content this doc files at R5. **(2)** FX's own `dimensionUsePositionModeGraph` (then named `affineDimensionModeGraph`) is one-object *and* carries modal (position) content, machine-checked. **Object count is a presentation choice.** Replacement in §1.2. |
| ★ **the seam is `+`**: grade ⟺ has addition (sharing); mode ⟺ composition only (position) | **DESIGN CLAIM** (2026-07-16, replaces the refuted row above). Its *negative half* — that a 2-category cannot carry `+` — is **ESTABLISHED** (a 2-category has objects/1-cells/2-cells/composition; exhaustive check of MATT Figs 2–6 finds no rule that sums, joins or splits an annotation). That `+` is the *right* invariant is the design call. |
| ★ **`B_R` ≠ `R`** — delooping keeps `(R,·,1,≤)` and discards the `+`; beneath ≠ alongside **even for static grades** | **ESTABLISHED.** Refutes the first edition's §2.1 coincidence claim. |
| ★ **lock ⟂ count are INCOMPARABLE** — two separators in opposite directions; `f(context,position)` vs `g(term)`, disjoint inputs | **ESTABLISHED, machine-checked zero-axiom** in the kernel (diagonal: lock accepts / count rejects; single fibrant use: lock rejects / count accepts; `control_countIsContextBlind`). |
| ★ **the lock is not affine** — it rejects a *single* fibrant use; it is a use-position tag | **ESTABLISHED, machine-checked — and ACTED ON 2026-07-16.** `ElimRuleTable.lean:66` already named it "The USE-POSITION MODALITY". The `affineDimension*` family is now `dimensionUsePosition*`; the docstrings calling it a count-free replacement were **REFUTED** and repaired (`2d7dadd54`). The old name also collided with `MultiplierStructureClass.affine`, a genuine Nuyts structure class that stays. |
| ★ **Shulman's MATT open question (vi)** — *"Is there a context-lock approach to substructurality?"* — is the box FX stands in, and FX answers it **NO** | **question ESTABLISHED** (MATT §7, verbatim `:632`); **the negative answer is PROVEN** (the row above) but **NOT YET WRITTEN UP as kernel theorems** — it lives in scratch probes. This is the beyond-MATT result. |
| ★ **LNL cannot express affine** — its `|σ⁻¹(j)| ≠ 1 ⟹ nonlinear` clause bundles weakening+contraction; no sort admits `≤ 1`; it realizes `{1, ω}` | **ESTABLISHED** (`shulman-lnl-…:847`; zero hits for `affine\|graded` in 1821 lines). |
| ★ **the ladder is not monotone** — LNL has *many* objects and **zero** 2-cells | **ESTABLISHED** (`shulman-lnl-…:1603`). LNL removed from the R4 cell; the two-dial structure is §2.3. |
| `categorify ⊣ decategorify`, grade = π₀(mode) | ★ **CORRECTED — false in general, true with coproducts.** `π₀` of a bare category is a **monoid** (1-cells under composition); the round trip `R ↦ B_R ↦ π₀(B_R)` returns `(R,·,1)` and **loses the `+`**. It holds where the categorified object has **coproducts** to shadow into `+` — which is exactly CSHD's groupoid-cardinality setting (#1478–#1484), so **CSHD-5 is a real theorem while the general slogan is not**. See §6, item 2. |
| φ/δ/ℓ at rungs R4/R3/R1–2 | **DESIGN CLAIM** of this doc; load-bearing for placing φ as a mode property. |
| non-sharp ι ⟺ no `𝒰_ω : 𝒰_ω` as *one* obstruction | **CONJECTURE** — structural parallel ("no reflective collapse at the limit"), not yet a uniform theorem; a target for `O-OBSTRUCT` #1434 / `fib-10` #1588. |
| ~~The 4×7 grid collapses to one product-graded object (#1872)~~ | ★★ **REFUTED AS POSED** (2026-07-16). "Unify beneath and alongside" is impossible: alongside has no `+` (§2.1). **Retarget #1872** to the pair it can actually have — **impossibility** (no context-lock carries a grade; = the (vi) answer) **+ coexistence** (the lock/grade pair is sound as two orthogonal premises, because disjoint inputs). See §7.6. |
| ★ **the word-problem engine is not load-bearing for the kernel** — `rg -ln 'import FX1Poly.Polygraph' FX1Poly/Typed/Engine/` is **empty**; every live kernel mode signature has `twoCell := Empty`; `lockCons` stores no modality at all | **ESTABLISHED, by census** (2026-07-16). The engine is genuine and first-ever; it decides over an **empty** 2-cell family, so its kernel content is currently vacuous. First real load = the adjunction triangles (`fxMode_hasAdjunctionTriangleSaturation = false`). **Not a wiring gap for affinity — counting is not a word problem, and never will be.** |
| The R7 fixpoint = the self-formalizing kernel (#1591/#1874) | **ROADMAP-TARGET / telos.** |
| chromatic / motivic geometric grades | **EXTERNAL / NASCENT** — not yet internalizable; the deepest open prize. |
| quotient = (beneath/alongside × δ × decidability) product position; set-quot = π₀(classifying) | **DESIGN CLAIM** (2026-07-02); realization = EXT-2/3/6/7 + the QUOT admission table. |
| usage `{0,1,ω}` measures failure of 1-semiadditivity (X7) | **CONJECTURE** — novel framing; falsifiable at the CSHD/cardinality instance. |
| R7 fixpoint = terminal coalgebra of `categorify` (X3) | **CONJECTURE** — fib-13 as a universal property. |
| the mode carrier is swappable data (`Polygraph/Computad/`); fib-3 at affine + fibrancy points | **SHIPPED carrier / ROADMAP instantiation** (2026-07-02 refactor + fib-3d). |

---

*Status: the record of the grade↔mode design discussion — **second edition,
2026-07-16**. Fibrancy is one mode property (`Axis/Mode/FibrancyMode`, shipped);
the earlier proposal to extract a standalone `Axis/Fibrancy/` classifier has been
dropped.*

*The first edition called itself "settled." It was not: its central theorem (§1.2)
and its §2.1 coincidence claim were **false**, and both were marked ESTABLISHED in
this ledger. They were load-bearing — they are why a use-position tag got named
`affineDimensionModeGraph` (renamed 2026-07-16), why six docstrings promised a "count-free replacement"
that cannot exist, and why #1872 aims at an impossible unification. **The lesson
is not that the ladder was wrong** — axis-1 richness is a real measure and the
4×7 reading still holds. **The lesson is that a rung is not a classifier**, and
that an ESTABLISHED row with no machine-checked witness is a claim, not a fact.*

*Every row this edition marks ESTABLISHED is backed by either a verbatim paper
citation with a line number, or a zero-axiom kernel probe, or a census command
that can be re-run. Rows that are the author's synthesis are marked **DESIGN
CLAIM** and say so. **If you are about to build on a row here, check its tag
first — and if the tag is DESIGN CLAIM or CONJECTURE, build the separator before
the feature.** Five of seven briefed premises inverted under exactly that test on
the day this edition was written.*
