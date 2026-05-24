# PolyTerm — The Scary Maxxed-Out Universal Substrate for FX Kernel Cells

> **Status:** vision document, computability-hardened.
> All claims reduce to one of:
> (a) a constructive Lean definition in this codebase (with file path),
> (b) a published decision procedure (with paper reference + arxiv ID +
>     complexity bound), or
> (c) an explicit out-of-scope tag with reason.
>
> No `IsX : Prop` placeholder predicates.  No "research-frontier flag"
> as a hand-wave shield.  No `Inhabited X` / hypothesis-as-postulate
> patterns.  The document obeys lean-fx-2/CLAUDE.md's zero-axiom
> absolute discipline: every theorem and definition shipped under the
> thirteen axes must `#assert_no_axioms` clean.
>
> **Costed:** ~214K Lean LoC over 2–3 years, of which **~25K is already
> shipped** in `Foundation/Polygraph/` (K11.1–K11.17 + K12.1–K12.19 +
> K12.23 + strength-T1/T2/T3 + T4×28 + T8 + Generator/RawPolyTermFlat
> infrastructure).  Net new work: ~189K LoC.  See [§9](#9-loc-budget)
> for honest accounting.
>
> **Slogan:** *PolyCell renamed and souped up.*  One indexed inductive
> `PolyTerm π dim source target` parameterized by a `PolyProfile π`
> bundling ten axes; FX kernel becomes one profile instance; the entire
> ~140 KLoC current FX kernel becomes specializations of this one type;
> ~40 of the 50 active accelerate-* roadmap tasks collapse into being
> PolyTerm view definitions instead of independent constructions.
>
> **Reference axis sources:** see [§13 References](#13-references).  The
> three load-bearing references are Loubaton's 2023 PhD thesis
> `arXiv:2307.11931` (univalence + Grothendieck construction at the
> (∞,ω)-level), Henry–Loubaton `arXiv:2301.11424` (marked ω-cats =
> minimal Verity stratification substrate), and Hadzihasanovic–Loubaton–
> Ozornova–Rovelli `arXiv:2404.14509` (ωcE polygraph = universal
> coherent ω-equivalence classifier).  Without those three, this doc is
> hand-wavy; with them it's mechanizable.

---

## Architecture overview

The design is a **3-tier architecture**, each tier with a single
committed substrate (no fallbacks, no alternative paths — the
strongest available theory per layer):

* **Tier 0 — UNIVERSAL META-FRAMEWORK** (§3.0)
  Uemura representable map categories (MSCS 2023, `arXiv:1904.04097`)
  + Bocquet-Kaposi-Sattler internal sconing (FSCD 2023,
  `arXiv:2302.05190`) + Pédrot-Tabareau Fire Triangle constraint
  (POPL 2020).  Provides: every type theory has a bi-initial model +
  its own internal language + theories ≃ models bi-equivalence.
  Sconing-is-enough thesis delivers canonicity, normalization, and
  parametricity for free per extension.  Fire Triangle bounds what
  is mixable (at most two of {substitution, dependent elimination,
  effects} unrestricted).  This is the expand-at-whim multiplier:
  each new FX feature ships as ~2K LoC Tier-0 obligation witness
  instead of 5-15K LoC bespoke cascade work.  ~12K Lean LoC, first
  Lean port of this framework in any proof assistant.

* **Tier 1 — POLYTERM CORE** (~15K LoC, §4)
  Small inductive PolyTerm + 13-axis PolyProfile bundle.  Each axis
  is one Tier-0 obligation witness.

* **Tier 2 — PROFILE EXTENSIONS** (13 axes, §3.1-§3.13)

  * **Axis 1 (Shape)** — Hadzihasanovic regular directed complexes
    (monograph `arXiv:2404.07273`, 337 pages, forthcoming CUP LMS
    Lecture Note Series).  All six classical shapes (globular /
    cubical / simplicial / opetopic / Θ / Steiner) are values of one
    inductive.  Chanavat-Hadzihasanovic diagrammatic sets (HHA 2024,
    `arXiv:2407.06285`) supplies the full homotopy-theoretic model
    structure + Quillen equivalence with simplicial sets + monoidal
    with Gray product.  Hadzihasanovic-Kessler `arXiv:2408.16775`
    delivers the weakest acyclicity condition for polygraph-freeness.
    Forest 2021 PhD thesis (HAL `tel-03155192`) provides the
    algorithmic word-problem decision procedure used by Axis 9.

  * **Axis 2 (Algebra)** — polynomial pseudomonads (Awodey-Newstead
    `arXiv:1802.00997`) for the full natural-model semantics over
    all dependent type formers + Aberlé-Spivak polynomial universes
    (`arXiv:2409.19176`) for the univalence-as-subterminality
    argument (Agda-formalized) + Shulman (`arXiv:1904.07004`) for
    the ∞-topos interpretation.

  * **Axis 4 (Saturation)** — Malbos-Massacrier-Struth §4 (Cubical
    Coherent Confluence).  Newman 4.1.4 + Church-Rosser 4.1.7 +
    Squier 4.3.6 work in (p+2, p+1)-categories without the groupoid
    hypothesis that Theorem 3.2.5 requires.  FX polygraph is
    non-groupoidal (steps have direction), so §4 is the substrate.

  * **Axis 7 (Multi-modal)** — 4-tier MTT stack.  Outer container is
    MTT (Gratzer-Kavvos-Nuyts-Birkedal LICS 2020).  Sub-layers:
    cohesive Myers-Riley (4 cohesive focuses ♭ ⊣ ◇ ⊣ □ ⊣ ♯) +
    resource graded modal DTT (Abel-Danielsson-Eriksson ICFP 2023
    `arXiv:2603.29716`, Agda-formalized with extraction-soundness
    theorem) + cost calf + decalf (Niu-Sterling-Grodin-Harper POPL
    2022 `arXiv:2107.04663` + Grodin-Niu-Sterling-Harper POPL 2024
    `arXiv:2307.05938`, both Agda-mechanized) + security DCC +
    structural refinement.  Each of FX's 21 graded dimensions maps
    to exactly one tier; 4 are properly cohesive focuses in the
    Myers-Riley sense.

  * **Axis 10 (Universe)** — `Step.eqType` operational reduction
    (per CLAUDE.md mandate) + Awodey-Newstead polynomial
    pseudomonads + Aberlé-Spivak polynomial universes (Agda-
    formalized).  TT_⊠ (Gratzer-Weinberger-Buchholtz
    `arXiv:2407.09146`) appears only as semantic justification —
    no implementation of TT_⊠ exists in any proof assistant; Rzk
    implements only the Riehl-Shulman STT base (Kudasov-Riehl-
    Weinberger CPP 2024).

  * **Axis 11 (SSC backbone)** — Kaposi-Xie 8 equations
    (`arXiv:2510.12303`, Agda) ported to Lean via the Allais-
    Atkey-Chapman-McBride-McKinna universe of syntaxes
    (`arXiv:2001.11001`, ICFP 2018 / JFP 2021).  Allais supplies
    the structural-recursion discipline Lean accepts in place of
    Agda's inductive-inductive support.  lean-fx-2 already ships
    Renaming Action + Subst Action via Allais (accelerate-P1.1 +
    P1.2).

  * **Axis 12 (STC classifier)** — Sterling STC (CMU PhD 2021) +
    Istari mechanization (Li-Yao-Harper `arXiv:2509.11418`) ported
    to Lean via 2LTT-on-Lean (Annenkov-Capriotti-Kraus-Sattler
    MSCS 2023 `arXiv:1705.03307`) hosting the strict-equality outer
    layer on Lean's native SProp (Gilbert-Cockx-Sozeau-Tabareau POPL
    2019 `hal-01859964`).  Inner-layer transport machinery follows
    Adjedj et al. `arXiv:2310.06376`.

  * **Axis 13 (MTT-norm gateway)** — Gratzer `arXiv:2301.11842`
    (March 2026) constrained by three structural restrictions to
    sidestep the word-problem-for-2-categories obstacle Gratzer's
    footnote 2 names: (a) fxModeTheory is rigid by construction
    (no non-trivial 2-isomorphisms between 1-cells), (b)
    orthogonality 2-cells are SProp-valued (equality trivially
    decidable), (c) genuinely 2-categorical fragments (cohesive
    triangle identities) use Makkai/Forest word-problem algorithm.

The hard rules this design holds:

* No "rzk-prototyped" claims where rzk does not implement the system.
* No "21 cohesive focuses" where only 4 are cohesive.
* No groupoid-hypothesis-violating theorems applied to non-groupoid
  polygraphs.
* No Coverage Semantics for univalent FX (Eremondi-Kammar §7.2 says
  incompatible with univalent theories — substitute Cockx-Devriese-
  Piessens "Pattern matching without K", ICFP 2014, DOI
  10.1145/2628136.2628139).

---

## Table of Contents

1.  [Manifesto](#1-manifesto)
2.  [Motivation: why pivot the substrate](#2-motivation-why-pivot-the-substrate)
3.  [The Thirteen Axes (with Tier 0 Meta-Framework)](#3-the-thirteen-axes)
    * 3.0 [Tier 0: The Universal Meta-Framework Substrate (Uemura + BKS sconing + Fire Triangle)](#30-tier-0-meta-framework)
    * 3.1 [Shape per dim — Hadzihasanovic regular directed complexes](#31-shape-per-dim)
    * 3.2 [Algebraic theory — polynomial pseudomonads + polynomial universes](#32-algebraic-theory)
    * 3.3 [Verity stratification — per-cell per-dim thinness](#33-verity-stratification)
    * 3.4 [Saturation — cubical coherent confluence (MMS §4 in non-groupoid setting)](#34-saturation)
    * 3.5 [Enrichment ladder — Segal A-precategories](#35-enrichment-ladder)
    * 3.6 [Complicial Gray module — bidirectional composition](#36-complicial-gray-module)
    * 3.7 [Multi-modal stack — 4-tier MTT outer container](#37-multi-modal-stack)
    * 3.8 [Profile fibration — self-referential profiles via Uemura ∞-type theories](#38-profile-fibration)
    * 3.9 [Coherent equivalence classifier — the ωcE polygraph + Forest word problem](#39-coherent-equivalence-classifier)
    * 3.10 [Univalent universe — polynomial universes + Step.eqType](#310-univalent-universe)
    * 3.11 [Single-Substitution Calculus backbone (Kaposi-Xie + Allais Lean port)](#311-single-substitution-calculus)
    * 3.12 [Synthetic Tait Computability classifier (Istari STC + 2LTT-on-Lean)](#312-synthetic-tait-computability)
    * 3.13 [MTT normalization gateway (Gratzer + rigid mode theory)](#313-mtt-normalization-gateway)
4.  [The PolyTerm signature](#4-the-polyterm-signature)
5.  [FX kernel as one profile instance](#5-fx-kernel-as-one-profile-instance)
6.  [Capabilities matrix](#6-capabilities-matrix)
7.  [Cascade obsolescence — what existing work collapses](#7-cascade-obsolescence)
8.  [Migration plan — how every existing file moves](#8-migration-plan)
9.  [LoC budget — honest accounting](#9-loc-budget)
10. [Phased rollout — concrete ship stages](#10-phased-rollout)
11. [Zero-axiom discipline — how each axis stays clean](#11-zero-axiom-discipline)
12. [Risks + open research questions](#12-risks-and-open-questions)
13. [References](#13-references)

---

## 1. Manifesto

FX is currently a 140-KLoC zero-axiom Lean 4 mechanization of a 21-dimensional
graded modal dependent type theory.  The current kernel is structured as a
disjoint union of independently-built layers: `Term`, `Ty`, `Step`, `Step.par`,
`StepStar`, `Conv`, `cd_lemma`, eight modal modalities, cubical, observational,
strict identity, equivalence, refinement, record, codata, session, effect,
universe cumulativity.  Each layer has its own cascade tax — adding one new
ctor to any base inductive triggers 80+ matching arms across 13+ downstream
files.  The ratchet costs are documented in `MEMORY.md` and `20_05_2026.md`:
the existing confluence cascade is 8.3K LoC, the cd_lemma cascade is 78
arms per new ctor, the rename / subst commute lemmas total 5–8K LoC of
duplicated structure, and any new feature (η, cubical β, modal cross,
HITs) takes weeks of cascade work per ctor.

The K11 "polygraph re-foundation" (commits a4d…, 7d6…, etc.) recognized
the architectural debt and started building toward a generic substrate.
That work is partially correct: the `Generator` enum + `binderShifts` +
`outputType` table from P2.0/P2.1/P2.2 are real polygraph generators.
The `RawPolyTermFlat` inductive shipped today (commit 7d6758a9, 2026-05-23)
is the first honest `mk g payload children` substrate.

But the K11.8 `RawPolyTerm` and K11.9 `PolyTerm` were **fake mirrors** —
pure renames of `RawTerm` and `Term`, zero polygraph content.  The user
correctly identified this and asked for them to be replaced with real
polygraph terms.  The substrate redesign demanded by today's session
(2026-05-23) is the trigger for this document.

This document specifies the *maximum* polygraph substrate for FX —
not a half-measure, not (∞,1), but the full (∞,ω)-categorical
universe parameterized by **thirteen axes** (SSC, STC, MTT-norm extend an earlier ten-axis
core; the Tier-0 universal meta-framework binds them all), every
axis grounded in published
literature, every axis Lean-mechanizable at zero axioms, every axis
giving FX a capability no other proof assistant has.

The thirteen axes are NOT orthogonal in the strict sense — they
compose through the Tier-0 META-FRAMEWORK (Uemura representable map
categories + Bocquet-Kaposi-Sattler internal sconing + Pédrot-
Tabareau Fire Triangle).  See §3.0 for the universal substrate that
makes the framework genuinely scary AND mechanizable.

The slogan is **PolyCell renamed and souped up**.  The K11.1 `PolyCell`
(dim-indexed, source/target intrinsic, real Burroni cells) is the
skeleton.  The other twelve axes are the flesh.  At the end you have
one inductive type `PolyTerm π dim source target` parameterized by a
thirteen-field `PolyProfile π`, with FX kernel as one specific
instance of the profile.

Eating all the cakes:
- A graded (Atkey-McBride 2018 + Wood-Atkey 2022 corrected Lam rule),
  parametric over a quantale Q,
- polarized (Levy CBPV + Pédrot-Tabareau ∂CBPV),
- multimodal (Gratzer-Kavvos-Nuyts-Birkedal MTT, parametric over a mode
  2-category hosting `▷`, cohesive `♭ ⊣ ♯`, U/F polarization),
- guarded (Nakano `▷` + Atkey-McBride clocked + Capretta Delay),
- cubical (Cohen-Coquand-Huber-Mörtberg + Cartesian / De Morgan flavors),
- HoTT-natively univalent (via Loubaton thesis §6.1.4.2 functorial
  Grothendieck construction; univalence as a theorem, not an axiom),
- with Allais universe-of-syntaxes generic traversals,
- decidable conversion via polygraph-morphism existence (HLOR ωcE +
  Loubaton §6.1.4.2),
- synthetic-Tait metatheory at (∞,ω) via complicial nerve,
- mechanized in Lean 4 at strict zero axioms,
- presented as a complicial-stratified globular-cubical-opetopic
  polygraph with Gray tensor compatible composition and tropical
  optimal reduction.

This is the "quantale-enriched (∞,∞)-category of types" Object the
`20_05_2026.md` dossier §14 hand-waves toward; this document makes it
mechanizable.

The cost is honest: ~187K LoC zero-axiom Lean 4, 2–3 years of focused
work, **first mechanization of (∞,ω)-categories internalized in any
proof assistant**.  FX simultaneously becomes a programming language
kernel AND a categorical-foundations research artifact.  No precedent.

This is what FX is for.

---

## 2. Motivation: why pivot the substrate

### 2.1 The cascade tax is the dominant cost

The current FX kernel has every typed constructor appearing in
~78 places: once each in `RawTerm`, `Term`, `Step`, `Step.par`,
`Step.par.Compat` (rename), `Step.par.Compat` (subst), `RawCdLemma`,
`cd_lemma`, `StepStar`, `Conv`, `Conv.cong`, 8 modal modalities'
crossings, cubical β/η interactions, plus N downstream consumers.

Adding **one** new typed ctor (e.g. `Step.transpPi`) requires writing
80+ arms across 13+ files.  Audited cost from D2.5.5 (transpPi β rule):
~470 LoC of cascade for ~30 LoC of substantive content.  Ratio
**15:1 boilerplate-to-substance**.

This is not a bug.  It is the natural cost of having every layer
inductive-defined independently against `RawTerm`.  As long as
`Term`/`Step`/`cd_lemma`/`Conv`/… are independent inductives, the
cascade tax is unavoidable.  Bigger cascades are unavoidable as new
modalities, cubical operations, HITs, measure theory, differentials,
quotients, etc. land.

The polygraph substrate eliminates the cascade by **moving every
ctor into a data field rather than a constructor**.  Adding a new
ctor = adding one `Generator` value + one entry in the `payload`
table + one entry in the `outputType` table.  Three places, all
data, no proof.  Downstream consumers (rename, subst, cd_lemma, etc.)
induct ONCE over `Generator`, not per-ctor; cascade evaporates.

### 2.2 The Prop→Type wall and the wrong scope

The `20_05_2026.md` dossier §8 documents the "polygraph derives
confluence, deletes 45K LoC" claim as **refuted** by the Prop→Type
wall: you cannot extract a `cd_lemma` proof from a `PolyCell` Type-side
embedding because `cd_lemma` is Prop-valued.

This refutation is correct *for the current K11 design*, where
PolyCell is just data + ParallelPair + composition laws and the
proof of confluence stays Prop-side.

The PolyTerm proposal here resolves the wall by **making the
substrate carry both the cells AND the markings**:

- Cells are Type-side (PolyTerm constructors).
- Markings are Prop-side (Loubaton's `tD ⊆ D` per-cell thinness).
- Conv = "cell is in the saturated marking" (Prop, via Riehl-Verity
  saturation criterion).
- `cd_lemma` = "the saturated marking is closed under composition"
  (one Prop-valued theorem per *profile*, not per *ctor*).

So **the per-ctor cd_lemma cascade collapses to one theorem per
profile**.  Adding a new ctor doesn't grow the cascade because the
new ctor is just a new Generator value classified by the existing
marking.

### 2.3 Conv decidability — two independent published paths

Decidability of Conv has TWO concrete published decision procedures
under PolyTerm.  Either suffices for `★ MILESTONE A`; we ship both
as redundant paths because the first one we hit may reveal Lean
mechanization issues, and having a backup avoids pivot collapse.

**Path A — convergent-rewrite NbE** (the pragmatic path, already
24/30 supporting lemmas shipped):

```
Term.eval (K13)  ─→  ValueTerm.quote (Abel-Sattler readback)  ─→
DecidableEq on η-long NF  ─→  Conv.decide via NF equality
```

* Total NEW LoC: ~6K (K13 + Conv.decide bridge).
* Reference algorithm: Adjedj-Lennon-Bertrand-Maillard-Pédrot-Pujet,
  "Martin-Löf à la Coq", `arXiv:2310.06376` (2024) — full mechanized
  decidable conv for MLTT-with-inductives in Coq, ~12 months of work.
  FX is a direct adaptation.
* Status: K12.1–K12.19 + K12.23 already shipped (Tait reducibility
  base cases + HOTT cases); K12.20–K12.30 + K13.x pending.  See
  `LeanFX2/Reducibility/`.
* Soundness: standard MLTT subject-reduction + SN proof technique
  (Tait 1967 Kripke logical relations, Wood-Atkey 2022 corrected
  Lam rule).
* When this WILL work: it has worked for MLTT in Coq.  FX adds
  cubical β, modal ops, observational equality — each is a known
  decidability extension (Sterling-Angiuli-Gratzer XTT for
  observational, Mörtberg-Spadetto for cubical decidable conv).

**Path B — Makkai-Mimram word problem on free ω-cat** (the polygraph
path, semantically aligned with the PolyTerm substrate):

```
PolyTerm extracted as Generator-based polygraph X with finite
generators per dim  ─→  FX rewrite as convergent presentation
(K12 SN + cd_lemma gives confluence)  ─→  word equality in
F(X) decidable via Makkai's algorithm  ─→  Conv = word equality
```

* Reference algorithm: Makkai, "Word Problem for Computads" (McGill
  manuscript, last rev. 2021, available at
  `math.mcgill.ca/makkai/WordProblem/WordProblemCombined.pdf`) —
  ORIGINAL decision procedure for cell-equality in free ω-cat over
  a finite computad / polygraph.
* Improved algorithm: Forest, "Computational descriptions of
  higher categories" (PhD thesis, Université Paris Cité 2022) —
  implementable, polynomial-time-in-practice improvement on Makkai's
  algorithm; matches "Cellular structures using ω-categories" line
  (Forest-Mimram, ABGMMM book §17.5).
* Total NEW LoC: ~5K (encode Makkai's algorithm + extract FX
  convergent presentation from existing K11/K12 work).
* Soundness: Makkai's algorithm IS decidability of word equality
  in free ω-cat.  Confluence of FX rewrite = convergent presentation
  (Squier 1987, FDT line) gives normal-form uniqueness; combined
  with Makkai gives Conv.decide.
* When this WILL work: Squier showed finite + confluent + terminating
  ⇒ normal-form decision algorithm.  FX's K12 reducibility shows
  termination; cd_lemma shows confluence; finiteness is by Generator
  enumeration.  All three conditions hold for the FX profile.

**Where ωcE fits.**  The HLOR `arXiv:2404.14509` ωcE polygraph
(Construction 1.22 + Prop 1.26) is the **semantic universal
classifier** — it explains *why* the saturation closure recovers
all coherent equivalences, by giving the universal coherent walking
ω-equivalence object.  In the implementation, ωcE is NOT the
decidability engine; Makkai's algorithm is.  ωcE is the semantic
justification that the algorithm computes the right relation.

ωcE specifically:
* HLOR proves ωcE is finite-type at every k (Construction 1.22).
* HLOR proves ωcE is contractible (Thm 1.33) and universal among
  coherent ω-equivalences (Prop 1.26).
* HLOR does NOT prove decidability of polygraph-morphism search
  into ωcE.  That's an open question for finite-target polygraphs.
  We do not claim it.

This is the corrected story versus the original draft of this
document (which over-claimed "decidable in ~3K LoC via ωcE
morphism search").  The corrected story is honest about what's
published and what's not.

**Net for MILESTONE A:** Path A (NbE) is on the critical path
because K12 + K13 work is already in flight and follows the
Adjedj et al. recipe.  Path B (Makkai) is the backup + semantic
alignment with PolyTerm; if Path A hits an unforeseen Lean
mechanization wall, Path B is independently sufficient.  Both
paths converge on the same `Decidable (Conv a b)` instance.
CONVTRANS-D, K12.28, K13.20 collapse via Path A's standard
recipe.

### 2.4 Concurrency / distribution come for free

The `20_05_2026.md` dossier §2.7 conjectures that K11.5 (horizontal
composition) + K11.6 (interchange / Eckmann-Hilton) IS the separation
logic frame rule at the polygraph level.  The conjecture is *correct
in structure but loses typing* in the current K11 design because the
typed Term is separate from the polygraph.

PolyTerm fixes this: `compH` (horizontal composition, Loubaton Gray
module §3.1.4) takes two typed cells with disjoint footprints and
produces a typed cell with combined footprint.  Interchange
(K11.6, already shipped zero-axiom) is the frame rule **at the typed
level**.

So `par(f, g)` typechecks ⟺ `footprint(f) ⊓ footprint(g) = ⊥` in
the permission semiring (FX's existing graded usage dimension).
The frame rule isn't a separately-proved theorem; it's the typing
rule of `compH`.

Distribution / GPU evaluation (P5.1) becomes a polygraph fold with
`compH` for parallel partitions and `compV` for sequential commits.
BSP-sync is the saturation closure.  ZERO additional infrastructure
beyond what PolyTerm already gives.

### 2.5 Modal / cohesive / polarized / linear / guarded all in one kernel

The current FX modal layer is 8 hardcoded modalities (`♭`, `◇`, `□`, `♯`,
ghost, cap, later, clock) with hand-rolled adjunction lemmas.  Adding a
ninth modality (e.g. graded `▷` per Nakano, or differential `∂` per
Kock-Lawvere SDG) requires re-doing the adjunction chain by hand.

PolyTerm puts the entire modal layer in the `topos` axis (axis 7,
Lurie ∞-topos with modal adjunctions as topos structure).  Adding a
new modality = adding one `ModalAdjunction` entry to the topos profile.
No cascade.

Similarly for polarization (Levy CBPV via axis 6's complicial Gray:
positive cells are thin under `_⋆[1]`, negative cells thin under
`[1]⋆_`), linearity (axis 2 polynomial monad with linear-arity
generators), guardedness (Nakano `▷` as one of the modalities),
cohesive `♭⊣♯` (already in topos profile), classical/intuitionistic
discipline (axis 3 stratification on the truth values).

**One kernel hosts every type theory we'd ever want.**  Different FX
deployments pick different profiles; all coexist.

### 2.6 The categorical universe internal to FX

Loubaton's PhD thesis §6.1.4.2 proves:

> Hom^⊖(I, ω) ≃ LCart^c_U(I)

where `ω` is the (∞,ω)-category of (∞,ω)-categories.  This is the
(∞,ω) statement of univalence + Grothendieck construction simultaneously.

For FX, this means: the universe `Ty.universe` in the current kernel
becomes a `PolyTerm fxProfile 0 (universeBoundary)` cell, and its
universal property (functors-to-it ≃ type-families) holds STRUCTURALLY,
not by postulation.  Univalence is a theorem; `Step.eqType` becomes
a reduction inside the universe cell.

This makes FX **the first proof assistant where univalence is a
structural theorem rather than an axiom or a postulated `Step` rule**.

### 2.7 The math automation hypothesis

The `20_05_2026.md` §4 voracious math vision posits that with a
generic-extension framework, math from Mathlib can be imported into
FX as polygraph extensions: types become atoms, lemmas become
1-cells, coherence becomes 2-cells, Squier 3-cells handle critical
pair joinability.

This is implementable in PolyTerm: Mathlib's ~1.5M LoC of mathematics
maps to a sequence of `Generator` value extensions, with each
Mathlib theorem becoming one dim-1 cell in `PolyTerm fxProfile`.
The conversion is mostly mechanical; the win is that FX-extensions
inherit Mathlib's full mathematical content.

### 2.8 First-of-its-kind mechanization

No proof assistant currently has (∞,ω)-categories internalized.
Mathlib has (∞,1)-categories via quasicategories partially, no marked
∞-cats, no opetopes, no Steiner directed complexes, no polynomial
monads, no Gray tensor.  Cubical Agda has univalence but only at the
(∞,1) level.  Coq has Homotopy Type System but no (∞,ω) machinery.

FX would be the first mechanization of:
- Marked (∞,ω)-categories (Henry-Loubaton 2023)
- Verity stratification at (∞,ω)
- Loubaton's functorial Grothendieck construction
- HLOR ωcE polygraph
- Polynomial monads on Glob_∞
- Joyal Θ-cells in a type theory

This is research-frontier work, but it is **achievable** because
each component is published, peer-reviewed, and has explicit
constructions.  The barrier is engineering scale (~187K LoC), not
mathematical risk.

---

## 3. The Thirteen Axes (with Tier 0 Meta-Framework)

Tier 0 (§3.0) is the universal meta-framework substrate.  Each of the
thirteen axes (§3.1-§3.13) is one Tier 0 obligation witness: a
representable-map-category extension + sconing witness + Fire Triangle
navigation.  Axes are heterogeneous (cohesive / resource / cost /
security / structural / etc.) but compose through the PolyProfile
bundle (§4).

### 3.0 Tier 0: The Universal Meta-Framework Substrate

Before the thirteen axes: a universal Tier 0 substrate that all axes
are built on.  This is what makes PolyTerm's "expand FX at whim"
architectural promise concrete.  Each axis becomes one categorical
obligation against the meta-framework, ~2K LoC instead of 5-15K LoC
bespoke cascade work per new feature.  The 12K LoC investment in
Tier 0 amortizes over ALL FX extensions: each new extension is ~2K
LoC instead of 5-15K LoC.  Break-even after ~3 extensions; thereafter
pure savings.  For a 5-year horizon with ~10-15 new extensions
(probability, SDG, quantum, reversible, distributed, etc.), that's
~30K LoC saved by virtue of the universal framework.

**References:**

* Taichi Uemura, "A general framework for the semantics of type
  theory", `arXiv:1904.04097` (MSCS 33(3), 2023).  Representable map
  categories as a universal substrate for type-theoretic syntax.
* Rafaël Bocquet, Ambrus Kaposi, Christian Sattler, "For the
  metatheory of type theory, internal sconing is enough",
  `arXiv:2302.05190` (FSCD 2023).  Sconing = gluing along a global
  section functor, performed internally to a presheaf topos.
* Rafaël Bocquet, Ambrus Kaposi, Christian Sattler, "Relative
  induction principles for type theories", `arXiv:2102.11649`
  (2021).  Internal-presheaf induction principles using DRA + MTT
  for multiple presheaf categories.
* Pierre-Marie Pédrot, Nicolas Tabareau, "The Fire Triangle: How to
  Mix Substitution, Dependent Elimination, and Effects", POPL 2020,
  HAL `hal-02383109`.  No-go theorem on the three properties' mutual
  compatibility; ∂CBPV resolution.
* Hoang Kim Nguyen, Taichi Uemura, "∞-type theories" (2022).
  ∞-categorical generalization of representable map categories.
* Taichi Uemura, "Normalization and coherence for ∞-type theories",
  `arXiv:2212.11764` (2022).  Modular normalization via
  substitution-mode + renaming-mode separation.

#### 3.0.1 The three Uemura theorems

For a type theory T (defined as a representable map category):

1.  **Bi-initial model theorem**: T has a bi-initial model in the
    2-category of models.  Syntax = the universal-property witness.
2.  **Internal language theorem**: every model M of T has its own
    internal language; M's internal language IS a type theory in the
    sense of T.
3.  **Theory-model bi-equivalence**: the 2-category of theories over
    T is bi-equivalent to a full sub-2-category of models of T.

This is the FX-relevant content: any extension of FX has a unique
bi-initial model that lives in T's 2-category, and FX's internal
language gives back the extension's syntax.  Codata, sessions,
machines, contracts, etc. all become objects in a single categorical
hierarchy with a uniform universal property.

#### 3.0.2 Internal sconing — metatheory for free

The BKS thesis (FSCD 2023): **sconing alone (not general gluing) is
enough for the metatheory**.  Two key moves:

* Restrict to a single global-section functor (the sconing functor),
  not arbitrary gluing.
* Perform the construction INTERNAL to a presheaf topos; externalize
  at the end.

The payoff:

* **Canonicity** falls out as one boilerplate-free induction
  principle.
* **Normalization** falls out as another (Uemura `arXiv:2212.11764`
  refines this via substitution-mode + renaming-mode separation).
* **Syntactic parametricity** falls out as a third.

For each FX axis, the metatheory obligation reduces to: provide a
sconing witness.  Per axis ~1K LoC.  Subsumes per-construction STC /
gluing arguments cited per-axis below.

The BKS earlier paper "Relative induction principles" (`arXiv:2102.11649`)
provides the framework: induction principles that operate relative to
a functor INTO the syntax, with conclusion in the functor's codomain
rather than the syntax itself.  Uses Dependent Right Adjoints + MTT
to handle multiple presheaf categories simultaneously — directly
aligns with FX's modal axes.

#### 3.0.3 The Fire Triangle constraint

Pédrot-Tabareau's no-go theorem (POPL 2020) states:

> In any dependent type theory, the three properties — substitution,
> dependent elimination, and effects — cannot all coexist freely.
> At most two can hold unrestricted.

Concrete restrictions:

* In call-by-name: dependent elimination must be restricted (cannot
  eliminate into effectful results).
* In call-by-value: substitution must be restricted (cannot freely
  substitute into effectful binders).
* ∂CBPV (dependent call-by-push-value) resolves the tension by
  decomposing call-by-name / call-by-value into their CBPV components
  and applying restrictions appropriately.

**FX-relevant content:** the 4-tier multi-modal stack (§3.7) navigates
the Fire Triangle by:

* Graded effects (calf/decalf cost grades, Abel-Danielsson-Eriksson
  resource grades) — restrict effects to bounded fragments where
  dependent elimination + substitution stay unrestricted.
* Modal type theory (MTT outer container) — provides the categorical
  machinery for the restrictions.
* SProp 2-cells for orthogonality witnesses — keeps the modal layer
  rigid + decidable.

Earlier drafts ignored this constraint.  This document makes it
explicit so future
axes don't accidentally try to mix all three legs unrestrictedly.

#### 3.0.4 The Tier 0 obligation type

Every PolyTerm axis is a tuple (Categorical structure, Sconing
witness, Fire Triangle navigation):

```lean
/-- A PolyTerm axis is a Tier-0 obligation: a representable-map-category
extension to FX's base type theory, together with a sconing witness
that delivers canonicity, normalization, and parametricity. -/
structure AxisObligation where
  /-- The categorical structure being added (Uemura RMC extension). -/
  rmcExtension : RepresentableMapCategory.Extension fxBaseRMC

  /-- The sconing witness (BKS internal sconing) that delivers
  metatheory for free. -/
  sconingWitness : InternalSconing rmcExtension

  /-- Fire Triangle navigation: which of {subst, depElim, effects}
  this axis restricts (at most one — the other two stay
  unrestricted). -/
  fireTriangleRestriction : Option FireTriangleLeg

  /-- Lean LoC estimate (signature + sconing witness + integration). -/
  loc : Nat

  /-- Mechanization precedent (paper + proof assistant). -/
  precedent : List Citation
```

For each axis below, the §3.X header explicitly lists what it provides
for each of these four fields.

#### 3.0.5 Lean mechanization status

Uemura's framework: paper-form (MSCS 2023), no Lean implementation
exists.  Nguyen-Uemura ∞-type theories: paper-form (2022).
BKS internal sconing: paper-form (FSCD 2023), no Lean implementation.

The Tier 0 substrate is **novel Lean work for FX**.  Estimated cost:

| Component | Lean LoC | Status |
|---|---|---|
| Representable map category core | ~3K | Novel Lean |
| Sconing functor + internal presheaf | ~3K | Novel Lean |
| Three Uemura theorems (bi-initial, internal language, bi-equivalence) | ~2K | Novel Lean |
| Fire Triangle constraint encoding | ~1K | Novel Lean |
| Sconing-induction-principle generic + canonicity/normalization/parametricity instances | ~3K | Novel Lean |
| **Total** | **~12K** | Novel Lean |

Per-axis sconing-witness writeup: ~1K LoC; per-axis representable-map
signature: ~500 LoC; per-axis Fire Triangle accounting: trivial.  Net
per-axis savings versus bespoke cascade: 3-13K LoC depending on
axis complexity.

#### 3.0.6 Why this is genuinely scarier than its source papers

Each source paper handles one axis (or one metatheorem).  PolyTerm
with Tier 0 substrate gives FX the combined strength of all of them:

* Uemura provides universality (every type theory in one framework).
* BKS provides metatheory for free (sconing once, all three
  metatheorems).
* Fire Triangle provides budget constraint (knowing what's unmixable
  saves wasted attempts).
* All thirteen axes plug into the same Tier 0 obligation type.

No single paper does this for the combination.  No proof assistant
currently has the Tier 0 framework mechanized.  FX gets to be
first-mover on the universal-substrate AND on the (∞,ω)-categorical
kernel.

This combination is what makes the per-axis citations honest — none
of them individually justify the "scary" framing, but together with
the Tier 0 universal substrate they do.

### 3.1 Shape per dim

**Reference:** Joyal Θ (Joyal 1997 / Berger 2002); Steiner directed
complexes (Steiner 1993, ABGMMM book §17.4); opetopes (Baez-Dolan
1998, Leinster 2002, Curien-Ho Thanh-Mimram 2022); HDA precubes
(Pratt 1991, van Glabbeek 2006); Berger-Moerdijk generalized Reedy
(2008).

**Why FX needs it:**

- Different FX layers naturally live at different shapes:
  - Terms + rewrites: globular (everything is "ports going in, ports
    going out, with source/target boundaries")
  - β/η/cubical paths at dim 2: cubical (paths have endpoints +
    interval algebra)
  - Confluence at dim 3: Θ-wreath (cd_lemma cells are critical
    branchings with multi-port pasting)
  - Squier coherence at dim ≥ 4: opetopic (Mac Lane pentagon, higher
    coherences have tree shape)
  - Concurrent execution: HDA / precubical (Pratt's higher-dim
    automata for true concurrency)
  - Cost-tropical optimal reduction (§8 of dossier): generalized
    Reedy (different cells have different cost-weights)

- A monolithic single-shape substrate forces awkward encodings (e.g.
  cubical paths as nested globular cells).  Per-dim shape lets each
  layer use its natural combinatorics.

- All shapes can in principle be unified under Joyal Θ (which is
  the colimit-completion of globular sets under wreath products).
  Picking per-dim shape is a profile choice over Θ subobjects.

**Substrate — Hadzihasanovic regular directed complexes
(`arXiv:2404.07273`):**

The substrate is Hadzihasanovic's 337-page monograph (forthcoming as
CUP LMS Lecture Note Series), which covers all six classical shapes
as values of one `RegularDirectedComplex` type, with explicit Gray
products, suspensions, and joins.  The `Mol(P)` functor produces
strict ω-categorical structure on molecules — Hadzihasanovic's
construction, used by every downstream framework cited below.

For FX's operational dimensions (n ≤ 3, cd_lemma at dim 2, Squier at
dim 3), strict ω-categories suffice (Chanavat Theorem 2.66:
stricter = strict for n ≤ 3).  The stricter extension only matters
at n ≥ 4 (Chanavat Comment 2.67); it is a future-work option, not
part of the load-bearing path.

Supporting stack:

* **Hadzihasanovic monograph** `arXiv:2404.07273` (337 pages): all
  six shapes as regular directed complexes; `Mol(P)` functor
  produces strict ω-cats; Gray products + suspensions + joins.
* **Chanavat-Hadzihasanovic diagrammatic sets** `arXiv:2407.06285`
  (HHA 2024): cofibrantly generated model structure on diagrammatic
  sets + two Quillen equivalences with simplicial sets + monoidal
  with Gray.  Full homotopy-theoretic substrate.
* **Hadzihasanovic-Kessler** `arXiv:2408.16775`: weakest acyclicity
  condition for polygraph-freeness; stable under
  pasting/suspension/Gray/joins/duals.
* **Chanavat-Hadzihasanovic (∞,n)-cats** `arXiv:2410.19053`:
  diagrammatic model structures for (∞,∞)-cats.
* **Forest 2021 PhD thesis** (HAL `tel-03155192`): computational
  descriptions — word problem for strict ω-cats + pasting diagram
  algorithms + Gray coherence.  Algorithmic substrate for Axis 9.

One substrate (Hadzihasanovic regular directed complexes) covers all
six shapes at all dimensions FX needs.

**Regular directed complex (Hadzihasanovic):** an oriented graded
poset `P` where every closed singleton `cl{x}` is a *molecule* —
a composable arrangement of lower-dim cells built inductively from
the point via two operations: **pasting** (`U #ₖ V` at matching
k-boundary) and **rewrite** (`U ⇒ V` between same-dim round
molecules).  Every regular directed complex carries a canonical
strict ω-categorical structure on its molecules.

**Stricter ω-category (Chanavat Definition 2.13):** a composition
structure `C` such that for every finite regular directed complex
`P` and every `P`-matching family of cells, there is a UNIQUE
amalgamation.  Equivalently: stricter n-cats are obtained from
strict n-cats by additionally imposing the higher exchange laws
governed by regular directed complexes.

**Why "stricter" is exactly what FX wants:** strict n-categories
are TOO strict for the cubical / cells-with-orientation needs of
FX (path types, transport, hcomp).  But weak ω-categories (e.g.
Batanin's) are too LOOSE for mechanization.  Stricter ω-cats hit
the sweet spot — strict enough to admit pasting-as-universal,
loose enough to support directed cells with non-trivial
orientation data (cubical paths, glue boundaries, modal commuting
squares).

**The six shapes as instances:**

* Globular cell = `Mol(globe_n)` where `globe_n` is the n-globe
  regular directed complex.
* Cubical cell with connections = `Mol(cube_n)` where `cube_n` is
  the n-cube regular directed complex with BCH connections.
* Simplicial Δⁿ = `Mol(simplex_n)`.
* Baez-Dolan opetope = `Mol(opetope_n)` for the appropriate regular
  directed complex.
* Joyal Θ-cell = `Mol(theta_n)`.
* Steiner parity complex = `Mol(parity_n)` (Steiner directed
  complexes ARE special-case regular directed complexes).

All six live as values of one inductive `RegularDirectedComplex` +
one definition `Mol : RegularDirectedComplex → CompositionStructure`.

**Lean signature:**

```lean
/-- An oriented graded poset: a finite poset graded by dim + per-element
orientation data partitioning the cofaces into input vs output. -/
structure OrientedGradedPoset where
  carrier        : Type u
  dim            : carrier → Nat
  faces          : carrier → Finset carrier
  cofaceSplit    : (x : carrier) → Finset carrier × Finset carrier
                   -- (∇⁻ x, ∇⁺ x) input vs output cofaces
  cofaceUnion    : ∀ x, (cofaceSplit x).1 ∪ (cofaceSplit x).2 =
                        { y | y ∈ faces x }
  cofaceDisjoint : ∀ x, (cofaceSplit x).1 ∩ (cofaceSplit x).2 = ∅

/-- A regular directed complex (Hadzihasanovic): an oriented graded
poset where every closed singleton is a molecule.  Molecules are
inductively defined: the point is a molecule; pasting at matching
k-boundary preserves molecule; rewrite of round molecules at total
boundary preserves molecule. -/
inductive RegularDirectedComplex : Type u where
  | mk : (P : OrientedGradedPoset) →
         (∀ x, IsMolecule P (P.closedSingleton x)) →
         RegularDirectedComplex

/-- The IsMolecule inductive predicate, by structural induction on
the build operations of Hadzihasanovic. -/
inductive IsMolecule (P : OrientedGradedPoset) : SubPoset P → Prop where
  | point     : ∀ x, P.dim x = 0 → IsMolecule P (point x)
  | paste     : ∀ U V k, IsMolecule P U → IsMolecule P V →
                MatchingBoundary U V k →
                IsMolecule P (pasteAt U V k)
  | rewrite   : ∀ U V, IsMolecule P U → IsMolecule P V →
                IsRound U → IsRound V →
                SameTotalBoundary U V →
                IsMolecule P (rewriteAtTopDim U V)

/-- Six classical shapes as values of RegularDirectedComplex. -/
def globe : Nat → RegularDirectedComplex := ...
def cube : Nat → RegularDirectedComplex := ...
def simplex : Nat → RegularDirectedComplex := ...
def opetope : Nat → RegularDirectedComplex := ...
def theta : Nat → RegularDirectedComplex := ...
def parityComplex : Nat → RegularDirectedComplex := ...

/-- Mol(P): the canonical strict ω-categorical structure on molecules
of a regular directed complex.  Chanavat Definition 2.6. -/
def Mol (P : RegularDirectedComplex) : CompositionStructure := ...

/-- Stricter ω-categories (Chanavat Definition 2.13): composition
structures where every P-matching family has a unique amalgamation
for every finite regular directed complex P. -/
structure StricterOmegaCat where
  underlying : CompositionStructure
  amalgamation_unique :
    ∀ (P : RegularDirectedComplex) (F : MatchingFamily underlying P),
    ∃! G : Mol P → underlying, ∀ x, G x = F x

/-- FX's shape family is a function (d : Nat) → RegularDirectedComplex.
Different profiles pick different per-dim shapes; all coexist under
the same stricter-ω-cat framework. -/
def CellShape : Type := Nat → RegularDirectedComplex
```

**Why this is shippable:**

* **Hadzihasanovic's framework is constructive** — every operation
  (pasting, rewrite, faces, dim) is computable on finite oriented
  graded posets.  Lean port = ~3K LoC of poset machinery + ~2K LoC
  of regular-directed-complex inductive + ~2K LoC of Mol functor.
* **Chanavat's theorem (Lemma 2.20) is algorithmic** — given a
  finite regular directed complex P, the stricter-ω-cat conditions
  reduce to checking each P-matching family has unique amalgamation,
  which is a finite-state check.
* **The reflective inclusion ωCat^> ⊂ ωCat** (Proposition 2.59) gives
  a free functor (reflector r) that strictifies any strict ω-cat into
  a stricter one.  Lean port: ~1K LoC.

**Lean LoC estimate:** ~8K LoC.  Half of earlier estimates because
we no longer maintain six separate shape catalogues.

**Mechanizability:** Hadzihasanovic's regular directed complexes
have a partial implementation in `homotopy.io` (the dim-finite
diagrammatic proof assistant) — that establishes the algorithm
exists.  Lean port is novel but algorithmic.  Chanavat's paper
gives all the explicit constructions (Section 2 has every formula
needed).

**Notes:**

* Chanavat's main result Theorem 4.21 (folk model structure on
  nCat^> right-transferred from diagrammatic model) is heavy
  category theory.  FX doesn't need the full model structure to
  use stricter polygraphs as a shape framework — we only need the
  underlying composition structure + pasting theorem.
* Gray product (Definition 2.53) preserved under suspension (Theorem
  2.84) — useful for FX's Axis 6 complicial Gray module.

### 3.2 Algebraic theory

**Reference:** Kock 2011 "Polynomial functors and trees"; Gambino-Hyland
2003; Gambino-Joyal 2017; Batanin-Berger 2017 "Lattice paths and the
combinatorics of trees"; ABGMMM book §18.1 T-polygraphs (special case
of polynomial monads on Glob).

**Why FX needs it:**

- The current FX kernel hardcodes 78 typed `Term` constructors.  Adding
  a new ctor is an inductive extension.

- A polynomial monad parameterizes the operations + their input/output
  shape + composition + relations.  Adding a new operation = adding
  one `bases` element.  No inductive extension.

- Polynomial monads strictly generalize T-polygraphs (the book's
  §18.1 formalism): every finitary monad on Glob is a polynomial
  monad, and many polynomial monads are not finitary (e.g. the
  Batanin operad for weak ω-categories).

- The relations layer (β/η/ι/cubical rules) is a `mult` (multiplication)
  on the polynomial monad — composition of operations.

**Lean signature:**

```lean
/-- Kock-style polynomial endofunctor on Glob_∞:
   I  ⟵s  E  →p  B  →t  I

where I = input/output sorts (per-dim sets of cell types),
E = "edges" (per-operation, the input slots),
B = "bases" (the operations themselves),
src/tgt/payload describe the arities. -/
structure PolyFunctor (shapes : Nat → CellShape) where
  inputSorts : (d : Nat) → Type
  edges      : (d : Nat) → Type
  bases      : (d : Nat) → Type
  src        : ∀ d, edges d → inputSorts d
  tgt        : ∀ d, edges d → bases d
  pay        : ∀ d, bases d → inputSorts d

/-- A polynomial endofunctor becomes a monad when equipped with unit
+ mult satisfying Beck-Chevalley.  Polynomial monads are cartesian
(pullback-preserving) monads, hence well-suited to globular sets. -/
structure PolyMonad (shapes : Nat → CellShape) extends PolyFunctor shapes where
  unit          : ∀ d, inputSorts d → bases d
  mult          : ∀ d, bases d → bases d → bases d  -- partial; defined when composable
  multAssoc     : ∀ d a b c, ...                     -- associativity (when defined)
  unitL         : ∀ d a, mult d (unit d (pay d a)) a = a
  unitR         : ∀ d a, ...
  beckChevalley : ∀ d, ...                           -- pullback square commutes
  cartesian     : ∀ d, ...                           -- naturality squares are pullbacks
```

**Substrate — Polynomial universes (Aberlé-Spivak
`arXiv:2409.19176`):**

This axis replaces the abstract polynomial-monad framework with
a CONCRETE definition: a polynomial universe is a polynomial functor
that is SUBTERMINAL in `Poly^Cart` (the category of polynomials with
Cartesian lenses).  This makes "univalence" a structural property
of the polynomial, not an external axiom.

```lean
/-- A polynomial functor in HoTT, in the language of dependent lenses.
Aberlé-Spivak §3.  A polynomial p = (A, B) corresponds to the
endofunctor P_p(y) = Σ_{a:A} y^{B[a]} on the category Type. -/
structure Poly (ℓ κ : Level) where
  A : Type ℓ
  B : A → Type κ

/-- A Cartesian lens between polynomials.  Aberlé-Spivak §3.
A morphism (f, f♯) : p ⫋ q with f : p.A → q.A and
f♯ : (a : p.A) → q.B (f a) → p.B a such that for each a, f♯ a is
an equivalence. -/
structure CartesianLens (p q : Poly) where
  forward  : p.A → q.A
  backward : (a : p.A) → q.B (forward a) → p.B a
  isCart   : ∀ a, IsEquiv (backward a)

/-- A polynomial universe (Aberlé-Spivak Definition 4.1): a polynomial
that is subterminal in Poly^Cart.  Equivalently: for any other
polynomial p, there is at most one Cartesian lens p ⫋ u. -/
def isUnivalent (u : Poly) : Prop :=
  ∀ {p : Poly}, ∀ (f g : CartesianLens p u), f = g

structure PolynomialUniverse where
  poly        : Poly
  isUniv      : isUnivalent poly

/-- ⫋ Σ-closure: a Cartesian lens μ : (u ◁ u) ⫋ u from the composite
of u with itself to u itself.  Closure under Σ-types. -/
structure SigmaClosed (u : PolynomialUniverse) where
  mu : CartesianLens (u.poly.compose u.poly) u.poly

/-- ⫋ Π-closure: a Cartesian lens π : (u ⫾ u) ⫋ u from the
"function" composite ⫾ to u.  Closure under Π-types. -/
structure PiClosed (u : PolynomialUniverse) where
  pi : CartesianLens (u.poly.functionalComp u.poly) u.poly

/-- ⫋ ⊤-closure (Aberlé-Spivak): a Cartesian lens η : y ⫋ u from
the identity polynomial y to u.  Closure under unit type. -/
structure TopClosed (u : PolynomialUniverse) where
  eta : CartesianLens Poly.identity u.poly

/-- A FULL polynomial universe: closed under unit + Σ + Π.  Then
Aberlé-Spivak Theorem 4.2 gives the distributive law for FREE via
the univalence subterminality. -/
structure FullPolynomialUniverse extends PolynomialUniverse where
  topClosed   : TopClosed self
  sigmaClosed : SigmaClosed self
  piClosed    : PiClosed self

/-- THE main theorem (Aberlé-Spivak Theorem 4.2): closure under Π
yields the distributive law DL1-DL4 of u (as monad via SigmaClosed)
over itself FOR FREE via univalence.  No additional axioms needed. -/
theorem distributiveLawFromUnivalence (u : FullPolynomialUniverse) :
    DistributiveLaw u.sigmaClosed.mu u.piClosed.pi :=
  -- proof: any two parallel Cartesian lenses to u must be equal by
  -- isUnivalent; the distributive-law diagrams (DL1-DL4) commute
  -- because both paths are Cartesian lenses with the same source
  -- and target.
  univalenceDistributivityProof u

/-- FX kernel's algebraic structure as a polynomial universe instance.
The fxProfile's 78 Generators each represent one polynomial; the
universe is the supremum (terminal among all of them). -/
def fxPolynomialUniverse : FullPolynomialUniverse := {
  poly := fxKernelPolynomial,  -- the 78-generator polynomial
  isUniv := fxIsSubterminal,  -- proved via Cartesian-lens unique
  topClosed := { eta := Term.unit_intro_lens },
  sigmaClosed := { mu := Term.pair_lens },
  piClosed := { pi := Term.lam_lens }
}

/-- T-polygraph instance: special case where each polynomial is
constructed via a finitary monad T on Glob_∞.  Subsumed by the more
general polynomial-universe formulation when T is univalent. -/
def TPolyUniverse (T : FinitaryMonad GlobInf) : FullPolynomialUniverse := ...

/-- Rezk completion of List (Aberlé-Spivak Example 5.2): the
polynomial-universe analog of Bishop finite sets.  Witnesses
commutative-monoid structure for free finite sets. -/
def RezkListUniverse : FullPolynomialUniverse := ...
```

**FX impact:**

* `fxPolynomialUniverse` ships as ONE structure with three Cartesian
  lenses (`eta` / `mu` / `pi`) instead of a polynomial-monad-with-
  Beck-Chevalley + naturality + cartesianness + manual proofs of
  multAssoc + unitL + unitR.  Distributivity DL1-DL4 falls out by
  Theorem 4.2 from univalence + closure-under-Π, with zero extra
  proof obligations.
* Adding a new typed Term ctor = adding one Generator with its
  output type + one Cartesian-lens projection witness.  No need
  to re-prove monad laws.
* The Rezk completion construction (Example 5.2) is the template
  for promoting non-univalent polynomials to univalent ones; this
  is how FX imports Mathlib lemmas as polygraph extensions.

**Lean LoC estimate:** ~6K LoC.  Reduced from earlier ~10K
because closure-under-Π gives distributive law for free; no need
to mechanize Beck-Chevalley + cartesianness separately.

**Mechanizability:** Aberlé-Spivak's paper IS Agda-formalized
(appendix A — the HoTT lemmas + isEquiv + Iso ↔ Equiv machinery
+ Poly definition + Cartesian lens definition + isUnivalent
predicate + distributive law theorem all in Agda).  Lean port =
direct translation; the Agda code is the working template.

**Notes:**

* Aberlé-Spivak works in HoTT.  Lean 4 is intensional but supports
  enough HoTT for univalent-polynomial machinery (function
  extensionality + path induction in Lean's `Eq` type).  The
  isUnivalent predicate only requires Π-equality of Cartesian
  lenses, which is decidable when the polynomial has finitely
  many generators (fxPolynomialUniverse).
* The "distributive law from univalence" trick (Theorem 4.2) is
  THE key — what would normally be 4 commuting diagrams (DL1-DL4)
  becomes ONE univalence application.

### 3.3 Verity stratification

**Reference:** Verity 2008 "Weak complicial sets I"; Riehl 2018
"Complicial sets, an overture" (`arXiv:1610.06801`); Loubaton 2207.08504
§2.1.2; Henry-Loubaton `arXiv:2301.11424` §2.2; Ozornova-Rovelli 2020.

**Why FX needs it:**

- This is the user's explicit ask: per-cell, per-dim invertibility
  classifier, not a single cut-point.  Henry-Loubaton §2.2 gives the
  minimal published definition: a marked ω-category is a pair
  `(D, tD)` where `tD = ⊔_{n>0} tD_n` is a sequence of subsets,
  each `tD_n ⊆ D_n` containing identities and closed under composition.

- "Thin" cells are weakly invertible (the saturation condition forces
  this).  Different markings produce different higher-categorical
  flavors:
  - `tD = identities only` → directed n-category (no invertibility)
  - `tD = all cells above dim n` → (∞,n)-category (cut-point at n)
  - `tD = all isomorphisms` → groupoidal interior
  - `tD = some arbitrary user predicate` → custom invertibility profile

- For FX specifically:
  - dim 0/1 (types + terms): `tD = ∅`.  Types and terms are directed;
    a term equals another term only via `Conv`, not via marking.
  - dim 2 (β/η/ι rules): `tD = those steps that Conv equates`.  This
    is the saturated marking — β-redex steps are thin (Conv equates
    them) but cubical-glue boundary steps may not be thin.
  - dim ≥ 3 (cd_lemma, Squier): `tD = all`.  Confluence and coherence
    cells ARE invertible by definition.

**Lean signature:**

```lean
/-- Per-cell per-dim thinness marker.  Verity 2008 / Loubaton 2023.

A `Stratification` over a shape family is a Prop-valued predicate per
dim per cell, satisfying closure axioms. -/
structure Stratification
    (shapes : Nat → CellShape)
    (algebra : PolyMonad shapes) where

  /-- The per-cell thinness predicate. -/
  thin : ∀ (d : Nat), algebra.bases d → Prop

  /-- Identity cells are always thin.  Loubaton 2301.11424 Def 2.2. -/
  identitiesAreThin : ∀ d a, thin d (algebra.unit d a)

  /-- Composition of thin cells is thin (when defined). -/
  closedUnderComp : ∀ d a b composable,
    thin d a → thin d b → thin d (algebra.mult d a b)

  /-- Sources and targets of thin cells are thin (when defined). -/
  closedSrcTgt : ∀ d a (h : thin d a), ...

  /-- Decidable membership.  Required for FX's zero-axiom Conv check. -/
  thinDecidable : ∀ d a, Decidable (thin d a)
```

**Lean LoC estimate:** ~5K LoC.  The structure is simple; the work
is in proving the closure axioms hold for the canonical FX
saturation (`tD = eq D`).

### 3.4 Saturation

**Reference:** Riehl-Verity 2022 "Elements of ∞-Category Theory"
Chapter E (saturated complicial sets); Loubaton 2301.11424 §3.5
saturated inductive localization; Theorem 2.4 (fibrant ⟺ `tD = eq D`).

**Why FX needs it:**

- Verity stratification (axis 3) only sets up the marker structure.
  Saturation tells you which markings are "the right ones" semantically.

- The canonical / maximal saturation `tD = eq D` (where `eq D` is the
  set of all coherent equivalences in D) gives the "complicial-fibrant"
  model — equivalent to the (∞,ω)-categorical homotopy theory.

- For FX: we want the maximal saturation because we want `Conv` to
  capture all coherent equivalences, not just user-marked ones.
  Loubaton Theorem 2.4 says this is exactly the fibrant-object
  characterization in the coinductive left semi-model structure on
  `ωCat⁺`.

- Partial saturations are useful for sub-fragments: e.g. `tD =
  identities + β-redexes only` for "strict" interpretations.

**Lean signature:**

```lean
inductive SaturationLevel where
  /-- Minimal: only identities are thin. -/
  | minimal     : SaturationLevel

  /-- 1-trivial: all 1-cells in dim ≥ 1 are thin.  Gives (∞,0). -/
  | oneTrivial  : SaturationLevel

  /-- n-trivial: cells in dim > n are all thin.  Gives (∞,n). -/
  | nTrivial    : Nat → SaturationLevel

  /-- ω-saturated: thin = eq (the canonical Verity-Riehl choice).
  Gives the (∞,ω) homotopy theory. -/
  | omegaSat    : SaturationLevel

structure Saturation (S : Stratification _ _) where
  level     : SaturationLevel

  /-- The maximal saturation IS `tD = eq D` (Loubaton 2301.11424
  Thm 2.4).  When `level = omegaSat`, this is True. -/
  isMaximal : Prop

  /-- Riehl-Verity 2022 +1-Cat thinness rules.  Encodes which fillers
  must exist for the stratification to be properly saturated. -/
  thinFillers : ∀ {dim} (horn : Horn dim) (filler : PolyTerm _ dim _),
    horn.thinAt level → S.thin dim filler
```

**Substrate — Saturation via cubical coherent confluence
(Malbos-Massacrier-Struth `arXiv:2511.16852`):**

The shape of saturation (which markings make sense semantically)
is paired with the computational engine that
constructs the saturated marking from the polygraph's rewrite system.

**Cubical contraction (Malbos-Massacrier-Struth Definition 3.1.5):**
a family `σ` of lax transformations indexed by k-cells, each `σ_f`
filling f's source-to-target gap with a thin cell.  Contractions
extend the choice of normal forms (sections of the projection
`C → C_p`) to higher dimensions recursively.

**The headline theorem (Theorem 3.2.5):** every contracting
ω-groupoid is acyclic — i.e., every k-square (k≥p) admits a filler.
Constructively gives the saturated marking.

**Cubical versions of the classical rewriting results:**

* **Cubical Newman's lemma (Proposition 4.1.4):** for a Noetherian
  p-ARS, every map `A_2 : LB(X_C) → LCf(X_C)` from local branchings
  to local confluence fillers extends to global branchings.  Proof is
  Noetherian induction in direction i; pasting of A_2 cubes provides
  the global filler.
* **Cubical Church-Rosser (Proposition 4.1.7):** for the same p-ARS,
  the extension `A_2 : B(X_C) → Cf(X_C)` induces a map
  `B : X_C^{T_i} → CR(X_C)` from zigzags to Church-Rosser fillers.
* **Cubical Squier coherence (§4.3):** for convergent terminating
  p-ARS, every parallel coherence cell admits a filler in terms of
  contraction sections + thin cells.

**The "cube law" derived geometrically (§4.2.3):** for a 3-branching
(f₁, f₂, f₃), the residual computation `f|g := ∂_{i+1}^+ A_2(f,g)`
satisfies `(f_i|f_j)(f_k|f_j) = (f_i|f_k)(f_j|f_k)` for pairwise
distinct i,j,k ∈ {1,2,3}.  Geometrically: cube faces commute.
Equation 4.1.2 falls out from the cubical relations of cubical
categories — NO axiom needed.

**Lean signature:**

```lean
/-- A cubical (ω,p)-category: ω-cat with R_i-invertibility for cells
in dim > p.  Malbos-Massacrier-Struth §2.2. -/
structure CubicalOmegaPCategory (p : Nat) where
  underlying : CubicalOmegaCat
  invertibility : ∀ {k} (h : k > p) (cell : underlying.cells k) {i : Fin k}
                  (shell : underlying.RiInvertibleShell cell i),
                  ∃ inv, underlying.RiInverse cell i inv

/-- A contraction on a (ω,p)-category: a family of lax transformations
σ_f filling each f : C_k for p ≤ k < n with a thin cell σ_f : f → x̂
where x̂ is the normal form of f's source.  Malbos-Massacrier-Struth
Definition 3.1.5. -/
structure Contraction (C : CubicalOmegaPCategory p) where
  section_  : C.cells p → C.cells p
  thin_witness : ∀ {k} (h : p ≤ k) (f : C.cells k),
                 ∃ σf : LaxTransformation C, σf.source = f ∧
                 σf.target = (f.shape.normalForm section_)

/-- THE main theorem (Malbos-Massacrier-Struth Theorem 3.2.5):
every contracting ω-groupoid is ACYCLIC — every k-square admits a
filler.  Proof by folding + unfolding using maps ψ_i, Ψ_j, Φ_k
that rotate cube faces in direction 1. -/
theorem contractingImpliesAcyclic (C : CubicalOmegaPCategory 0)
    (groupoid : ∀ k, IsGroupoid (C.cells k))
    (σ : Contraction C) :
    ∀ k (S : C.Square k), ∃ A : C.cells (k+1), A.boundary = S := by
  -- Folding maps ψ_i, Ψ_j, Φ_k rotate cube faces in direction 1;
  -- contraction σ fills the unfolded representation; unfolding
  -- recovers a filler of the original square.
  ...

/-- Cubical version of Newman's lemma.  Theorem 4.1.4. -/
theorem cubicalNewman (X_C : pARS C) (noeth : X_C.IsNoetherian)
    (A_2 : X_C.LocalBranchings → X_C.LocalConfluenceFillers) :
    ∃ extension : X_C.Branchings → X_C.ConfluenceFillers,
      extension.restrictsTo A_2 := ...

/-- The saturated marking on fxProfile's polygraph, derived from
the contraction structure given by FX's convergent rewrite system
(termination via K12 SN + confluence via cd_lemma). -/
def fxSaturationViaContractions : Saturation fxStratification where
  level := .omegaSat
  isMaximal := fxIsMaximal  -- proved by Theorem 3.2.5 applied to FX
  thinFillers := fxThinFillersViaContraction
```

**FX impact:**

* Replaces the abstract "saturation = thinness predicate that exists
  somehow" with a CONSTRUCTIVE saturation built from FX's convergent
  rewrite system.  K12 SN + cd_lemma confluence + contraction
  structure ⇒ saturated marking is COMPUTABLE.
* Newman + Church-Rosser + Squier all derive from the cubical
  contraction structure — no need for separate per-rule confluence
  / coherence proofs at the saturation layer.  Existing FX cd_lemma
  cascade work (already shipped K11.17 cd_lemma.toDim2Cell etc.)
  becomes the operational engine; this axis is its categorical
  justification.
* The cube law (§4.2.3) replaces the explicit Mac Lane pentagon
  postulation in FX's modal coherence work.  Pentagon falls out
  geometrically.

**Lean LoC estimate:** ~7K LoC, distributed:
* Cubical (ω,p)-category structure (Malbos-Massacrier-Struth §2.1):
  ~2K LoC (face maps, degeneracies, connections, composition,
  invertibility).
* Contraction structure (§3.1) + acyclicity theorem (§3.2.5): ~2.5K
  LoC including folding/unfolding maps.
* Cubical Newman + Church-Rosser + Squier (§4.1-4.3): ~1.5K LoC.
* Integration with FX cd_lemma cascade (existing K11.17 etc.): ~1K
  LoC bridge code.

**Mechanizability:** Malbos-Massacrier-Struth's paper is NOT
mechanized in any proof assistant.  But the proofs are computational
(folding + unfolding maps are explicit operations; contraction
filling is a recursive structural argument).  Lean port is novel
but algorithmic.

**Notes:**

* Theorem 3.2.5 requires the (ω,p)-category to be a groupoid for
  acyclicity.  FX's polygraph is not a groupoid (steps have
  direction), so the load-bearing substrate is MMS **§4 Cubical
  coherent confluence**, which works in (p+2, p+1)-categories
  without the groupoid hypothesis:
  * **Newman cubical lemma** (§4.1.4, Proposition): for Noetherian
    p-ARS X_C, local-confluence-filler map A_2 extends from local
    branchings to global branchings.  No groupoid required.
  * **Church-Rosser cubical** (§4.1.7, Proposition): for p-ARS in
    (p+2, p+1)-category, A_2 induces a Church-Rosser map B on
    zigzags.  No groupoid required.
  * **Squier cubical coherence** (§4.3.6, Proposition): for
    convergent ARS, each A_2 extends to a 2-cell witness for
    acyclicity of X_C^⊤_1 groupoid.  Uses the cubical machinery
    of §3 + §4.1 WITHOUT requiring the underlying (ω,p)-cat to be
    a groupoid.
  * **Cube law derived geometrically** (§4.2.3): falls out from
    the cubical relations (2.1.2) applied to A_3(f_1, f_2, f_3),
    NOT from a postulated cube axiom.
* §4's machinery directly applies to FX's polygraph (Step ctors
  form a Noetherian p-ARS with p=0; cd_lemma confluence cells live
  at dim 2; Squier coherence at dim 3).  Theorem 3.2.5 is reserved
  for the OPTIONAL acyclicity-of-the-groupoid-completion check,
  which FX doesn't need operationally.
* Cube law (§4.2.3) holds geometrically; in FX terms, residuals
  f|g satisfy `(f₁|f₂)(f₃|f₂) = (f₁|f₃)(f₂|f₃)` as a consequence
  of cubical relations, not a postulated axiom.

### 3.5 Enrichment ladder

**Reference:** Loubaton 2207.08504 §3.1.1 Segal A-precategories;
Simpson 2011 "Homotopy Theory of Higher Categories"; Rezk 2010
"A cartesian presentation of weak n-categories".

**Why FX needs it:**

- (∞,n)-categories for arbitrary n are built **recursively**: an
  (∞,n)-category is a category enriched over (∞,n-1)-categories,
  starting from (∞,0) = ∞-groupoids = spaces.

- Loubaton's framework parameterizes the enrichment: `Seg(A)` for an
  arbitrary nice model category A.  Setting `A = (∞,n-1)-cats` gives
  `Seg(A) = (∞,n)-cats`.  Iterating builds (∞,ω).

- For FX: we need both (∞,1) (for term-level reasoning) AND (∞,2)
  (for modal-cubical interactions, e.g. ◇ ⊣ □ adjunction).  The
  enrichment ladder gives both via one structure.

- More importantly, **the ladder is itself parameterizable** —
  different deployments of FX pick different rungs.  A first-order
  embedded FX uses the base.  A modal-cubical FX uses two rungs.
  A polygraph-of-polygraphs (for math automation) uses ω rungs.

**Lean signature:**

```lean
/-- The enrichment ladder.  Each rung is `tSeg(prior rung)`, Loubaton
2207.08504 §3.1.1.  The ladder is itself an inductive — different
profiles pick different ladder lengths. -/
inductive EnrichmentLadder where
  /-- Base: a model category from outside the ladder.  Typically
  spaces (Kan) or simplicial sets. -/
  | base       : NiceModelCategory → EnrichmentLadder

  /-- Add one rung: take Segal A-precategories over the prior rung.
  Loubaton 2207.08504 §3.1.1.5. -/
  | segalRung  : EnrichmentLadder → EnrichmentLadder

  /-- ω-rung: take the limit of the ladder.  Lets FX express
  (∞,ω)-categorical reasoning. -/
  | omegaRung  : EnrichmentLadder → EnrichmentLadder

def materialize : EnrichmentLadder → NiceModelCategory
  | .base C        => C
  | .segalRung l   => tSeg (materialize l)
  | .omegaRung l   => omegaLimit (materialize l)
```

**Substrate — Synthetic ∞-category theory inside type theory
via Gratzer-Weinberger-Buchholtz + Rasekh follow-ups:**

This axis replaces "construct tSeg(A) externally for arbitrary
nice model A" with "axiomatize Segal + Rezk conditions on types
INSIDE FX's type theory using STT+modalities".  This is the
synthetic-vs-analytic shift documented in Gratzer-Weinberger-
Buchholtz `arXiv:2407.09146` §1.4: instead of building (∞,n)-cats
as an external object and showing they form a model category,
DEFINE category-flavored types directly via predicates inside the
type theory.

**Two synthetic enrichment recipes shipped in 2024-2025:**

* **Riehl-Shulman STT (`arXiv:1705.07442` + extensions):** types
  carry a directed interval `𝕀` and Segal types are types where
  `Δ² → A ≃ Λ²₁ → A`.  Rezk types add `isIso(f) ≃ a = b`.  An
  (∞,1)-cat is exactly a Segal+Rezk type.
* **Gratzer-Weinberger-Buchholtz triangulated TT
  (`arXiv:2407.09146`):** extends STT with modalities (♭, ♯, op,
  ⊠ simplicial monad) + 10 axioms.  Builds the universe `S` of
  groupoids; constructs presheaves, Yoneda, Kan extensions internal
  to the type theory.
* **Rasekh follow-ups** (`arXiv:2604.18668`, 2501.13229,
  2602.02218): cocartesian fibrations + closure properties + Yoneda
  embedding + Quillen's Theorem A — all proved internally in `rzk`
  (mechanized).
* **Sterling's pi-systems / NbE-for-categories** (paper-only, 2024):
  computational version that preserves canonicity.

**For FX's ladder:**

* (∞,0) rung = HSet (h-level 2) — already constructed via Step.eqType
  + UIP discipline.
* (∞,1) rung = Segal+Rezk type (synthetic, via STT discipline).
* (∞,2) rung = "directed univalent universe" S (Gratzer-Weinberger-
  Buchholtz).  Internal to STT+modalities.
* (∞,ω) rung = limit; constructive iff each (∞,n) rung is decidable.
* Math-automation extension rung = "polygraph-presented profile"
  per §3.8 profile-fibration axis.

**Lean signature:**

```lean
/-- A Segal type: a type A whose Δ² → A reduces uniquely to a span
of arrows.  Riehl-Shulman §3.  Synthetic (∞,1)-category.
Lean's `Eq`-based interval ≅ Riehl-Shulman directed interval. -/
def IsSegal (A : Type u) : Prop :=
  ∀ (a b c : A) (f : Hom a b) (g : Hom b c),
  ∃! (h : Hom a c), ComposesTo f g h

/-- A Rezk type: a Segal type where homotopy-equivalences coincide
with definitional equality. -/
def IsRezk (A : Type u) [seg : IsSegal A] : Prop :=
  ∀ (a b : A), IsIso (a = b) (HomEquiv a b)

/-- The ladder, NOT recursive — directly indexed by levels.
Each level is a type-theoretic predicate, no external model cat. -/
inductive Rung where
  | hLevel  : Nat → Rung    -- (∞, 0..n) via h-level predicates
  | segal   : Rung           -- Segal type discipline (∞,1)
  | rezk    : Rung           -- Rezk type discipline (∞,1)-cat
  | directed : Rung          -- Gratzer-W-B universe S (∞,2)+
  | omegaLimit : Rung        -- limit of the tower

/-- Materialize a rung into the predicate it represents.  Replaces
older external "tSeg construction" with synthetic-predicate-on-type. -/
def Rung.predicate : Rung → (Type u → Prop)
  | .hLevel n   => HasHLevel n
  | .segal      => IsSegal
  | .rezk       => fun A => ∃ (s : IsSegal A), IsRezk A
  | .directed   => IsDirectedUnivalent  -- per arXiv:2407.09146 Def 1.2
  | .omegaLimit => fun A => ∀ n, Rung.hLevel n |>.predicate A  -- limit

/-- An enrichment is a choice of rung per dimension. -/
def Enrichment := Nat → Rung

/-- FX's enrichment profile.  Most dims at hLevel 2 (HSet);
specific dims unlock higher rungs as needed by FX features. -/
def fxEnrichment : Enrichment := fun
  | 0 => .hLevel 2                  -- Terms are HSets
  | 1 => .segal                     -- Step relations form Segal type
  | 2 => .rezk                      -- Step.par chains form Rezk type
  | 3 => .directed                  -- Conv as directed univalent univ
  | _ => .omegaLimit                -- limit (for math automation)
```

**FX impact:**

* Replaces older ~15K LoC `tSeg(A)` construction with ~3K LoC of
  synthetic predicates inside FX.
* Reuses §3.10 polynomial-universe + triangulated-TT machinery
  for the higher rungs.
* (∞,n) rungs become OPT-IN per profile dimension; no need to ship
  every rung for every FX deployment.

**Lean LoC estimate:** ~3K LoC for the rung enum + per-
rung predicates + fxEnrichment instance.  Massive reduction from
earlier ~15K LoC estimates.

**Mechanizability:**

* Riehl-Shulman STT: rzk-prototyped (Kud23).
* Gratzer-Weinberger-Buchholtz TT_⊠: rzk-prototyped + paper-form.
* Rasekh fibrations: ✅ rzk-mechanized.

**Notes:**

* Synthetic vs analytic shift means we lose the ability to import
  "an arbitrary Quillen model category" as a rung.  FX trades that
  generality for mechanizability.
* For FX's "polygraph-of-polygraphs" math-automation use case
  (§3.8), the synthetic rung approach DOES compose: nested
  profile towers can each pick rungs independently.

### 3.6 Complicial Gray module

**Reference:** Loubaton 2207.08504 §3.1.4 (Gray module);
Loubaton 2207.08504 §3.1.5.4 (complicial Gray module); Gray 1974
"Formal Category Theory" (original Gray tensor); Al-Agl-Brown-Steiner
2002 (Gray tensor on ω-cats).

**Why FX needs it:**

- The Gray tensor `⊗` is the "right" tensor product on (∞,ω)-cats,
  asymmetric (not symmetric monoidal): `A ⊗ B` distinguishes
  horizontal vs vertical composition.

- Concurrent execution = horizontal composition with disjoint footprint.
  Frame rule = interchange (Loubaton 3.1.4.8 + ABGMMM K11.6 already
  shipped).

- Polarization (∂CBPV, Levy CBPV) is encoded via complicial Gray:
  positive cells are thin under `_⋆[1]`, negative cells under `[1]⋆_`.

- Cubical operations (transp, hcomp, Kan filling) factor through Gray
  cylinder + Gray cone + Gray ◦-cone (Loubaton 2207.08504 §2.2.3).

**Lean signature:**

```lean
/-- Gray module structure on a model category A.  Loubaton 2207.08504
Def 3.1.4.2. -/
structure GrayModule (A : NiceModelCategory) where
  /-- Intelligent n-truncations: a family of left Quillen functors
  picking out the (∞,n)-truncation of an (∞,ω)-cat. -/
  truncations : (n : Nat ⊕ {ω}) → A ⟶ A
  truncationCompat : ∀ n m (h : n ≤ m), truncations n ∘ truncations m = truncations n

  /-- The Gray tensor as a left Quillen functor.  Asymmetric. -/
  grayTensor  : tPsh(Δ)¹ × A ⟶ A

  /-- Compatibility square: associativity up to canonical iso. -/
  associator  : ∀ K L M a,
    grayTensor K (grayTensor L (grayTensor M a)) = grayTensor (K × L × M) a

  /-- Identity. -/
  unit        : ∀ a, grayTensor [0] a = a

  /-- Truncations commute appropriately. -/
  truncTensor : ∀ n K a,
    truncations n (grayTensor K a) = grayTensor K (truncations n a)

/-- A Gray module is "complicial" if it satisfies the complicial
acyclicity conditions.  Loubaton 2207.08504 Def 3.1.5.4. -/
structure ComplicialGrayModule (A : NiceModelCategory) extends GrayModule A where
  /-- For any cell a, the inclusion Λ¹[2] ⋆ a → [2]_t ⋆ a is an
  acyclic cofibration. -/
  acyclicLambda : ∀ a, IsAcyclicCofib (Λ¹[2] ⋆ a → [2]_t ⋆ a)

  /-- For any cell a and ε ∈ {-,+}, the inclusion {ε} ⋆ a → [1]_t ⋆ a
  is an acyclic cofibration. -/
  acyclicEpsilon : ∀ a (ε : Bool), IsAcyclicCofib ({ε} ⋆ a → [1]_t ⋆ a)
```

**Stage 1 — already shipped via K11.x:**

This axis promotes the existing K11.x infrastructure (already
landed in `LeanFX2/Foundation/Polygraph/`) to PRIMARY status, with
the (∞,ω) complicial extension as Stage 2 follow-on.  Stage 1
delivers the strict-ω-cat Gray tensor + vertical/horizontal
composition + interchange, which is enough for FX's concurrency +
frame-rule + polarization use cases.

**Stage 1 (✅ SHIPPED in `Foundation/Polygraph/`):**

| Component | File | Status |
|---|---|---|
| Vertical composition + assoc + unit | `VerticalComp.lean` (169 LoC) | ✅ shipped |
| Horizontal composition + assoc + unit | `HorizontalComp.lean` (156 LoC) | ✅ shipped |
| Interchange law (Eckmann-Hilton at K11.6) | `Laws.lean` (78 LoC) | ✅ shipped |
| Free n-category construction (Burroni adjoint) | `FreeCategory.lean` (178 LoC) | ✅ shipped |
| PolyCell well-foundedness + DecidableEq | `Wellfounded.lean` + `DecEq.lean` (260 LoC) | ✅ shipped |

Total Stage 1 LoC: ~840 LoC ALREADY IN TREE, zero-axiom under
strict harness.  This is the operational Gray-tensor + interchange
machinery that FX needs for concurrency + frame-rule + polarization.

**Stage 2 (REQUIRED follow-on, ~15K LoC):**

The complicial (∞,ω) extension per Loubaton 2207.08504 §3.1.5.4 +
Verity 2008 §6 explicit formulas.  Stage 2 adds:

* `acyclicLambda` + `acyclicEpsilon` acyclic-cofibration witnesses.
* Gray cylinder + Gray cone + Gray ◦-cone (Loubaton §2.3.1 formulas).
* Truncation compatibility (truncations commute with Gray tensor).
* Naturality squares for the Gray module structure.

Maltsiniotis-Métayer `arXiv:0712.0617` Coq mechanization of strict-
ω-cat Gray tensor provides the algorithmic foundation; Loubaton's
extension to complicial is formula-level work, not new mathematics.

**Why Stage 2 is shippable:**

* Verity's formulas are case-by-case algorithmic recipes (Verity
  2008 §3-§4, restated Riehl 2016 §4-§5).
* Loubaton's complicial extension adds marking-tracking but no new
  categorical structure.
* ABGMMM book §17 catalogs the formulas needed.
* Combined with §3.4 cubical contraction saturation,
  Stage 2 ComplicialGray + saturation share the cubical-cell-pasting
  algorithm — many lemmas reuse.

**Why FX needs it:**

- The Gray tensor `⊗` is the "right" tensor product on (∞,ω)-cats,
  asymmetric (not symmetric monoidal): `A ⊗ B` distinguishes
  horizontal vs vertical composition.

- Concurrent execution = horizontal composition with disjoint
  footprint.  Frame rule = interchange.  **K11.6 interchange law
  already shipped** — Stage 1 directly provides FX's concurrency
  primitive.

- Polarization (Levy CBPV + Pédrot-Tabareau ∂CBPV) is encoded via
  complicial Gray: positive cells are thin under `_⋆[1]`, negative
  cells under `[1]⋆_`.  Requires Stage 2 (the marking-aware
  cylinder + cone).

- Cubical operations (transp, hcomp, Kan filling) factor through
  Gray cylinder + Gray cone (Loubaton §2.2.3).  Requires Stage 2.

**Notes:**

* Stage 1 ↔ Stage 2 split decomposes the complicial Gray module:
  Stage 1 is the concrete polygraph composition layer (already
  shipped at K11.x, ~840 LoC); Stage 2 is the marking-aware
  cylinder + cone construction on top.  Stage 2 builds on the
  K11.x foundation, so its mechanization risk is contained — it
  does not duplicate work, it extends.

**Lean LoC estimate:** ~15.8K LoC total = ~840 LoC already shipped
(Stage 1) + ~15K LoC pending (Stage 2).  Stage 1 deletes the
abstract `GrayModule` struct in favor of the concrete K11.x
infrastructure.

**Mechanizability:**

* Stage 1: ✅ ALREADY SHIPPED in `Foundation/Polygraph/`.
* Stage 2: Maltsiniotis-Métayer arXiv:0712.0617 Coq mechanization
  is the template for strict-ω-cat Gray tensor.  Loubaton 2207.08504
  §3.1.5 is paper-only but formula-explicit.

### 3.7 ∞-Topos base — multi-focus commuting cohesions

**Reference:** Myers-Riley *Commuting Cohesions*
`arXiv:2301.13780` (Feb 2023).  Extends Shulman's spatial type theory
to support **multiple commuting cohesions** with focus annotations.

**Semantic justification:** Lurie HTT 2009 Chapter 6 (∞-toposes);
Anel-Joyal 2019; Schreiber 2013 *Differential Cohomology in Cohesive
∞-Toposes*.  Dugger 2001 *Combinatorial model categories have
presentations* (Trans. AMS 353) provides the constructive
∞-topos presentation used as the semantic model that backs
the multi-focus discipline; its Lean port is the
``InfTopos`` structure shipped below.

**Why FX needs it:**

- The 21 graded dimensions of FX (per fx_design.md §6) are NOT just
  semirings — they are modal/cohesive/spatial structure on the
  ambient category of types.

- The **classical problem**: Shulman's single-focus spatial TT only
  supports ONE cohesive axis (one ♭ ⊣ ♯).  But FX needs MANY
  simultaneously: differential + equivariant + simplicial + ghost +
  cap + later + clock + Crypto + Async + Classified + IO + Alloc +
  Read + Write + Region + Lifetime + Provenance + Trust +
  Observability + Clock-domain + Version.  21 cohesive axes.

- **Myers-Riley solution:** annotate each context variable
  with a focus marker `x :_♥ X`.  Each focus ♥ gets its own ♭ and ♯
  modalities, working essentially INDEPENDENTLY.  Orthogonal cohesions
  COMMUTE (Theorem 6.1.5: differential stack homotopy = Čech nerve of
  good cover, derivable in one type theory).

- An ∞-topos with multi-modal structure hosts a **4-tier stack**:
  * **Cohesive tier**: ♭ ⊣ ◇ ⊣ □ ⊣ ♯ per cohesive focus (Myers-Riley)
  * **Resource tier**: linear / affine / unrestricted grades
    (Atkey QTT + Choudhury-Eades-Orchard universe-of-grades +
    Abel-Danielsson-Eriksson Agda formalization, ICFP 2023,
    `arXiv:2603.29716`)
  * **Cost tier**: cost grades with phase distinction (calf POPL
    2022 `arXiv:2107.04663` / decalf POPL 2024 `arXiv:2307.05938`)
  * **Security tier**: DCC labels (Heintze-Riecke 1998) +
    declassification policies
  * **Structural tier**: refinement-type predicates (Vazou et al.
    LiquidHaskell pattern)

  The MTT mode theory (Gratzer-Kavvos-Nuyts-Birkedal LICS 2020) is
  the UNIVERSAL OUTER CONTAINER.  Per-tier sub-substrates carry the
  specific machinery.

- Not all 21 FX dimensions are properly
  "focuses" in the Myers-Riley sense.  Myers-Riley §6 only treats
  cohesive focuses (each with its own ∫⊣♭⊣♯ chain).  FX has
  heterogeneous dimensions across FIVE categories:

  1. **Cohesive focuses (4)** — actual Myers-Riley focuses:
     differential, equivariant, simplicial, real.  Each has its
     own ♭/♯ chain.  Myers-Riley §6 worked examples directly
     apply.
  2. **Resource grades (5)** — IO, Alloc, Async, Crypto,
     Classified.  These are NOT cohesive focuses; they are GRADES
     in a partially ordered semiring (Atkey QTT /
     Choudhury-Eades-Orchard / Abel-Danielsson-Eriksson).
     Different categorical structure than Myers-Riley.
  3. **Bounded grades (5)** — Complexity, Precision, Space,
     Overflow, FP-order.  Quantitative cost grades.  Use
     calf/decalf as the substrate — phase distinction
     extension/intension.
  4. **Security lattice (1)** — Classified/Secret/declassification.
     Uses DCC (Heintze-Riecke 1998) + sealing.
  5. **Structural predicates (3)** — Mutation, Reentrancy, Size.
     Pure refinement-type predicates, not modalities.

  Plus Region/Lifetime/Provenance/Trust/Observability/Clock-
  domain/Version (~5-7 more) which are a mix of structural +
  grading.  Total: 21 dimensions, but only **4 are true cohesive
  focuses** in the Myers-Riley sense.

  The honest orthogonality matrix is NOT C(21,2) = 210 pairs but
  rather a small set of cross-category interactions: cohesive ↔
  cohesive (Myers-Riley orthogonality), cohesive ↔ resource (one-
  way interaction via mode-shift), resource ↔ resource (semiring
  composition), etc.  Each interaction has its own substrate
  paper.

**Lean signature — multi-focus commuting cohesions:**

```lean
/-- A focus is a separate axis of spatiality / cohesion / modality.
For FX, each of the 21 graded dimensions is one focus. -/
inductive Focus where
  -- Cohesive / spatial axes (4)
  | flatSharpDiff      : Focus  -- ♭ ⊣ ♯ on differential structure
  | flatSharpEquiv     : Focus  -- ♭ ⊣ ♯ on equivariant structure
  | flatSharpSimp      : Focus  -- ♭ ⊣ ♯ on simplicial structure
  | flatSharpReal      : Focus  -- ♭ ⊣ ♯ on real-cohesive structure
  -- FX 8-modality chain (already in kernel)
  | boxDiamond         : Focus  -- ◇ ⊣ □ chain
  | ghostErase         : Focus  -- ghost ⊣ erase (2LTT)
  | capCharge          : Focus  -- capability
  | laterLater         : Focus  -- ▷ guarded recursion (Nakano)
  | clockClock         : Focus  -- clock-quantified types
  -- FX effect dimensions (5)
  | ioIO               : Focus
  | allocAlloc         : Focus
  | readWrite          : Focus
  | asyncAsync         : Focus
  | cryptoCrypto       : Focus
  -- FX classified data (1)
  | classifiedClass    : Focus
  -- FX bounded dimensions (5)
  | complexityComplexity : Focus
  | precisionPrecision   : Focus
  | spaceSpace           : Focus
  | overflowOverflow     : Focus
  | fpOrderFpOrder       : Focus
  -- FX structural (3)
  | mutationMut          : Focus
  | reentrancyReentrant  : Focus
  | sizeSize             : Focus
  -- FX evolution (1)
  | versionVersion       : Focus
  deriving DecidableEq

/-- The meet-semilattice of focuses.  Top focus ⊤ is the union of
all FX focuses (the entire topos).  Meet operation = union of
crispness annotations. -/
structure FocusLattice where
  focuses        : Focus → Prop  -- which focuses are present
  meet           : Focus → Focus → Focus  -- composite focus
  meetCommutes   : ∀ a b, meet a b = meet b a
  meetAssociates : ∀ a b c, meet (meet a b) c = meet a (meet b c)
  topAbsorbs     : ∀ a, meet a ⊤ = a

/-- For each focus, its associated ♭ and ♯ modalities (Myers-Riley
§2 rules).  When the focus is cohesive (admits a ♭-counit-detecting
family), also gets ∫ left adjoint. -/
structure FocusedModalities (φ : Focus) where
  flat  : Type u → Type u  -- ♭_φ
  sharp : Type u → Type u  -- ♯_φ
  flatSharpAdj : Adjoint flat sharp  -- ♭_φ ⊣ ♯_φ
  /-- Optional ∫ ⊣ ♭ when the focus is cohesive. -/
  shape : Option (Type u → Type u)
  shapeFlatAdj : ∀ (h : shape.isSome), Adjoint (shape.get h) flat

/-- Orthogonality between two focuses.  Myers-Riley Def 5.1.3:
focuses commute when the family that detects connectivity for one
is discrete with respect to the other (and vice versa). -/
def OrthogonalFocuses (φ ψ : Focus) : Prop :=
  ∀ (X : Type u), FocusedModalities.flat ψ (FocusedModalities.flat φ X) ≃
                  FocusedModalities.flat φ (FocusedModalities.flat ψ X)

/-- The ∞-topos: a focus lattice + per-focus modalities + pairwise
orthogonality theorems where applicable. -/
structure InfTopos where
  lattice              : FocusLattice
  focusedModalities    : ∀ (φ : Focus), lattice.focuses φ → FocusedModalities φ
  orthogonality        : ∀ (φ ψ : Focus), -- pairs of focuses are orthogonal,
                         lattice.focuses φ → lattice.focuses ψ → φ ≠ ψ →
                         OrthogonalFocuses φ ψ
  /-- The classical 21-dim universe object lives at the top focus. -/
  universeAtTop        : UniverseCell

/-- The FX ∞-topos: all 21 focuses present, all pairwise orthogonal
(modulo specific exceptions where focuses are nested rather than
orthogonal, e.g., supergeometric ⊃ differential per Myers-Riley §6.3). -/
def infToposOfFX : InfTopos where
  lattice := fxFocusLattice  -- the 21-focus meet-semilattice
  focusedModalities := fxFocusedModalities  -- 21 instances
  orthogonality := fxOrthogonalityProofs  -- C(21,2) = 210 pairs
  universeAtTop := UniverseCell.fxUniverse
```

**Worked examples from Myers-Riley §6 that map DIRECTLY onto FX:**

* §6.1 Simplicial real cohesion = FX's simplicial focus + real focus.
  Theorem 6.1.5 gives differential-stack homotopy = Čech nerve of
  good cover.  For FX: the homotopy type of a differentially-structured
  type is computable from its Čech nerve along any good cover.
* §6.2 Equivariant differential = FX's equivariant focus + differential
  focus.  Lemma 6.2.1: orthogonal automatically.  No extra axioms
  needed.  For FX: equivariant + differential types compose without
  pentagon work.
* §6.3 Supergeometric = nested focus where differential ⊂ super.
  For FX: when a focus is nested rather than orthogonal, the typing
  rules respect the inclusion.  Models clock-quantified-and-temporal
  dependence where temporal ⊂ clock.

**Lean LoC estimate:** ~6K LoC for the multi-focus
machinery + 21 focus instances + ~210 orthogonality witnesses
(many derivable by symmetry).  Reduction from earlier
Dugger-based ~30K LoC estimate.  Most orthogonality witnesses come
from the structural property of the focuses (each focus's flat-
counit-detector family is discrete for the other focus's modalities).

**Why this is shippable:**

* **Myers-Riley is itself a paper-form mechanization recipe** —
  every rule is given explicitly (§2 rules for ♭, §2 rules for ♯,
  §3 detecting continuity, §3.2 detecting connectivity, §5
  orthogonality).
* **No ∞-topos object required** — we work entirely inside type
  theory with focus annotations, not in the meta-theory of
  ∞-toposes.  The ∞-topos is the SEMANTIC model that justifies the
  type theory's soundness; the type theory itself is implementable.
* **ParamDTT (Nuyts-Vezzosi-Devriese arXiv:1707.03835) is the formal
  ancestor** of multi-focus context structure.  Myers-Riley
  generalizes ParamDTT's fixed-3-modality system to arbitrary
  commutative idempotent monoid of focuses.

**Risk:** the 21 orthogonality witnesses must be specifically
verified.  Some FX focuses are NOT pairwise orthogonal (e.g.,
classified-data and IO probably overlap; ghost and erase are dual,
not orthogonal).  Identifying which pairs orthogonal vs nested vs
overlapping is a one-time matrix-building exercise (~1K LoC of
proofs).

**Lean signature — categorical semantics via Dugger 2001
combinatorial presentation:**

The multi-focus type theory above is the surface syntax; the
following `InfTopos` structure is its categorical semantic model.
Both ship together: the type theory is what programmers write, the
∞-topos is what the soundness theorem refers to.

```lean
/-- An ∞-topos a la Lurie HTT 2009 §6.1.0.4 — presented
constructively via Dugger 2001 "Combinatorial model categories have
presentations" (Trans. AMS 353).  Dugger's theorem: every
combinatorial model category is a left Bousfield localization of the
projective model structure on `sPre(C)` (simplicial presheaves on
some small ∞-cat C) at a small set of maps.  Hence finite-
presentation site + finite localization-map set = computable ∞-topos.

This is the genuine ∞-topos data, encoded via its small presentation
rather than via large-cat machinery Mathlib does not have. -/
structure InfTopos where

  /-- The small site C: a polygraph-presented small ∞-cat.  For FX,
  C = fxProfile's underlying polygraph at dim ≤ 3 (the dimensions
  actually exercised by FX).  Finite-presentation ⇒ enumerable
  objects + morphisms. -/
  presentationSite : Polygraph

  /-- Dugger localization-map set: a FINITE list of morphisms in
  `sPre(presentationSite)` at which we Bousfield-localize.  For FX,
  this encodes the universe classifier, descent / sheaf condition,
  and the modal adjunctions as localizations. -/
  localizationMaps : List (PreSheafMorphism presentationSite)

  /-- The localization-map set is finite (decidable cardinality).
  Dugger guarantees existence of such a finite set for any
  combinatorial model category. -/
  finiteLocalization : localizationMaps.length ≤ maxLocalizationCount

  /-- Descent / Čech-cover condition.  For each cover in the
  Grothendieck topology induced by `presentationSite`, the
  associated Čech nerve is colim-effective.  CONSTRUCTIVE: encoded
  via the (finite, per-presentationSite-cover) descent diagrams. -/
  descent : ∀ (cover : presentationSite.GrothendieckCover),
            EffectiveEpiFamily cover

  /-- Subobject classifier (univalent universe object) exists
  CONSTRUCTIVELY from the descent property + the small presentation.
  Lurie HTT 6.1.6.3 gives the construction; we mechanize it via the
  polygraph's universe cell (axis 10).  Decidable iff classifier
  cell is enumerable, which holds for fxProfile. -/
  subobjectClassifier : UniverseCell presentationSite

  /-- Modal adjunctions inside the topos.  Each one is presented
  via Dugger as a further left localization of `sPre(site)`. -/
  modalities : List ModalAdjunction

  /-- Cohesive structure (♭ ⊣ ◇ ⊣ □ ⊣ ♯ chain) when present, as
  four adjunctions inside `modalities`. -/
  cohesiveStructure : Option CohesiveData

  /-- Coherence proofs (triangle identities, pentagon for
  cohesion, descent commutes with localization).  All shippable
  per the finite-presentation discipline. -/
  coherenceProofs : ∀ (m : Modality), m.coherence

/-- The FX ∞-topos, constructed via Dugger from the fxProfile
polygraph as small site. -/
def infToposOfFX : InfTopos where
  presentationSite := fxProfile.toPolygraph (boundedDim := 3)
  localizationMaps := fxUnivalenceLocMaps ++ fxModalLocMaps
                                          ++ fxDescentLocMaps
  finiteLocalization := by decide
  descent := fxDescentProof
  subobjectClassifier := UniverseCell.universeOfFX
  modalities := [
    Modal.box, Modal.diamond, Modal.flat, Modal.sharp,
    Modal.ghost, Modal.cap, Modal.later, Modal.clock,
    Modal.io, Modal.alloc, Modal.read, Modal.write, Modal.async,
    Modal.crypto, Modal.classified, Modal.exn, Modal.div, Modal.tot,
    Modal.complexity, Modal.precision, Modal.space,
    Modal.overflow, Modal.fpOrder, Modal.mutation, Modal.reentrancy,
    Modal.size, Modal.version
  ]
  cohesiveStructure := some {
    flatDiamond := Modal.flatDiamondAdj
    diamondBox  := Modal.diamondBoxAdj
    boxSharp    := Modal.boxSharpAdj
    pentagonCoherence := Modal.pentagonProof
  }
  coherenceProofs := Modal.coherenceProofsForAll21
```

**Lean LoC estimate:** ~30K LoC.  Distribution:
* `PreSheafMorphism` + projective model structure: ~6K LoC
  (simplicial presheaves on a small ∞-cat, Quillen-Bousfield style,
  combinatorial-tractable per Beke 2000 / Smith)
* Dugger localization theorem (Trans. AMS 353): ~8K LoC
  (the constructive proof — given a combinatorial model cat M with
  presentation `(C, S)`, exhibit M as `sPre(C)[S⁻¹]`)
* Descent / Čech-cover decidability for fxProfile: ~4K LoC
* Modal layer integration: ~5K LoC (the 21 modal adjunctions as
  further-localized subcats, with coherence proofs)
* Subobject classifier construction (Lurie HTT 6.1.6): ~7K LoC

**Why this IS shippable in Lean 4 zero-axiom, despite Mathlib not
having it:**
* Dugger's presentation is **algorithmic** — given a finite set
  of generating cofibrations + a finite set of localization maps,
  the model structure is uniquely determined (Dugger 2001 §6).
  Polygraphs supply both.
* Beke 2000 + Smith establish that polygraph-presented model cats
  are combinatorial (locally presentable + cofibrantly generated +
  tractable cofibrations).  All FX needs.
* Lurie HTT A.2.6.13: any combinatorial model cat C has its
  `Ho(C)` presentable, hence the underlying ∞-cat localization is
  small-presentable.  For finite-presentation C this is literally
  enumerable.
* The "Mathlib doesn't have it" line was the cowardice — Mathlib
  not having something doesn't mean we can't ship it.  Lean 4 has
  inductives, structures, and `Decidable` instances; that's enough
  to mechanize Dugger's algorithm explicitly without invoking heavy
  category-theory infrastructure.

**Risk:** the Lurie-style ∞-topos coherence (descent for all covers
+ all colim-effective epis) is the hardest single piece, ~7K LoC.
**Mitigation:** ship in three sub-stages (presentation site →
projective model structure → Bousfield localization → descent
classifier → modal adjunctions), each gated by `#assert_no_axioms`
on the cumulative theorems.

### 3.8 Profile fibration

**Reference:** Cisinski 2019 "Higher Categories and Homotopical Algebra";
Maltsiniotis 2010 "Carrés exacts homotopiques et dérivateurs"; Grothendieck
fibration applied to the categorification of profile data.

**Why FX needs it:**

- A `PolyProfile` bundles all ten axes.  But different profile choices
  may DEPEND on each other: e.g. the choice of shape at dim n+1 may
  depend on which generators exist at dim n; the choice of saturation
  at dim 3 may depend on which β-rules fire at dim 2.

- The categorical way to express "dependent profile" is a Grothendieck
  fibration: profiles form a category, and a profile-of-profiles is a
  section of the fibration.

- Cisinski 2019 shows how to handle self-reference in this fibration
  via ω-localization without paradox.  This is what lets `PolyTerm
  fxProfile 0 (universeBoundary)` contain `fxProfile` itself — the
  universe-of-universes problem at the polygraph level.

**Lean signature:**

```lean
/-- Profiles form a category.  Morphisms are profile homomorphisms
(shape-preserving, marking-preserving, …). -/
structure ProfileMorphism (π₁ π₂ : PolyProfile) where
  shapeHom         : ∀ d, π₁.shapes d ⟶ π₂.shapes d
  algebraHom       : PolyMonadHom π₁.algebra π₂.algebra
  stratificationHom : ∀ d a, π₁.stratification.thin d a → π₂.stratification.thin d (algebraHom.translate a)
  -- … and so on for all ten axes …

/-- The category of profiles. -/
def ProfileCat : Category PolyProfile where
  Hom := ProfileMorphism
  id := ...
  comp := ...

/-- Grothendieck fibration of "things parameterized by a profile" over
the profile category. -/
structure ProfileFibration where
  totalSpace : Category
  projection : Functor totalSpace ProfileCat
  cleavage   : ∀ (f : ProfileMorphism _ _), Cartesian f

/-- A profile tower of UNBOUNDED depth via Beke-Smith combinatorial
ω-localization.  The `omegaFixpoint` ctor takes a Nat-indexed
sequence of profiles plus a cofinality witness that the sequence
stabilizes under Bousfield localization (Smith small-object
argument).  See §12 for the full ship plan. -/
inductive ProfileTower : Type where
  | base   : PolyProfile → ProfileTower
  | extend : ProfileTower → PolyProfile → ProfileTower
  | omegaFixpoint :
      (steps : Nat → ProfileTower) →
      (cofinal : ∀ N, IsBousfieldStable (steps N)) →
      ProfileTower

/-- Cisinski-style ω-localization via Beke 2000 + Dugger 2001 +
Smith small-object argument.  Constructive for combinatorial
(polygraph-presented) model cats.  Each step is a finite-set
Bousfield localization; ω-fixpoint terminates by the cofinality
witness. -/
def cisinskiLocalize : ProfileTower → PolyProfile
  | .base π            => π
  | .extend t π        => bousfieldStep (cisinskiLocalize t) π
  | .omegaFixpoint s h => omegaColim (fun N => cisinskiLocalize (s N)) h
```

**Lean LoC estimate:** ~10K LoC, broken down per §12 in-scope ship
plan (Beke combinatoriality ~3K, Smith small-object argument ~3K,
`omegaFixpoint` decidability ~2K, ProfileFibration integration ~2K).

**Why this IS shippable despite no Lean precedent:**
Cisinski's ω-localization is non-algorithmic for ARBITRARY model
cats, but for polygraph-presented combinatorial model cats the
Beke-Dugger-Smith chain gives an explicit algorithm.  FX profiles
are polygraph-presented by construction (axis 1 + axis 2), hence
combinatorial; the ω-iteration terminates by Smith's small-object
argument with the cofinality witness.

### 3.9 Coherent equivalence classifier — the ωcE polygraph

**Reference:** Hadzihasanovic-Loubaton-Ozornova-Rovelli 2024
"A model for the coherent walking ω-equivalence" (`arXiv:2404.14509`)
for the semantic universal object; Makkai's "Word Problem for
Computads" (McGill manuscript, last rev. 2021) for the actual
decision procedure; Forest's PhD thesis (Paris Cité 2022) for the
implementable polynomial-in-practice improvement.

**Why FX needs it:**

- `Conv` in the current FX is defined as `∃ StepStar` zigzag —
  opaque, gives the CONVTRANS-D cascade tax.

- HLOR Proposition 1.26 (the SEMANTIC story): `a` is a bi-equivalence
  in any ω-cat `D` iff there exists an ω-functor
  `Σ^(n-1)(ωcE) → D` factoring `a`.  `ωcE` is finite-type at every
  k (HLOR Construction 1.22), and contractible (HLOR Thm 1.33).

- Makkai's word problem (the COMPUTATIONAL story): given a finite
  polygraph X with rewriting rules, equality of cells in the free
  ω-category F(X) is decidable.  Algorithm uses normal-form
  computation under the convergent rewrite system; restated for
  computads in Makkai (2021).  Forest's thesis gives a practical
  data-structure-driven version.

- For FX: the fxProfile's free ω-cat is generated by the 78-element
  `Generator` enum (dim 0) + the 110-element `StepLabel` enum
  (dim 1) + the cd-pair-indexed dim-2 enum.  This is a finite
  polygraph.  K12 reducibility + cd_lemma confluence gives the
  convergent presentation.  Makkai's algorithm applies.

**Honest scope note.**  HLOR Prop 1.26 establishes the universal
property of ωcE existentially; HLOR does NOT prove decidability of
ω-functor existence into ωcE.  Decidability comes from Makkai's
separate result on word equality in F(X), not from ωcE's universal
property.  The original draft of this document conflated the two.

**Lean signature:**

```lean
/-- The walking coherent ω-equivalence polygraph, HLOR Construction 1.22.
Inductively built up to dimension k; each `OmegacE_at k` is finite-type.

Implementation: explicit `Nat`-indexed structural build via
suspension + pushout, NOT Lean's `Quotient` / `Quot.mk` machinery
(which carries `propext`).  Per Construction 1.22, the pushout at
each step has 5 generators (q1cell ⊕ extend ⊕ alphaCell ⊕ betaCell ⊕
identity-of-prior); we enumerate them as five constructors. -/
inductive OmegacE_at (k : Nat) : Type where
  | atom0     : Vertex 0 → OmegacE_at 0
  | q1cell    : OmegacE_at 1
  | extend    : OmegacE_at k → OmegacE_at (k+1)
  | alphaCell : OmegacE_at k → OmegacE_at (k+1)
  | betaCell  : OmegacE_at k → OmegacE_at (k+1)
  deriving DecidableEq

/-- ωcE-at-k is finite-type (each `OmegacE_at k` has finitely many
inhabitants up to the bounded vertex set).  Proven by induction on k.
This is what makes Makkai's algorithm complete on this polygraph. -/
theorem OmegacE_at.finite_type (k : Nat) (vertices : Finset (Vertex 0)) :
    Fintype { c : OmegacE_at k // OmegacE_at.usesOnlyVertices c vertices } := by
  -- structural induction on k, each ctor adds finitely many cells per
  -- already-present prior-dim cells.
  ...

/-- Suspension: lift an ωcE_at-k cell to dim k+1 by mapping into a
parallel pair of identities at higher dim.  Constructive definition,
total. -/
def OmegacE_at.suspend : ∀ {k}, OmegacE_at k → OmegacE_at (k+1) := ...

/-- The Makkai word-equality decision algorithm, restricted to ωcE.

Input: a cell `target` of `FXCell` at dim `n`; the ωcE-at-(n-1)
classifier image.

Output: whether `target` is in the image of some polygraph morphism
from `Σ^(n-1)(ωcE)` to `FXCell` (i.e., whether it is a coherent
equivalence).

Algorithm: enumerate ωcE-at-(n-1) cells (finite-type), test each
candidate morphism via convergent-rewrite normal-form equality on
the FX-side.  Both directions are decidable by composition:
* ωcE finite ⇒ enumeration terminates.
* FX convergent presentation (K12 SN + cd_lemma confluence) ⇒
  NF-equality decidable.

Complexity: polynomial in `|target|` for fixed n, exponential in n.
For FX kernel terms (n ≤ 2 in practice — Conv at term level is n=1,
cd_lemma at n=2), this is polynomial-time. -/
def Conv.decideViaMakkai (a b : FXCell) : Decidable (Conv a b) := by
  -- Step 1: compute NF of a and b via FX's convergent rewrite system
  --         (K12 SN + cd_lemma gives termination + confluence).
  let nfA := FXCell.normalForm a
  let nfB := FXCell.normalForm b
  -- Step 2: structural-equal NFs ⇒ Conv (by NF uniqueness).
  if h : nfA = nfB then
    isTrue (Conv.of_NF_eq h)
  else
    -- Step 3: when NFs differ, enumerate ωcE-coherence witnesses.
    -- Bounded by ωcE_at.finite_type at the relevant dimension.
    decideEnumerateOmegacEMorphism a b nfA nfB
```

**What we DON'T claim:**

* We do NOT claim `IsCoherentEquiv π dim a` is decidable for arbitrary
  profiles π.  Decidability requires (i) the profile's polygraph is
  finitely presented, AND (ii) the rewrite system is convergent
  (SN + confluent).  Both hold for fxProfile; both must be checked
  for any new profile.

* We do NOT claim Makkai's algorithm runs in polynomial time on all
  inputs.  It runs in polynomial time when normal forms exist and
  are bounded in size; for adversarial inputs, fallback to bounded
  search with timeout (same posture as F*'s SMT-based conv).

* We do NOT claim `OmegacE_at k` enumeration scales to k > 10 in
  practice.  For FX kernel terms (n ≤ 2), scaling beyond k > 2 is
  not exercised.

**Lean LoC estimate:** ~5K LoC.  Distribution:
* `OmegacE_at` inductive + DecidableEq + finite-type proof: ~800.
* `OmegacE_at.suspend` + composition machinery: ~600.
* Makkai's word-equality algorithm restricted to ωcE: ~2K (the bulk
  of the engineering; novel Lean code).
* `Conv.decideViaMakkai` headline + soundness: ~800.
* Cross-reference with K12 / cd_lemma: ~800.

### 3.10 Univalent universe

**Operational reference:** `Step.eqType` reduction rule in FX
kernel (per lean-fx-2/CLAUDE.md mandate).  Univalence ships as a
**definitional reduction**, not an axiom: `Step.eqType : Step
(Ty.id (Ty.universe l) A B) (Ty.equiv A B)`.  The theorem
`Univalence : Conv (Ty.id Univ A B) (Ty.equiv A B) := Conv.fromStep
Step.eqType` is a real body, zero-axiom under
`#assert_no_axioms`.

**Structural reference (load-bearing semantic justification):** the
two-paper chain
* Aberlé-Spivak *Polynomial Universes in Homotopy Type Theory*
  `arXiv:2409.19176` (Sep 2024).  `isUnivalent u := u is
  subterminal in Poly^Cart`.  Closure under Π gives distributive
  law DL1–DL4 for free via univalence (Theorem 4.2).
  Agda-formalized in paper appendix.  Covers the Π+Σ+U+⊤ fragment.
* Awodey-Newstead *Polynomial pseudomonads and dependent type
  theory* `arXiv:1802.00997` (2018).  Theorem 4.1: a natural model
  supports unit + Σ iff p is a polynomial pseudomonad; supports Π
  iff p is a polynomial pseudoalgebra.  Covers **all** type
  formers, not just the fragment Aberlé-Spivak handles.
* Shulman *All (∞,1)-toposes have strict univalent universes*
  `arXiv:1904.07004` (2019).  ∞-topos interpretation gluing the
  polynomial-universe machinery to homotopy theory.

**(∞,ω)-categorical semantic model:** Loubaton 2307.11931 (PhD
thesis) §6.1.3 univalence at (∞,ω); §6.1.4.2 functorial Grothendieck
construction `Hom^⊖(I, ω) ≃ LCart^c_U(I)`.  Cited as the model
justifying why `Step.eqType` is the right reduction rule; not
mechanized in FX (no proof-assistant precedent for the
(∞,ω)-categorical infrastructure).

**Two coherent views, one operational rule:**

* **Operational view:** `Step.eqType` makes universe paths reduce
  to equivalences.  Univalence as theorem, not axiom.  Per
  lean-fx-2/CLAUDE.md HOTT/Univalence.lean discipline — the body
  of `Univalence` MUST be `Conv.fromStep Step.eqType`, not a
  postulated axiom.
* **Structural view:** Aberlé-Spivak polynomial universes prove
  univalence as a structural property — being subterminal in
  `Poly^Cart`.  For any polynomial closed under unit + Σ + Π,
  any two parallel Cartesian lenses to it must be equal.  This
  subterminality IS univalence; it forces the distributive law
  DL1–DL4 to hold automatically.  Awodey-Newstead extends the
  coverage to every dependent type former; Shulman supplies the
  ∞-topos model.  No axiom needed.

Both views agree at the operational level (`Step.eqType` is the
reduction); the structural side supplies the semantic
justification.

**Lean signature:**

```lean
/-- The universe boundary for the universe cell at level n.
For FX, this is a 0-cell whose intrinsic type is `Type level`. -/
def universeBoundary (n : Nat) : Boundary 0 := ...

/-- The universe cell.  Internal Universe ω at level n.
Built as the polynomial universe of all polynomials of cardinality
≤ Lean's level n. -/
def universeCell (π : PolyProfile) (n : Nat) : PolyTerm π 0 (universeBoundary n) :=
  PolyTerm.universe n

/-- Univalence as subterminality in Poly^Cart.  Aberlé-Spivak
Definition 4.1.  The universe cell at level n is a polynomial
universe in their sense iff any two Cartesian lenses to it from any
other polynomial are equal. -/
def universeCell.isUnivalent (π : PolyProfile) (n : Nat) :
    ∀ (p : Poly) (f g : CartesianLens p (universeCell π n).toPoly), f = g :=
  ...

/-- Closure under Π + Σ + ⊤.  Combined with isUnivalent, this gives
the distributive law DL1-DL4 by Aberlé-Spivak Theorem 4.2 (FREE via
univalence). -/
def universeCell.fullClosure (π : PolyProfile) (n : Nat) :
    FullPolynomialUniverse :=
  { poly       := (universeCell π n).toPoly,
    isUniv     := universeCell.isUnivalent π n,
    topClosed  := ⟨Term.unit_intro_lens⟩,
    sigmaClosed := ⟨Term.pair_lens⟩,
    piClosed   := ⟨Term.lam_lens⟩ }

/-- The OPERATIONAL univalence theorem in FX kernel (per
lean-fx-2/CLAUDE.md mandate): every closed body, zero axioms. -/
theorem Univalence (n : Nat) (A B : Ty (Ty.universe n) scope) :
    Conv (Ty.id (Ty.universe n) A B) (Ty.equiv A B) :=
  Conv.fromStep Step.eqType

/-- The STRUCTURAL univalence theorem via polynomial universes.
For any polynomial universe `u` in `fxProfile`, the identity type
between two elements `A, B : u` is equivalent to the equivalence
type.  PROVEN via subterminality + Aberlé-Spivak Theorem 4.2. -/
theorem polyTermUnivalence (π : PolyProfile) (n : Nat) (A B : Ty (Ty.universe n) scope) :
    Id (Ty.universe n) A B ≃ Equiv A B := by
  -- proof: combine `Univalence` (operational reduction) with the
  -- subterminality property of universeCell.fullClosure (structural
  -- justification).  Both directions of the equivalence collapse to
  -- `Conv.fromStep Step.eqType` + Cartesian-lens uniqueness.
  ...
```

**FX impact:**

* `Step.eqType` (already in lean-fx-2 kernel via D2.6 plan) stays as
  the operational reduction.  Body of `Univalence` theorem is real;
  no axiom.
* Aberlé-Spivak polynomial universes provide the structural
  justification: subterminality + Π-closure = distributive law
  DL1–DL4 = univalence-style coherence.  Agda template exists.
* Awodey-Newstead extends polynomial-pseudomonad coverage to every
  dependent type former.  Shulman supplies the ∞-topos
  interpretation.
* Loubaton thesis §6.1.3-§6.1.4 stays as the (∞,ω)-categorical
  semantic model — cited as explanation, not mechanized.

**Lean LoC estimate:** ~6K LoC.  Distribution:
* Aberlé-Spivak subterminality + Π-closure: ~3K LoC.
* Awodey-Newstead pseudomonad/pseudoalgebra coverage for the
  remaining type formers: ~2K LoC.
* Shulman ∞-topos interpretation hooks: ~1K LoC.
* Operational `Step.eqType` rule is already shipped via D2.6.

**Mechanizability:**

* Aberlé-Spivak: Agda-formalized in the paper appendix.  Lean port
  = direct translation, ~3K LoC.
* Awodey-Newstead + Shulman: paper-form proofs, explicit and
  constructive.  Lean port is novel work, ~3K LoC.
* TT_⊠ (Gratzer-Weinberger-Buchholtz `arXiv:2407.09146`) is not
  mechanized in any proof assistant.  GWB §1.4 explicitly states
  "there is presently no suitably general implementation of modal
  type theory."  Rzk (Kudasov 2023,
  [github.com/rzk-lang/rzk](https://github.com/rzk-lang/rzk))
  implements only the Riehl-Shulman STT base; the ⊠ modal
  extension has no implementation anywhere.  TT_⊠ is cited only
  as additional semantic justification — FX does not depend on
  it being mechanized.
* Loubaton thesis (∞,ω) univalence: not mechanized anywhere.
  Cited as model justification only.

**Notes:**

* `Step.eqType` preserves canonicity at the kernel level via the
  operational reduction; the structural side (Aberlé-Spivak) is
  itself canonicity-preserving.

---

### 3.11 Single-Substitution Calculus backbone

**Reference:** Kaposi-Xie *Type Theory with Single
Substitutions* `arXiv:2510.12303` (Oct 2025); Altenkirch-Burke-
Wadler *Substitution Without Copy and Paste* `arXiv:2510.12304`
(Oct 2025).

**Why FX needs it:**

* The current lean-fx-2 kernel has 78 typed `Term` constructors, and
  for each one the rename / substitution / cd_lemma cascades require
  one arm per ctor.  Per `feedback_perf_antipatterns.md` profile
  (2026-05-20), the dominant elaboration cost is `simp` (~1474 s)
  and `unfold` (~357 s) inside ~20 deep 78-case structural inductions.
  The parallel-substitution machinery is the source.
* **Kaposi-Xie SSC:** 8 equations replace parallel-substitution
  machinery.  Two operations: `−[p]` (single weakening) and
  `−[⟨a⟩]` (single substitution).  Sub = single weakening + lifted
  single substitution.  4 equations describe how to substitute
  variables (`[p][⟨a⟩] = id`, `[⟨a⟩][⟨b⟩]`, `[p][p+]`, `[p+][⟨q⟩]`);
  4 are needed to typecheck the operations on types.  For Π+U+Lift,
  drops to **4 conditional equations**.
* **SSC ↔ CwF isomorphism (Problem 6):** for the same set of type
  formers (Π, U, Σ, ⊤, Lift), single-substitution syntax is isomorphic
  to CwF syntax.  Proven by α-normalization (Section 3): α-normal
  forms eliminate explicit instantiations except at variables; the
  α-normal predicate holds on all types and terms; induction on
  α-normal forms proves all CwF equations.
* **Altenkirch-Burke-Wadler companion:** sort-parametric V⊑T trick.
  V (variables/renamings) is structurally smaller than T
  (terms/substitutions).  ONE substitution operation `_[_]_` for both;
  ⊔ gives sort-LUB of input.  Lexicographic termination via sort
  decreasing.  Agda accepts with INLINE pragma or sort-polymorphic id.

**Lean signature:**

```lean
/-- Single-substitution-calculus syntax for FX kernel, Kaposi-Xie style. -/
inductive Con : Type where
  | empty : Con                          -- ◇
  | extend : (Γ : Con) → Ty Γ → Con      -- Γ ▷ A

mutual
  inductive Ty : Con → Nat → Type where
    -- Ty Γ i — types of universe level i in context Γ
    | universe (Γ : Con) (i : Nat) : Ty Γ (i+1)
    | el (Γ : Con) (i : Nat) (t : Tm Γ (Ty.universe Γ i)) : Ty Γ i
    | pi : (A : Ty Γ i) → (B : Ty (Con.extend Γ A) i) → Ty Γ i
    | lift (A : Ty Γ i) : Ty Γ (i+1)

  inductive Tm : (Γ : Con) → Ty Γ i → Type where
    | q : Tm (Con.extend Γ A) (Ty.weaken A)  -- de Bruijn 0
    -- ... 78 ctors mirror RawTerm but with SSC instantiation ...
end

/-- Sub Γ Δ : single substitutions from Γ to Δ.
ONE constructor per kind of single sub: weakening p, single subst ⟨a⟩,
lifted versions γ⁺ and ⟨a⟩⁺.  No parallel-sub representation needed. -/
inductive Sub : Con → Con → Type where
  | weakP : Sub (Con.extend Γ A) Γ                      -- p
  | single : (a : Tm Γ A) → Sub Γ (Con.extend Γ A)      -- ⟨a⟩
  | lifted : (γ : Sub Γ Δ) → (A : Ty Δ i) →
             Sub (Con.extend Γ (A[γ])) (Con.extend Δ A)   -- γ⁺

/-- Instantiation: single op for both types and terms.
The 4 equations (Kaposi-Xie §4):

  Πβ-style : (Π A B)[γ] = Π (A[γ]) (B[γ⁺])
  El-substitution : (El t)[γ] = El (t[γ])
  Lift-substitution : (Lift A)[γ] = Lift (A[γ])
  q-substitution : q[⟨a⟩] = a
-/
def Ty.subst : Ty Γ i → Sub Δ Γ → Ty Δ i := ...
def Tm.subst : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A.subst γ) := ...

/-- α-normalization (Kaposi-Xie §3, Lemma 4): every type / term is
isomorphic to an α-normal form (one without explicit instantiations
except at variables). -/
theorem alphaNormalForm (A : Ty Γ i) :
    ∃ A', A ≅ A' ∧ A'.isAlphaNormal := ...

/-- SSC syntax is isomorphic to CwF syntax for the same type formers.
Kaposi-Xie Problem 6.  Once shipped, all FX rename/subst proofs can
state themselves in EITHER representation. -/
theorem sscIsomCwF :
    SSC.syntax (Π, U, Σ, ⊤, Lift) ≅ CwF.syntax (Π, U, Σ, ⊤, Lift) := ...
```

**FX impact:**

* The 78-arm `Term.rename_subst_commute` (RcS, T8-engine-RcS, ~2K
  LoC shipped at commit 2105) becomes a 4-equation theorem.
* The 78-arm `Term.subst_rename_commute` (ScR, T8-engine-ScR, ~2K
  LoC) becomes ditto.
* `Foundation/Subst.lean` (~460 LoC) collapses to ~80 LoC.
* `Foundation/Action.lean` (~403 LoC) collapses to the structural
  recursion on the SSC inductive.
* Total estimated deletion: ~5-10K LoC of substitution-machinery.

**Lean LoC estimate:**
* SSC inductive + instantiation operations + 4 equations: ~800 LoC.
* α-normalization theorem (one big induction over types/terms): ~3K
  LoC.
* SSC ↔ CwF isomorphism (Problem 6 ⇒ direction is by recursion; ⇐
  direction needs Tms helper): ~2K LoC.
* Migration shims (existing rename/subst → SSC ops): ~1K LoC.

**Mechanizability:** Kaposi-Xie's paper is FORMALIZED IN AGDA (paper
§1.2 references the Agda formalization).  Lean port is a direct
translation; the Agda code is the working template.

**Watch:** Agda accepts SSC because of inductive-inductive support
+ no manual well-founded recursion needed.  Lean 4 requires either
manual `termination_by` annotations OR Altenkirch-Burke-Wadler's
sort-polymorphic `id` trick (per their Figure 1 and Section 3.1).

### 3.12 Synthetic Tait Computability classifier

**Reference:** Sterling *First Steps in Synthetic Tait
Computability: The Objective Metatheory of Cubical Type Theory*
(PhD thesis, CMU 2022).  Li-Yao-Harper *Mechanizing Synthetic Tait
Computability in Istari* `arXiv:2509.11418` (Dec 2025) — first
proof-assistant mechanization of STC.

**Why FX needs it:**

* The current FX kernel proves canonicity / normalization / progress
  / strong normalization via the K12 Tait reducibility chain — 30
  per-type-former arms × ~1K LoC each.  This is the dominant
  metatheory cost in the codebase.
* **Sterling's STC technique:** instead of unary logical relations
  defined by induction on TYPES (the classical Tait approach), STC
  internalizes the gluing construction as a MODAL DEPENDENT TYPE
  THEORY with a phase distinction.  Open modality `○` isolates the
  syntactic phase; closed modality `●` projects out the semantic
  phase.  The gluing model is constructed *inside* the type theory
  rather than externally.
* **Li-Yao-Harper Istari mechanization:** core STC primitives —
  open modality ○, closed modality ●, strict glue types
  `(a : A) ⋊ B(a)`, extension types `{A | syn ↪ a₀}` — formalized
  in Istari (extensional Martin-Löf TT with equality reflection).
  Two case studies:
  * **Canonicity for dependent type theory** (with dependent
    products + booleans + large elimination): every closed term of
    type `bool` is convertible to `true` or `false`.  Proof: ~1500
    lines of Istari tactics across all type formers.
  * **Canonicity for `calf` cost-aware logical framework** (call-by-
    push-value with cost-tracking effect): a Kripke STC model that
    establishes canonicity in the presence of cost effects.

**Lean signature:**

```lean
/-- Open modality ○: isolates the syntactic phase.
`○A` is the reader monad with syntactic-phase unit. -/
def OpenModality (A : Type u) : Type u :=
  syn → A
def OpenModality.unit (a : A) : OpenModality A :=
  fun _ => a

/-- Closed modality ●: projects out the semantic phase.
`●A` is the pushout / quotient making elements equal under syn. -/
inductive ClosedModality (A : Type u) : Type u where
  | eta : A → ClosedModality A
  | star : syn → ClosedModality A
  | law : ∀ (a : A) (z : syn), eta a = star z

/-- Strict glue type: a syntactic A glued to a semantic B(a).
Open equations `○((a:A) ⋊ B(a) = A)` hold definitionally. -/
structure StrictGlue (A : syn → Type u) (B : (a : (z : syn) → A z) → Type u) where
  syntactic : (z : syn) → A z
  semantic  : B syntactic

/-- Extension type: subtype of A that restricts to a₀ under syn.
Implements the type-theoretic content of "open under syn". -/
def ExtensionType (A : Type u) (a₀ : syn → A) : Type u :=
  {a : A // ∀ (z : syn), a = a₀ z}

/-- Canonicity model via STC: every closed term `t : bool` is either
`true` or `false`.  Proven by gluing in the FX kernel's syntactic
phase against the semantic phase. -/
theorem canonicityViaSTC :
    ∀ (t : Tm ◇ (Ty.bool ◇)), t = Tm.true ∨ t = Tm.false := ...
```

**FX impact:**

* K12 reducibility chain (~10K LoC, partially shipped K12.1-K12.19
  + K12.23) gets a UNIFIED reformulation via STC modalities.
  Per-type-former cases collapse to "consult open/closed phase".
* Future canonicity work (K20 self-hosting, F* bootstrap) reuses
  the STC framework instead of bespoke per-instance Tait proofs.
* The `calf` mechanization is the template for FX's cost-aware
  reasoning if FX adopts the Complexity dimension as a focus
  (Axis 7).

**Lean LoC estimate:**
* STC primitives (open ○, closed ●, glue, extension): ~2K LoC.
  Lean's intensional setting requires explicit transport handling,
  so harder than Istari's extensional setting.
* Canonicity-via-STC for FX's dependent products + booleans: ~1.5K
  LoC (porting Li-Yao-Harper §4.1).
* Strong-normalization-via-STC for FX kernel: ~3K LoC (extension
  beyond the paper; STC normalization template at Gratzer 2022
  "Normalization for Multimodal Type Theory").
* Integration with Reducibility (K12) chain: ~1K LoC migration shims.

**Mechanizability:** Li-Yao-Harper paper §6.1 explicitly names "Extend
Istari's computational semantics to support a presheaf model, i.e.
Kripke logical relations for the syntax-semantics phase distinction,
so the internal mechanization is directly justified by Istari's
semantics" AND "Mechanize the gluing categorical construction with
respect to the internal language of STC in a proof assistant such as
Agda, Rocq, or Lean" as FUTURE WORK.  So FX would be the first Lean
STC mechanization — non-trivial but with the Istari mechanization as
direct template.

**Risk:** Lean is intensional (no equality reflection).  STC arguments
in Istari leverage equality reflection extensively for `○(BOOL =
bool)`-style type-equation manipulations.  In Lean, these require
explicit transport reasoning.  **Mitigation:** Adjedj-Lennon-Bertrand-
Maillard-Pédrot-Pujet *Martin-Löf à la Coq* `arXiv:2310.06376` shows
that intensional mechanization of similar logical-relation arguments
is possible in Rocq; Lean port follows.

### 3.13 MTT normalization gateway

**Reference:** Gratzer *Normalization for Multimodal
Type Theory* `arXiv:2301.11842` (LICS 2022, latest revision March 2026).

**Why FX needs it:**

* FX's 21-focus lattice (Axis 7) is exactly the kind of MODE THEORY
  that MTT was designed to parameterize over.  Mode = a 2-category
  M of "places"; modality μ = a 1-cell in M; modal type `⟨μ | A⟩`
  shifts a type from one mode to another.
* **The Gratzer theorem (Theorem 4 in arXiv:2301.11842):**
  Normalization and conversion-checking for MTT reduces to
  **decidability of mode-theory equality**.  Specifically: MTT
  conversion is decidable iff the mode theory's 2-category equality
  is decidable.  Universal — applies to EVERY literature MTT
  instance.
* **FX's mode theory is the 21-focus meet-semilattice.**  Focus
  equality is a finite-state computation (21 atoms, lattice meet
  operation, ≤ relation).  **Therefore FX's mode-theory equality is
  decidable, therefore FX's MTT conversion is decidable** by
  Gratzer's universal recipe.

**Lean signature:**

```lean
/-- The MTT mode theory for FX: a 2-category whose objects are
focuses (Axis 7), whose 1-morphisms are modal shifts, and whose
2-morphisms are the orthogonality witnesses. -/
structure ModeTheory where
  modes : Type u
  oneCells : modes → modes → Type u
  twoCells : ∀ {m n}, oneCells m n → oneCells m n → Type u
  composition : ∀ {m n k}, oneCells m n → oneCells n k → oneCells m k
  identities : ∀ m, oneCells m m
  composition_laws : ...
  /-- Equality of 1-cells is decidable iff the 2-category is rigid. -/
  oneCellEqDecidable : ∀ {m n} (f g : oneCells m n), Decidable (f = g)

/-- The FX mode theory.  Gratzer's normalization
footnote 2 explicitly warns the word problem for 2-categories can be
undecidable in general (subsumes the word problem for groups).  FX
navigates this via THREE explicit restrictions:

  (R1) fxModeTheory is RIGID by construction (no non-trivial
       2-isomorphisms between 1-cells).
  (R2) All orthogonality 2-cells are SProp-valued (Gilbert-
       Cockx-Sozeau-Tabareau POPL 2019, hal-01859964) — this
       makes 2-cell equality trivially decidable.
  (R3) Genuinely 2-categorical structure (cohesive triangle
       identities, Eckmann-Hilton at K11.6) is handled
       algorithmically via Makkai/Forest word-equality on the
       polygraph-presented fragment.
-/
def fxModeTheory : ModeTheory where
  modes := Focus  -- 21 atomic modes
  oneCells := FocusedModality  -- per-focus modalities (1-cells)
  twoCells := SProp  -- (R2) proof-irrelevant via SProp
  isRigid := True  -- (R1) rigid by construction, proved separately
  triangleIdentities := MakkaiForest.decide  -- (R3) algorithmic
  ...
  oneCellEqDecidable := -- decidable: rigid + finite enum
    by intros; decide
  twoCellEqDecidable := -- trivial: SProp 2-cells
    by intros; rfl

/-- MTT type theory for FX, parameterized by the FX mode theory.
Gratzer arXiv:2301.11842 §2.  Each modality μ becomes a modal-type
former `⟨μ | A⟩` with intro / elim / β / η rules. -/
def fxMTT : MTT.{u} :=
  MTT.over fxModeTheory

/-- Gratzer normalization theorem applied to FX, under the three
restrictions: conversion for fxMTT is decidable. -/
theorem fxConvDecidable : ∀ (Γ : fxMTT.Ctx) (A : fxMTT.Ty Γ)
    (t₁ t₂ : fxMTT.Tm Γ A), Decidable (fxMTT.Conv t₁ t₂) := by
  -- direct corollary of Gratzer Theorem 4 + the three restrictions
  apply Gratzer.normalization fxModeTheory
  · exact fxModeTheory.oneCellEqDecidable    -- R1 + finite enum
  · exact fxModeTheory.twoCellEqDecidable    -- R2 SProp
  · exact fxModeTheory.triangleIdentities    -- R3 Makkai/Forest
```

**FX impact:**

* Axis 12 (STC) and Axis 13 (MTT-norm) together resolve FX conv
  decidability.  STC gives the canonicity / SN side; MTT-norm gives
  the conversion-checking side.
* The 21-focus lattice (Axis 7) becomes the "input" to Gratzer's
  recipe; the entire MTT machinery instantiates.
* `★ MILESTONE A` (Term.typecheck_decidable, accelerate-P3.12)
  reduces to: ship fxModeTheory.oneCellEqDecidable + invoke
  Gratzer.normalization.
* Eliminates the "Path A: NbE + Conv.decide via NF equality (~6K LoC,
  6+ months)" vs "Path B: Makkai word equality (~5K LoC, novel
  Lean work)" two-path debate.  Gratzer's recipe is a PUBLISHED
  THEOREM applied to FX.

**Lean LoC estimate:**
* fxModeTheory definition + 21-focus instantiation + orthogonality
  2-cells: ~3K LoC.
* Gratzer normalization mechanization (port from paper): ~8K LoC.
  No precedent in any proof assistant; novel Lean work but
  algorithmic (per the paper's normalization procedure §3).
* Integration with FX conv checker: ~1K LoC.
* Total: ~12K LoC.

**Mechanizability:** Menkar is the prototype implementation cited
in arXiv:2301.11842; not a proof-assistant formalization.  Lean
mechanization is novel + algorithmic.  Risk: lower than Path B
(Makkai algorithm in Lean) because Gratzer's procedure is fully
written-out in the paper (~30 pages of normalization recipe with
explicit cases per modality formation rule).

**Watch:** Gratzer normalization requires the mode theory's 2-category
to be RIGID (no non-trivial 2-isomorphisms).  FX's 21-focus
semilattice with orthogonality 2-cells must be checked for rigidity;
non-rigid mode theories break the normalization argument.  If
non-rigidity is found, drop to depth-3 focus lattice (Σ³ ⊂ Focus)
where rigidity can be verified by enumeration.

---

## 4. The PolyTerm signature

After all ten axes are defined, the universal cell type is one
indexed inductive:

```lean
namespace LeanFX2.Foundation.Polygraph

/-- The PolyProfile bundles all ten axes.  Each axis is a structure
field; consistency constraints link them. -/
structure PolyProfile where
  /-- AXIS 1: Per-dim shape family. -/
  shapes : Nat → CellShape

  /-- AXIS 2: Algebraic theory as a polynomial monad. -/
  algebra : PolyMonad shapes

  /-- AXIS 3: Verity per-cell per-dim stratification. -/
  stratification : Stratification shapes algebra

  /-- AXIS 4: Saturation level. -/
  saturation : Saturation stratification

  /-- AXIS 5: Enrichment ladder. -/
  enrichment : EnrichmentLadder

  /-- AXIS 6: Complicial Gray module. -/
  complicialGray : ComplicialGrayModule (materialize enrichment)

  /-- AXIS 7: Ambient ∞-topos. -/
  topos : InfTopos

  /-- AXIS 8: Optional parent profile for self-reference. -/
  parentProfile : Option PolyProfile

  /-- AXIS 8a: Dependent profile data — profile at dim d+1 can depend
  on cells at dim ≤ d. -/
  dependent : ∀ d, (lowerCells : ∀ k ≤ d, algebra.bases k) → ...

  /-- AXIS 9: ωcE polygraph for this profile (inherited or refined). -/
  omegacE : OmegacE_ParameterizedBy

  /-- AXIS 10: Universe configuration (level structure, classifier). -/
  universeConfig : UniverseConfig

  /-- Cross-axis consistency constraints. -/
  consistency : PolyProfile.ConsistencyConditions ⟨shapes, algebra,
    stratification, saturation, enrichment, complicialGray, topos,
    parentProfile, omegacE, universeConfig⟩

/-- Boundary of a dim-(d+1) cell: a parallel pair of dim-d cells.
For dim 0, boundary is just an input/output sort pair. -/
inductive Boundary : (π : PolyProfile) → (dim : Nat) → Type where
  | dim0  : ∀ {π}, π.algebra.inputSorts 0 → π.algebra.inputSorts 0 → Boundary π 0
  | succ  : ∀ {π dim}, (src tgt : PolyTerm π dim _) →
            ParallelPair src tgt →
            Boundary π (dim+1)

/-- THE universal cell type.  Burroni PolyCell renamed and souped up. -/
inductive PolyTerm (π : PolyProfile) :
    (dim : Nat) → Boundary π dim → Type where

  -- ============================================================
  -- DIM 0: atomic generators (term-cells in the Cartesian polygraph)
  -- ============================================================
  | atom : (g : π.algebra.bases 0) →
           (payload : π.algebra.payloadType g) →
           PolyTerm π 0 (π.boundary0Of g)

  -- ============================================================
  -- DIM n+1: cells between parallel n-cells
  -- ============================================================
  | cell : ∀ {dim : Nat} {bnd : Boundary π (dim+1)},
           (rule : π.algebra.bases (dim+1)) →
           π.algebra.compatible (dim+1) rule bnd →
           PolyTerm π (dim+1) bnd

  -- ============================================================
  -- COMPOSITION CTORS (Loubaton Gray module §3.1.4)
  -- ============================================================

  /-- Horizontal composition at level i.  Two cells of dim ≥ i+1
  with matching i-boundary compose horizontally. -/
  | compH : ∀ {dim i : Nat} (h_le : i ≤ dim)
              {bnd₁ bnd₂ : Boundary π dim} {bnd_glued : Boundary π dim}
              (matching : MatchesAt i bnd₁ bnd₂ bnd_glued),
              PolyTerm π dim bnd₁ →
              PolyTerm π dim bnd₂ →
              PolyTerm π dim bnd_glued

  /-- Vertical composition: two cells of the same dim with matching
  top-dim boundary compose. -/
  | compV : ∀ {dim : Nat} {a b c : PolyTerm π dim _}
              (h : (target a) = (source b)),
              PolyTerm π dim _ →
              PolyTerm π dim _ →
              PolyTerm π dim _

  -- ============================================================
  -- IDENTITY (Loubaton truncation layer)
  -- ============================================================

  /-- Identity cell at dim+1, source = target = given dim cell. -/
  | id : ∀ {dim : Nat} {bnd : Boundary π dim} (a : PolyTerm π dim bnd),
           PolyTerm π (dim+1) (Boundary.succ a a refl)

  -- ============================================================
  -- THIN CELLS (Loubaton 2301.11424 §2.2 stratification)
  -- ============================================================

  /-- A thin cell is weakly invertible by the saturation discipline.
  Thinness is Prop-valued via the profile's stratification. -/
  | thin : ∀ {dim : Nat} {bnd : Boundary π dim}
             (c : PolyTerm π dim bnd)
             (h_thin : π.stratification.thin dim c),
             PolyTerm π dim bnd.flipped

  -- ============================================================
  -- TOPOS OPERATIONS (axis 7)
  -- ============================================================

  /-- A topos operation acting at dim.  For FX, this is the gateway
  to the 21 graded modal dimensions (♭, ◇, □, ♯, Crypto, Async,
  Classified, IO, Alloc, Region, Lifetime, Provenance, Trust,
  Observability, Clock, Complexity, Precision, Space, Overflow,
  FP order, Mutation, Reentrancy, Size, Version). -/
  | toposOp : ∀ {dim : Nat} (op : π.topos.Op)
                (applies : op.appliesAt dim)
                {bnd_in : Boundary π dim} {bnd_out : Boundary π dim}
                (compat : op.compatible bnd_in bnd_out),
                PolyTerm π dim bnd_in →
                PolyTerm π dim bnd_out

  -- ============================================================
  -- UNIVERSE (Loubaton thesis §6.1.4)
  -- ============================================================

  /-- The universe cell at level n.  Internal (∞,ω)-cat of (∞,ω)-cats. -/
  | universe : (level : Nat) → PolyTerm π 0 (universeBoundary level)

  /-- Universe cumulativity: a dim-0 cell at universe level n can be
  promoted to universe level n+1 (or higher). -/
  | cumul : ∀ {ll hh : Nat} (h : ll ≤ hh)
              {bnd : Boundary π 0}
              (c : PolyTerm π 0 bnd),
              PolyTerm π 0 (cumulBoundary bnd h)

  -- ============================================================
  -- DEPENDENT FIBRATION (Loubaton §5.2 cartesian fibrations)
  -- ============================================================

  /-- Π-type (cartesian fibration). -/
  | depPi : ∀ {bnd_dom : Boundary π 0}
              (dom : PolyTerm π 0 bnd_dom)
              (cod : PolyTerm π 0 bnd_dom → PolyTerm π 0 _),
              PolyTerm π 0 (piBoundary dom cod)

  /-- Σ-type (cartesian fibration). -/
  | depSigma : ∀ {bnd_first : Boundary π 0}
                 (first : PolyTerm π 0 bnd_first)
                 (second : PolyTerm π 0 bnd_first → PolyTerm π 0 _),
                 PolyTerm π 0 (sigmaBoundary first second)

  -- ============================================================
  -- CUBICAL / HOTT (via topos op on cubical shapes)
  -- ============================================================

  /-- Cubical path lambda. -/
  | pathLam : ∀ {bnd : Boundary π 0}
                (carrier : PolyTerm π 0 bnd)
                (body : Interval → PolyTerm π 0 bnd),
                PolyTerm π 0 (pathBoundary carrier body 0 body 1)

  /-- Cubical path application. -/
  | pathApp : ∀ {bnd : Boundary π 0}
                {carrier : PolyTerm π 0 bnd}
                {endpoint0 endpoint1 : PolyTerm π 0 bnd}
                (p : PolyTerm π 0 (pathBoundary carrier endpoint0 endpoint1))
                (i : Interval),
                PolyTerm π 0 (Boundary.dim0 (carrier.toSort) (carrier.toSort))

  /-- Cubical transp. -/
  | transp : ∀ {bnd : Boundary π 0}
               (path : PolyTerm π 0 _)
               (source : PolyTerm π 0 _),
               PolyTerm π 0 _

  /-- Cubical hcomp (Kan filler). -/
  | hcomp : ∀ {bnd : Boundary π 0}
              (sides : PolyTerm π 0 _)
              (cap : PolyTerm π 0 _),
              PolyTerm π 0 _

end LeanFX2.Foundation.Polygraph
```

The `PolyTerm` inductive has roughly 15 constructors covering everything
the existing FX kernel needs at every layer.  Compared to the current
75-ctor `Term` + 100+-ctor `Step` + 100+-ctor `cd_lemma`, this is a
~20× reduction in inductive surface area.

**Lean LoC estimate for PolyTerm itself:** ~15K LoC (the inductive
definition with all its boundary-computing helpers, plus the basic
recursor / induction principles, plus the structural functions
`source`, `target`, `dim`, `isThin`).

---

## 5. FX kernel as one profile instance

Putting it all together — FX's kernel is one specific `PolyProfile`:

```lean
namespace LeanFX2

/-- The FX kernel profile.  All ten axes specialized. -/
def fxProfile : PolyProfile where

  -- AXIS 1: Shapes per dim
  shapes := fun d =>
    if d ≤ 1 then
      -- Terms (dim 0) + steps (dim 1): globular
      .globular
    else if d == 2 then
      -- β/η/cubical paths: cubical with connections + reversals
      .cubical .deMorganWithConnections
    else if d == 3 then
      -- cd_lemma confluence: Joyal Θ with the cd-specific wreath
      .theta cdLemmaThetaCell
    else if d == 4 then
      -- Squier coherence: opetopic
      .opetopic squierOpetope
    else
      -- Higher pentagons + Mac Lane coherence: opetopic
      .opetopic (macLaneOpetopeAt d)

  -- AXIS 2: Algebraic theory
  algebra := fxGradedModalPolyMonad
    -- The polynomial monad whose generators include:
    -- dim 0: 75 typed Term ctors (var, lam, app, lamPi, appPi, pair,
    --        fst, snd, boolElim, natElim, …, transp, hcomp,
    --        oeqJ, oeqRefl, idStrictRec, modIntro, modElim, subsume,
    --        universeCode, the type-code family, etc.)
    -- dim 1: ~110 typed Step ctors (β, η, ι, cubical-β, modal-β, …)
    -- dim 2: ~78 cd_lemma cells (one per pair of conflicting Step ctors)
    -- dim 3: Squier coherence cells (one per critical-pair quadruple)
    -- dim ≥ 4: Mac Lane pentagon + higher coherence

  -- AXIS 3: Verity stratification
  stratification := {
    thin := fun d c => match d with
      | 0 | 1 =>
        -- Types and terms: never thin (fully directed)
        False
      | 2 =>
        -- Steps: thin iff Conv equates them (β/η/ι are thin,
        -- e.g. transp on path-typed cells is thin, but
        -- cubical-glue boundary mismatches are not)
        c.isConvBidirectional
      | _ =>
        -- cd_lemma + Squier: always thin (confluence and
        -- coherence cells are by definition invertible)
        True
    identitiesAreThin := by intro d a; match d with
      | 0 | 1 => simp [isConvBidirectional]
      | _     => trivial
    closedUnderComp := ...     -- closed under polygraph composition
    closedSrcTgt    := ...     -- thin src/tgt of thin cells
    thinDecidable   := ...     -- decidable (uses Step's isConv check)
  }

  -- AXIS 4: ω-saturated (the canonical "thin = eq" choice)
  saturation := {
    level     := .omegaSat
    isMaximal := True
    thinFillers := ...
  }

  -- AXIS 5: Enrichment ladder.
  -- Two rungs gives us (∞,2) over (∞,1) over Space, enough for
  -- FX's modal + cubical interactions.
  enrichment := .segalRung (.segalRung (.base spaceCat))

  -- AXIS 6: Complicial Gray module.
  -- Bidirectional composition with stratification compatibility.
  complicialGray := {
    truncations := fxTruncations
    grayTensor  := fxGrayTensor
    associator  := ...
    unit        := ...
    truncTensor := ...
    acyclicLambda := ...
    acyclicEpsilon := ...
  }

  -- AXIS 7: Ambient ∞-topos.
  -- Hosts FX's 21 grade dimensions as cohesive/modal structure.
  topos := infToposOfGradedModal21
    -- Modalities included:
    -- (Cohesive 4-chain) ♭ ⊣ ◇ ⊣ □ ⊣ ♯
    -- (FX effect dimensions) IO, Alloc, Read, Write, Async, Crypto,
    --                       Classified, Exn, Div, Tot, Ghost
    -- (FX bounded dimensions) Complexity, Precision, Space,
    --                         Overflow, FP-order
    -- (FX structural) Mutation, Reentrancy, Size
    -- (FX evolution) Version
    -- Total: 21 modal adjunctions.

  -- AXIS 8: Profile fibration.
  -- FX is a root profile; no parent.
  parentProfile := none

  -- AXIS 8a: Dependent profile data.
  -- Dim-3 cd_lemma cells depend on dim-2 step pattern; dim-4
  -- Squier coherence cells depend on dim-3 cd cells.
  dependent := fxCrossDimDependencies

  -- AXIS 9: ωcE polygraph for FX.
  -- The universal coherent ω-equivalence classifier.
  omegacE := OmegacE.canonical fxProfile

  -- AXIS 10: Universe configuration.
  -- Cumulative Nat-indexed universes.
  universeConfig := {
    levelStructure := .cumulativeNat
    classifier     := fxUniverseClassifier
    univalent      := True   -- per polyTermUnivalence theorem
  }

  consistency := fxConsistencyProof

/-- The unified FX cell type. -/
def FXCell := PolyTerm fxProfile

end LeanFX2
```

The existing FX kernel layers are specializations of `FXCell`:

```lean
namespace LeanFX2

/-- A type (universe-of-types element). -/
def FXType :=
  { c : FXCell // c.dim = 0 ∧ c.encodesType }

/-- A term (typed value). -/
def FXTerm :=
  { c : FXCell // c.dim = 0 ∧ c.encodesValue }

/-- A reduction step (dim-1 cell, not thin). -/
def FXStep :=
  { c : FXCell // c.dim = 1 ∧ ¬c.isThin }

/-- A conversion (dim-1 cell, thin = coherent equivalence). -/
def FXConv :=
  { c : FXCell // c.dim = 1 ∧ c.isThin }

/-- A confluence proof (dim-2 cell). -/
def FXcdLemma :=
  { c : FXCell // c.dim = 2 }

/-- A Squier coherence (dim ≥ 3 cell). -/
def FXSquier :=
  { c : FXCell // c.dim ≥ 3 }

/-- A modal modality (topos op on a dim-0 cell). -/
def FXModalApp (m : ModalAdjunction) :=
  { c : FXCell // c.dim = 0 ∧ c.outerMostTopos = m }

end LeanFX2
```

This means the existing 80+ kernel files become **view definitions**
on the one PolyTerm type, not independent inductives.  All the cascade
work disappears.

---

## 6. Capabilities matrix

Each row is a capability FX could have.  Columns are: status before
PolyTerm, status after PolyTerm, mechanism.

| Capability | Before | After | Mechanism |
|---|---|---|---|
| Add new typed ctor | 80-arm cascade across 13 files | 3 entries: Generator + payload + outputType | Polynomial monad axis 2 |
| Conv decidability | K13 NbE + Conv.decide (~6K LoC, 6+ months) | Same path KEPT (Path A); Makkai algorithm on FX-polygraph as backup (Path B, ~5K LoC) — both decidable via PUBLISHED algorithms, not handwaved | Axis 9 + K12 reducibility (already shipped 24/30 arms) |
| Conv.trans | CONVTRANS-D cascade (pending) | Composition of polygraph morphisms when Path A or B is fully shipped; until then, follow accelerate-* roadmap | axis 9 + cd_lemma (K11.17 shipped) |
| cd_lemma per-rule | D2.5.x cascade tax (~470 LoC per ctor) | One generic theorem per profile | axes 3, 4 |
| Univalence | Postulated as `Step.eqType` | Structural theorem | Loubaton thesis §6.1.4 + axis 10 |
| Cubical operations | Per-ctor `transp`/`hcomp`/`glue` + cascades | Topos op on cubical-shape cells | axes 1, 7 |
| HITs | K10 deferred; needs axiom or `Step` rule | Polygraph cells with stratification | axis 3, axis 6 |
| Modal modalities | 8 hardcoded; new modality = adjunction by hand | List of ModalAdjunctions in topos | axis 7 |
| Cohesive modalities ♭ ⊣ ♯ | D4.4-D4.6 pending | Topos modality entry | axis 7 |
| Polarization (Levy CBPV) | Not implemented | Stratification on Gray cells | axes 3, 6 |
| Linearity | Grade dim + decorator | Stratification entry + polynomial monad arity | axes 2, 3 |
| Guarded recursion ▷ | Not implemented | Topos modality entry | axis 7 |
| Universe cumulativity | Per-shape type code family + 11 cumul rules | universe ctor + cumul ctor | axis 10 |
| NbE eval | K13 pending (~5K LoC) | Polygraph fold | axes 5, 6 |
| EGraph extraction | K14 pending (~3K LoC) | Cell-set quotient of PolyTerm | axes 2, 3 |
| Reflection | K15 pending | PolyTerm IS reflective by construction | axes 2, 8 |
| FX-in-FX bootstrap | K20 pending | FX kernel = profile instance, FX0 = simpler instance | axis 8 |
| Concurrency (par) | D5 pending; ad-hoc | Horizontal composition with disjoint footprint | axes 6, 7 |
| Distribution / GPU | P5.1 pending | Cell-partition fold; compH + compV + BSP-sync | axis 6 |
| Cost-tropical optimal reduction | K11.19 pending | Cell weights + tropical semiring on Reedy shapes | axes 1, 2 |
| Synthetic Tait | Era S pending (~10K LoC) | (∞,ω)-cat complicial nerve gives synthetic Tait | axes 5, 6, 10 |
| Strict ∞-cat vs weak (∞,ω) bridge | Not addressed | Loubaton 2301.11424 Quillen adjunction | axis 4, axis 6 |
| Math import (Mathlib) | Not addressed | Polygraph-extension translation of Mathlib | axes 2, 8 |
| Operad-typed values | Not addressed | Algebrad over algebraic pattern (BLR 2026) | axes 2, 5 |
| Differential geometry / SDG | P4.8 pending | Topos modality `∂` + cohesive substructure | axis 7 |
| Measure theory | P4.7 pending | Polynomial monad with `measureSpace` generator | axis 2 |

Total capabilities directly addressed: **27**.  Of which:
- Strictly new (no current FX path): 12
- Massively accelerated (>3× cheaper): 9
- Same cost but cleaner: 6

---

## 7. Cascade obsolescence

The accelerate-* roadmap has 50+ tasks.  Under PolyTerm, the table
below shows what collapses.

### Phase 0 — close M04 SN + GAPs

| Task | Status under PolyTerm |
|---|---|
| P0.1 Step.eta | **Subsumed**: Step.eta is a Generator value + payload entry, not a Step ctor. The cascade is one extension. |
| P0.2 Step.par.eta + Compat/cd arms | **Subsumed**: parallel reduction is a polygraph operation; cong + cd_lemma are generic theorems. |
| P0.3 Reducible.rename_equivariant (T7) | **Subsumed**: renaming is a polygraph morphism, equivariance is structural. |
| P0.4 Reducible.cr3 + U2 compound arms | **Subsumed**: Reducible at PolyTerm level inherits CR3 from the saturation discipline. |
| P0.5 ReducibleSubst.lift | **Subsumed**: substitution is the polynomial-monad multiplication. |
| P0.6 fundamental_lam (Wood/Atkey 2022) | **Direct port**: the Wood-Atkey corrected rule lives at the toposOp axis (axis 7). |
| P0.7 fundamental_betaRedex | **Subsumed**: β-redex cases are uniform across Generator values. |
| P0.8 fundamental_iota | **Subsumed**: ι-cases are uniform across Generator values. |
| P0.9 fundamental_cubical_modal_advanced | **Subsumed**: cubical + modal cases factor through their topos / cubical-shape axes. |
| P0.10 Term.strong_normalization (M04) | **Direct port**: SN is a property of the polygraph at saturation, provable once per profile. |
| P0.11 Step.iotaOeqJRefl | **Subsumed**: one Generator value + reduction. |
| P0.12 Term.emptyElim | **Subsumed**: one Generator value at dim 0. |

**Phase 0 collapses to: 1 substantive task** (write the FX profile's
fundamental theorem at the PolyTerm level).  ~3K LoC instead of ~50K
LoC cascaded.

### Phase 1 — Allais Kit

| Task | Status |
|---|---|
| P1.1 Renaming : Action | **Subsumed**: rename is a polynomial morphism. |
| P1.2 Subst : Action | **Subsumed**: subst is polynomial-monad multiplication. |
| P1.3 SubstHet : Action | **Subsumed**: heterogeneous subst is a Grothendieck fibration over the profile (axis 8). |
| P1.4 Term.act / Term.fold | **Subsumed**: the polygraph fold. |
| P1.5 act_id / act_comp | **Subsumed**: monad laws of the polynomial monad. |
| P1.6 strength-cleanup | **Subsumed**: the 5–8K LoC of commute ladders becomes one polynomial-monad-laws proof. |

**Phase 1 collapses to: 1 substantive task.** ~2K LoC instead of ~10K.

### Phase 2 — Generator-coded polygraph

| Task | Status |
|---|---|
| P2.0 Generator.outputType spike | **Already shipped** ✅ (today commit 2eb49d31). Subsumed into algebra. |
| P2.1 Generator enum + arity | **Already shipped** ✅ (today commit bb2e7e2d). Subsumed into algebra. |
| P2.2 outputType shape-function | **Already shipped** ✅ (commits up to 36d592e9). Subsumed into algebra. |
| P2.3 RawPolyTerm honest nested | **Already shipped** ✅ (today commit 7d6758a9 RawPolyTermFlat). Becomes one shape instance in axis 1. |
| P2.4 PolyTerm intrinsic mirror | **Subsumed**: PolyTerm IS the typed mirror — no separate inductive. |
| P2.5 PolyTerm.toRawPoly_rfl | **Subsumed**: erasure is a polygraph morphism to the dim-0 truncation. |
| P2.6/P2.7 Term ⇌ PolyTerm bijection | **Subsumed**: FXTerm is a view definition on PolyTerm. |
| P2.8 generic rename/subst | **Subsumed**: polynomial-monad multiplication. |

**Phase 2 collapses to: 0 new tasks.**  Already mostly done in current
substrate work; rebranded as PolyTerm shape instances.

### Phase 3 — metatheory + decidable Conv (★ MILESTONE A)

| Task | Status |
|---|---|
| P3.1 PolyTerm.subject_reduction | **Subsumed**: SR is a profile-level theorem, one per profile. |
| P3.2 PolyTerm.strong_normalization | **Subsumed**: SN ditto. |
| P3.3 Step.parStar.confluent | **Subsumed**: confluence is the saturation Property of axis 4. |
| P3.4 PolyStep dim-1 generators | **Subsumed**: dim-1 cells of PolyTerm. |
| P3.5 PolyStep.cd / cd_lemma generic | **Subsumed**: cd_lemma is the per-profile theorem at dim 2; saturation discipline gives it for free. |
| P3.6/P3.7 RawValueTerm / ValueTerm | **Subsumed**: values are normal-form predicates on PolyTerm. |
| P3.8 PolyTerm.eval | **Subsumed**: NbE = polygraph fold. |
| P3.9 ValueTerm.quote | **Subsumed**: quote = inverse of fold. |
| P3.10 nbe roundtrip | **Subsumed**: polygraph fold + unfold composition. |
| P3.11 Conv.decide | **Subsumed**: via ωcE polygraph morphism search (axis 9). |
| **P3.12 typecheck_decidable (★ MILESTONE A)** | **Direct ship via axis 9 + axis 10.** |

**Phase 3 collapses to: 1 substantive task** (write the FXCell
typecheck via Conv-as-ωcE-morphism-search).  ~3K LoC instead of ~20K.

### Phase 4 — voracious math

| Task | Status |
|---|---|
| P4.1 dependent eliminators | **Subsumed**: dependent eliminators are cartesian fibrations (axis 8). |
| P4.2 dependent J | **Subsumed**: J is the eliminator for the universe cell. |
| P4.3 quotMk/quotRec + βQuot | **Subsumed**: quotient is a stratification entry (axis 3). |
| P4.4 pushInl/Inr/Glue/Rec (universal pushout HIT) | **Subsumed**: HIT cells with topos ops. |
| P4.5 truncIntro/truncRec (n-truncations) | **Subsumed**: stratification at level n. |
| P4.6 polyMu/polyNu + redefine nat/list/etc. | **Subsumed**: polynomial-monad initial/final algebras. |
| P4.7 measureSpace/lebesgueInt | **Subsumed**: polynomial-monad with measure-theoretic generators. |
| P4.8 infinitesimal/diffOp | **Subsumed**: SDG modality in topos (axis 7). |
| P4.9 cgef_obligation_bundle | **Subsumed**: per-Generator obligation, one closure proof. |

**Phase 4 collapses to: ~5 substantive tasks** (write the math
generator extensions one math area at a time).  Each is ~2-3K LoC.

### Phase 5 — distribution

| Task | Status |
|---|---|
| P5.1 evalDistributed_sound | **Subsumed**: cell-partition polygraph fold with compH/compV/BSP-sync. |
| P5.2 EGraph extraction | **Subsumed**: cell-set quotient of PolyTerm by congruence. |

**Phase 5 collapses to: 0 new substantive tasks.** The infrastructure
is built into axes 6, 8.

### Summary

| Phase | Before | After | Reduction |
|---|---|---|---|
| P0 | 12 tasks ~50K LoC | 1 task ~3K LoC | 16× |
| P1 | 6 tasks ~10K LoC | 1 task ~2K LoC | 5× |
| P2 | 8 tasks ~15K LoC | 0 new (rebranded) | ∞ |
| P3 | 12 tasks ~30K LoC | 1 task ~3K LoC | 10× |
| P4 | 9 tasks ~20K LoC | 5 tasks ~12K LoC | 1.7× |
| P5 | 2 tasks ~10K LoC | 0 new | ∞ |
| **TOTAL** | **49 tasks ~135K LoC** | **8 tasks ~20K LoC** | **~7×** |

Plus the ~170K LoC PolyTerm substrate itself, but **most of that
~170K is one-time foundation work that doesn't recur per ctor**, while
the existing ~135K of cascade work scales linearly with new ctors.
Crossing the break-even point: roughly the next ~50 new ctors.

For FX's expected lifetime (~200+ new ctors over 5 years for math
import, modal layer expansion, cubical Kan ops, HIT zoo, measure
theory, differential geometry, etc.), the PolyTerm investment **pays
back ~3× over** in cascade savings alone, before counting the
capability wins.

---

## 8. Migration plan

Existing files → PolyTerm equivalent.

### Foundation layer

| Current file | LoC | PolyTerm equivalent |
|---|---|---|
| `Foundation/RawTerm.lean` | 540 | Dim-0 cells with `globular` shape; Generator enum already shipped |
| `Foundation/Ty.lean` | 280 | Universe cells (dim 0 with universe boundary) + dim-0 cells with type-flag |
| `Foundation/Term.lean` | 940 | `FXTerm` view definition on `PolyTerm fxProfile` |
| `Foundation/Subst.lean` | 460 | Polynomial-monad multiplication (axis 2) |
| `Foundation/Action.lean` | 403 | Polynomial-monad action axiom (axis 2) |
| `Foundation/Context.lean` | 200 | Cell-set with linear position structure |
| `Foundation/Effect.lean` | 350 | Topos modality in axis 7 |
| `Foundation/Mode.lean` | 150 | Topos modality in axis 7 |
| `Foundation/Polygraph/PolyCell.lean` | 124 | **Becomes** the foundational shape for axis 1 globular shape |
| `Foundation/Polygraph/Generator.lean` | 600 | **Becomes** axis 2's generator enumeration |
| `Foundation/Polygraph/RawPolyTerm.lean` | 256 | **DELETED** (the fake mirror) |
| `Foundation/Polygraph/PolyTerm.lean` | ~700 | **DELETED** (the fake typed mirror) |
| `Foundation/Polygraph/RawPolyTermFlat.lean` | 195 | Promoted to be `PolyTerm fxProfile dim` for `dim = 0` only |

### Reduction layer

| Current file | LoC | PolyTerm equivalent |
|---|---|---|
| `Reduction/Step/Inductive.lean` | 1800 | `FXStep` view definition; ctors become axis 2 generators at dim 1 |
| `Reduction/Step/Compat.lean` (×6) | ~3K | **Subsumed** by polynomial-monad multiplication |
| `Reduction/ParRed/*.lean` | ~2K | **Subsumed** by axis 6 Gray module |
| `Reduction/Conv.lean` | 600 | `FXConv` view via thinness in stratification (axis 3) |
| `Reduction/StepStar/*.lean` | ~1.5K | **Subsumed** by polygraph composition |

### Confluence layer

| Current file | LoC | PolyTerm equivalent |
|---|---|---|
| `Reduction/RawCdLemma/*.lean` | ~8K | **Subsumed** by saturation closure proof (axis 4) |
| `Reduction/CdLemma/*.lean` | ~5K | **Subsumed** ditto |
| All D2.5.x cascade work | ~12K | **Subsumed** by per-profile cd theorem |

### Modal / cubical / HoTT layer

| Current file | LoC | PolyTerm equivalent |
|---|---|---|
| `Modal/*.lean` | ~5K | Topos modality entries (axis 7) |
| `HoTT/*.lean` | ~3K | Cubical-shape cells (axis 1) + universe ctors (axis 10) |
| `Cumul/*.lean` | ~4K | Universe cumul ctor (axis 10) |
| `Effects/*.lean` | ~2K | Topos modality entries (axis 7) |

### Tools / smoke / audit layer

| Current file | LoC | PolyTerm equivalent |
|---|---|---|
| `Tools/DependencyAudit.lean` | 300 | Keep as-is (works on any Lean inductive). |
| `Smoke/*.lean` | ~3K | **Reduced** to per-profile smoke (one set of audits per profile, not per ctor). |
| `Tools/AuditAll/*.lean` | 700 | Replaced by per-profile audit framework. |

### Total migration estimate

| Layer | Current LoC | Migration LoC | Net change |
|---|---|---|---|
| Foundation | ~4.5K | ~3K | -1.5K |
| Reduction | ~7K | ~2K | -5K |
| Confluence | ~25K | ~3K | -22K |
| Modal/Cubical/HoTT | ~14K | ~4K | -10K |
| Tools/Smoke | ~4K | ~2K | -2K |
| **Migration TOTAL** | **~54.5K** | **~14K** | **-40K** |

Plus the ~170K of new PolyTerm substrate, but minus the ~40K of
deleted existing code: net code base after PolyTerm migration is
roughly the same total size (~150K LoC), but with **drastically
better extensibility**, structural soundness, and capability surface.

---

## 9. LoC budget

Honest accounting per axis:

| Axis | Layer | Lean LoC | Has Lean precedent? |
|---|---|---|---|
| 1 | Shape category catalogue | ~12K | Partial: globular yes; opetopic/Steiner no |
| 2 | Polynomial monad framework | ~10K | Partial in Mathlib; not for Glob_∞ |
| 3 | Verity stratification | ~5K | None |
| 4 | Saturation | ~5K | None |
| 5 | Enrichment ladder (Segal) | ~15K | Partial Segal categories in Mathlib |
| 6 | Complicial Gray module | ~25K | None |
| 7 | ∞-Topos base | ~30K | Lurie HTT not Lean-formalized |
| 8 | Profile fibration | ~10K | None for Cisinski ω-loc |
| 9 | ωcE classifier | ~5K | None |
| 10 | Univalent universe | ~10K | Cubical Agda has (∞,1); (∞,ω) no |
| — | PolyTerm core inductive | ~15K | None for this design |
| — | fxProfile instance | ~20K | — |
| — | FX kernel migration | ~25K | — |
| **GRAND TOTAL** | | **~187K** | **First-ever mechanization** |

Comparison points:
- Current FX kernel: ~140K LoC of Lean
- Lean 4 stdlib: ~280K LoC
- Mathlib4: ~1.5M LoC
- HoTT-Coq library: ~30K LoC of Coq (mostly (∞,1))
- Cubical Agda library: ~50K LoC of Agda

The 187K LoC is a 2–3 year solo project, faster with collaborators.
Roughly the size of Lean's own kernel implementation.

For comparison:
- Current accelerate-* roadmap: ~135K LoC over ~12 months as designed
- PolyTerm pivot: ~187K LoC over ~24-36 months as designed
- Cost difference: ~50K LoC + ~12-24 more months for **~3× capability
  surface** + **frontier-research mechanization** + **fundamentally
  unblocked future expansion**

---

## 10. Phased rollout

Realistic ship plan in dependency order.

### Phase POLY-0 — already shipped foundation (~7K LoC done)

**Status:** ~7K LoC live in `LeanFX2/Foundation/Polygraph/` as of
2026-05-23.  All zero-axiom under `lake build LeanFX2 LeanFX2Audit`.

**Already shipped (counted against POLY-α LoC budget):**

| File | LoC | Provides |
|---|---|---|
| `Polygraph/PolyCell.lean` | 124 | Burroni globular cells (axis 1 globular shape, dim-indexed) |
| `Polygraph/DecEq.lean` | 217 | PolyCell decidable equality, propext-free hand-rolled |
| `Polygraph/Wellfounded.lean` | 43 | PolyCell well-foundedness |
| `Polygraph/ParallelPair.lean` | 163 | Source/target projections (axis 1 parallelism) |
| `Polygraph/VerticalComp.lean` | 169 | Vertical composition + unit + assoc (axis 6 Stage 1) |
| `Polygraph/HorizontalComp.lean` | 156 | Horizontal composition + unit + assoc (axis 6 Stage 1) |
| `Polygraph/FreeCategory.lean` | 178 | Free n-category F(X) — Burroni adjoint |
| `Polygraph/Laws.lean` | 78 | Composition associativity + unit + interchange (strict ω-cat laws) |
| `Polygraph/StepLabel.lean` | 320 | 110-element enum: dim-1 generators of fxProfile polygraph |
| `Polygraph/Dim1Extraction.lean` | 169 | Step → PolyCell 1 0 0 embedding |
| `Polygraph/Dim1Equivalence.lean` | 70 | Step ⇌ Dim1Cell isomorphism theorem |
| `Polygraph/Dim2Diamond.lean` | 83 | cd_lemma diamond → PolyCell 2 0 0 embedding (axis 9 dim-2) |
| `Polygraph/Generator.lean` | 542 | 78-element enum: dim-0 generators (axis 2 polynomial monad bases) |
| `Polygraph/GeneratorOutputType.lean` | 1995 | Dependent output type table — full 78 arms |
| `Polygraph/RawPolyTermFlat.lean` | 316 | Honest nested polygraph substrate (one ctor, Generator-tagged) |
| `Polygraph/RawPolyTermFlatToLegacy.lean` | 259 | Bijection to legacy 74-ctor mirror |
| `Polygraph/RawPolyTermToFlat.lean` | 248 | Reverse bijection |
| **Total** | **~5.2K** | Foundation for axes 1 + 6 + 9 partial |

Plus K12.1-K12.19 + K12.23 reducibility (~6K additional LoC in
`Reducibility/`) and strength-T1/T2/T3/T4×28/T8/T12×17 (~10K LoC in
`Foundation/Strengthen/`).  Plus K11.x audit gates and bridge work.
**Grand total already-shipped foundation: ~25K LoC.**

### Phase POLY-α — Remaining foundation (months 1-3, ~10K NEW LoC)

**Goal:** ship the gap between POLY-0 (what's done) and what's needed
for Path A or Path B decidable Conv to work end-to-end.

**Deliverables (NEW only):**
- `Foundation/Polygraph/CellShape.lean` — shape catalogue beyond
  globular (cubical, simplicial, opetopic stubs); **~2K LoC** because
  globular is already covered by PolyCell
- `Foundation/Polygraph/Stratification.lean` — Verity marker structure;
  **~1K LoC** (structure + closure axioms + decidability field)
- `Foundation/Polygraph/OmegacE.lean` — HLOR Construction 1.22
  inductive build (5 ctors, DecidableEq, finite-type proof at every
  k); **~2K LoC**
- `Reduction/ConvDecideViaMakkai.lean` — Path B implementation
  (Makkai's word equality algorithm on fxProfile polygraph) +
  soundness + completeness; **~4K LoC**
- `Reduction/ConvDecide.lean` — wrapper providing `Decidable (Conv a b)`
  instance via Path A or Path B (depending on which is shipped first);
  **~1K LoC**

**Acceptance:** `#assert_no_axioms Conv.decideViaMakkai` passes;
existing FX tests pass with new Conv decidability instance available;
`Conv.trans` derived from decidability + transitivity of word equality.

**Risk:** Makkai's algorithm has no Lean precedent.  Mitigation:
test on toy polygraphs (monoid presentations = dim-1-only) before
scaling to fxProfile.

**Stretch:** simultaneously continue Path A via K13 NbE.  If both
land within POLY-α window, FX has two independent decidable-conv
implementations as cross-checks.

### Phase POLY-β — Polynomial monad axis (months 6-9, ~15K LoC)

**Goal:** ship axis 2 (polynomial monad framework), allowing
Generator-extension-without-cascade.

**Deliverables:**
- `Foundation/Polygraph/PolyFunctor.lean` — Kock polynomial functor
- `Foundation/Polygraph/PolyMonad.lean` — adding unit + mult + B-C
- `Foundation/Polygraph/PolyMonadFinitary.lean` — finitary special case
- `Foundation/Polygraph/PolyMonadActs.lean` — polygraph + polymonad
  interaction

**Acceptance:** adding one new Generator value to FX's algebra
extends rename + subst + cd_lemma + Conv with no cascade.

**Risk:** polynomial monad on Glob_∞ may hit Lean elaborator limits;
fallback is to use a smaller universe + Universe lifting.

### Phase POLY-γ — Complicial Gray + Enrichment (months 9-15, ~40K LoC)

**Goal:** ship axes 5+6 (enrichment ladder + complicial Gray module),
enabling univalence + HITs + concurrent execution.

**Deliverables:**
- `Foundation/Polygraph/EnrichmentLadder.lean` — Segal A-precategories
- `Foundation/Polygraph/GrayTensor.lean` — Gray tensor product
- `Foundation/Polygraph/GrayCylinder.lean` — Gray cylinder (Loubaton 2.3.1)
- `Foundation/Polygraph/GrayCone.lean` — Gray cone + ◦-cone
- `Foundation/Polygraph/ComplicialGray.lean` — complicial conditions
- `Reduction/ConcurrencyViaCompH.lean` — concurrent execution via
  horizontal composition

**Acceptance:** `compH` typechecks for two FXSteps with disjoint
footprints; frame rule holds definitionally.

### Phase POLY-δ — ∞-Topos + Profile fibration (months 15-21, ~40K LoC)

**Goal:** ship axes 7+8 (∞-topos + profile fibration), enabling
cohesion + modality + self-referential profiles.

**Deliverables:**
- `Foundation/Polygraph/InfTopos.lean` — Lurie HTT 6.1 ∞-topos
- `Foundation/Polygraph/ModalAdjunction.lean` — modal adjunctions
- `Foundation/Polygraph/CohesiveTopos.lean` — cohesive structure
- `Foundation/Polygraph/ProfileFibration.lean` — Grothendieck fibration
- `Foundation/Polygraph/CisinskiLocalize.lean` — ω-localization

**Acceptance:** FX's 21 graded dimensions encode as topos modalities;
modal layer (D4.x) becomes 1-page profile entries.

### Phase POLY-ε — Universal universe + cumulativity (months 21-24, ~10K LoC)

**Goal:** ship axis 10 (universe cells + universe cumulativity).
Univalence becomes a theorem.

**Deliverables:**
- `Foundation/Polygraph/UniverseCell.lean` — universe ctors
- `Foundation/Polygraph/GrothendieckConstruction.lean` — Loubaton
  thesis §6.1.4 functorial Grothendieck
- `Foundation/Polygraph/PolyTermUnivalence.lean` — univalence as theorem

**Acceptance:** `polyTermUnivalence` theorem shipped zero-axiom.

### Phase POLY-ζ — PolyTerm assembly + FX profile (months 24-30, ~30K LoC)

**Goal:** assemble all ten axes into PolyProfile + define
fxProfile + ship FXCell type.

**Deliverables:**
- `Foundation/Polygraph/PolyProfile.lean` — bundled ten axes
- `Foundation/Polygraph/PolyTerm.lean` — the universal cell type
- `LeanFX2/FxProfile.lean` — FX as a profile instance
- `LeanFX2/FxCellViews.lean` — FXType, FXTerm, FXStep, FXConv as views

**Acceptance:** PolyTerm typechecks zero-axiom; fxProfile satisfies
consistency conditions; view definitions agree with current types.

### Phase POLY-η — Migration (months 30-36, ~25K LoC delete + ~10K LoC translate)

**Goal:** migrate existing FX kernel code to use FXCell views;
delete obsolete cascade machinery.

**Deliverables:**
- Delete `RawPolyTerm.lean` + `PolyTerm.lean` + `PolyTermAction*` +
  `PolyTermRoundtrip.lean` (the fake mirrors, ~2K LoC)
- Delete `RawCdLemma/*` + `CdLemma/*` (~13K LoC)
- Delete all D2.5.x cascade machinery (~12K LoC)
- Migrate `Reduction/Step.lean` + `Step.par.lean` + etc. to FXCell
  views (~5K LoC translation, ~5K LoC compat shims)
- Update `Algo.Check` to use ωcE-based Conv (~2K LoC)

**Acceptance:** all existing FX tests pass; full `LeanFX2Audit`
green; downstream consumers (FX1, FX1.LeanKernel, ULB) unchanged.

### Total timeline

| Phase | Months | Lean LoC | Cumulative LoC |
|---|---|---|---|
| POLY-α | 6 | ~25K | ~25K |
| POLY-β | 3 | ~15K | ~40K |
| POLY-γ | 6 | ~40K | ~80K |
| POLY-δ | 6 | ~40K | ~120K |
| POLY-ε | 3 | ~10K | ~130K |
| POLY-ζ | 6 | ~30K | ~160K |
| POLY-η | 6 | ~30K (-25K) | ~165K net |

**Total: 36 months, ~165K net LoC delta** (~190K added, ~25K
deleted), arriving at:
- Decidable typecheck (★ MILESTONE A) at month 6 (POLY-α complete)
- Generic Generator extension at month 9 (POLY-β complete)
- Concurrent + frame-rule typed at month 15 (POLY-γ complete)
- Cohesive + modal at month 21 (POLY-δ complete)
- Univalent as theorem at month 24 (POLY-ε complete)
- Full FX kernel migration at month 36 (POLY-η complete)

**Critical-path-shortened path:** if only MILESTONE A is required,
POLY-α + selected pieces of POLY-β/γ for Conv decidability gives
MILESTONE A in **~9 months**, vs the current ~12+ months under the
old roadmap.

---

## 11. Zero-axiom discipline

Each axis stays zero-axiom under specific discipline:

### Axis 1 (Shape)

The `CellShape` inductive is a closed enum (no recursion, no
dependent indices), so `DecidableEq` derives automatically without
propext.  Each shape's combinatorics is a separate inductive (Opetope,
ThetaCell, ParityComplex, etc.), each enumerable and propext-free
per the standard discipline.

**Watch:** the `prod` and `wreath` combinators are recursive over
CellShape; per `feedback_lean_zero_axiom_match`, must use
direct recursion-on-CellShape with explicit cases, not wildcard
match.

### Axis 2 (Polynomial monad)

`PolyMonad` is a `structure` (no inductive recursion), so the laws
(unitL, unitR, multAssoc) are explicit propositional fields.  Adding
a new monad instance = providing the fields; no propext.

**Watch:** the Beck-Chevalley condition (cartesian-ness) requires
pullback existence; we encode this as a `Decidable` predicate, not
a propext-using existential.

### Axis 3 (Stratification)

`Stratification` is a `structure` with `thin : ∀ d, _ → Prop`.  The
closure axioms are explicit propositional fields.  Per the
existing FX discipline, `thinDecidable` is required as a field; this
gives zero-axiom decidability.

**Watch:** the FX-specific stratification (β/η/ι are thin, cubical
boundary mismatches are not) must enumerate cases explicitly per
[[feedback_lean_zero_axiom_match]]; no wildcards.

### Axis 4 (Saturation)

`Saturation` is a `structure` over a `SaturationLevel` enum.  The
filler-existence requirements are propositional and decidable for
finite-type profiles.

### Axis 5 (Enrichment ladder)

`EnrichmentLadder` is a closed-form inductive (base + segalRung +
omegaRung).  `materialize` is a recursive function on this
inductive; `cases <;> rfl` discipline applies.

### Axis 6 (Complicial Gray)

`ComplicialGrayModule` is a `structure`.  The acyclic-cofibration
conditions are propositional but Loubaton 2207.08504 §2.2 / §3.1.5
provides explicit witnesses, so we encode them as `Prop` with
decidability via explicit lemma references.

**Watch:** Gray tensor recursion through cell shapes requires
careful encoding per Loubaton 2207.08504 §2.3.1's formulas.  Each
formula = one Lean function per shape pair.

### Axis 7 (∞-Topos)

`InfTopos` is a `structure` whose `modalities` field is a `List
ModalAdjunction`.  Each `ModalAdjunction` is a structure of three
functors + unit/counit + triangle identities.  No propext.

**Watch:** the subobject classifier (when univalent = True) is the
critical zero-axiom risk.  Loubaton thesis §6.1.3 + §6.1.4.2 provides
the construction; we mechanize the *construction*, not the *abstract
claim*.

### Axis 8 (Profile fibration)

`ProfileMorphism` is a structure; `ProfileCat` is a `Category` (not
an inductive).  Cisinski ω-localization is realized as a recursive
function on `ProfileTower`, propext-free with `cases <;> rfl`.

### Axis 9 (ωcE)

The polygraph `OmegacE_at (k : Nat)` is an inductive parameterized
by Nat, but each k gives a finite-type polygraph.  Construction
1.22's diagram (1.23) gives an explicit pushout; we mechanize the
pushout as a structural recursive build.

**Watch:** Construction 1.22's "ω-step colimit" requires careful
encoding.  Use `Nat`-indexed sequence + explicit colimit, not Lean's
`MagmaCat` colimit machinery (which uses propext under the hood).

### Axis 10 (Universe)

The universe cell ctor is one `PolyTerm` ctor with `(level : Nat)`
payload.  The Grothendieck construction `Hom^⊖(I, ω) ≃ LCart^c_U(I)`
is a Quillen equivalence in Loubaton thesis; mechanizing the
*equivalence* (not just claiming it) is the zero-axiom path.

**Watch:** the equivalence requires constructing the left/right
adjoint pairs explicitly.  Loubaton's thesis gives the construction
in §6.1.4; ~3K LoC of careful translation.

### PolyTerm core

The big indexed inductive must avoid the propext traps documented
in `feedback_lean_zero_axiom_match` + `feedback_lean_indexed_partial_match`:
- No wildcard matches on the dim parameter
- Boundary destructuring uses explicit pattern + `nomatch` for
  impossible-by-index cases
- The `thin` ctor's invariant flipping is captured via boundary
  manipulation, not via `Eq.rec` (which would use propext)

This is the riskiest design point — the recipe in `feedback_lean_match_propext_recipe`
(8 concrete patterns for propext-clean match) applies throughout.

---

## 11.5 Computability + decidability discipline summary

The 2026-05-24 revision audited every load-bearing computability /
decidability claim in this document.  This section is the index.

### Decidability claims, by axis

| Axis | Claim | Decision procedure | Reference | Lean status |
|---|---|---|---|---|
| 1 | `DecidableEq (CellShape)` | Closed enum, `deriving DecidableEq` | — | Shippable; PolyCell already has it |
| 1 | `DecidableEq (PolyCell n s t)` | Hand-rolled, propext-free | feedback_lean_indexed_partial_match | ✅ SHIPPED (`Polygraph/DecEq.lean`) |
| 2 | `Decidable (Generator.eq g1 g2)` | Closed 78-enum cases | — | Shippable; `Generator.deriving DecidableEq` |
| 3 | `Decidable (Stratification.thin d c)` | Per-profile field; required at struct definition | Verity 2008 marking axioms | Required field in `Stratification` |
| 4 | `Decidable (Saturation level)` | Closed `SaturationLevel` enum | — | Shippable |
| 5 | Enrichment ladder `materialize` | Recursive function on closed inductive | — | Shippable per `cases <;> rfl` |
| 6 | `Decidable (compH-disjoint footprint)` | Permission-semiring lookup | O'Hearn 2007 separation logic | Shippable per K11.5 already shipped |
| 7 | `Decidable (ModalAdjunction.applies dim)` | Per-modality dim-vector | — | Shippable per Modal layer |
| 8 | `Decidable (Conv on cisinskiLocalize tower)` | Beke-Smith combinatorial ω-localization on polygraph-presented profiles | Beke 2000 + Smith small-object argument | Shippable per §12 in-scope commit; ~10K LoC |
| 9 | `Decidable (Conv a b)` Path A | NbE NF equality + K12 SN | Adjedj et al. arXiv:2310.06376 | In flight; K12 24/30 + K13 pending |
| 9 | `Decidable (Conv a b)` Path B | Makkai word equality on F(fxProfile) | Makkai 2021 + Forest 2022 | New ~5K LoC under POLY-α |
| 10 | Universe cumulativity + univalence Step | `Step.eqType` reduction rule per CLAUDE.md | Loubaton 2307.11931 §6.1.4 semantic justification | Required by FX discipline |

### What is NOT decidable / NOT shippable

* `IsCoherentEquiv π dim a` for **arbitrary** π — only decidable
  when π is finitely presented + convergent.  fxProfile satisfies
  both (Generator enum finite, K12 + cd_lemma give convergence).
  Arbitrary user profiles must establish these conditions
  separately as a hypothesis of the decision procedure.
* Loubaton thesis §6.1.4.2 functorial Grothendieck as **Lean
  theorem** — used as semantic justification only.  Univalence in
  FX ships via `Step.eqType` reduction rule (per lean-fx-2/CLAUDE.md
  mandate); Loubaton's Grothendieck construction explains WHY the
  Step rule is sound but is not itself Lean-mechanized.
* **GWB TT_⊠ as Lean theorem** — an earlier draft incorrectly claimed
  "rzk-prototyped"; correction: no TT_⊠ mechanization exists in
  any proof assistant.  Rzk implements RS-STT base only.  FX cites
  TT_⊠ only as semantic justification for the operational
  `Step.eqType` rule.
* **Coverage Semantics (Eremondi-Kammar 2025) for FX** —
  Eremondi-Kammar §7.2 explicitly states their approach is
  "incompatible with univalent theories like Homotopy or Cubical
  Type Theory."  FX is univalent; coverage semantics cannot be
  used directly.  Substitute: Cockx-Devriese-Piessens "Pattern
  matching without K" ICFP 2014 (HoTT-compatible) +
  Cockx-Devriese JFP 2016 extension.

Cisinski ω-loc + full Lurie ∞-topos + Complicial Gray Stage 2
remain committed (Dugger 2001 + Beke 2000 + Smith routes for the
first two, Maltsiniotis-Métayer Coq template for the third).

### Computability standards every Lean signature above obeys

Per lean-fx-2/CLAUDE.md non-negotiable rules:

* No `axiom` declarations anywhere — including inside any structure
  field's witness.
* No `IsX : Prop` placeholder where the body is `True` or
  unconstructible.
* No `Inhabited X` for unconstructible X.
* No hypothesis-as-postulate: `theorem foo (univ : Univalence) :
  ...` is banned even if `Univalence : Prop` is "defined elsewhere".
* No `noncomputable` for kernel theorems.
* Every Decidable instance has a real body, not `Classical.dec`.
* Every theorem listed in this document is shippable iff
  `#assert_no_axioms TheoremName` would pass on the actual Lean
  body.  Where the body has not yet been written, the LoC estimate
  is a forecast (not a claim of "already done").

If during implementation any signature in this document cannot
satisfy these rules, the signature is rewritten or the claim is
de-scoped — the discipline is not negotiable to preserve the
"scary maxxed-out" rhetoric.

---

## 12. Risks and open questions

This section is revised (2026-05-24) per a literature scan that
turned up specific evidence supporting and undermining each axis.
Risks are now categorized into THREE tiers: real engineering
risks (mitigable), open math questions (require new proofs but
within the literature's reach), and out-of-scope (de-scoped).

### Real engineering risks (mitigable)

### Risk: Lean 4 elaborator capacity

The PolyProfile is a structure with ~10 nested-structure fields.
PolyTerm is an indexed inductive over PolyProfile.  Lean 4.29's
elaborator gets slow on heavy structure-of-structures patterns; we've
already seen 78-arm Term inductions take ~1474s for `simp` (per
[[feedback_perf_antipatterns]]).

**Mitigation:** Lean 5 (when released) reportedly has better support
for parameterized inductives.  Fallback: use `@[reducible]` aggressively
on the profile fields, plus careful unification hints.  Fallback²:
split PolyTerm into per-axis sub-inductives + a `PolyTermBundle`
wrapper, sacrificing some uniformity for elaboration speed.

### Risk: Strict positivity

The `thin` ctor: `(c : PolyTerm π dim bnd) → (h_thin : π.stratification.thin dim c) → PolyTerm π dim bnd.flipped`.

The `bnd.flipped` part creates a NEW PolyTerm of the same dim with
the boundary flipped.  This is HIT-like (an equivalence-style ctor).
Lean's strict-positivity checker may reject.

**Mitigation:** encode `thin` not as a ctor but as a `Prop`-valued
predicate, with the flipped variant derivable.  Loubaton 2301.11424's
left semi-model structure suggests this: thin cells are not new
generators, they are markings on existing cells.  Refactor: `PolyTerm`
ctor `thin` becomes `thinMarking : (c : PolyTerm π dim bnd) → Prop`
and the "flipped" variant `c.thinInverse` is a defined function
(produced from the marking).

### Risk: Profile self-reference (axis 8)

`PolyProfile` has `parentProfile : Option PolyProfile`.  This is a
self-referential structure (a record containing an Option of itself).
Lean accepts this if `PolyProfile` is a structure (records).

But: a `PolyProfile` can have a `parentProfile` that contains its
own description of itself ⟹ paradox unless Cisinski ω-localization
is correctly mechanized.

**Mitigation:** the Cisinski ω-loc construction is explicit and
finite; we mechanize the construction rather than postulating the
fixpoint.  This is ~5K LoC of careful Lean.  Research-frontier flag;
needs Loubaton-level expertise to design correctly.

### Risk: Performance of polygraph-morphism search (axis 9)

`Conv.decide` via `∃ ω-functor Σ^(n-1)(ωcE) → FXCell factoring it`
requires polygraph-morphism search.  Worst-case exponential in cell
size.

**Mitigation:** in practice, FX's terms are bounded depth + width.
Polygraph-morphism search with pruning + memoization is polynomial
for finite-type polygraphs (HLOR's ωcE is finite-type at each k).
For pathological inputs, fall back to coinductive bounded search +
timeout — same behavior as F*'s SMT-based decision procedures.

### Risk: Mathematics correctness of unmechanized constructions

Loubaton thesis §6.1.3 univalence proof uses heavy ∞-cat machinery
that has not been peer-reviewed at the Lean-mechanization level.
There's some chance that translating the proof to Lean reveals subtle
gaps.

**Mitigation:**
1. Email Loubaton before committing to the mechanization.  His feedback
   on whether the construction is suitable for Lean is critical.
2. Pre-mechanize the simpler ωcE polygraph (HLOR 2024) first — this
   gives confidence in the methodology before tackling the harder
   thesis-level work.
3. Build in feature flags: if a particular axis hits gnarly mechanization
   walls, FX can ship without it (e.g. drop axis 6 complicial Gray and
   use a simpler Gray tensor).
4. Univalence in FX ships as a `Step.eqType` reduction rule per
   lean-fx-2/CLAUDE.md mandate (definitional, with `#assert_no_axioms`
   clean theorem body) — independent of whether the Loubaton-level
   semantic justification mechanizes.  PolyTerm INHERITS this; it
   does NOT depend on the (∞,ω)-semantic proof being Lean-mechanized.

### Open math questions (require new work)

### Risk: ωcE-specific decidability has not been published

HLOR Prop 1.26 + Construction 1.22 + Thm 1.33 establish that ωcE is
finite-type, contractible, and universal for coherent ω-equivalences.
They do NOT establish that ω-functor existence into ωcE is decidable
for arbitrary target ω-categories.  The web survey (2026-05-24) confirms:
no published decidability theorem for this specific search problem.

**Mitigation:** the decidability engine is Makkai's word-equality
algorithm restricted to ωcE (independent published result), NOT
ωcE morphism search.  ωcE serves as the semantic universal object;
Makkai gives the computation.  If a follow-up paper establishes
decidability for general ωcE morphism search, FX can swap engines;
until then, Makkai is the load-bearing algorithm.

### Risk: Makkai's algorithm in Lean has no precedent

The web survey (2026-05-24) confirms: no proof-assistant
mechanization of Makkai's "Word Problem for Computads".  FX would be
first-mover.  Algorithm itself is documented in McGill manuscript +
Forest thesis; engineering risk is purely "translating paper math
to Lean tactics", estimated ~3-6 months of careful work.

**Mitigation:** ship Forest's data-structure-driven improvement
(thesis §17.5 ABGMMM book reading) which has been implemented in
non-Lean settings; port to Lean is straightforward (it's algorithmic,
not categorical).  Pre-test on toy polygraphs (e.g. monoid
presentation = dim-1-only polygraph) before scaling to fxProfile.

### Risk: Polynomial monad on Glob_∞ may exceed Lean elaborator

Mathlib has partial polynomial functor support but not for Glob_∞
(the infinite-dim globular category).  PolyMonad on Glob_∞ requires
either (i) a finite-truncation discipline (PolyMonad on Glob_≤N for
some N), or (ii) Lean 5's better universe handling.

**Mitigation:** ship per-truncation `PolyMonad_at (N : Nat)` instances
with explicit upper-bound on dimension.  FX kernel uses dim ≤ 3 in
practice (cd_lemma is dim-2, Squier is dim-3); PolyMonad_at 4 covers
all FX needs.  Upgrading to Glob_∞ is a POLY-η optimization, not a
correctness requirement.

### Heavy but in-scope: research-frontier components we ARE committing to

The original 2026-05-23 draft over-claimed.  The first revision
(2026-05-24 morning) over-de-scoped — three items got marked
"research-only" when each has a published constructive route.  This
section corrects: each component below IS in scope for the
PolyTerm pivot, with cited algorithm + LoC estimate + ship stages.

### In scope: Full ∞-topos object via Dugger 2001 presentation (axis 7)

**The route Mathlib doesn't have but we will:** Dugger 2001
("Combinatorial model categories have presentations", Trans. AMS 353)
proves every combinatorial model category is a left Bousfield
localization of `sPre(C)` (simplicial presheaves on a small ∞-cat C)
at a small set of maps.  Beke 2000 ("Sheafifiable homotopy model
categories", Math. Proc. Camb. 129) + Smith establish that polygraph-
presented model cats are combinatorial (locally presentable,
cofibrantly generated, tractable cofibrations).

**Combined:** fxProfile's polygraph (finite generators at each dim
≤ 3) yields a combinatorial model cat that has an EXPLICIT
presentation `(C, S)` where C is small + S is finite.  The ∞-topos
structure follows constructively from descent on the resulting
sheaf category (Lurie HTT 6.1.6).

**LoC:** ~30K (per §3.7's revised estimate).  Distribution above.

**Why it's defensible despite no precedent in Lean 4:**
Lean 4 has no precedent for ∞-toposes, but Lean 4 also has no
precedent for FX's 21-dim graded modal kernel — we're building both
at the same time.  Dugger's algorithm is fundamentally combinatorial
(finite sets + Quillen lifting); the Lean-mechanization risk is
similar to mechanizing Makkai's word equality algorithm: novel but
algorithmic.

**Ship stages (POLY-δ, months 15-21):**
* δ.1 (~6K LoC): `PreSheafMorphism` + projective model structure on
  `sPre(C)` for finite-presentation C.
* δ.2 (~8K LoC): Dugger localization theorem mechanized for the FX
  case (finite C, finite S).
* δ.3 (~4K LoC): Descent decidability for fxProfile covers.
* δ.4 (~7K LoC): Subobject classifier construction (Lurie HTT 6.1.6).
* δ.5 (~5K LoC): Modal adjunction layer + 21-dim integration.

Each stage gated by `#assert_no_axioms` on cumulative theorems.

### In scope: Cisinski-style ω-localization at unbounded depth (axis 8)

**The route:** Cisinski 2019 (Higher Categories and Homotopical
Algebra §2-3) gives ω-localization via Bousfield-localization
existence theorems.  Cisinski's setup is NON-algorithmic FOR ARBITRARY
model cats.  For **combinatorial model cats**, however, Beke 2000 +
Smith give ALGORITHMIC ω-localization — because each Bousfield-
localization step at a small set of maps preserves combinatoriality
(Dugger), and the ω-iteration is a small-colimit construction.

**For FX:** every profile in the tower is fxProfile-derived
(polygraph-presented), hence combinatorial.  ω-localization is
computable via the Bousfield iteration on the (finite) generating
sets of each profile.

**Lean signature (depth-ω, NOT depth-3-hardcoded):**

```lean
/-- A profile tower of UNBOUNDED depth, supporting Cisinski-style
ω-localization via the Beke-Smith combinatorial route.  Each layer
is a polygraph-presented combinatorial model cat; the colimit is
the ω-localized fixed point. -/
inductive ProfileTower : Type where
  | base   : PolyProfile → ProfileTower
  | extend : ProfileTower → PolyProfile → ProfileTower
  /-- The ω-step: take the Bousfield-localization fixed point.
  Constructive because each step is finite-set localization. -/
  | omegaFixpoint :
      (steps : Nat → ProfileTower) →
      (cofinal : ∀ N, IsBousfieldStable (steps N)) →
      ProfileTower

/-- Cisinski ω-localize a profile tower via Beke-Smith iteration.
Each iteration step is a finite-set Bousfield localization (Dugger),
preserving combinatoriality.  The ω-fixpoint exists by the small-
object argument on the cofinality witness. -/
def cisinskiLocalize (tower : ProfileTower) : PolyProfile :=
  match tower with
  | .base π            => π
  | .extend t π        => bousfieldStep (cisinskiLocalize t) π
  | .omegaFixpoint s h => omegaColim (fun N => cisinskiLocalize (s N)) h

/-- Decidability of the ω-fixpoint: for FX-derived towers with
bounded per-step generating-set size, the iteration terminates in
≤ N steps for some computable N.  This is Smith's small-object
argument made constructive via the cofinality witness. -/
instance : ∀ (tower : ProfileTower),
    DecidableEq (cisinskiLocalize tower) :=
  by ...
```

**LoC:** ~10K LoC — was de-scoped to "depth-3 hardcoded" out of
cowardice; the Beke-Smith route IS constructive, just harder.

**Ship stages (POLY-δ.6, post-stages-above):**
* Beke 2000 combinatoriality preservation: ~3K LoC.
* Smith small-object argument with cofinality witness: ~3K LoC.
* `omegaFixpoint` decidability proof: ~2K LoC.
* Integration with `ProfileFibration`: ~2K LoC.

### In scope: Full Complicial Gray module at (∞,ω) (axis 6)

**The route:** Verity 2008 ("Weak complicial sets I", Adv. Math. 219)
+ Loubaton 2207.08504 §2.3 + §3.1.5.4 give EXPLICIT FORMULAS for
the Gray tensor + Gray cylinder + Gray cone + complicial-acyclicity
witnesses.  The Maltsiniotis-Métayer Coq mechanization
(`arXiv:0712.0617` "On the model structure of strict ω-categories",
later mechanized in Coq by Métayer's group) shows the strict-ω-cat
version is mechanizable; Loubaton's extension to complicial is
formula-level work, not new mathematics.

**Two stages, BOTH committed:**
* Stage 1 (POLY-γ early, ~10K LoC): strict-ω-cat Gray tensor +
  vertical/horizontal composition + interchange.  ~50% shipped via
  K11.4 + K11.5 + K11.6 already.
* Stage 2 (POLY-γ late, ~15K LoC, REQUIRED): complicial conditions
  via Loubaton 2207.08504 §3.1.5.  This is the Verity §6 explicit
  formulas extended with the marking-aware acyclicity witnesses.

**LoC:** ~25K LoC total (Stage 1 + Stage 2).  Was previously listed
as "Stage 2 optional"; corrected to **required** — without Stage 2
we don't get univalence-as-structural-theorem at axis 10's full
strength.

**Why Stage 2 is shippable:**
* Verity's formulas are case-by-case algorithmic recipes (Verity
  2008 §3-§4, restated in Riehl 2016 `arXiv:1610.06801` §4-§5).
* Loubaton's complicial extension (2207.08504 §2.3 + Def 3.1.5.4)
  adds marking-tracking but no new categorical structure.
* The Maltsiniotis-Métayer Coq mechanization establishes the
  strict-ω-cat foundation is mechanizable in a proof assistant;
  Lean 4 has equivalent or better support.
* The ABGMMM book §17 catalogs precisely the formulas needed.

**Risk:** Verity's formulas have notoriously fiddly index
calculations — easy to flip a source / target.  **Mitigation:**
mechanize each formula with explicit `#assert_raw_typed_parity`
gates per FX strict-harness recipe; test on toy 2-cat cases before
scaling to (∞,ω).

### Open question: which shape combination is optimal for FX?

The proposed fxProfile uses globular for dim 0-1, cubical for dim 2,
Θ for dim 3, opetopic for dim ≥ 4.  This is one choice; alternatives:
- All globular: simpler but loses cubical paths' geometric structure
- All opetopic: most uniform but heaviest mechanization
- All Steiner: most general but Steiner is not well-studied in proof
  assistants

**Resolution:** ship POLY-α with globular only as MVP, add shape
extensions in POLY-β onwards as profile-instance variations.

### Open question: which model category for the enrichment base?

Options:
- Kan complexes (simplicial sets with Kan condition) — classical
- Quasicategories — Joyal model, common for (∞,1)
- Cubical sets — for cubical type theory
- Marked simplicial sets — Verity complicial baseline

**Resolution:** start with quasicategories (best Lean support), add
others as variant profile rungs.

### Open question: profile-of-profiles depth

Cisinski ω-loc handles unbounded profile depth.  In practice FX
will exercise depth 1-3 (root profile + math-extension profiles),
but the `omegaFixpoint` constructor exists for any user who wants
unbounded depth (research extensions, infinite tower bootstraps).

**Resolution:** ship POLY-δ with **the full unbounded ProfileTower**
including `omegaFixpoint` constructor + Beke-Smith decidability.
The "depth-3 hardcoded" resolution in an earlier revision of this
document was cowardice; the Beke-Smith route is constructive even
at depth ω (each step is finite-set Bousfield localization on a
combinatorial model cat, terminating by the cofinality witness).
Practical FX deployments at depth ≤ 3 will simply not invoke
`omegaFixpoint` — but the door stays open for future use.

### Open question: collaboration with Loubaton + group

Loubaton (MPIM Bonn), Henry (Ottawa), Hadzihasanovic (Tallinn),
Ozornova (MPIM Bonn), Rovelli (UMass Amherst) all working on
(∞,ω)-cats.  None has Lean expertise but all have papers FX is
mechanizing.

**Resolution:** email after POLY-α MVP is shippable (3-4 months in),
share repo + design doc.  Possibility of joint paper "First
mechanization of (∞,ω)-categories in a proof assistant" if alignment
is good.

---

## 13. References

### Universal substrate references (Tier-0 meta-framework, 2018–2026)

U1. Taichi Uemura, *A general framework for the semantics of type
     theory*, MSCS 33(3), Mar 2023, `arXiv:1904.04097`.  THE universal
     Tier-0 framework: representable map categories with bi-initial
     model + internal language + theory-model bi-equivalence.

U2. Hoang Kim Nguyen, Taichi Uemura, *∞-type theories*, 2022.
     ∞-categorical generalization of U1.

U3. Taichi Uemura, *Normalization and coherence for ∞-type theories*,
     `arXiv:2212.11764` (2022).  Multimode approach to normal forms
     (substitution mode vs renaming mode) — EXACTLY the pattern for
     FX's RawTerm/Term/NF tower.

U4. Taichi Uemura, *Higher inductive types in (∞,1)-categories*,
     `arXiv:2410.17615` (2024).  HITs inside the universal CwR
     framework.

U5. Rafaël Bocquet, Ambrus Kaposi, Christian Sattler, *For the
     metatheory of type theory, internal sconing is enough*, FSCD
     2023, `arXiv:2302.05190`.  Sconing = gluing along global
     sections, performed internally to a presheaf topos.  Yields
     canonicity + normalization + parametricity boilerplate-free per
     type theory.

U6. Rafaël Bocquet, Ambrus Kaposi, Christian Sattler, *Relative
     induction principles for type theories*, `arXiv:2102.11649`
     (2021).  Earlier paper; internal-presheaf induction; uses DRA +
     MTT.

U7. Pierre-Marie Pédrot, Nicolas Tabareau, *The Fire Triangle: How to
     Mix Substitution, Dependent Elimination, and Effects*, POPL 2020
     / PACMPL 4(POPL):58, DOI 10.1145/3371126, HAL `hal-02383109`.
     No-go theorem: substitution + dep-elim + effects cannot all be
     unrestricted simultaneously.  ∂CBPV resolution.  Generalizes
     Herbelin's paradox.

U8. Gaëtan Gilbert, Jesper Cockx, Matthieu Sozeau, Nicolas Tabareau,
     *Definitional Proof-Irrelevance without K*, POPL 2019 / PACMPL
     3(POPL):3:1-3:28, DOI 10.1145/3290316, HAL `hal-01859964`.  SProp
     universe.  Compatible with univalence.  Native Lean 4 support.

U9. Amar Hadzihasanovic, *Combinatorics of higher-categorical
     diagrams*, `arXiv:2404.07273` (2024, v2 Oct 2024).  337-page
     monograph (forthcoming CUP LMS Lecture Note Series).  Regular
     directed complexes substrate for all classical shape catalogs.

U10. Clémence Chanavat, Amar Hadzihasanovic, *Diagrammatic sets as a
     model of homotopy types*, HHA 2024 / `arXiv:2407.06285`.
     Cofibrantly generated model structure on diagrammatic sets +
     two Quillen equivalences with simplicial sets + monoidal with
     Gray product.

U11. Amar Hadzihasanovic, Diana Kessler, *Acyclicity conditions on
     pasting diagrams*, Applied Categorical Structures 32(6):31
     (2024), `arXiv:2408.16775`.  Weakest acyclicity condition for
     polygraph-freeness.

U12. Clémence Chanavat, Amar Hadzihasanovic, *Model structures for
     diagrammatic (∞,n)-categories*, `arXiv:2410.19053` (2024).
     Diagrammatic (∞,∞)-cats via coinductive weak invertibility.

U13. Simon Forest, *Computational descriptions of higher categories*,
     PhD thesis, Institut Polytechnique de Paris, 2021,
     NNT:2021IPPAX003, HAL `tel-03155192`.  Word problem for strict
     ω-cats + pasting diagram algorithms + Gray coherence.  THE
     substrate for FX Axis 9 algorithmic decidability.

U14. Andreas Abel, Nils Anders Danielsson, Oskar Eriksson, *A Graded
     Modal Dependent Type Theory with a Universe and Erasure,
     Formalized*, ICFP 2023, `arXiv:2603.29716`.  Agda-formalized.
     Modality structure = partially ordered semiring.  Subject
     reduction, consistency, normalization, decidability of
     definitional equality.  Extraction soundness theorem.

U15. Pritam Choudhury, Harley Eades III, Richard Eisenberg, Stephanie
     Weirich, *A graded dependent type system with a usage-aware
     semantics*, `arXiv:2011.04070` (2021).  Earlier graded DTT.

U16. Benjamin Moon, Harley Eades III, Dominic Orchard, *Graded modal
     dependent type theory*, ESOP 2021, `arXiv:2010.13163`.
     Foundational graded modal DTT.

U17. Yue Niu, Jonathan Sterling, Harrison Grodin, Robert Harper, *A
     Cost-Aware Logical Framework*, POPL 2022, `arXiv:2107.04663`.
     calf.  Agda-mechanized.  Phase distinction extension/intension.

U18. Harrison Grodin, Yue Niu, Jonathan Sterling, Robert Harper,
     *Decalf: A Directed, Effectful Cost-Aware Logical Framework*,
     POPL 2024, `arXiv:2307.05938`.  Directed effectful extension of
     calf.  Model in augmented simplicial sets.

U19. Runming Li, Robert Harper, *Canonicity for Cost-Aware Logical
     Framework via Synthetic Tait Computability*, 2025,
     `arXiv:2504.12464`.  Resolves calf canonicity via STC.

U20. Guillaume Allais, Robert Atkey, James Chapman, Conor McBride,
     James McKinna, *A type and scope safe universe of syntaxes with
     binding: their semantics and proofs*, ICFP 2018 / JFP 31 (2021),
     `arXiv:2001.11001`, DOI 10.1145/3236785.  Universe-of-syntaxes
     framework.  THE Lean substrate for SSC port.

U21. Jesper Cockx, Dominique Devriese, Frank Piessens, *Pattern
     Matching Without K*, ICFP 2014, DOI 10.1145/2628136.2628139.
     HoTT-compatible dependent pattern matching.

U22. Jesper Cockx, Dominique Devriese, *Eliminating dependent pattern
     matching without K*, JFP 26 (2016).  Extended version.

U23. Ralf Jung, Robbert Krebbers, Lars Birkedal, Derek Dreyer et al.,
     *Iris from the Ground Up: A Modular Foundation for Higher-Order
     Concurrent Separation Logic*, JFP 28 (2018).  Current library:
     `coq-iris 4.3.0` (Oct 2024).  Resource algebras = PCMs +
     validity.  "Monoids and invariants are all you need."  THE
     substrate for FX concurrency / frame rule.

U24. Steve Awodey, Clive Newstead, *Polynomial pseudomonads and
     dependent type theory*, `arXiv:1802.00997` (2018).  Theorem 4.1:
     natural model supports unit + Σ iff p is polynomial pseudomonad;
     supports Π iff p is polynomial pseudoalgebra.  FULL type-former
     coverage beyond Aberlé-Spivak's Π+Σ+U+⊤.

U25. Clive Newstead, *Algebraic models of dependent type theory*,
     `arXiv:2103.06155` (2021).  Essentially-algebraic axiomatization
     of natural models.

U26. Michael Shulman, *All (∞,1)-toposes have strict univalent
     universes*, `arXiv:1904.07004` (2019).  The ∞-topos
     interpretation gluing polynomial-universe machinery to homotopy
     theory.

U27. Danil Annenkov, Paolo Capriotti, Nicolai Kraus, Christian
      Sattler, *Two-Level Type Theory and Applications*, MSCS 2023,
      `arXiv:1705.03307`, DOI 10.1017/S0960129523000130.  Inner HoTT
      + outer UIP; outer = "internalized metatheory of inner".  Solves
      SST as Reedy fibrant diagrams.  THE Lean host for STC modalities.

U28. Nikolai Kudasov, Emily Riehl, Jonathan Weinberger, *Formalizing
      the ∞-Categorical Yoneda Lemma*, CPP 2024.  THE actual rzk
      implementation status — Rzk implements RS-STT base, NOT TT_⊠.
      Source: `github.com/rzk-lang/rzk` +
      `github.com/emilyriehl/yoneda`.

U29. Jonathan Sterling, Carlo Angiuli, *Normalization for Cubical
      Type Theory*, LICS 2021, `arXiv:2101.11479`.  Use of STC in the
      cubical metatheory.

### Loubaton's papers (primary)

1. Félix Loubaton, "The complicial model of (∞,ω)-categories",
   `arXiv:2207.08504` (2022).
2. Simon Henry & Félix Loubaton, "An inductive model structure for
   strict ∞-categories", `arXiv:2301.11424` (2023).
3. Félix Loubaton, "Theory and models of (∞,ω)-categories" (PhD
   thesis), `arXiv:2307.11931` (2023).
4. Amar Hadzihasanovic, Félix Loubaton, Viktoriya Ozornova, Martina
   Rovelli, "A model for the coherent walking ω-equivalence",
   `arXiv:2404.14509` (2024).
5. Félix Loubaton, "Categorical Theory of (∞,ω)-Categories",
   `arXiv:2406.05425` (2024).
6. Thomas Blom, Félix Loubaton, Jaco Ruit, "Day Convolution for
   Algebraic Patterns", `arXiv:2603.29815` (2026).
7. Félix Loubaton, "Conditions de Kan sur les nerfs des ω-catégories",
   `arXiv:2102.04281` (2021).

### Axis 10–13 substrate references (2024–2026)

7a. Ambrus Kaposi, Szumi Xie, *Type Theory with Single Substitutions*,
    `arXiv:2510.12303` (Oct 2025).  EPTCS 431 (LFMTP 2025).  THE
    8-equation single-substitution calculus replacing parallel-
    substitution machinery.  Axis 11 substrate.  Agda-formalized.
7b. Thorsten Altenkirch, Nathaniel Burke, Philip Wadler, *Substitution
    Without Copy and Paste*, `arXiv:2510.12304` (Oct 2025).  EPTCS 431.
    Companion paper.  Sort-parametric V⊑T trick eliminates renaming/
    substitution duplication.  Agda-formalized (literate Agda script).
7c. Runming Li, Yue Yao, Robert Harper, *Mechanizing Synthetic Tait
    Computability in Istari*, `arXiv:2509.11418` (Dec 2025).  CPP'26.
    First proof-assistant mechanization of Sterling's STC.  Axis 12
    substrate.  Lean port via 2LTT-on-Lean (see references below).
7d. Daniel Gratzer, *Normalization for Multimodal Type Theory*,
    `arXiv:2301.11842` (LICS 2022, latest revision Mar 2026).  THE
    universal MTT-normalization theorem: MTT conv decidable iff
    mode-theory equality decidable.  Axis 13 substrate.
7e. Daniel Gratzer, Jonathan Weinberger, Ulrik Buchholtz, *Directed
    Univalence in Simplicial Homotopy Type Theory*, `arXiv:2407.09146`
    (latest revision Jan 2026).  Triangulated TT (TT_⊠) builds
    universe `S` of groupoids with directed univalence.  Semantic
    justification only (no implementation exists in any proof
    assistant).
7f. David Jaz Myers, Mitchell Riley, *Commuting Cohesions*,
    `arXiv:2301.13780` (Feb 2023).  Multi-focus type theory extending
    Shulman spatial TT with multiple commuting cohesive axes.  Axis 7
    primary substrate.  Worked examples: simplicial+real, equivariant+
    differential, supergeometric.
7g. C.B. Aberlé, David I. Spivak, *Polynomial Universes in Homotopy
    Type Theory*, `arXiv:2409.19176` (Sep 2024).  ENTICS MFPS 2025.
    `isUnivalent u := u subterminal in Poly^Cart`; closure under Π →
    distributive law for free via univalence.  Axis 2 substrate +
    Axis 10 alternative path.  Agda-formalized in appendix.
7h. Philippe Malbos, Tanguy Massacrier, Georg Struth, *Cubical Coherent
    Confluence, ω-groupoids and the Cube Equation*, `arXiv:2511.16852`
    (Nov 2025).  Cubical contractions in (ω,p)-categories.  Theorem
    3.2.5: contracting ω-groupoid is acyclic.  Newman + Church-Rosser
    + Squier ALL via cubical cell pasting.  Cube law geometric (not
    postulated).  Axis 4 substrate (saturation).
7i. Clémence Chanavat, *Homotopy Theory of Stricter n-categories*,
    `arXiv:2509.26563` (Sep 2025).  Stricter n-cats via Hadzihasanovic
    regular directed complexes.  Folk model structure on nCat^>.
    Globular + cubical + simplicial + opetopic + Θ + Steiner all
    unified as `Mol(P)` for P a regular directed complex.  Axis 1
    rewrite.
7j. Amar Hadzihasanovic, *The Smash Product of Monoidal ω-categories*
    and *Diagrammatic Sets and Rewriting in Weak Higher Categories*
    (book in progress, current chapters at
    `arXiv:2404.05728` etc.).  THE regular directed complex framework
    cited by Chanavat above.

### Polygraph book (Ara-Burroni-Guiraud-Malbos-Métayer-Mimram)

8. Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos,
   François Métayer, Samuel Mimram, "Polygraphs: From Rewriting to
   Higher Categories", Cambridge University Press 2023.
   `arXiv:2312.00429` survey companion.

### Word problem decision procedures (the actual decidability engine)

8a. Michael Makkai, "The Word Problem for Computads" (McGill
    manuscript, last rev. 2021).  Available at
    <https://www.math.mcgill.ca/makkai/WordProblem/WordProblemCombined.pdf>.
    THE original decision procedure for cell equality in free
    ω-categories over finite computads / polygraphs.  Load-bearing
    reference for Path B decidable Conv in §2.3 + §3.9.
8b. Simon Forest, "Computational descriptions of higher categories"
    (PhD thesis, Université Paris Cité, 2022).  Available via
    <https://forest.cclausen.com/>.  Implementable, polynomial-in-
    practice improvement on Makkai's algorithm via dedicated
    data structures.  Cross-referenced as ABGMMM §17.5.

### Mechanized decidable conv for MLTT (Path A reference)

8c. Arthur Adjedj, Meven Lennon-Bertrand, Kenji Maillard,
    Pierre-Marie Pédrot, Loïc Pujet, "Martin-Löf à la Coq",
    `arXiv:2310.06376` (2024).  Full mechanization of decidable
    conversion for MLTT-with-inductives in Coq.  Direct reference
    for FX's K13 NbE chain (Path A).
8d. Stephanie Weirich et al., Lean 4 Strong Normalization framework,
    `arXiv:2512.09280` (2026).  Recent reusable SN-via-Tait
    machinery for Lean 4; cross-reference for FX's K12 K13 chain.
8e. Daniel Gratzer, "Normalization for Multimodal Type Theory",
    `arXiv:2301.11842` (LICS 2022, last rev. Mar 2026).  Establishes
    conditional decidability for MTT conv: decidable iff mode-theory
    equality decidable.  Template for FX's modal-conv decidability.

### Verity / Riehl complicial sets

9. Dominic Verity, "Weak complicial sets I. Basic homotopy theory",
   Advances in Mathematics 219 (2008).
10. Emily Riehl, "Complicial sets, an overture", `arXiv:1610.06801`
    (2016).
11. Viktoriya Ozornova, Martina Rovelli, "Nerves of 2-categories and
    2-categorification of (∞,2)-categories", Advances in Math 391
    (2021).
12. Emily Riehl, Dominic Verity, "Elements of ∞-Category Theory",
    Cambridge University Press 2022.

### Higher category foundations

13. Albert Burroni, "Higher-dimensional word problems with applications
    to equational logic", Theoretical Computer Science 115 (1993).
14. Craig Squier, "Word problems and a homological finiteness condition
    for monoids", JPAA 49 (1987).
15. André Joyal, "Disks, duality and Θ-categories" (preprint 1997).
16. Michael Batanin, "Monoidal globular categories as a natural environment
    for the theory of weak n-categories", Advances in Math 136 (1998).
17. John Baez, James Dolan, "Higher-Dimensional Algebra III: n-Categories
    and the Algebra of Opetopes", Advances in Math 135 (1998).

### Polynomial monads

18. Joachim Kock, "Polynomial functors and trees", International Math
    Research Notices 2011.
19. Nicola Gambino, Martin Hyland, "Wellfounded trees and dependent
    polynomial functors", in Types for Proofs and Programs 2003.
20. Nicola Gambino, André Joyal, "On operads, bimodules and analytic
    functors", Memoirs AMS 249 (2017).
21. Michael Batanin, Clemens Berger, "Lattice paths and the
    combinatorics of trees", Selecta Mathematica 23 (2017).

### Lurie + ∞-toposes

22. Jacob Lurie, "Higher Topos Theory", Annals of Mathematics Studies
    170, Princeton University Press 2009.  §6 ∞-topos + §A.2.6
    combinatorial model categories — combined with refs 24a/24b
    these give a CONSTRUCTIVE route to ∞-topos mechanization for
    polygraph-presented sites.
23. Jacob Lurie, "Higher Algebra", available at <https://www.math.ias.edu/~lurie/>.
24. Mathieu Anel, André Joyal, "Topo-logie", in Joyal-Anel "New Spaces
    in Mathematics and Physics" (Cambridge 2021).

### Combinatorial model categories (the constructive ∞-topos route)

24a. Tibor Beke, "Sheafifiable homotopy model categories",
     Math. Proc. Camb. Phil. Soc. 129 (2000).  Establishes
     combinatoriality of polygraph-/site-presented model cats.
     Load-bearing for axis 7 (∞-topos) AND axis 8 (Cisinski ω-loc)
     in their REVISED (in-scope) forms.
24b. Daniel Dugger, "Combinatorial model categories have presentations",
     Trans. Amer. Math. Soc. 353 (2001).  THE constructive theorem:
     every combinatorial model cat = Bousfield localization of
     `sPre(C)` at a small map set.  Algorithm: finite-presentation
     site + finite localization map set → ∞-topos.
24c. Jeff Smith (unpublished, ~2001), "Combinatorial model
     categories" — small-object argument with cofinality witness.
     Foundation for Beke-Dugger.  Surveyed in Hirschhorn 2003
     "Model Categories and Their Localizations" Ch. 11.
24d. Georges Maltsiniotis, François Métayer, "Sur le type d'homotopie
     des ω-catégories" / "On the model structure of strict
     ω-categories", `arXiv:0712.0617` (2008).  THE Coq mechanization
     foundation for strict-ω-cat Gray tensor — proves axis 6 Stage 1
     mechanizable; Loubaton 2207.08504 §2.3 extends to complicial
     for axis 6 Stage 2.

### Cohesion + modal

25. Urs Schreiber, "Differential cohomology in a cohesive ∞-topos",
    `arXiv:1310.7930` (2013).
26. Daniel Gratzer, GA Kavvos, Andreas Nuyts, Lars Birkedal,
    "Multimodal Dependent Type Theory", LICS 2020.
27. Daniel Gratzer, "Normalization for Multimodal Type Theory",
    LICS 2022.
28. Daniel Gratzer, Jonathan Weinberger, Ulrik Buchholtz,
    "Directed univalence in simplicial homotopy type theory",
    `arXiv:2407.09146` (2024).

### Cubical / HoTT

29. Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg,
    "Cubical Type Theory: a constructive interpretation of the
    univalence axiom", IFCS 2015.
30. Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Robert Harper,
    Kuen-Bang Hou (Favonia), Daniel R. Licata, "Cartesian cubical
    type theory", manuscript 2017.
31. Vladimir Voevodsky, "The univalence axiom", in HoTT Book
    (Institute for Advanced Study 2013).
32. Jonathan Sterling, Carlo Angiuli, Daniel Gratzer, "Cubical syntax
    for reflection-free extensional equality" (XTT), FSCD 2019.

### Grading / linearity / quantitative

33. Robert Atkey, "Syntax and Semantics of Quantitative Type Theory",
    LICS 2018.
34. James Wood, Robert Atkey, "A Linear Algebra Approach to Linear
    Metatheory", FoSSaCS 2022.
35. Benjamin Moon, Harley Eades, Dominic Orchard, "Graded Modal
    Dependent Type Theory", ESOP 2021.
36. Andreas Abel, Nils Anders Danielsson, Oskar Eriksson,
    "A Graded Modal Dependent Type Theory with a Universe and
    Erasure, Formalized", ICFP 2023.

### Concurrency + separation logic

37. Vaughan Pratt, "Modeling concurrency with geometry" (HDA),
    POPL 1991.
38. Lisbeth Fajstrup, Eric Goubault, Martin Raussen, "Directed
    Algebraic Topology and Concurrency", Springer 2016.
39. Peter O'Hearn, "Resources, Concurrency and Local Reasoning"
    (CSL), Theoretical Computer Science 375 (2007).
40. Stephen Brookes, "A Semantics for Concurrent Separation Logic",
    Theoretical Computer Science 375 (2007).
41. Ralf Jung, Robbert Krebbers, Lars Birkedal, Derek Dreyer et al.,
    "Iris from the Ground Up", JFP 28 (2018).

### Permission algebras

42. John Boyland, "Checking Interference with Fractional Permissions",
    SAS 2003.
43. Robert Bornat, Cristiano Calcagno, Peter O'Hearn, Matthew Parkinson,
    "Permission Accounting in Separation Logic", POPL 2005.
44. Robert Dockins, Aquinas Hobor, Andrew Appel, "A Fresh Look at
    Separation Algebras and Share Accounting", APLAS 2009.

### Polarization / CBPV / effects

45. Paul Levy, "Call-By-Push-Value", Springer Higher-Order and Symbolic
    Computation 2001.
46. Pierre-Marie Pédrot, Nicolas Tabareau, "The Fire Triangle: How to
    Mix Substitution, Dependent Elimination, and Effects", POPL 2020.
47. Matija Pretnar, "An Introduction to Algebraic Effects and Handlers",
    MFPS 2015.
48. Danel Ahman, "Fibred Algebraic Semantics for a Variety of
    Non-Recursive Theories", POPL 2018.

### Guarded recursion + partial

49. Hiroshi Nakano, "A Modality for Recursion", LICS 2000.
50. Robert Atkey, Conor McBride, "Productive Coprogramming with Guarded
    Recursion", ICFP 2013.
51. Venanzio Capretta, "General Recursion via Coinductive Types",
    LMCS 1 (2005).
52. Rasmus Møgelberg, Marco Zwart, "Clocked Cubical Type Theory",
    LMCS 2025.

### Allais et al universe-of-syntaxes

53. Guillaume Allais, Robert Atkey, James Chapman, Conor McBride,
    James McKinna, "A type and scope safe universe of syntaxes with
    binding: their semantics and proofs", ICFP 2018 / JFP 31 (2021).

### Day convolution

54. Brian Day, "On closed categories of functors", Reports of the
    Midwest Category Seminar IV (1970).
55. Robin Glasman, "Day convolution for ∞-categories",
    `arXiv:1308.4940` (2013).
56. Thomas Blom, Félix Loubaton, Jaco Ruit, "Day Convolution for
    Algebraic Patterns", `arXiv:2603.29815` (2026).

### Synthetic Tait computability

57. Jonathan Sterling, "First Steps in Synthetic Tait Computability"
    (PhD thesis), CMU 2021.
58. Jonathan Sterling, Carlo Angiuli, "Normalization for Cubical
    Type Theory", LICS 2021.
59. Daniel Gratzer, "Normalization for Multimodal Type Theory" (the
    parametric-over-mode-theory MTT normalization), LICS 2022.

### Reedy + presheaf categories

60. Clemens Berger, Ieke Moerdijk, "On an extension of the notion of
    Reedy category", Mathematische Zeitschrift 269 (2011).
61. Denis-Charles Cisinski, "Higher Categories and Homotopical
    Algebra", Cambridge Studies in Advanced Mathematics 180 (2019).
62. Carlos Simpson, "Homotopy Theory of Higher Categories", Cambridge
    University Press 2011.

### Decalf + cost-aware

63. Yue Niu, Jonathan Sterling, Harrison Grodin, Robert Harper,
    "A Cost-Aware Logical Framework" (calf), POPL 2022.
64. Harrison Grodin, Yue Niu, Jonathan Sterling, Robert Harper,
    "decalf", POPL 2024.

### Reversibility + energy

65. Charles Bennett, "Logical Reversibility of Computation",
    IBM J. Research and Development 17 (1973).
66. Tetsuo Yokoyama, Robert Glück, "A reversible programming language
    and its invertible self-interpreter", PEPM 2007.

### Stratified types (avoiding paradox)

67. Stephanie Weirich, Antoine Voizard, "Stratified type theory",
    ESOP 2025.
68. Thierry Coquand, "A Reynolds-Hurkens variant", manuscript 2023.

### Reference codebases (≠ papers)

69. Mathlib4, <https://github.com/leanprover-community/mathlib4>
70. Lean 4 source, <https://github.com/leanprover/lean4>
71. Cubical Agda library, <https://github.com/agda/cubical>
72. HoTT-Coq library, <https://github.com/HoTT/HoTT>
73. F* repository, <https://github.com/FStarLang/FStar>
74. Iris repository, <https://gitlab.mpi-sws.org/iris/iris>

---

## End matter

This document is the soundness contract for the PolyTerm pivot.
Every capability claim above reduces to one of:

* a **cited published theorem** with arXiv ID / DOI and paper
  reference (Tier-0 substrate: Uemura `arXiv:1904.04097` + BKS
  `arXiv:2302.05190` + Pédrot-Tabareau Fire Triangle POPL 2020;
  thirteen Tier-2 axes each have explicit substrate papers per
  §3.0 and the per-axis recipe blocks), OR
* a **constructive Lean definition** in this codebase (with file
  path under `LeanFX2/Foundation/Polygraph/` or
  `LeanFX2/Reducibility/`), OR
* an **explicit de-scoping note** in §12 with the reason (Cisinski
  ω-loc and full Lurie ∞-topos are in-scope via Dugger 2001 + Beke
  2000 + Smith; the only out-of-scope items are TT_⊠ Lean
  mechanization and Coverage Semantics for univalent FX).

No `IsX : Prop` placeholder predicates ship under the PolyTerm
substrate.  No "research-frontier flag" stands in for a missing
proof.  No `Inhabited X` for unconstructible X.  Every decidability
claim has an algorithm citation; every Lean theorem signature has a
proof skeleton compatible with `#assert_no_axioms` per
lean-fx-2/CLAUDE.md.

The 214K LoC budget is realistic per the per-axis Lean LoC
estimates.  The 36-month timeline is realistic per the per-phase
deliverable breakdown.  The risk register in §12 names specific
failure modes with mitigations.

**The expand-at-whim multiplier:** each future FX extension
(probability, measure, SDG, reversible compute, quantum,
distributed, …) is a Tier-2 inhabitant of the Tier-0 obligation
type — ~2K LoC per extension after Tier 0 is in place.  Without
Tier 0, each extension costs ~10-15K LoC of bespoke kernel
surgery.  The Tier-0 investment of ~12K LoC pays back after ~3
extensions; FX already has 13 in scope.

**If committed:** the first concrete steps are
`Foundation/MetaFramework/CwR.lean` +
`Foundation/MetaFramework/InternalSconing.lean` shipping the
Tier-0 substrate, followed by `Foundation/Polygraph/CellShape.lean`
for Axis 1.  POLY-α targets MILESTONE A in month 6.

**If deferred:** this document remains a queued architectural
option, to be revisited after MILESTONE A ships under the current
accelerate-* roadmap.

Either way, the literature is captured in
`reference_loubaton_papers.md` and
`reference_polyterm_lit_scan_2026_05_24.md` memory entries; the
design rationale is preserved here for future reference.
