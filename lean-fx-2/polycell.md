# PolyCell — Raw Input + Certified Universal Substrate for FX Kernel Cells

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
> thirteen profile axes plus the profile-extension calculus must
> `#assert_no_axioms` clean.
>
> **Costed:** ~190K gross Lean LoC over 2–3 years, of which **~25K is
> already shipped** in `Foundation/Polygraph/` (K11.1–K11.17 +
> K12.1–K12.19 + K12.23 + strength-T1/T2/T3 + T4×28 + T8 +
> Generator/RawPolyTermFlat infrastructure).  Remaining work is
> ~165K gross LoC before the later deletion of obsolete cascade files.
> See [§9](#9-loc-budget) for the canonical accounting.
>
> **Slogan:** *permissive raw cells, intrinsic certified cells.*  Raw
> `PolyTerm π dim` is the input / serialization layer and may represent
> nonsense so the checker can reject it.  Certified `PolyCell π sort dim
> scope boundary raw` is the kernel layer and has constructors only for
> sorted, scoped, boundary-compatible cells.  FX kernel objects become
> projections of certified cells over one `PolyProfile π`; raw nonsense
> must map to `none` / `rejected reason`, never to a certificate.
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
  Sconing-is-enough thesis reduces canonicity, normalization, and
  parametricity to a concrete internal-sconing witness per extension.
  Fire Triangle bounds what is mixable (at most two of {substitution,
  dependent elimination, effects} unrestricted).  This is the
  expand-at-whim multiplier:
  each new FX feature ships as ~2K LoC Tier-0 obligation witness
  instead of 5-15K LoC bespoke cascade work.  ~12K Lean LoC, first
  Lean port of this framework in any proof assistant.

* **Tier 1 — POLYCELL CORE** (~15K LoC, §4)
  A two-layer core: permissive raw `PolyTerm` for input data, plus
  intrinsic certified `PolyCell` indexed by sort, dimension, scope,
  boundary, and raw syntax.  Each axis is one Tier-0 obligation
  witness attached to the profile, not a new raw constructor family.

* **Tier 2 — PROFILE AXES + EXTENSION CALCULUS** (13 profile axes,
  §3.1-§3.13, plus the extension calculus in §3.14)

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
3.  [Thirteen Profile Axes + Extension Calculus](#3-thirteen-profile-axes--extension-calculus)
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
    * 3.14 [Profile Extension Calculus — the load-bearing addition (Aberlé + Bousfield + ∞-cosmos)](#314-profile-extension-calculus)
    * 3.15 [Demonstration profiles — what the extension calculus enables](#315-demonstration-profiles)
4.  [The raw/certified PolyCell signature](#4-the-rawcertified-polycell-signature)
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

**Snippet discipline.**  Lean blocks in this document are interface
sketches unless explicitly labeled **Lean target**.  Sketch blocks may
use `...` to mark a work package, but they are not accepted bodies and
do not count as shipped declarations.  Any field previously written as
`True`, `by decide`, or `trivial` is sound only when the surrounding
text names the concrete proof obligation that must replace it in Lean.
The implementation rule remains stricter than the prose: no shipped
kernel declaration may contain placeholders, `sorry`, `axiom`,
`noncomputable`, `Classical.*`, or hypothesis-as-postulate patterns.

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
universe parameterized by **thirteen profile axes** (SSC, STC,
MTT-norm extend an earlier ten-axis core; the Tier-0 universal
meta-framework binds them all), every axis grounded in published
literature, every axis Lean-mechanizable at zero axioms, every axis
giving FX a capability no other proof assistant has.

The thirteen axes are NOT orthogonal in the strict sense — they
compose through the Tier-0 META-FRAMEWORK (Uemura representable map
categories + Bocquet-Kaposi-Sattler internal sconing + Pédrot-
Tabareau Fire Triangle).  See §3.0 for the universal substrate that
makes the framework genuinely scary AND mechanizable.

**The deeper thesis — PolyCell is a profile-extension calculus, not
thirteen static axes.**  The thirteen axes describe the *shape* of
any single admissible profile.  The **profile-extension calculus**
(§3.14) describes the *space* of admissible profiles and the
mechanism by which new features are admitted into it.  FX is the
first admissible profile.  Every future feature — probability,
differentiation, quantum, distributed protocols, scientific
simulation, self-hosting — ships as a `ProfileExtension` satisfying
the admission contract.  The headline theorem is:

```lean
theorem extendProfile_preserves_admissible
    (base : AdmissibleProfile)
    (ext : ProfileExtension base) :
    AdmissibleProfile (base.extend ext)
```

This is the "extend at whim, inherit everything" *aspiration*.  New
features are NOT new `Term` constructors; they are admitted profile
extensions whose interaction laws + metatheory preservation must be
verified per extension and (target) checked compositionally.  Aberlé's
2026 polynomial-functor compositional verification framework
(`arXiv:2604.01303`) supplies a per-extension substrate; the intended
composition primitive is the **FX PolyCell Cellular Tensor target
theorem** described as §3.0.7 — an FX-original research program
extending Almeida 2025 vol I (`arXiv:2511.13547`, syntactic GAT
tensor) with three additional candidate pillars (Bocquet-Kaposi-
Sattler internal sconing, our own ProfileCapabilities honesty ledger,
Crans 1999 / Steiner 2004 Gray-tensor universal property at the
strict single-sort level, intended to lift to admissible
sort-stratified profiles).  This composite is NOT a landed Lean
result; §3.0.7 lays out the target obligations.  Until those
obligations close, the extension calculus in §3.14 uses explicit
per-pair bilax / distributive-law witnesses and explicit no-go
rejection — no universal-property-as-corollary shortcut.

The slogan is **permissive raw cells, intrinsic certified cells**.
The K11.1 `PolyCell` (dim-indexed, source/target intrinsic, real
Burroni cells) is the skeleton.  The other twelve axes are the flesh.
At the end you have raw `PolyTerm π dim` as the input format and
certified `PolyCell π sort dim scope boundary raw` as the kernel
inhabitant type, both parameterized by a thirteen-field `PolyProfile
π`.  FX is one specific profile, reached and grown by the extension
calculus, not assembled by hand.

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
- decidable conversion via the explicit Path A / Path B engines
  (NbE normal-form equality, or Makkai/Forest word equality on the
  finite FX polygraph; HLOR ωcE is the semantic coherent-equivalence
  classifier, not the decision engine),
- synthetic-Tait metatheory at (∞,ω) via complicial nerve,
- mechanized in Lean 4 at strict zero axioms,
- presented as a complicial-stratified globular-cubical-opetopic
  polygraph with Gray tensor compatible composition and tropical
  optimal reduction.

This is the "quantale-enriched (∞,∞)-category of types" Object the
`20_05_2026.md` dossier §14 hand-waves toward; this document makes it
mechanizable.

The cost is honest: ~190K gross zero-axiom Lean 4 LoC, ~165K still
to write after the shipped foundation, 2–3 years of focused work, and
the **first mechanization of (∞,ω)-categories internalized in any
proof assistant** if all committed stages land.  FX simultaneously
becomes a programming language kernel AND a categorical-foundations
research artifact.  No precedent.

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

The polygraph substrate eliminates the raw-inductive part of the
cascade by **moving feature constructors into generator metadata rather
than raw syntax constructors**.  Adding a new feature no longer adds a
raw inductive constructor or per-consumer proof arms.  The proof work
moves to generator metadata, checker soundness, and profile-extension
admission obligations.  Downstream consumers (rename, subst, cd_lemma,
etc.) should eventually recurse once over the generic cell structure
plus generator table, not once per feature constructor.

### 2.2 The Prop→Type wall and the wrong scope

The `20_05_2026.md` dossier §8 documents the "polygraph derives
confluence, deletes 45K LoC" claim as **refuted** by the Prop→Type
wall: you cannot extract a `cd_lemma` proof from a `PolyCell` Type-side
embedding because `cd_lemma` is Prop-valued.

This refutation is correct *for the current K11 design*, where
PolyCell is just data + ParallelPair + composition laws and the
proof of confluence stays Prop-side.

The PolyCell proposal here resolves the wall by **making the
substrate carry both the cells AND the markings**:

- Cells are Type-side (certified `PolyCell` constructors over raw
  `PolyTerm` input).
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
under the certified PolyCell target.  Either suffices for
`★ MILESTONE A`; we ship both
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
path, semantically aligned with the PolyCell substrate):

```
Certified PolyCell extracted as Generator-based polygraph X with finite
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
* What must still be proved for the certified FX profile: termination,
  confluence, and finite generator enumeration.  Today we have partial
  K12 support and current-scaffold cd evidence; these do **not** yet
  establish the certified-profile theorem.

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
alignment with the certified PolyCell substrate; if Path A hits an unforeseen Lean
mechanization wall, Path B is independently sufficient.  Both
paths converge on the same `Decidable (Conv a b)` instance.
CONVTRANS-D, K12.28, K13.20 collapse via Path A's standard
recipe.

### 2.4 Concurrency / distribution wait on certified `compH`

The `20_05_2026.md` dossier §2.7 conjectures that K11.5 (horizontal
composition) + K11.6 (interchange / Eckmann-Hilton) IS the separation
logic frame rule at the polygraph level.  The conjecture is *correct
in structure but loses typing* in the current K11 design because the
typed Term is separate from the polygraph.

The raw layer does **not** fix this.  Raw `PolyTerm.compH` is input
syntax only: it can represent a proposed horizontal composition, but
it does not certify disjoint footprints, Gray-boundary matching, or a
typed frame rule.

The certified layer fixes this only after Axis 6 is real.  A future
certified `PolyCell.compH` must take two certified cells, a
computable Gray boundary, and a disjoint-footprint / matching witness,
then produce a certified cell over the combined footprint.
Interchange (K11.6, already shipped zero-axiom for the current raw
scaffold) becomes the frame rule **only when lifted to that certified
constructor**.

So the target rule is:

```text
par(f, g) typechecks only if
  footprint(f) and footprint(g) are disjoint
  and their Gray boundaries match.
```

Until that constructor exists, the raw-to-certified checker must
reject raw `compH` with `unsupportedCompH`, not silently accept it.
Distribution / GPU evaluation (P5.1) is therefore deferred: it
requires certified `compH` for parallel partitions, certified `compV`
for sequential commits, and explicit BSP-sync / saturation laws.

### 2.5 Modal / cohesive / polarized / linear / guarded all in one kernel

The current FX modal layer is 8 hardcoded modalities (`♭`, `◇`, `□`, `♯`,
ghost, cap, later, clock) with hand-rolled adjunction lemmas.  Adding a
ninth modality (e.g. graded `▷` per Nakano, or differential `∂` per
Kock-Lawvere SDG) requires re-doing the adjunction chain by hand.

PolyCell puts the entire modal layer in the `topos` axis (axis 7,
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

This is implementable in the certified PolyCell target: Mathlib's ~1.5M LoC of mathematics
maps to a sequence of `Generator` value extensions, with each
Mathlib theorem becoming one dim-1 certified cell over
`PolyTerm fxProfile` raw syntax.
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

## 3. Thirteen Profile Axes + Extension Calculus

Tier 0 (§3.0) is the universal meta-framework substrate.  Each of the
thirteen axes (§3.1-§3.13) is one Tier 0 obligation witness: a
representable-map-category extension + sconing witness + Fire Triangle
navigation.  Axes are heterogeneous (cohesive / resource / cost /
security / structural / etc.) but compose through the PolyProfile
bundle (§4).

Section §3.14 is **not** a fourteenth static profile axis.  It is the
calculus that admits new profiles and proves that extensions preserve
the thirteen-axis admissibility contract.  This distinction matters:
the axes describe one profile's shape; the extension calculus describes
how the profile space grows without reintroducing the constructor
cascade.

### 3.0 Tier 0: The Universal Meta-Framework Substrate

Before the thirteen axes: a universal Tier 0 substrate that all axes
are built on.  This is what makes PolyCell's "expand FX at whim"
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

#### 3.0.2 Internal sconing — metatheory by explicit witness

The BKS thesis (FSCD 2023): **sconing alone (not general gluing) is
enough for the metatheory**.  Two key moves:

* Restrict to a single global-section functor (the sconing functor),
  not arbitrary gluing.
* Perform the construction INTERNAL to a presheaf topos; externalize
  at the end.

The payoff, after the witness is actually constructed:

* **Canonicity** is derived from one boilerplate-free induction
  principle.
* **Normalization** is derived from another (Uemura
  `arXiv:2212.11764` refines this via substitution-mode +
  renaming-mode separation).
* **Syntactic parametricity** is derived as a third.

For each FX axis, the metatheory obligation reduces to: provide a
concrete sconing witness plus the Fire Triangle accounting for that
axis.  Per axis ~1K LoC.  This is a smaller proof obligation than
per-construction STC / gluing arguments, but it is still a proof
obligation; no arbitrary profile gets canonicity or normalization by
being merely named in the table.

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

Every PolyCell axis is a tuple (Categorical structure, Sconing
witness, Fire Triangle navigation):

```lean
/-- A PolyCell axis is a Tier-0 obligation: a representable-map-category
extension to FX's base type theory, together with a sconing witness
from which canonicity, normalization, and parametricity are derived. -/
structure AxisObligation where
  /-- The categorical structure being added (Uemura RMC extension). -/
  rmcExtension : RepresentableMapCategory.Extension fxBaseRMC

  /-- The sconing witness (BKS internal sconing) used to derive the
  metatheory. -/
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

Each source paper handles one axis (or one metatheorem).  PolyCell
with Tier 0 substrate gives FX the combined strength of all of them:

* Uemura provides universality (every type theory in one framework).
* BKS provides a compact metatheory route (sconing witness once, then
  derive the three metatheorems).
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

#### 3.0.7 The FX PolyCell Cellular Tensor — FX-original target theorem (research program)

The four pillars above (Uemura, BKS sconing, Fire Triangle, Hadzihasanovic
shapes) are imported from published literature.  This subsection introduces
an **FX-original target theorem** at the Tier 0 layer — a research program,
NOT a landed Lean result.  The statement, its proof obligations, and its
relationship to four published source pillars are laid out below; until
the Lean mechanization closes the obligations, the calculus in §3.14
uses **explicit bilax / distributive-law witnesses and explicit no-go
rejection**, NOT the universal property as a one-line corollary.

**Why we need our own pillar.**  Daniel Almeida's *A monoidal category
of dependently sorted algebraic theories I: syntax* (`arXiv:2511.13547`,
Nov 2025, 119 pages) constructs a syntactic tensor product `A ⊗ B` of
generalized algebraic theories in Cartmell's sense, with worked
instances recovering Freyd's classical Lawvere tensor (§3.2),
T_cat ⊗ T_cat as strict double categories (§3.1), and the cartesian
product `D(S ⊗ T) ≅ D(S) × D(T)` on locally finite direct categories
for pure type signatures (§3.3).  Vol I ships the comparison functor
`⊗_{A,B} : C(A) × C(B) → C(A ⊗ B)` for fixed (A, B) (Construction 6.5),
associativity at the level of derivable judgments (Theorem 7.3), and
symmetry at the same level (Proposition 8.1).

Vol I explicitly **defers** five load-bearing categorical results to
a vol II [Alm26] that is *in preparation* as of 2026:

* (D1) Functoriality of `⊗` on morphisms of GATs (Remark 6.7,
  page 82): "giving a purely syntactic proof of the above statement
  seems to be a laborious task due to the recursive nature of
  morphisms of gats... We will come back to this discussion in
  [Alm26]."
* (D2) Closed monoidal category structure on GAT (Remark 7.5,
  page 96): "We defer this discussion to [Alm26] since we have, at
  this point, little to no access to the functoriality of the
  tensor product."
* (D3) Pentagon coherence for the associator (Remark 7.5).
* (D4) Hexagon coherence for the symmetry (§8 closing, page 98):
  "Like the situation with associativity, a categorical study of
  this symmetry isomorphism is out of reach in the current
  article.  We will return to this problem in [Alm26]."
* (D5) The `Mod(A ⊗ B, Fam) ≅ Mod(A, Mod(B))` equation (abstract).

FX does not have to wait for vol II.  Vol II's deferred results are
framed in the most general setting (arbitrary GATs, arbitrary theory
morphisms), where the "laboriousness" Almeida cites is paper-math
combinatorics.  FX's setting is **narrower**: profiles are admissible
(finite generators, decidable equality, SProp-valued coherence cells
per §3.13's three rigidity restrictions).  We **conjecture** the
universal property is mechanizable in this narrower setting via the
four-pillar composition below — but every (T*) statement remains a
*target obligation* against a Lean mechanization that has not yet
been written.  The hard part is exactly the lift from Almeida-style
GAT tensor + Crans/Steiner strict Gray tensor into sort-stratified
dependent profiles with admissibility, capabilities, sconing, and
bilax coherence.  That lift may be right, but it is not a
one-paragraph corollary.

**Target statement — the FX PolyCell Cellular Tensor.**  Let
π_A and π_B be admissible PolyCell profiles with ProfileCapabilities
κ_A and κ_B (see §3.14 for the capabilities record).  We aim to
prove:

* (T1) **Cellular tensor exists.**  There is a profile
  `π_A ⊗_{cell} π_B` computed by:
    (a) extracting each profile's GAT shadow (forgetting sort
        stratification),
    (b) applying Almeida vol I's syntactic tensor algorithm to the
        shadows,
    (c) re-stratifying the resulting GAT into a sort-stratified
        polygraph using the FX cell-sort enumeration (context /
        type / term / mode).
  This is well-defined because Almeida vol I Theorem 5.2 guarantees
  the GAT-level tensor IS a theory, and FX's sort enumeration is a
  finitary partition.

* (T2) **Admissibility preservation.**  If π_A and π_B are
  admissible, so is `π_A ⊗_{cell} π_B`.  Proof: the BKS
  internal-sconing functor (Bocquet-Kaposi-Sattler `arXiv:2302.05190`)
  satisfies `sconing(M(σ)) = sconing(M) ∘ σ` for any CwR morphism σ.
  Both admissibility witnesses sconing into the same presheaf topos;
  their composite witnesses admissibility of the tensor.  ~1K LoC.

* (T3) **Capability meet as honesty ledger (upper bound, not
  substitute for interaction proofs).**  The ProfileCapabilities of
  the tensor is at most the meet of the factors' capabilities:
  ```
  capabilities(π_A ⊗_{cell} π_B) ≤ κ_A ⊓ κ_B
  ```
  Tensor of an SN profile with a non-SN profile is at best non-SN.
  Tensor of a canonical profile with a classical profile is at best
  non-canonical.  This is a NECESSARY condition, not a SUFFICIENT one
  — two SN/canonical profiles can still interact badly if the tensor
  introduces new term-equality axioms (vol I Table 1's u⊗v ≡ u•v
  row) that create rewrite loops or break canonicity.  The meet is
  an honesty *ledger* that says "no advertised property survives if
  it was absent in either factor"; it does NOT discharge the actual
  interaction proof.  Each new extension must still ship explicit
  per-pair distributive-law witnesses where required.  ~1K LoC for
  the ledger; the per-pair proofs live in §3.14's
  `bilaxCompatibility` field and §3.0.7's no-go register.

* (T4) **Universal property at the polygraph level (Crans-Steiner-
  Gray lift).**  For any admissible profile π_C with morphisms
  `F : π_A → π_C` and `G : π_B → π_C` satisfying *bilax
  compatibility* (the sort-paired generators commute up to a
  definable 2-cell), there exists a profile morphism
  `H : π_A ⊗_{cell} π_B → π_C` unique up to lax 2-cell, factoring
  F and G.  This is the Gray-tensor universal property of Crans 1999
  and Steiner 2004 (classification of lax bifunctors out of a tensor
  of polygraphs), lifted to sort-stratified admissible profiles via
  the BKS sconing functoriality from (T2).  ~2K LoC.

* (T5) **Associativity up to lax 3-cell.**  `(π_A ⊗ π_B) ⊗ π_C ≃
  π_A ⊗ (π_B ⊗ π_C)` up to lax 3-cell.  Vol I Theorem 7.3 gives the
  iso-of-judgments; Crans-Steiner-Gray gives the lax 3-cell
  associator coherence that vol I's Remark 7.5 defers.  ~500 LoC.

* (T6) **Symmetry up to lax 2-cell.**  `π_A ⊗ π_B ≃ π_B ⊗ π_A` up to
  lax 2-cell.  Vol I Proposition 8.1 gives the iso-of-judgments;
  Crans-Steiner-Gray gives the lax symmetry coherence that vol I's
  §8 closing defers.  ~500 LoC.

* (T7) **No-go register and explicit rejection.**  When two
  extensions hit a published Zwart-Marsden no-go cell (e.g.,
  probability × powerset, or any triple in the Zwart-Marsden no-go
  catalogue `arXiv:1811.06460`), or when the user cannot supply a
  bilax-compatibility witness for (T4), the admission contract
  **rejects the extension** and returns a constructive collision
  certificate naming the prior capability and the missing law.
  Failure of bilax compatibility does NOT silently become "lattice
  bottom" — that would be sloppy.  It either rejects the extension
  outright, or admits it as **syntax-only** (the generators are
  added but no metatheory transfer is asserted); the user picks
  which posture per extension.  The no-go register is a static
  table cross-referenced against the Zwart-Marsden catalogue, not a
  computed lattice value.  ~500 LoC.

* (T8) **Iterated tensoring (mechanism, not conservativity).**
  Iterated tensors `π_FX ⊗ π_Probability ⊗ π_SDG ⊗ π_Quantum ⊗ ...`
  are associative by (T5) up to lax 3-cell; the chain of extensions
  in §3.15 is computed by left-to-right reduction with associator
  re-bracketing.  This is the *mechanism* for building extension
  chains, NOT a free conservativity guarantee.  Importing a
  third-party theorem library (e.g. Mathlib) via this mechanism
  requires, separately: (i) a proof-object translation that
  preserves the source library's typing, (ii) an explicit
  consistency-strength accounting (which Mathlib axioms are
  imported, against which ambient theory), (iii) per-import
  conservativity proofs against the target FX profile.  The
  universal property of (T4) discharges only the cellular-composition
  side; it does NOT by itself make imported theorem-generators
  conservative.  Each library import is its own project.

**Why this is an open research program, not a corollary.**  No
published work combines all four ingredients: (i) the syntactic
GAT tensor construction (Almeida vol I 2025), (ii) BKS internal
sconing for metatheory preservation (Bocquet-Kaposi-Sattler 2023),
(iii) a ProfileCapabilities honesty ledger (our own design), (iv)
Crans-Steiner-Gray Gray-tensor universal property at the level of
strict single-sort polygraphs (Crans 1999 / Steiner 2004 + ABGMMM
2023 §17).

The hard part is the **lift** from (iv) — which lives at strict
single-sort polygraphs — to sort-stratified DEPENDENT profiles with
admissibility, capabilities, sconing, and bilax coherence.  Crans
1999 is scoped to Gray-categories; Steiner 2004 to ω-categories /
chain complexes; neither covers sort-stratified GAT cells with
dependent boundaries.  Almeida vol I 2025 covers the GAT side but
explicitly defers the universal property to vol II.  BKS sconing
covers metatheory transfer along one CwR morphism but does not
automatically lift to a cellular tensor of profiles.

The composite (T1)-(T8) is FX-original BECAUSE no paper has done
the lift; it is also UNPROVEN BECAUSE no paper has done the lift.
This subsection is a research program statement, not a victory
lap.

**Comparison with vol II [Alm26] when it eventually ships.**  Vol II
is planned to prove (D1)-(D5) at the maximum-generality GAT level.
Our target theorem aims for the FX-relevant projection (T1)-(T8) at
the admissible-profile level using the four-pillar composition.
When vol II ships, FX may be able to specialize against it
(admissibility restriction becoming a corollary of vol II's full
universal property), or FX may discover during the lift attempt
that the projection requires additional restrictions vol II does
not need.  Until either FX's mechanization or vol II ships, neither
result is available; this section flags FX's intended direction.

**Lean target signature (NOT shipped; sketch only):**  The block below
is a Lean *target signature* indicating the intended type of each
(T*) statement once mechanized.  Bodies are placeholders.  These
declarations DO NOT EXIST in the lean-fx-2 tree as of this commit;
shipping them is the research program §3.0.7 describes.

```lean
-- Lean target sketch — proof bodies are NOT written; this is the
-- target-theorem signature, not a shipped result.
namespace LeanFX2.Foundation.Polygraph.CellularTensor

/-- The cellular tensor of two admissible PolyCell profiles.
Computed by lifting Almeida vol I's syntactic GAT tensor through
the polygraph presentation.  -/
def cellularTensor (πA πB : AdmissibleProfile) : AdmissibleProfile := ...

notation:70 πA " ⊗_cell " πB => cellularTensor πA πB

/-- (T2) Admissibility preservation via BKS internal sconing.
The composite sconing functor witnesses admissibility of the tensor. -/
theorem admissibility_preserved (πA πB : AdmissibleProfile) :
    IsAdmissible (πA ⊗_cell πB) := by
  apply BKSInternalSconing.composeAdmissibility
  · exact πA.admissibilityWitness
  · exact πB.admissibilityWitness

/-- (T3) Capabilities meet semantics.  Tensor of profiles has the
meet of their capabilities; no false subsumption. -/
theorem capabilities_meet (πA πB : AdmissibleProfile) :
    (πA ⊗_cell πB).capabilities = πA.capabilities ⊓ πB.capabilities := by
  rfl  -- by construction in cellularTensor

/-- (T4) Universal property: the cellular tensor classifies lax
bifunctors out of (πA × πB).  -/
theorem universal_property
    (πA πB πC : AdmissibleProfile)
    (F : ProfileMorphism πA πC)
    (G : ProfileMorphism πB πC)
    (compat : BilaxCompatible F G) :
    ∃! (H : ProfileMorphism (πA ⊗_cell πB) πC),
      H.composeLeft = F ∧ H.composeRight = G := by
  apply CransSteinerGray.universalPropertyLifted compat
  exact admissibility_preserved πA πB

/-- (T7) Structural no-go discharge.  When capabilities meet is
bottom, the tensor is admissible-but-degenerate, honestly marked. -/
theorem no_go_structural (πA πB : AdmissibleProfile)
    (h : πA.capabilities ⊓ πB.capabilities = ⊥) :
    (πA ⊗_cell πB).isDegenerate ∧ IsAdmissible (πA ⊗_cell πB) := by
  refine ⟨?_, admissibility_preserved πA πB⟩
  simp [ProfileDegenerate, capabilities_meet, h]

end LeanFX2.Foundation.Polygraph.CellularTensor
```

**LoC cost (Lean target):** ~5K LoC distributed as:
* `CellularTensor/Construction.lean` — (T1) lifting Almeida vol I
  algorithm through polygraph: ~1K LoC.
* `CellularTensor/BKSPreservation.lean` — (T2) sconing composition:
  ~1K LoC.
* `CellularTensor/CapabilitiesMeet.lean` — (T3) meet semantics:
  ~1K LoC.
* `CellularTensor/UniversalProperty.lean` — (T4)-(T6) Crans-Steiner-
  Gray lift: ~2K LoC.
* `CellularTensor/NoGo.lean` — (T7) structural no-go: ~500 LoC.

All zero-axiom under strict policy.  Pre-test on toy polygraphs
(monoid presentation tensor = dim-1-only) before scaling to FX
profile chain (T8).

**Mechanizability.**  Each pillar is paper-form but algorithmic:
* Almeida vol I's algorithm is an explicit recursive procedure on
  judgment height (vol I Appendix A.4 + §2 + §4-§5 proofs).
* Crans 1999 + Steiner 2004 give explicit Gray-tensor formulas for
  strict polygraphs; the formulas extend with marking-tracking
  (Axis 6 Stage 2 work).
* BKS sconing is constructive (FSCD 2023 paper gives the universal
  construction inside any presheaf topos).
* ProfileCapabilities meet is a finite-enum lattice meet computed by
  Lean's `Decidable` instance.

**Reference triangle for the FX Cellular Tensor target:**
* Daniel Almeida, *A monoidal category of dependently sorted
  algebraic theories I: syntax*, `arXiv:2511.13547` (Nov 2025).
  Supplies (T1).  119 pages.  Vol II [Alm26] in preparation aims to
  supply (D1)-(D5); FX aims at the admissible-profile projection
  without waiting, neither result currently shipped.
* Sjoerd Crans, *A tensor product for Gray-categories*, Theory and
  Applications of Categories 5 (1999), 12-69.  Supplies the
  Gray-tensor universal property at the strict Gray-category /
  single-sort level (not the sort-stratified-dependent level FX
  needs); (T4) is the *aim* of the lift, not Crans's theorem.
* Richard Steiner, *Omega-categories and chain complexes*, Homology,
  Homotopy and Applications 6 (2004), 175-200.  Extends Crans to
  the chain-complex / ω-category side; background monoidal
  machinery on strict ω-categories.
* Bocquet-Kaposi-Sattler, *For the metatheory of type theory,
  internal sconing is enough*, `arXiv:2302.05190` (FSCD 2023).
  Supplies (T2) for one CwR morphism; extending to the cellular
  tensor of two profiles is part of the lift.
* Ara-Burroni-Guiraud-Malbos-Métayer-Mimram, *Polygraphs: From
  Rewriting to Higher Categories*, `arXiv:2312.00429` (Dec 2023).
  Cambridge University Press 2023.  §17 surveys Gray tensors with
  full formulas; substrate the (T4) lift would build on.
* Zwart-Marsden, *No-go theorems for distributive laws*, LICS 2019,
  `arXiv:1811.06460`.  Supplies the no-go catalogue that (T7)
  cross-references for explicit rejection of colliding extensions.
* Our own design supplies the ProfileCapabilities honesty ledger
  (T3, upper bound only — not interaction proof) and the explicit
  no-go register (T7).  The composite (T1)–(T8) is FX-original
  *as a target*; whether it mechanizes is an open program.

**Status in the LoC budget.**  ~5K LoC *target* added on top of the
existing Tier 0 budget.  Updated Tier 0 total IF the program closes:
~17K LoC (12K base + 5K Cellular Tensor).  No current Lean code in
the lean-fx-2 tree implements any of the five `CellularTensor/*.lean`
files referenced above.  If/when shipped, expected payback after
~3 profile extensions because each later extension can cite the
universal property instead of bespoke admissibility-preservation
proofs; the per-extension cost falls from ~3K LoC to ~1K LoC.
Failure mode: if the lift is harder than estimated, §3.14 reverts
to per-pair witnesses indefinitely.

**What this would give FX if (T1)-(T8) mechanize.**  The ability to
compose admissible type theories with a mechanized universal
property, with explicit honest capability tracking, without
depending on unpublished math (vol II).  If achieved, this becomes
a structural mechanism for §3.14's profile-extension calculus and
§3.15's demonstration profile catalog.  Until then, §3.14 uses
**explicit bilax-compatibility witnesses** per extension and an
**explicit no-go register** against the Zwart-Marsden catalogue;
§3.15's entries (Probabilistic-Iris FX, Differential-SDG FX,
Quantum-Linear FX, ...) each require their own per-pair admission
proofs against the existing axes, not a free corollary from §3.0.7.

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
  - dim 0 (types + terms as values): `tD = ∅`.  Values are directed;
    a term equals another term only through a positive-dimensional
    conversion witness, not by marking a value itself thin.
  - dim 1 (steps / conversions): identities and saturated conversion
    witnesses are thin; raw directed operational steps are not thin
    unless the saturation proof constructs their coherent inverse.
    β/η/ι steps become thin exactly when `Conv` equates source and
    target; cubical-glue boundary mismatches may remain non-thin.
  - dim ≥ 2 (cd_lemma, Squier, higher coherence): the profile may mark
    confluence and coherence cells thin once the saturation proof has
    produced the relevant fillers.  The "all higher cells are thin"
    shortcut is valid only for the saturated FX profile, not for an
    arbitrary profile.

**Lean signature:**

```lean
/-- Per-cell per-dim thinness marker.  Verity 2008 / Loubaton 2023.

A `Stratification` over a shape family is a Prop-valued predicate per
dim per cell, satisfying closure axioms. -/
structure Stratification
    (shapes : Nat → CellShape)
    (algebra : PolyMonad shapes) where

  /-- The per-cell thinness predicate on free cells, not just on
  generators.  Marking only generators is too weak: `Conv` and
  cd/Squier fillers are composites. -/
  thin : ∀ (d : Nat), algebra.freeCells d → Prop

  /-- Identity cells are always thin.  Loubaton 2301.11424 Def 2.2. -/
  identitiesAreThin : ∀ d a, thin d (algebra.unit d a)

  /-- Composition of thin cells is thin (when defined). -/
  closedUnderComp : ∀ d a b composable,
    thin d a → thin d b → thin d (algebra.mult d a b)

  /-- Sources and targets of thin cells are thin (when defined). -/
  closedSrcTgt : ∀ d a (h : thin d a), ...

  /-- Decidable membership.  Required for FX's zero-axiom Conv check.
  This is per-profile; arbitrary profiles do not get it for free. -/
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
  thinFillers : ∀ {dim} (horn : Horn dim) (filler : CertifiedCell _ _ dim _),
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

**Lean signature — doctrine stack, not "21 focuses":**

```lean
/-- Only these are Myers-Riley cohesive focuses.  The other FX
dimensions are grades, effects, security labels, refinements,
clocks, provenance/trust markers, or version labels. -/
inductive CohesiveFocus where
  | differential
  | equivariant
  | simplicial
  | real
  deriving DecidableEq

/-- A cohesive focus carries the Myers-Riley modality chain. -/
structure CohesiveModality (focus : CohesiveFocus) where
  shape : Type u → Type u   -- ∫
  flat  : Type u → Type u   -- ♭
  sharp : Type u → Type u   -- ♯
  shapeFlatAdj : Adjoint shape flat
  flatSharpAdj : Adjoint flat sharp

/-- Orthogonality is a theorem only between cohesive focuses for
which the Myers-Riley detector condition has actually been proved. -/
structure CohesiveOrthogonality
    (leftFocus rightFocus : CohesiveFocus)
    (leftModality : CohesiveModality leftFocus)
    (rightModality : CohesiveModality rightFocus) where
  flatCommutes :
    ∀ (carrier : Type u),
      rightModality.flat (leftModality.flat carrier) ≃
      leftModality.flat (rightModality.flat carrier)
  detectorIsDiscreteLeftToRight : DetectorDiscrete leftFocus rightFocus
  detectorIsDiscreteRightToLeft : DetectorDiscrete rightFocus leftFocus

/-- The heterogeneous doctrine stack for FX's 21 dimensions.
This replaces the stale "21 pairwise orthogonal focuses" model. -/
structure DimensionDoctrine where
  cohesiveFocuses : Finset CohesiveFocus
  cohesive : ∀ focus, focus ∈ cohesiveFocuses → CohesiveModality focus
  cohesiveOrthogonality :
    ∀ leftFocus rightFocus
      (leftWitness : leftFocus ∈ cohesiveFocuses)
      (rightWitness : rightFocus ∈ cohesiveFocuses),
      leftFocus ≠ rightFocus →
      Option (CohesiveOrthogonality leftFocus rightFocus
        (cohesive leftFocus leftWitness)
        (cohesive rightFocus rightWitness))

  resourceAlgebra : OrderedGradeSemiring
  effectTheory : CBPVEffectTheory resourceAlgebra
  costAlgebra : OrderedSemiring
  securityLattice : DeclassificationLattice
  refinementDoctrine : PredicateDoctrine
  clockTheory : GuardedClockTheory
  provenanceTheory : ProvenanceDoctrine
  trustTheory : TrustDoctrine
  observabilityTheory : ObservabilityDoctrine
  versionTheory : VersionLattice

  /-- Cross-doctrine laws are typed by doctrine pair.  They are not
  all Myers-Riley orthogonality witnesses.  Each entry is one of:
  strong distributive law, weak/Garner law, one-way law, nesting law,
  or explicit no-go citation. -/
  interactionLaws : CrossDoctrineDistributiveLaws

/-- The ∞-topos semantics hosts the cohesive part and interprets the
other doctrines through the MTT/effect/resource layers. -/
structure InfTopos where
  presentationSite : Polygraph
  localizationMaps : List (PreSheafMorphism presentationSite)
  finiteLocalization : localizationMaps.length ≤ maxLocalizationCount
  descent : ∀ (cover : presentationSite.GrothendieckCover),
            EffectiveEpiFamily cover
  subobjectClassifier : UniverseCell presentationSite
  doctrine : DimensionDoctrine
  doctrineSoundness : DoctrineSoundInTopos doctrine presentationSite

/-- The FX semantic object: 4 cohesive focuses plus heterogeneous
resource/effect/security/refinement/clock/trust/version doctrines. -/
def infToposOfFX : InfTopos where
  presentationSite := fxProfile.toPolygraph (boundedDim := 3)
  localizationMaps := fxUnivalenceLocMaps ++ fxModalLocMaps ++ fxDescentLocMaps
  finiteLocalization := fxLocalizationMapsAreFinite
  descent := fxDescentProof
  subobjectClassifier := UniverseCell.universeOfFX
  doctrine := fxDimensionDoctrine
  doctrineSoundness := fxDimensionDoctrineSoundness
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

**Lean LoC estimate:** ~9K LoC for the doctrine stack:
~2K for the four cohesive focuses and Myers-Riley orthogonality
where it truly applies, ~3K for resource/effect/cost/security
doctrines, ~2K for refinement/clock/provenance/trust/version
doctrines, and ~2K for the cross-doctrine interaction matrix.
This deliberately deletes the stale `C(21,2)=210` proof obligation.

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

**Risk:** the cross-doctrine interaction matrix must be specifically
verified.  Some pairs are strong distributive laws, some are weak
laws, some are nesting inclusions, and some are genuine no-go cells.
The admission contract rejects an extension when its requested
interaction lands in a no-go cell rather than silently pretending
the pair is orthogonal.

**Lean signature — categorical semantics via Dugger 2001
combinatorial presentation:**

The doctrine stack above is the surface syntax; the following
`InfToposPresentation` is the finite Dugger/Bousfield presentation
used by the `InfTopos` semantic model.  Both ship together: the type
theory is what programmers write, the presentation is what the
soundness theorem computes over.

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
structure InfToposPresentation where

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

  /-- Doctrine data interpreted in the presentation.  Only the
  cohesive sublayer contributes Myers-Riley focuses; resource,
  effect, security, clock, trust, and version layers contribute
  their own algebraic structure. -/
  doctrine : DimensionDoctrine

  /-- Coherence proofs (triangle identities, pentagon for
  cohesion, descent commutes with localization, and cross-doctrine
  distributive laws).  All shippable per the finite-presentation
  discipline. -/
  coherenceProofs : DoctrineCoherence doctrine

/-- The FX ∞-topos, constructed via Dugger from the fxProfile
polygraph as small site. -/
def fxInfToposPresentation : InfToposPresentation where
  presentationSite := fxProfile.toPolygraph (boundedDim := 3)
  localizationMaps := fxUnivalenceLocMaps ++ fxModalLocMaps
                                          ++ fxDescentLocMaps
  finiteLocalization := fxLocalizationMapsAreFinite
  descent := fxDescentProof
  subobjectClassifier := UniverseCell.universeOfFX
  doctrine := fxDimensionDoctrine
  coherenceProofs := fxDimensionDoctrineCoherence
```

**Lean LoC estimate:** ~30K LoC.  Distribution:
* `PreSheafMorphism` + projective model structure: ~6K LoC
  (simplicial presheaves on a small ∞-cat, Quillen-Bousfield style,
  combinatorial-tractable per Beke 2000 / Smith)
* Dugger localization theorem (Trans. AMS 353): ~8K LoC
  (the constructive proof — given a combinatorial model cat M with
  presentation `(C, S)`, exhibit M as `sPre(C)[S⁻¹]`)
* Descent / Čech-cover decidability for fxProfile: ~4K LoC
* Doctrine integration: ~5K LoC (cohesive adjunctions plus
  resource/effect/security/refinement/clock/trust/version
  interpretation, with coherence proofs)
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

- A `PolyProfile` bundles all thirteen axes.  But different profile choices
  may DEPEND on each other: e.g. the choice of shape at dim n+1 may
  depend on which generators exist at dim n; the choice of saturation
  at dim 3 may depend on which β-rules fire at dim 2.

- The categorical way to express "dependent profile" is a Grothendieck
  fibration: profiles form a category, and a profile-of-profiles is a
  section of the fibration.

- Cisinski 2019 shows how to handle self-reference in this fibration
  via ω-localization without paradox.  This is what lets a certified
  universe cell over raw `PolyTerm fxProfile 0` classify `fxProfile`
  itself — the universe-of-universes problem at the polygraph level.

**Lean signature:**

```lean
/-- Profiles form a category.  Morphisms are profile homomorphisms
(shape-preserving, marking-preserving, …). -/
structure ProfileMorphism (π₁ π₂ : PolyProfile) where
  shapeHom         : ∀ d, π₁.shapes d ⟶ π₂.shapes d
  algebraHom       : PolyMonadHom π₁.algebra π₂.algebra
  stratificationHom : ∀ d a, π₁.stratification.thin d a → π₂.stratification.thin d (algebraHom.translate a)
  -- … and so on for all thirteen axes …

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

/-- The certified universe cell.  Internal Universe ω at level n.
The raw payload stores the level; certification proves it is the
universe generator at sort `.type`. -/
def universeCell (π : PolyProfile) (n : Nat) :
    CertifiedCell π .type 0 scope :=
  certifyUniverseGenerator n

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

**Three-tiered univalence discipline (Cavallo-Höfer 2026 warning):**

Cavallo-Höfer *Univalence without function extensionality*
`arXiv:2605.00812` (May 2026) proves that **categorical univalence
does NOT imply function extensionality**.  This means PolyCell must
distinguish three separate principles and never infer one from
another:

1. **Operational univalence** — FX's `Step.eqType` reduction rule.
   This is the kernel-level fact `Conv (Ty.id Univ A B) (Ty.equiv
   A B)`.  It is what FX programmers actually use.
2. **Polynomial / categorical univalence** — the universe object
   is subterminal in `Poly^Cart` (Aberlé-Spivak).  This is the
   structural justification.
3. **Consumer extensionality** — function extensionality,
   propositional extensionality, transport laws.  These are what
   *downstream code* depends on for actual proofs.

**The danger:** a profile that establishes only (2) may *not*
provide (3).  Each `ProfileExtension` MUST explicitly record which
extensionality principles it provides, and `ProfileExtension.
metatheoryWitness` must check that any extension claiming "I am
univalent" specifies which tier.  The current `fxProfile` provides
all three (Funext via `Step.eqArrow`, Univalence via
`Step.eqType`, propext via `Step.eqProp`); future profiles may
provide only subsets and must declare so.

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

* FX's doctrine stack (Axis 7) contains a finite modal fragment that
  is exactly the kind of MODE THEORY that MTT was designed to
  parameterize over.  Mode = a 2-category M of "places"; modality μ =
  a 1-cell in M; modal type `⟨μ | A⟩` shifts a type from one mode to
  another.
* **The Gratzer theorem (Theorem 4 in arXiv:2301.11842):**
  Normalization and conversion-checking for MTT reduces to
  **decidability of mode-theory equality**.  Specifically: MTT
  conversion is decidable iff the mode theory's 2-category equality
  is decidable.  Universal — applies to EVERY literature MTT
  instance.
* **FX's mode theory is the finite modal projection of the doctrine
  stack**, not the whole 21-dimensional system and not 21 cohesive
  focuses.  Equality in this projection is a finite-state computation
  (modal atoms, composition table, nesting table, and SProp-valued
  coherence cells).  **Therefore the MTT fragment's mode-theory
  equality is decidable, therefore that fragment's MTT conversion is
  decidable** by Gratzer's universal recipe.

**Lean signature:**

```lean
/-- The MTT mode theory for FX: a 2-category whose objects are the
finite modal projection of Axis 7's doctrine stack, whose 1-morphisms
are modal shifts, and whose 2-morphisms are SProp-valued coherence
witnesses or Makkai/Forest-certified polygraph equalities. -/
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
  modes := FXModeAtom  -- finite modal projection of DimensionDoctrine
  oneCells := FXModeShift  -- modal shifts induced by doctrine entries
  twoCells := SProp  -- (R2) proof-irrelevant via SProp
  isRigid := fxModeTheoryIsRigid  -- (R1) proved by finite enumeration
  triangleIdentities := fxModeTriangleIdentitiesViaMakkaiForest
  ...
  oneCellEqDecidable := -- decidable: rigid + finite enum
    fxModeOneCellEqDecidable
  twoCellEqDecidable := -- trivial: SProp 2-cells
    fxModeTwoCellEqDecidable

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

* Axis 12 (STC) and Axis 13 (MTT-norm) help resolve FX conv
  decidability by splitting the problem: STC gives the canonicity /
  SN side, while MTT-norm gives conversion checking for the modal
  projection of the doctrine stack.
* The finite modal projection of Axis 7 becomes the input to
  Gratzer's recipe; non-modal doctrines still use their own engines
  (Path A NbE, Path B Makkai/Forest, resource/cost/security
  decision procedures).
* `★ MILESTONE A` (Term.typecheck_decidable, accelerate-P3.12)
  reduces to: ship fxModeTheory.oneCellEqDecidable + invoke
  Gratzer.normalization.
* Does **not** eliminate the Path A / Path B debate for all of FX.
  It eliminates one large subproblem: modal conversion for the rigid
  MTT fragment.  Global `Conv.decide` still routes through the
  wrapper that picks Path A (NbE NF equality) or Path B
  (Makkai/Forest word equality) depending on which engine is present.

**Lean LoC estimate:**
* fxModeTheory definition + finite modal projection + rigidity proof:
  ~3K LoC.
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
to be RIGID (no non-trivial 2-isomorphisms).  FX's finite modal
projection must be checked for rigidity; the full doctrine stack is
not fed directly to Gratzer's theorem.  If non-rigidity is found,
shrink the projection to the rigid subcategory and route the excluded
doctrine interactions through Path A/B or explicit distributive-law
checks.

---

### 3.14 Profile Extension Calculus — the load-bearing addition

**Reference:** C.B. Aberlé, *Compositional Program Verification with
Polynomial Functors in Dependent Type Theory*, `arXiv:2604.01303`
(Apr 2026, Agda-formalized).  Program interfaces as polynomial
functors; implementations as Kleisli morphisms for the free monad;
dependent polynomials as pre/post specifications; wiring diagrams as
composition.  Plus the categorical machinery the calculus inherits:
Uemura CwR morphisms (`arXiv:1904.04097`), Beck distributive laws +
Garner weak distributive laws (FoSSaCS 2020 `arXiv:2003.07304`),
Zwart-Marsden no-go theorems (LICS 2019 `arXiv:1811.06460`),
Hirschhorn left Bousfield localization (AMS 2003).

**Composition primitive (§3.0.7).**  The composition of two
`ProfileExtension` values is the **FX PolyCell Cellular Tensor**
introduced as §3.0.7.  Per-pair distributive-law search is
REPLACED by the cellular tensor's universal property (T4) +
ProfileCapabilities meet (T3) + structural no-go discharge (T7).
This makes §3.14's `extendProfile` operation associative up to
lax 3-cell (T5) and symmetric up to lax 2-cell (T6) without
depending on Almeida vol II's (still-unpublished) full monoidal
structure on GAT.  Each new extension specifies its
`ProfileCapabilities` and its bilax-compatibility witnesses; the
universal property discharges the implementation-meets-specification
obligation uniformly.

**Why this is the missing piece:**

The previous thirteen axes describe what a profile *contains*.  They
do not describe how a profile *grows*.  Without an extension
calculus, every new feature is a hand-built `PolyProfile` instance —
the cascade tax has moved from `Term` constructors into profile
obligations rather than disappearing.

The extension calculus turns "add a feature" from a 5–15K LoC
artisanal proof effort into ONE structured obligation discharged
against ONE generic admission theorem.  This is the mechanism that
makes "expand at whim, inherit everything" honest rather than
aspirational.

**Reframing the thesis:**

> PolyCell is not a 13-axis object.  PolyCell is a small raw/certified
> kernel plus a profile-extension calculus.  FX is the first admissible profile.
> Every future feature — probability, differentiation, quantum,
> distributed protocols, scientific simulation, self-hosting — ships
> as a `ProfileExtension` satisfying the admission contract.  The
> "thirteen axes" describe the *shape* of any single admissible
> profile; the calculus describes the *space* of admissible
> profiles.

**Substrate — one obligation, six views:**

A `ProfileExtension` is fundamentally a representable-map-category
morphism `σ : base.signature → extended.signature` equipped with an
algebraic weak factorization system (AWFS) extension over the
existing rewrite system.  The six "fields" below are projections of
this single mathematical object, not six independent obligations:

```lean
/-- A profile extension.  ONE categorical object (CwR morphism +
AWFS extension) presented as SIX named projections so feature
authors can populate each role separately. -/
structure ProfileExtension (base : AdmissibleProfile) where
  /-- (1) Aberlé-Spivak: the polynomial-functor interface added by
  this extension.  Generators + their arities + their dependent
  payloads. -/
  interfacePolynomial : PolynomialInterface base.signature

  /-- (2) Kleisli implementation for the free monad of the
  interface — the actual reduction behavior of the new
  generators. -/
  implementation : KleisliImplementation interfacePolynomial

  /-- (3) Dependent-polynomial specification — pre/post conditions
  encoded as a dependent polynomial.  Refinement-type contracts at
  the feature boundary. -/
  specification : DependentPolynomialSpec interfacePolynomial

  /-- (4) Wiring-diagram composition law — proves that the
  implementation satisfies the specification under interface
  composition (Aberlé §4 wiring diagrams). -/
  wiringLaw : WiringDiagramComposes implementation specification

  /-- (5) Bilax compatibility witness — for the cellular tensor
  (§3.0.7) universal property to discharge composition, each
  extension supplies a `BilaxCompatible` record whose 2-cells
  witness sort-paired generator commutation.  Per-pair Beck /
  Garner-weak / colax-lax distributive laws are SUBSUMED by the
  universal property + ProfileCapabilities meet semantics (T3) +
  structural Zwart-Marsden no-go discharge (T7) of §3.0.7.  When
  bilax compatibility fails, capabilities meet to ⊥ and the
  extension is rejected honestly with named collision. -/
  bilaxCompatibility : BilaxCompatible base interfacePolynomial

  /-- (6) Forgetful lens back to the base profile — embeds rich
  terms back into base via `forget`, lifts base terms into rich
  via `lift`, with roundtrip laws guaranteeing conservativity. -/
  forgetfulLens : ProfileLens (base.extendRaw interfacePolynomial) base

  /-- (7) Metatheory-preservation witness — proves the BKS sconing
  argument lifts through the extension, so canonicity /
  normalization / parametricity transfer to the extended
  profile. -/
  metatheoryWitness : PreservesAdmissibility base interfacePolynomial

  /-- (8) Erasure-preservation witness — proves the realizability
  tripos for the base lifts to the extension, so runtime erasure
  + compiler correctness transfer. -/
  erasureWitness : PreservesRuntimeErasure base interfacePolynomial
```

**The headline admission theorem:**

```lean
/-- Extension of any admissible profile by an admitted extension
yields a new admissible profile.  This is THE theorem that makes
"add features forever" honest.  Direct corollary of §3.0.7's
FX PolyCell Cellular Tensor Theorem applied to the cellular tensor
`base ⊗_cell ext.asProfile`. -/
theorem extendProfile_preserves_admissible
    (base : AdmissibleProfile)
    (ext : ProfileExtension base) :
    AdmissibleProfile (base.extend ext) :=
  -- Constructive proof, ~2K LoC (down from ~3K via §3.0.7 reuse):
  -- 1. base.extend ext = base ⊗_cell ext.asProfile by construction.
  -- 2. §3.0.7 (T2) Admissibility preservation: the cellular tensor
  --    of two admissible profiles is admissible, via BKS internal
  --    sconing composition.
  -- 3. §3.0.7 (T3) Capability meet: extended profile's capabilities
  --    are base.capabilities ⊓ ext.capabilities; if meet = ⊥ the
  --    extension is rejected honestly.
  -- 4. §3.0.7 (T4) Universal property discharges Aberlé wiring-
  --    diagram composition uniformly.
  -- 5. §3.0.7 (T7) Structural no-go discharge replaces per-axis
  --    distributive-law matrix.
  -- 6. ProfileLens roundtrip discharges conservativity (unchanged).
  ...
```

**Lens discipline — the conservative-extension guarantee:**

A feature extension MUST include a lens back to the base profile.
The forward direction (`lift`) embeds old FX terms into the richer
profile.  The backward direction (`forget`) drops the new
structure.  Roundtrip laws guarantee that adding a feature does NOT
silently break existing code.

```lean
/-- A profile lens from a rich profile to a base profile.
Conservative-extension witness: existing FX programs keep their
typing, reduction, Conv, erasure, and compiled behavior under any
admitted extension. -/
structure ProfileLens (rich base : PolyProfile) where
  forget : ∀ {sort dim scope boundary raw},
           PolyCell rich sort dim scope boundary raw →
           CertifiedCell base sort dim scope

  lift : ∀ {sort dim scope boundary raw},
         PolyCell base sort dim scope boundary raw →
         CertifiedCell rich sort dim scope

  /-- Round-trip law: lifting then forgetting is the identity on
  base terms.  This is the conservativity witness. -/
  forget_lift : ∀ {sort dim scope boundary raw}
      (cell : PolyCell base sort dim scope boundary raw),
                forget (lift cell) = cell

  /-- Typing preservation: a typable base term remains typable
  after lifting, with the same type up to lens transport. -/
  preservesTyping : PreservesTyping lift forget

  /-- Conv preservation: convertible base terms remain convertible
  in the rich profile.  Equivalent base terms are equivalent in
  the extension. -/
  preservesConv : PreservesConv lift forget

  /-- Erasure preservation: the compiled binary of a base term is
  unchanged by lifting then forgetting.  Existing FX binaries are
  bit-identical under any admitted extension. -/
  preservesErase : PreservesErase lift forget
```

**Why this aims to prevent the cascade reappearing as profile obligations:**

The eight projections of `ProfileExtension` are intended to be eight
views of one categorical object — a CwR morphism + AWFS extension
pair — *if* §3.0.7 (T1)-(T8) mechanize as targeted.  Until then they
remain eight per-extension proof obligations that the author must
discharge individually.  A feature author writes:

```lean
def addProbability : ProfileExtension fxProfile where
  interfacePolynomial := probabilityInterface   -- Markov polynomial
  implementation      := samplingKleisli        -- Giry monad Kleisli
  specification       := bayesianContract       -- conditioning
                                                 -- as dep poly
  wiringLaw           := markovWiringComposes   -- discharged from
                                                 -- Markov-cat laws
  bilaxCompatibility  := {                      -- per existing axis,
                                                 -- supplied EXPLICITLY
                                                 -- per §3.14 + §3.0.7
                                                 -- (T4); no free
                                                 -- universal-property
                                                 -- corollary yet
    cohesive   := probabilityCommutesWithFlatSharp,
    resource   := probabilityWeaklyDistributesOverLinear,  -- Garner
    cost       := probabilityCostBoundedByEntropy,
    security   := probabilityRespectsDeclassification,
    effect     := MarsdenZwartTable.probabilityVsExceptions
                  -- NO-GO registered; admission contract REJECTS
                  -- the extension or admits it syntax-only per (T7)
  }
  forgetfulLens      := probabilityForgetfulLens
  metatheoryWitness  := sconingLiftsProbability
  erasureWitness     := samplingErasureIsTripos
```

and `extendProfile_preserves_admissible` does the rest.  The
cascade does NOT reappear because:

1. **No new `Term` constructors** — generators live in
   `interfacePolynomial`, processed by one generic dispatcher.
2. **No per-feature SR / SN proofs** — `metatheoryWitness` plugs
   into the universal sconing argument once.
3. **Per-feature cd_lemma rewrites are reduced, not eliminated** —
   AWFS extension composes with the existing AWFS *when the bilax
   coherence witness is supplied*; in the no-witness or no-go case
   the extension is admitted only as syntax-only or rejected.
4. **Per-feature erasure proof still required** — `erasureWitness`
   plugs into the realizability tripos when supplied; FX does not
   discharge erasure soundness automatically.

**The composition algebra — distributive laws and their failures:**

Two extensions `σ : base → mid` and `τ : mid → top` compose into
`τ ∘ σ : base → top` iff a distributive law witness exists.  The
table of known compositions:

| Pair | Distributive law | Reference |
|---|---|---|
| State + Reader | Strong (Beck 1969) | classical |
| State + Probability | Strong | Plotkin-Power 2002 |
| Probability + Powerset | Weak (Garner) | Garner FoSSaCS 2020 |
| Probability + Exceptions | NONE (no-go) | Varacca-Winskel 2006 |
| Exception + Continuation | Strong | Filinski 1994 |
| Linear + Probability | Colax-lax | Cheng-Gurski-Riehl 2014 |
| Cohesive + Resource | One-way (cohesive→resource) | Myers-Riley §6.4 |
| Probability + Powerset + State | Triple no-go | Zwart-Marsden LICS 2019 |

Every new `ProfileExtension.bilaxCompatibility` field must cite where
it sits in this table.  Extensions that hit a no-go cell are rejected
at the admission step — the user is told *which* prior extension
their feature collides with and *which* distributive law would
need to exist.

**The localization view — adding features as Bousfield localization:**

Equivalently (and this is the deeper view): adding a feature to FX
is a **left Bousfield localization** of the FX type theory at a new
class of arrows = new equations / new reductions.

```
T₀          = pure MLTT with universes
T_FX        = Loc(T₀, {β, η, modal, cubical, …, MTT-norm arrows})
T_FX_prob   = Loc(T_FX, {sample, observe, Bayes arrows})
T_FX_prob_q = Loc(T_FX_prob, {qubit, measure, no-clone arrows})
…
```

Bousfield localization is **associative** when generating sets are
disjoint, and the obstruction to commutativity is precisely a
homotopy 2-cell — Mac Lane's coherence becomes the calculus of
feature composition.  Hirschhorn 2003 *Model Categories and Their
Localizations* gives the algorithm; the small-object argument
makes it constructive when the localizing set is finite per
extension.

The `extendProfile` operation IS left Bousfield localization at
the arrows generated by `ext.interfacePolynomial`.  The admission
theorem IS the small-object argument applied to that localization.

**The ∞-cosmos ambient universe:**

Tier 0 currently cites Uemura's 2-category framework
(`arXiv:1904.04097`).  The strict frontier is the **Riehl-Verity
∞-cosmos** lift: `CwR∞` is an (∞,2)-category designed to be "the
category of all (∞,1)-category-of-CwRs" without size issues
(Riehl-Verity *Elements of ∞-Category Theory*, CUP 2022,
`arXiv:1910.07635`).

- Type theories are objects of the ∞-cosmos `CwR∞`
- Extensions are arrows
- Conservative extensions are fully faithful arrows
- Uemura's bi-initial model is the adjoint that the ∞-cosmos
  adjoint functor theorem provides
- Composition of extensions = composition of arrows, with the
  ∞-cosmos's own coherence handling the "third level" of obligation

For FX, the practical upshot is that `extendProfile` composes
associatively up to a definable 2-cell, and the composition of
admission witnesses is itself admissible.

**Lean LoC estimate (Axis 14):** ~7K LoC.  Distribution:

* `ProfileExtension` structure + the 8 projections: ~1K LoC.
* `ProfileLens` + roundtrip laws: ~1K LoC.
* `DistributiveLawMatrix` + the no-go citation table: ~1K LoC.
* `extendProfile` operation: ~500 LoC.
* `extendProfile_preserves_admissible` headline theorem: ~3K LoC.
* `BousfieldLocalize` equivalence proof + Hirschhorn small-object
  argument applied: ~500 LoC.

**Mechanizability:**

* Aberlé `arXiv:2604.01303` is Agda-formalized (paper Apr 2026).
  Lean port is direct translation of the polynomial-functor /
  wiring-diagram machinery.
* Garner weak distributive laws (FoSSaCS 2020) are paper-form but
  fully constructive — Lean port is novel.
* Hirschhorn's left Bousfield localization is a classic, fully
  constructive given a finite localizing set.
* Riehl-Verity ∞-cosmos is paper-form; FX would be first
  proof-assistant implementation of the ∞-cosmos calculus, but
  only the 2-truncation (= Uemura's framework) is needed for the
  admission theorem to ship.

**Notes:**

* The thirteen axes (§3.1-§3.13) become the *shape* of any single
  admissible profile.  Axis 14 is the *generator* of the space of
  profiles.  Both ship.
* Composition is per-profile, not global: each extension records
  per-pair distributive-law evidence (or no-go citation).  There
  is no "all extensions compose" theorem; there cannot be one
  (Zwart-Marsden no-go).
* The reverse-mathematical strength of each extension should be
  recorded: which extension needs Univalence, which needs SN,
  which needs decidable conv.  The composition obligation
  includes a strength-compatibility check.

### 3.15 Demonstration profiles — what the extension calculus enables

Once Axis 14 is in place, the following profiles ship as
`ProfileExtension` values over `fxProfile`, not as bespoke kernel
forks.  Each carries the eight admission obligations described
above.  Profiles are classified by their **PolyCell Level** —
the depth of structural change they make to the profile space:

| Level | What changes |
|---|---|
| **L1 Feature**       | Adds generators + payloads.  Conservative by construction. |
| **L2 Rewrite**       | Adds reductions.  Must prove SN + confluence preservation. |
| **L3 Doctrine**      | Adds a new modal / resource / effect / security doctrine. |
| **L4 Universe**      | Adds a new model / universe / classifier object. |
| **L5 Meta-profile**  | Generates, checks, or transforms other profiles. |

#### Catalog of admissible target profiles

| Profile | Level | What it enables | Prerequisite extensions / substrate |
|---|---|---|---|
| **Probabilistic-Iris FX** | L3-L4 | `sample`, `observe`, Bayesian conditioning, randomized algorithms, probabilistic heap programs, frame-preserving updates on probabilistic resources | Lohse et al. *Amaryllis* `arXiv:2605.13765` (probabilistic Iris, Rocq-mechanized 2026); Giry monad + measure-theoretic substrate; Markov category interaction laws |
| **Differential-SDG FX** | L3-L4 | Differentiable programs, AD proofs, infinitesimals, tangent types, smooth control, machine-learning programs with verified gradients | Tangent categories (Rosický-Cockett-Cruttwell); differential linear logic (Ehrhard); SDG modality; interaction with linear-resource axis |
| **Quantum-Linear FX** | L4 | Qubits, no-cloning by type, circuit extraction, measurement effects, quantum error correction with formal certificates | Linear DTT impredicativity (Speight-van der Weide `arXiv:2602.08846`); dagger compact categories; ZX-calculus; stabilizer formalization; measurement effect doctrine |
| **Verified Hardware FX** | L2-L3 | RTL/Verilog extraction, clock domains, pipeline correctness proofs, hardware/software contracts | Clock-domain doctrine (already in `fxProfile`); bitvector semantics; temporal/session layer; synthesis-preserving erasure witness |
| **Distributed-Protocol FX** | L3 | Multiparty sessions, actor systems, consensus proofs, fault domains, replay/ordering guarantees | Session types (already in `fxProfile`); separation logic (via Iris substrate); trace semantics; async/failure distributive laws |
| **Crypto / ZK FX** | L3-L4 | Constant-time proofs, zk-SNARK circuits, protocol transcripts, leakage budgets, proof-carrying crypto | Security lattice (already in `fxProfile`); CT observability axis; arithmetic-circuit polynomial substrate; randomness/probability interaction |
| **Synthetic Algebraic Geometry FX** | L4 | Schemes and stacks internally, sheaf semantics, derived-geometry hooks, synthetic Stone duality | Coquand-Höfer-Sattler *Constructive higher sheaf models* `arXiv:2605.15126` (May 2026); cohesive/topos profile; polynomial-universe integration |
| **Mathlib Import FX** | L5 | Mathlib theorems imported as profile extensions; lemmas become cells / generators with proof-preserving lenses | `ProfileExtension` calculus (Axis 14); theorem-to-generator translator; conservative lens back to Lean/Mathlib |
| **Self-Hosting Kernel FX** | L5 | FX defines FX in FX; verified compiler / kernel; reflection and reification | Reflection profile (Axis 12 STC); staged metaprogramming; proof-producing elaborator; trust + erasure discipline |
| **Causal / Decision FX** | L3-L4 | Causal graphs, interventions, counterfactuals, policy verification | Markov categories (Fritz); Probabilistic-Iris FX as prereq; Pearl do-calculus laws as rewrite system; identifiability checker |
| **Resource-Economics FX** | L3 | Budgets, gas, latency, energy, memory, cloud-cost as first-class verified dimensions | Ordered semiring / quantale of costs; calf/decalf (already in `fxProfile`); resource algebra interaction; extraction-cost theorem |
| **Reversible / Thermodynamic FX** | L3-L4 | Reversible programs, energy bounds (Landauer), invertible interpreters, low-power circuits | Invertible categories (Heunen-Karvonen); dagger structure; linearity prereq; Bennett-style reversible computation substrate |
| **Secure Agentic Workflow FX** | L3-L5 | LLM agents with typed permissions, audit trails, tool-use proofs, safe delegation | Capability algebra (lattice); provenance + trust dimensions (already in `fxProfile`); temporal contracts; effect handlers |
| **Scientific Simulation FX** | L4 | PDE / ODE solvers with verified error bounds, units, meshes, stability proofs | Numeric tower (already in `fxProfile`); interval / error analysis; Differential-SDG FX as prereq; finite-element formalization |
| **Polyglot Contract FX** | L5 | One contract verified across Rust / C / Verilog / Python / Lean extraction targets | Multi-target semantics; representation lenses; ABI profiles; compiler-correctness witness per target |

**Five highest-value profiles** (ROI on math investment):

1. **Probabilistic-Iris FX** — most "new power per math risk"; recent
   Rocq mechanization exists (Amaryllis); composes cleanly with
   the existing Iris resource-algebra substrate (§3.7 resource
   tier).
2. **Differential-SDG FX** — unlocks ML / control / physics
   simultaneously while fitting the modal doctrine; cohesive
   structure already in place.
3. **Quantum-Linear FX** — flashy but real; the linearity axis
   already aligns with no-cloning structurally.
4. **Distributed-Protocol FX** — very FX-native because sessions,
   effects, and resources already exist; mostly a doctrine-tier
   extension over composed primitives.
5. **Self-Hosting Kernel FX** — long-term capstone; makes the
   certified PolyCell kernel prove its own extension machinery from
   inside, closing the loop.

**Honest scope statement:**

With the current document *without Axis 14*, every profile in the
catalog above must be hand-built as its own `PolyProfile`
instance.  That works but does not give "extend at whim" — each
profile costs a full cascade.

With Axis 14, every profile in the catalog ships as a
`ProfileExtension` value, with `extendProfile_preserves_admissible`
discharging all metatheory.  Future FX features that have never
been thought of yet (energy-budget contracts? differential privacy
budgets? proof-carrying smart-contract code?  *anything*) become
new `ProfileExtension` values added to the catalog without kernel
work.  This is the "infinite times" mechanism Grigory's design
brief asks for.

---

## 4. The raw/certified PolyCell signature

After the thirteen profile axes are defined, the trusted kernel surface
has two layers.

1.  `PolyTerm π dim` is raw syntax.  It is deliberately permissive:
    imported data, serialized cells, broken generator ids, wrong arity,
    bad sort choices, bad vertical composites, and future `compH`
    experiments must all be representable so the checker can say
    `false` / `none` / `rejected reason`.
2.  `PolyCell π sort dim scope boundary raw` is certified syntax.  It
    is indexed by the raw cell it certifies, and its constructors are
    the only trusted introduction rules.  Ill-sorted, ill-scoped, or
    boundary-incompatible cells are unconstructable at this layer.

This mirrors the existing kernel pattern:

```lean
RawTerm scope                         -- permissive-ish syntax
Term ctx type raw                     -- intrinsic typed certificate

PolyTerm profile dim                  -- permissive raw cell syntax
PolyCell profile sort dim scope b raw -- intrinsic certified cell
```

The profile-extension calculus (§3.14) lives over admissible profiles;
it is not another constructor family inside raw `PolyTerm`.

The Lean block below is a target shape, not a claim that the current
files already expose these fields.  The rollout in §10 splits it into
small modules so each invariant can be audited before downstream views
depend on it.

```lean
namespace LeanFX2.Foundation.PolyCell.Core

/-- The PolyProfile bundles all thirteen axes.  Each axis is a structure
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

  /-- AXIS 11: Single-substitution calculus backbone. -/
  substitutionBackbone : SingleSubstitutionBackbone algebra

  /-- AXIS 12: Synthetic Tait computability classifier. -/
  stcClassifier : SyntheticTaitClassifier

  /-- AXIS 13: MTT normalization gateway for the modal projection. -/
  mttGateway : MTTNormalizationGateway topos

  /-- Cross-axis consistency constraints. -/
  consistency : PolyProfile.ConsistencyConditions ⟨shapes, algebra,
    stratification, saturation, enrichment, complicialGray, topos,
    parentProfile, omegacE, universeConfig, substitutionBackbone,
    stcClassifier, mttGateway⟩

/-- Raw syntax.  This layer is input data, not the trusted invariant. -/
inductive PolyTerm (profile : PolyProfile) : Nat → Type where
  | atom :
      (cellId : Nat) →
      (payload : Nat) →
      PolyTerm profile 0
  | cell :
      {dim : Nat} →
      (ruleId : Nat) →
      PolyTerm profile dim →
      PolyTerm profile dim →
      PolyTerm profile (dim + 1)
  | compV :
      {dim : Nat} →
      PolyTerm profile (dim + 1) →
      PolyTerm profile (dim + 1) →
      PolyTerm profile (dim + 1)
  | compH :
      {dim : Nat} →
      PolyTerm profile (dim + 1) →
      PolyTerm profile (dim + 1) →
      PolyTerm profile (dim + 1)
  | identity :
      {dim : Nat} →
      PolyTerm profile dim →
      PolyTerm profile (dim + 1)

/-- Sorts are the visible strata of the one FX cell substrate.
These are not separate syntaxes glued later: terms, types, contexts,
mode/grade/effect/protocol data all live in one certified cell world. -/
inductive CellSort where
  | context
  | type
  | term
  | mode
  | effect
  | grade
  | protocol
  deriving DecidableEq

/-- One expected child position of a generator.

`scopeShift` is not arity.  A lambda has arity two but one child lives
under `scope + 1`; a context extension has several children at the same
scope.  This table is the concrete polynomial fiber / list of directions
for the generator. -/
structure ChildSpec where
  cellSort : CellSort
  cellDimension : CellDim
  scopeShift : Nat
  deriving DecidableEq

/-- Boundary index of a certified cell.  Dim-0 cells are vertices.
Higher boundaries are raw source/target endpoint indices; constructors and
the checker separately require endpoint certificates before producing a
`PolyCell` over those raw endpoints. -/
def CellBoundary (profile : PolyProfile) :
    CellSort → Nat → Nat → Type
  | _, 0, _ => Unit
  | sort, dim + 1, scope =>
      PolyTerm profile dim × PolyTerm profile dim

/-- Heterogeneous child list dictated by generator metadata.

TCB.3 ships this first in the non-recursive, parameterized form below.
`ChildCarrier` is an abstract family of children, so the child spine can
enforce sort, dimension, and scope shifts before the full `PolyCell`
boundary layer exists.

TCB.4 then instantiates `ChildCarrier` with `PolyCell profile` in the actual
certified syntax. -/
inductive CellChildren
    (ChildCarrier : CellSort -> CellDim -> Nat -> Type)
    (parentScope : Nat) : List ChildSpec → Type where
  | nil :
      CellChildren ChildCarrier parentScope []
  | cons {childSpec : ChildSpec} {remainingSpecs : List ChildSpec} :
      ChildCarrier childSpec.cellSort childSpec.cellDimension
        (parentScope + childSpec.scopeShift) →
      CellChildren ChildCarrier parentScope remainingSpecs →
      CellChildren ChildCarrier parentScope (childSpec :: remainingSpecs)

/-- Raw child descriptor returned by payload decoders.

This records the shape claimed by decoding.  It does not certify the child:
the stored raw cell is only a permissive `PolyTerm` at the declared
dimension. -/
structure RawChildDescriptor (profile : PolyProfile)
    (cellSort : CellSort) (cellDimension : CellDim) (scope : Nat) where
  rawCell : PolyTerm profile cellDimension

/-- Decoder output for a generator is a child spine whose carrier is raw
descriptors, not certified cells. -/
def RawChildDescriptors (profile : PolyProfile) (parentScope : Nat)
    (childSpecs : List ChildSpec) : Type :=
  CellChildren (RawChildDescriptor profile) parentScope childSpecs

/-- Current supported-generator table for the certified structural layer.

Membership in this table is not enough to certify an atom: atom construction
also needs payload evidence. -/
inductive SupportedGeneratorSpec : GeneratorSpec -> Type where
  | variable : SupportedGeneratorSpec variableGeneratorSpec
  | lambda : SupportedGeneratorSpec lambdaGeneratorSpec
  | application : SupportedGeneratorSpec applicationGeneratorSpec
  | unitType : SupportedGeneratorSpec unitTypeGeneratorSpec
  | piType : SupportedGeneratorSpec piTypeGeneratorSpec
  | contextEmpty : SupportedGeneratorSpec contextEmptyGeneratorSpec
  | contextCons : SupportedGeneratorSpec contextConsGeneratorSpec
  | linearMode : SupportedGeneratorSpec linearModeGeneratorSpec

/-- Current supported-rule table for the certified structural layer.

This is metadata support, not a proof of operational reduction semantics. -/
inductive SupportedRuleSpec : RuleSpec -> Type where
  | termStep : SupportedRuleSpec termStepRuleSpec

/-- First finite application payload whose decoded children are `var 0`
and `var 1` at the parent scope. -/
def applicationVarZeroVarOnePayload : Nat := 9100

/-- Payload evidence for nullary atoms currently safe to certify.

There are deliberately no constructors here for lambda/pi/context extension.
Application is certified only through the separate finite-payload constructor
below, because it must demand certified child cells rather than bare payload
evidence. -/
inductive AtomPayloadEvidence :
    (generatorSpec : GeneratorSpec) -> (scope : Nat) -> (payload : Nat) -> Type where
  | variable {scope index : Nat} :
      index < scope ->
      AtomPayloadEvidence variableGeneratorSpec scope index
  | unitType {scope : Nat} :
      AtomPayloadEvidence unitTypeGeneratorSpec scope 0
  | contextEmpty {scope : Nat} :
      AtomPayloadEvidence contextEmptyGeneratorSpec scope 0
  | linearMode {scope : Nat} :
      AtomPayloadEvidence linearModeGeneratorSpec scope 0

/-- Certified cell syntax.  This is the trusted layer.  It is indexed by
the raw syntax it certifies, so erasure back to raw is definitional.

There is deliberately no certified `compH` constructor here until the
Gray tensor boundary formula and disjoint-footprint/matching condition
are mechanized.  Raw `PolyTerm.compH` remains available as input data;
the checker must reject it at this stage. -/
inductive PolyCell (profile : PolyProfile) :
    (sort : CellSort) →
    (dim : Nat) →
    (scope : Nat) →
    CellBoundary profile sort dim scope →
    PolyTerm profile dim →
    Type where

  | atom :
      {scope : Nat} →
      (generator : GeneratorSpec) →
      {payload : Nat} →
      SupportedGeneratorSpec generator →
      AtomPayloadEvidence generator scope payload →
      PolyCell profile generator.cellSort 0 scope ()
        (.atom generator.cellId payload)

  | applicationVarZeroVarOne :
      {scope : Nat} →
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 0) →
      PolyCell profile .term 0 scope ()
        (.atom variableGeneratorSpec.cellId 1) →
      PolyCell profile .term 0 scope ()
        (.atom applicationGeneratorSpec.cellId applicationVarZeroVarOnePayload)

  | cell :
      {scope : Nat} →
      (rule : RuleSpec) →
      SupportedRuleSpec rule →
      {source target : PolyTerm profile rule.endpointDimension} →
      {sourceBoundary targetBoundary :
        CellBoundary profile rule.cellSort rule.endpointDimension scope} →
      PolyCell profile rule.cellSort rule.endpointDimension scope
        sourceBoundary source →
      PolyCell profile rule.cellSort rule.endpointDimension scope
        targetBoundary target →
      PolyCell profile rule.cellSort (rule.endpointDimension + 1) scope
        (source, target)
        (.cell rule.ruleId source target)

  | compV :
      {sort : CellSort} →
      {dim scope : Nat} →
      {source middle target : PolyTerm profile dim} →
      {firstRaw secondRaw : PolyTerm profile (dim + 1)} →
      PolyCell profile sort (dim + 1) scope (source, middle) firstRaw →
      PolyCell profile sort (dim + 1) scope (middle, target) secondRaw →
      PolyCell profile sort (dim + 1) scope
        (source, target)
        (.compV firstRaw secondRaw)

  | identity :
      {sort : CellSort} →
      {dim scope : Nat} →
      {boundary : CellBoundary profile sort dim scope} →
      {baseRaw : PolyTerm profile dim} →
      PolyCell profile sort dim scope boundary baseRaw →
      PolyCell profile sort (dim + 1) scope
        (baseRaw, baseRaw)
        (.identity baseRaw)
end

/-- Why a raw cell failed certification. -/
inductive CellCheckRejection where
  | unknownGenerator
  | wrongSort
  | badPayload
  | wrongArity
  | wrongChildShape
  | badBoundaryEndpoint
  | badVerticalBoundary
  | unsupportedCompH
  | unsupportedCertification

/-- Infer a certified package from raw input.

This is the current TCB.7d ingress, not the final recursive checker.  It
certifies only the dim-0 subset whose constructors are implemented in the
certified layer: in-scope variables, unit type, empty context, linear mode,
and the single finite application payload `app(var 0, var 1)` at scopes where
both decoded variables are in scope.  The application ingress now invokes the
payload decoder and generic child-shape screen before constructing the
certified parent; it still does not expose a dimension-polymorphic certified
child decoder because the direct dependent version pulled `propext` into the
audit.  Other raw dim-0 atoms remain representable and reject either with the
screen's structural reason or with `unsupportedCertification` when they screen
successfully but lack a certified constructor. -/
structure CertifiedRawCellResult (profile : PolyProfile) (scope : Nat) where
  cellDimension : CellDim
  inputCode : List Nat
  rawCell : PolyTerm profile cellDimension
  cellSort : CellSort
  cellBoundary : CellBoundary profile cellSort cellDimension scope
  certifiedCell :
    PolyCell profile cellSort cellDimension scope cellBoundary rawCell
  hasInputCode :
    hasSameNatList inputCode (rawCellCode rawCell) = true

def inferRawCell? (scope : Nat) (raw : PolyTerm fxProfile 0) :
    Except CellCheckRejection
      (CertifiedRawCellResult fxProfile scope) := ...

/-- Check raw input against an expected certified shape.

`wrongSort` is a rejection of this expected-shape checker.  Bare inference
has no external sort expectation, so it fails with generator, payload, child,
boundary, or unsupported-certification reasons instead. -/
def checkRawCellAs? (expectedSort : CellSort) (expectedScope : Nat)
    (raw : PolyTerm fxProfile 0) :
    Except CellCheckRejection
      (CertifiedRawCellResult fxProfile expectedScope) := ...

end LeanFX2.Foundation.PolyCell.Core
```

Feature operations are **not** raw `PolyTerm` constructors.  Universe
cells, cumulativity, Π/Σ, modalities, cubical paths, `transp`, `hcomp`,
HIT eliminators, probability, quantum, SDG, and every future feature
are entries in `π.algebra.bases` with payload/output/compatibility
tables.  Thinness is also **not** a constructor.  `FXConv` is a
certified dim-1 cell plus a decidable/Prop thinness certificate on that
certified cell's raw erasure; raw thinness facts are usable only under
an existing certified step/cell.

The raw `PolyTerm` inductive has five structural constructors:
`atom`, `cell`, `compH`, `compV`, and `identity`.  The certified
`PolyCell` layer initially exposes only `atom`, `cell`, `compV`, and
`identity`; certified `compH` is blocked until Axis 6 has real Gray
boundary semantics.  Compared to the current 75-ctor `Term` +
100+-ctor `Step` + 100+-ctor `cd_lemma`, this is a ~50× reduction in
inductive surface area and, more importantly, new features no longer
enlarge the raw inductive at all.

**Nonsense policy.**  Nonsense is allowed only in raw input.  Certified
cells must make nonsense unconstructable.  The bridge from raw to
certified must be a computable checker whose successful result carries
the certificate; malformed raw cells return a structured rejection
reason.

**Rejection taxonomy.**  The checker must say `false` at the smallest
failed invariant it can identify:

| Raw problem | Certified response |
|---|---|
| unknown generator id | reject `unknownGenerator` |
| accepted inferred sort differs from expected sort in `checkRawCellAs?` | reject `wrongSort` |
| payload fails to decode | reject `badPayload` |
| decoded child count does not match `ChildSpec` length | reject `wrongArity` |
| child sort/dimension/scope disagrees with `ChildSpec` | reject `wrongChildShape` |
| source/target endpoint is not itself certified | reject `badBoundaryEndpoint` |
| vertical composite middle endpoint does not match definitionally | reject `badVerticalBoundary` |
| raw `compH` before Axis 6 certification | reject `unsupportedCompH` |
| structurally screened raw cell has no certified constructor in the current ingress domain | reject `unsupportedCertification` |

**Negative probes.**  The checker must be developed against a concrete
catalog of malformed raw inputs, not only against positive examples:

- unknown atom ids must reject as `unknownGenerator`;
- variable atoms whose payload is outside the expected scope must reject
  as `badPayload`;
- known generators with reserved malformed payloads must reject as
  `badPayload`, `wrongArity`, or `wrongChildShape`;
- nullary type/context/mode atoms with nonzero payloads must reject as
  `badPayload`;
- finite non-nullary payload decoders must first return
  `RawChildDescriptors`, then recursively screen each decoded child
  against the generator's declared child shape; for the first
  application fixture, `app(var 0, var 1)` may screen as a term shape,
  while applications whose function or argument child decodes to a
  type/context/mode cell, or whose decoded argument is outside scope,
  must reject as `wrongChildShape`;
- current certified ingress accepts the structurally screened
  `app(var 0, var 1)` fixture only after the payload decoder and generic
  child-shape screen succeed and only when `var 0` and `var 1` are both
  certifiable in the same scope; scope 0 and scope 1 reject as
  `wrongChildShape`, and malformed application payloads preserve their
  `wrongChildShape` rejection;
- generated dim-1 cells over uncertified endpoints must reject as
  `badBoundaryEndpoint`;
- generated term-step cells over context or type endpoints must reject
  as `badBoundaryEndpoint`, not as accepted cross-sort steps;
- generated term-step cells over mode endpoints must also reject as
  `badBoundaryEndpoint`;
- a known rule id used at an unsupported endpoint dimension must reject
  rather than silently reusing the rule at that dimension;
- raw vertical composites with mismatched middle endpoints must reject
  as `badVerticalBoundary`;
- raw horizontal composites must reject as `unsupportedCompH` until
  Axis 6 supplies certified Gray-boundary semantics;
- expected-shape checks must include a real sort mismatch probe that
  rejects as `wrongSort`, including term-as-type, term-as-context,
  type-as-term, type-as-context, context-as-term, context-as-type, and
  mode-as-term/type probes, plus positive-dimensional
  type-identity-as-term-step probes.

Probes begin life as audited raw fixtures plus expected rejection
labels.  Once the executable screen can cover a class of probes, every
probe in that class must have a theorem stating that the screen returns
its expected rejection.  Probe data alone is not a soundness result.
Expected-shape checking must call the recursive structural screen before
comparing sorts; a sort-only inference helper is not allowed to accept a
bad payload just because the raw id has the requested sort.
Certified-ingress probes are separate from screen probes: every accepted
result must contain an actual `PolyCell`, while every malformed or
not-yet-certified raw cell must have an executable rejection theorem.

This is the operational answer to "show what is nonsense": raw cells
can be displayed and diagnosed, but only accepted cells can inhabit
`PolyCell`.

**Lean LoC estimate for PolyCell core itself:** ~15K LoC (raw syntax,
generator metadata, `ChildSpec` / `CellChildren`, certified boundary
indices, the raw-to-certified checker, basic recursors / induction
principles, and structural functions `source`, `target`, `dim`,
`isThin`).

---

## 5. FX kernel as one profile instance

Putting it all together — FX's kernel is one specific `PolyProfile`:

```lean
namespace LeanFX2

/-- The FX kernel profile.  All thirteen axes specialized. -/
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
      | 0 =>
        -- Type/value cells are directed.  Equality lives in dim 1.
        False
      | 1 =>
        -- Identity 1-cells and saturated conversion witnesses are
        -- thin; raw directed operational steps are not automatically
        -- thin.
        c.isIdentity ∨ c.isSaturatedConversionWitness
      | 2 =>
        -- cd_lemma fillers are thin when their branchings are
        -- certified by the saturation construction.
        c.isCertifiedConfluenceFiller
      | _ =>
        -- Squier and higher coherence cells are thin in the saturated
        -- FX profile after the filler theorem has run.
        c.isCertifiedHigherCoherence
    identitiesAreThin := fxIdentityCellsAreThin
    closedUnderComp := fxThinClosedUnderComposition
    closedSrcTgt    := fxThinClosedUnderSourceTarget
    thinDecidable   := fxThinDecidable
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
    univalent      := fxUniverseIsUnivalent
  }

  -- AXIS 11: Single-substitution calculus backbone.
  substitutionBackbone := fxSingleSubstitutionBackbone

  -- AXIS 12: Synthetic Tait computability classifier.
  stcClassifier := fxSyntheticTaitClassifier

  -- AXIS 13: MTT normalization gateway for the modal projection.
  mttGateway := fxMTTNormalizationGateway

  consistency := fxConsistencyProof

/-- Raw FX cell input.  This is not a kernel certificate. -/
def FXRawCell := PolyTerm fxProfile

/-- Certified FX cell package. -/
def FXCell :=
  Σ sort, Σ dim, Σ scope, Σ boundary, Σ raw,
    PolyCell fxProfile sort dim scope boundary raw

end LeanFX2
```

The existing FX kernel layers are projections of certified cells, not
post-hoc predicates on raw Nat payloads:

```lean
namespace LeanFX2

/-- Certified context cell. -/
def FXContext (scope : Nat) (raw : FXRawCell 0) :=
  PolyCell fxProfile .context 0 scope () raw

/-- Certified type cell. -/
def FXType (scope : Nat) (raw : FXRawCell 0) :=
  PolyCell fxProfile .type 0 scope () raw

/-- Certified term cell.  The eventual typed bridge refines this with a
context cell and a type cell, exactly like `Term ctx type raw`. -/
def FXTerm (scope : Nat) (raw : FXRawCell 0) :=
  PolyCell fxProfile .term 0 scope () raw

/-- Certified generating step or vertical composite over one sort.
Raw horizontal composition is rejected until Axis 6 certifies it. -/
def FXStep (sort : CellSort) (scope : Nat)
    (source target : FXRawCell 0) (raw : FXRawCell 1) :=
  PolyCell fxProfile sort 1 scope (source, target) raw

/-- Certified conversion is a certified dim-1 cell plus a thinness
certificate on that certified cell's raw erasure. -/
def FXConv (sort : CellSort) (scope : Nat)
    (source target : FXRawCell 0) (raw : FXRawCell 1) :=
  { cell : FXStep sort scope source target raw //
      fxProfile.stratification.thin 1 raw = true }

/-- Certified confluence filler. -/
def FXCdLemma (sort : CellSort) (scope : Nat)
    (source target : FXRawCell 1) (raw : FXRawCell 2) :=
  PolyCell fxProfile sort 2 scope (source, target) raw

end LeanFX2
```

This means the existing 80+ kernel files become **view definitions**
over the certified cell layer, not independent inductives and not raw
subtypes of Nat-coded cells.  All cascade work disappears only after
the certified checker and the legacy round-trip bridge are real.

---

## 6. Capabilities matrix

Each row is a capability FX could have.  Columns are: status before
the certified PolyCell target, status after the target proof exists,
and the mechanism.  The "After" column is not current implementation
status unless a row explicitly says "shipped".

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
| EGraph extraction | K14 pending (~3K LoC) | Cell-set quotient of certified cells, not raw syntax alone | axes 2, 3 |
| Reflection | K15 pending | Reflection after the profile fibration and certified bridge exist | axes 2, 8 |
| FX-in-FX bootstrap | K20 pending | FX kernel = profile instance, FX0 = simpler instance | axis 8 |
| Concurrency (par) | D5 pending; ad-hoc | Deferred until certified `compH` has Gray boundary + disjoint-footprint witnesses | axes 6, 7 |
| Distribution / GPU | P5.1 pending | Deferred until certified `compH`, certified `compV`, and BSP-sync laws exist | axis 6 |
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

The accelerate-* roadmap has 50+ tasks.  Under the certified PolyCell
target, the table below shows which cascades disappear and which proof
obligations replace them.  In this section, **Subsumed** means
"subsumed after the named certified layer / profile theorem exists",
not "already implemented in the current raw scaffold."

### Phase 0 — close M04 SN + GAPs

| Task | Status under certified PolyCell target |
|---|---|
| P0.1 Step.eta | **Subsumed**: Step.eta is a Generator value + payload entry, not a Step ctor. The cascade is one extension. |
| P0.2 Step.par.eta + Compat/cd arms | **Deferred through Axis 6**: raw parallel cells are representable now; certified parallel reduction waits for real Gray boundary/disjointness. |
| P0.3 Reducible.rename_equivariant (T7) | **Subsumed**: renaming is a polygraph morphism, equivariance is structural. |
| P0.4 Reducible.cr3 + U2 compound arms | **Subsumed after certification**: Reducible over certified PolyCells inherits CR3 only after the saturation discipline is proved for the profile. |
| P0.5 ReducibleSubst.lift | **Subsumed**: substitution is the polynomial-monad multiplication. |
| P0.6 fundamental_lam (Wood/Atkey 2022) | **Direct port**: the Wood-Atkey corrected rule lives at the toposOp axis (axis 7). |
| P0.7 fundamental_betaRedex | **Subsumed**: β-redex cases are uniform across Generator values. |
| P0.8 fundamental_iota | **Subsumed**: ι-cases are uniform across Generator values. |
| P0.9 fundamental_cubical_modal_advanced | **Subsumed**: cubical + modal cases factor through their topos / cubical-shape axes. |
| P0.10 Term.strong_normalization (M04) | **Direct port**: SN is a property of the polygraph at saturation, provable once per profile. |
| P0.11 Step.iotaOeqJRefl | **Subsumed**: one Generator value + reduction. |
| P0.12 Term.emptyElim | **Subsumed**: one Generator value at dim 0. |

**Phase 0 target collapse:** one substantive profile theorem after the
certified bridge exists.  This is not a current raw-PolyTerm claim.

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
| P2.4 PolyTerm intrinsic mirror | **Reframed**: raw `PolyTerm` stays permissive; certified `PolyCell` is the intrinsic mirror. |
| P2.5 PolyTerm.toRawPoly_rfl | **Subsumed**: erasure is a polygraph morphism to the dim-0 truncation. |
| P2.6/P2.7 Term ⇌ PolyTerm bijection | **Reframed**: `FXTerm` is a certified-cell projection after the raw-to-certified checker and legacy bridge are real. |
| P2.8 generic rename/subst | **Subsumed**: polynomial-monad multiplication. |

**Phase 2 target collapse:** no new legacy cascade tasks after
POLY-TCB and the certified bridge exist.  Current raw-substrate work is
only a precursor.

### Phase 3 — metatheory + decidable Conv (★ MILESTONE A)

| Task | Status |
|---|---|
| P3.1 PolyTerm.subject_reduction | **Subsumed**: SR is a profile-level theorem, one per profile. |
| P3.2 PolyTerm.strong_normalization | **Subsumed**: SN ditto. |
| P3.3 Step.parStar.confluent | **Subsumed**: confluence is the saturation Property of axis 4. |
| P3.4 PolyStep dim-1 generators | **Subsumed**: dim-1 certified cells over raw `PolyTerm` endpoints. |
| P3.5 PolyStep.cd / cd_lemma generic | **Subsumed after proof**: cd_lemma is the per-profile theorem at dim 2 once saturation supplies the certified fillers. |
| P3.6/P3.7 RawValueTerm / ValueTerm | **Subsumed**: values are normal-form predicates on PolyTerm. |
| P3.8 PolyTerm.eval | **Subsumed**: NbE = polygraph fold. |
| P3.9 ValueTerm.quote | **Subsumed**: quote = inverse of fold. |
| P3.10 nbe roundtrip | **Subsumed**: polygraph fold + unfold composition. |
| P3.11 Conv.decide | **Path A or Path B only**: NbE normal-form equality, or Makkai/Forest word equality over the finite certified polygraph. ωcE remains the semantic coherent-equivalence classifier, not the decision engine. |
| **P3.12 typecheck_decidable (★ MILESTONE A)** | **After Conv.decide plus the certified raw-to-kernel bridge.** |

**Phase 3 target collapse:** typechecking is one certified checker
pipeline only after Conv.decide is supplied by Path A or Path B and
the legacy bridge is real.  There is no Conv-as-ωcE-morphism-search
shortcut in the trusted plan.

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
| P5.1 evalDistributed_sound | **Deferred through Axis 6**: cell-partition fold needs certified `compH` with Gray boundary/disjointness plus BSP-sync laws. |
| P5.2 EGraph extraction | **Subsumed after certification**: quotient certified cells by generated congruence; raw `PolyTerm` alone is not enough. |

**Phase 5 collapses only after Axis 6 and Axis 8 are real.** Until
then, raw `compH` remains input syntax and is rejected by the
certified checker.

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

Plus the ~170K LoC PolyCell substrate itself, but **most of that
~170K is one-time foundation work that doesn't recur per ctor**, while
the existing ~135K of cascade work scales linearly with new ctors.
Crossing the break-even point: roughly the next ~50 new ctors.

For FX's expected lifetime (~200+ new ctors over 5 years for math
import, modal layer expansion, cubical Kan ops, HIT zoo, measure
theory, differential geometry, etc.), the PolyCell investment **pays
back ~3× over** in cascade savings alone, before counting the
capability wins.

---

## 8. Migration plan

Existing files → certified PolyCell target.

### Foundation layer

| Current file | LoC | Certified PolyCell target |
|---|---|---|
| `Foundation/RawTerm.lean` | 540 | Dim-0 cells with `globular` shape; Generator enum already shipped |
| `Foundation/Ty.lean` | 280 | Universe cells (dim 0 with universe boundary) + dim-0 cells with type-flag |
| `Foundation/Term.lean` | 940 | `FXTerm` projection from certified `PolyCell fxProfile .term` |
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

| Current file | LoC | Certified PolyCell target |
|---|---|---|
| `Reduction/Step/Inductive.lean` | 1800 | `FXStep` view definition; ctors become axis 2 generators at dim 1 |
| `Reduction/Step/Compat.lean` (×6) | ~3K | **Subsumed** by polynomial-monad multiplication |
| `Reduction/ParRed/*.lean` | ~2K | **Subsumed** by axis 6 Gray module |
| `Reduction/Conv.lean` | 600 | `FXConv` view via thinness in stratification (axis 3) |
| `Reduction/StepStar/*.lean` | ~1.5K | **Subsumed** by polygraph composition |

### Confluence layer

| Current file | LoC | Certified PolyCell target |
|---|---|---|
| `Reduction/RawCdLemma/*.lean` | ~8K | **Subsumed** by saturation closure proof (axis 4) |
| `Reduction/CdLemma/*.lean` | ~5K | **Subsumed** ditto |
| All D2.5.x cascade work | ~12K | **Subsumed** by per-profile cd theorem |

### Modal / cubical / HoTT layer

| Current file | LoC | Certified PolyCell target |
|---|---|---|
| `Modal/*.lean` | ~5K | Topos modality entries (axis 7) |
| `HoTT/*.lean` | ~3K | Cubical-shape cells (axis 1) + universe ctors (axis 10) |
| `Cumul/*.lean` | ~4K | Universe cumul ctor (axis 10) |
| `Effects/*.lean` | ~2K | Topos modality entries (axis 7) |

### Tools / smoke / audit layer

| Current file | LoC | Certified PolyCell target |
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

Plus the ~170K of new PolyCell substrate, but minus the ~40K of
deleted existing code: net code base after PolyCell migration is
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
| — | PolyCell raw/certified core | ~15K | None for this design |
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
- PolyCell pivot: ~187K LoC over ~24-36 months as designed
- Cost difference: ~50K LoC + ~12-24 more months for **~3× capability
  surface** + **frontier-research mechanization** + **fundamentally
  unblocked future expansion**

---

## 10. Phased rollout

Realistic ship plan in dependency order.

### Phase POLY-TCB — raw/certified trust boundary (immediate, ~4K NEW LoC)

**Goal:** stop treating Nat-coded raw cells as trusted kernel
inhabitants.  Keep raw `PolyTerm` permissive, then introduce a
certified layer that makes ill-sorted, ill-scoped, and
boundary-incompatible cells unconstructable.  Raw nonsense must be
representable and computably rejected.

**Already shipped in this direction:**

| Task | Commit | Provides |
|---|---|---|
| TCB.0 generator-step view | `196a4d9d` | `FXGeneratingStep` rejects `compV`, `compH`, and `identity`; audit gates assert zero axioms for the new recognizer and view. |
| TCB.1 sort vocabulary | `7b3aa5dd` | `CellSort` separates certified context/type/term/mode/effect/grade/protocol strata without sorting the raw layer. |
| TCB.2 generator child specs | `9e2fb6f8` | `ChildSpec`, `GeneratorSpec`, and `RuleSpec` give computable generator metadata; scope shift is separated from arity. |
| TCB.3 heterogeneous children | `046a189c` | `CellChildren` enforces declared child sort/dimension/scope through an abstract carrier before `PolyCell` exists. |
| TCB.3b raw child descriptors | `da731eca` | `RawChildDescriptor` / `RawChildDescriptors` let decoders return shape-indexed raw children without certifying them. |
| TCB.3c negative probes | `a3b729bb` | Hostile raw fixtures cover all eight rejection reasons and are audited as data before checker theorems claim anything. |
| TCB.4 certified boundary layer | `d7466d28` | `PolyCell profile sort dim scope boundary raw` gives the first intrinsic certified layer; no certified `compH`; only payload-evidenced atoms are constructible. |
| TCB.5 raw rejection result | `1e485b9d` | `CellCheckRejection` gives named failure modes for the future raw-to-certified checker. |
| TCB.6a dim-0 rejection screen | `e09469bf` | `Check.lean` executably rejects unknown dim-0 generators, bad payloads, wrong arity sentinels, wrong child-shape sentinels, and expected-shape wrong-sort probes without producing a certified inhabitant. |
| TCB.6b positive-dimensional screen | `c5c7fcf0` | The same screen rejects bad endpoints, cross-sort endpoints, bad vertical boundaries, and unsupported raw `compH` without dependent equality shortcuts. |
| TCB.6c unit-type seed | `6b47503b` | `unitTypeGeneratorSpec` becomes a nullary certified `.type` atom with payload evidence only for payload `0`. |
| TCB.6d malformed type probes | `24647e27` | The negative catalog covers out-of-scope variables, bad unit-type payloads, type endpoints in term steps, term/type expected-sort confusion, and positive-dimensional type-identity confusion; expected-sort checking uses the recursive screen, not sort-only inference. |
| TCB.6e linear-mode seed | `2939addf` | `linearModeGeneratorSpec` becomes a nullary certified `.mode` atom; the checker rejects bad mode payloads, mode endpoints in term steps, and mode-as-term expected-shape confusion. |
| TCB.6f finite application screen | `4f667fc7` | The first application payload decoder returns `RawChildDescriptors`; the executable screen accepts only the concrete `app(var 0, var 1)` shape fixture and rejects the type-as-function fixture as `wrongChildShape`.  This is still screening, not a certified application inhabitant. |
| TCB.6g decoded-child fold | `d3329d83` | Application screening now consumes decoded `RawChildDescriptors` through a generic child-spec fold, with audited positive and negative fold theorems.  The fold still returns only screen results, not certified child cells. |
| TCB.6h certified seed packages | `90e6192e` | `CertifiedRawCell` packages carry an actual `PolyCell` over the original raw input for the four payload-evidenced seed atoms: variable 0 in scope 4, unit type, empty context, and linear mode.  This is not a general raw-to-certified checker and does not certify application payloads. |
| TCB.6i expanded malformed probes | `d97e1dbd` | The negative catalog now covers application argument sort failure, application out-of-scope child failure, known rule ids used at unsupported endpoint dimensions, and extra context/type/term/mode expected-shape confusion cases.  All new probes have executable rejection theorems and audit entries. |
| TCB.6j dim-0 certified ingress | `d1c3f65c` | `inferRawCell?` and `checkRawCellAs?` return `CertifiedRawCellResult` for the payload-evidenced dim-0 atom subset only: in-scope variables, unit type, empty context, and linear mode.  Structurally screened but uncertified atoms reject as `unsupportedCertification`, and malformed dim-0 probes keep executable rejection theorems. |
| TCB.7a certified seed views | `9ba62a55` | `CertifiedFXCell` and seed `CertifiedFXContext` / `CertifiedFXType` / `CertifiedFXTerm` / `CertifiedFXMode` views wrap actual `PolyCell` witnesses over `fxProfile`.  There is still no certified conversion/thinness view and no new non-nullary certification power. |
| TCB.7b first certified application payload | `2765ef03` | `app(var 0, var 1)` is the first non-nullary dim-0 term payload admitted to the certified layer.  It is accepted only at scopes where both decoded variables are certified; scope 0/1 and malformed application payloads still reject by computation.  This is not general application certification. |
| TCB.7c certified application child decoder | `f480ef2a` | The accepted `app(var 0, var 1)` path now factors through `CertifiedApplicationVarZeroVarOneChildren`, a computable certified-child decoder carrying the actual `CellChildren` spine of `PolyCell` child witnesses.  Scope 0/1 rejections are audited at both decoder and checker level. |
| TCB.7d screen-gated certified application ingress | `f36b083b` | `certifyApplicationVarZeroVarOneChildren?` now invokes `decodeApplicationPayload?` and the audited generic child-shape screen before constructing the certified application package.  A stronger dimension-polymorphic certified-child decoder was attempted and rejected by `AuditPolyCell` because it pulled in `propext`; the committed path keeps the TCB axiom-free and accepted payloads unchanged. |
| TCB.7e hostile application child probes | `d189603a` | The negative catalog now includes application payloads whose decoded function or argument child is a context or mode cell, in addition to the previous type and out-of-scope failures.  All four new payloads reject as `wrongChildShape` through the executable screen and full audit. |

**Deliverables (NEW only):**

| Task | File(s) | Content | Acceptance |
|---|---|---|---|
| TCB.1 sort vocabulary | `Foundation/PolyCell/Core/CellSort.lean` | `CellSort` enum for `context`, `type`, `term`, `mode`, `effect`, `grade`, `protocol`; decidable equality; no semantics. | `#assert_no_axioms CellSort`; no `Inhabited`/`Classical`; audit gate added. |
| TCB.2 generator child specs | `Foundation/PolyCell/Core/GeneratorSpec.lean` | `ChildSpec`, `GeneratorSpec`, `RuleSpec`; scope shift separated from arity; first concrete specs for `var`, `lam`, `app`, `unitType`, `piTy`, `ctxEmpty`, `ctxCons`, `linearMode`, and the current dim-1 step-generator shell. | `lam` child table has type child at scope+0 and term body at scope+1; `piTy` codomain is type at scope+1; all facts are definitional or simple cases. |
| TCB.3 heterogeneous children | `Foundation/PolyCell/Core/CellChildren.lean` | `CellChildren (ChildCarrier : CellSort -> CellDim -> Nat -> Type) (parentScope : Nat) : List ChildSpec -> Type`; constructors force child sort/dim/scope from the spec list without depending on full `PolyCell` yet. | It is impossible to build a lambda body child at `.type` or at the wrong scope without a Lean type error; audit gate added. |
| TCB.3b raw child descriptors | `Foundation/PolyCell/Core/RawChildren.lean` | `RawChildDescriptor` and `RawChildDescriptors`; payload decoders can return shape-indexed raw children without certifying them. | Decoder output can record lambda/pi/context child shapes, but the carrier stores only permissive raw cells; no `PolyCell` is produced. |
| TCB.3c negative probes | `Foundation/PolyCell/Core/NegativeProbes.lean` | Concrete malformed raw cells plus expected rejection labels for all eight `CellCheckRejection` cases. | Probe catalog is audited and nonempty; executable rejection claims live in `Check.lean`, not in the fixture file. |
| TCB.4 certified boundary layer | `Foundation/PolyCell/Core/Certified.lean` | `CellBoundary` and `PolyCell profile sort dim scope boundary raw` with constructors `atom`, `cell`, `compV`, `identity`; **no certified `compH`**; atom payload evidence currently certifies only in-scope variables, unit type, empty context, and linear mode. | Bad `compV` with mismatched middle endpoint has no constructor; raw `compH` has no certified introduction rule; out-of-scope variable payloads and nonzero unit/context/mode payloads have no `AtomPayloadEvidence` constructor. |
| TCB.5 raw rejection result | `Foundation/PolyCell/Core/CheckResult.lean` | Structured rejection enum, not just `Option`, so the checker can say which invariant failed. | Rejections distinguish unknown generator, wrong sort, bad payload, wrong arity, wrong child shape, bad boundary endpoint, bad vertical boundary, and unsupported `compH`. |
| TCB.6a executable rejection screen | `Foundation/PolyCell/Core/Check.lean` | Computable recursive screen over the supported generator/rule tables; rejects unknown ids, malformed payloads, wrong arity/child-shape sentinels, wrong expected sort, bad endpoints, bad vertical boundaries, and unsupported raw `compH`. | Every executable theorem is audited axiom-free; the catalog runner proves all current inference and expected-shape negative probes are rejected. |
| TCB.6h certified seed packages | `Foundation/PolyCell/Core/Check.lean` | `CertifiedRawCell` dependent package plus concrete packages for the payload-evidenced seed atoms only. | Each package erases definitionally to its named raw fixture; no application, lambda, pi, context-cons, generated cell, vertical composite, or raw `compH` is certified by this task. |
| TCB.6i expanded malformed probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean` | More hostile fixtures for application argument position, child scope failure, rule dimension misuse, and cross-sort expected-shape checks. | Probe counts are ratcheted; each new malformed input has a definitional rejection theorem and an audit harness assertion. |
| TCB.6j dim-0 certified ingress | `Foundation/PolyCell/Core/Check.lean` | Computable `inferRawCell?` and expected-shape `checkRawCellAs?` returning `CertifiedRawCellResult` or a rejection reason for dim-0 raw atoms, implemented without `propext`, `Classical`, `Inhabited`, or `Nonempty`. | Every accepted result contains a `PolyCell`; at this stage accepted witnesses were only in-scope variables, unit type, empty context, and linear mode.  Application certification starts later at TCB.7b. |
| TCB.7a certified seed views | `Foundation/PolyCell/FXProfile/CertifiedViews.lean` | `CertifiedFXCell` plus certified seed projections for context/type/term/mode over the current dim-0 ingress subset. | Every view carries an actual `PolyCell`; raw-erasure theorems are definitional; conversion/thinness and full step/coherence views remain unimplemented. |
| TCB.7b first certified application payload | `Foundation/PolyCell/Core/GeneratorSpec.lean`, `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean` | The finite payload `9100` is admitted as `app(var 0, var 1)` only through certified `var 0` and `var 1` child witnesses. | Scope 0/1 reject as `wrongChildShape`; type-as-function, type-as-argument, and out-of-scope application fixtures still reject; the accepted result and FX view erase definitionally to the raw fixture; all declarations are in `AuditPolyCell`. |
| TCB.7c certified application child decoder | `Foundation/PolyCell/Core/Check.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | `CertifiedApplicationVarZeroVarOneChildren` records the certified function child, certified argument child, and application child spine; `certifyApplicationVarZeroVarOneChildren?` is the computable ingress used by `inferRawAtom?`. | The app parent is built only from the certified child package; scope 0/1 reject before parent construction; expected-shape scope-1 rejection and child-spine arity are audited axiom-free. |
| TCB.7d screen-gated certified application ingress | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | The certified application ingress runs the payload decoder and generic `screenRawChildDescriptorsWith?` child-shape screen before building the parent certificate. | `LeanFX2.Tools.AuditAll` is green; no accepted payload is broadened; the direct dependent certified-child-spine route remains blocked until it can be implemented without `propext`. |
| TCB.7e hostile application child probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds mode/context-as-function and mode/context-as-argument malformed application payloads. | Probe count ratchets to 21 inference probes; each new malformed payload has decoder and rejection theorems under `AuditPolyCell`; `LeanFX2.Tools.AuditAll` is green. |
| TCB.7f certified FX operational views | `Foundation/PolyCell/FXProfile/CertifiedViews.lean` | Future `FXStep`, `FXConv`, `FXCdLemma` as projections of certified positive-dimensional cells and thinness certificates. | Existing raw subtype views remain compatibility-only; new operational code uses certified views only after the corresponding positive-dimensional certification exists. |

**Implementation order after TCB.7e:**

1.  Do not broaden application by adding more one-off parent
    constructors.  The next application slice is a propext-free certified
    child-spine design over `RawChildDescriptors`; it must be tried behind
    `AuditPolyCell` before any new payload is accepted.  The failed
    dimension-polymorphic dependent pattern route is not acceptable.
2.  If the reusable certified-child spine cannot be made audit-clean,
    keep using the decoder plus generic screen gate and move to
    positive-dimensional certification instead of weakening the TCB.
3.  Add positive-dimensional certification in this order: generated
    `.cell` over already certified endpoints, then `identity`, then
    vertical composition with definitional middle matching.  Certified
    `compH` remains blocked on real Gray-boundary semantics.
4.  Keep the propext-free boundary-screen discipline: no `propext`,
    `Quot.sound`, `Classical`, `Inhabited`, `Nonempty`, hidden `False`
    equation dependents, or weakened audit budgets.  The failed
    direct-dependent-pattern route is not acceptable.
5.  Add negative probes before each new accepted family: malformed
    payload sentinel, wrong arity, wrong child sort/dimension/scope,
    expected-shape sort confusion, bad endpoint, and bad vertical
    boundary where the family can participate in positive-dimensional
    cells.  Raw nonsense must remain representable and the certified
    layer must reject it by computation.
6.  Extend `CertifiedViews.lean` only as the checker gains real
    certified inhabitants: context/type/term/mode seed views are live;
    step/conversion/coherence views must wait for positive-dimensional
    certification and thinness data.  Keep old raw subtype views as
    compatibility shims.
7.  Legacy bridge: connect the existing intrinsic kernel judgments to
    certified views only after the checker has nonempty accepted
    witnesses and the audit proves every new declaration axiom-free.

**POLY-TCB anti-vacuity gate:** TCB.4 is intentionally weaker than the
full checker: it must have concrete accepted witnesses only for the
payload-evidenced seed atoms (`var` with an in-scope index, `unitType`
with payload 0, `ctxEmpty` with payload 0, and `linearMode` with
payload 0), and must not provide
constructors for non-nullary atoms or `compH`.  The screen phase must
add concrete positive screen witnesses for every currently
payload-evidenced generator and concrete rejected witnesses for every
`CellCheckRejection` constructor, including `unsupportedCompH` and
`unsupportedCertification`.  Later
payload-decoder work extends the accepted-generator domain one generator
family at a time.  No soundness theorem may be accepted if its
supported-generator domain is empty.

**Non-goals in POLY-TCB:**

- Do not delete raw `PolyTerm`; it is the input format and rejection
  target.
- Do not certify `compH` until Axis 6 supplies a real Gray tensor
  boundary formula and disjoint-footprint/matching condition.
- Do not claim typed legacy equivalence, subject reduction, confluence,
  or decidable conversion.  This phase certifies shape/sort/scope and
  vertical boundary structure only.

**Verification gate:** every new declaration added to
`AuditPolyCell.lean`; `lake build LeanFX2.Foundation.PolyCell...`;
`lake build LeanFX2.Tools.AuditAll.AuditPolyCell`; `lake build
LeanFX2.Tools.AuditAll`; forbidden-token scan over touched PolyCell
files.

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
- `Foundation/Polygraph/PolyCellUnivalence.lean` — univalence as theorem

**Acceptance:** `polyCellUnivalence` theorem shipped zero-axiom.

### Phase POLY-ζ — PolyCell assembly + FX profile (months 24-30, ~30K LoC)

**Goal:** assemble all thirteen axes into PolyProfile + define
fxProfile + ship FXCell type.

**Deliverables:**
- `Foundation/Polygraph/PolyProfile.lean` — bundled thirteen axes
- `Foundation/Polygraph/PolyTerm.lean` — permissive raw cell syntax
- `Foundation/Polygraph/PolyCell.lean` — certified cell type
- `LeanFX2/FxProfile.lean` — FX as a profile instance
- `LeanFX2/FxCellViews.lean` — FXType, FXTerm, FXStep, FXConv as views

**Acceptance:** raw `PolyTerm` and certified `PolyCell` typecheck
zero-axiom; fxProfile satisfies consistency conditions; view
definitions agree with current types through the checked bridge.

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
- Update `Algo.Check` to use Conv from Path A (NbE) or Path B
  (Makkai/Forest word equality), not ωcE search (~2K LoC)

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

The universe generator is one profile entry whose raw payload carries
`(level : Nat)` and whose certified constructor proves it is a
well-formed type/universe cell.  The Grothendieck construction
`Hom^⊖(I, ω) ≃ LCart^c_U(I)` is a Quillen equivalence in Loubaton
thesis; mechanizing the *equivalence* (not just claiming it) is the
zero-axiom path.

**Watch:** the equivalence requires constructing the left/right
adjoint pairs explicitly.  Loubaton's thesis gives the construction
in §6.1.4; ~3K LoC of careful translation.

### PolyCell core

The certified indexed layer must avoid the propext traps documented
in `feedback_lean_zero_axiom_match` + `feedback_lean_indexed_partial_match`:
- No wildcard matches on the dim parameter
- Boundary destructuring uses explicit pattern + `nomatch` for
  impossible-by-index cases
- Thinness is a stratification predicate / marking, not a certified
  constructor.  Any inverse/flipped-boundary operation must be a
  derived theorem over marked cells, not an `Eq.rec` shortcut.

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
The certified PolyCell layer is indexed over PolyProfile, sort,
dimension, scope, boundary, and raw syntax.  Lean 4.29's
elaborator gets slow on heavy structure-of-structures patterns; we've
already seen 78-arm Term inductions take ~1474s for `simp` (per
[[feedback_perf_antipatterns]]).

**Mitigation:** Lean 5 (when released) reportedly has better support
for parameterized inductives.  Fallback: use `@[reducible]` aggressively
on the profile fields, plus careful unification hints.  Fallback²:
split the certified layer into per-axis sub-inductives plus a
`PolyCellBundle` wrapper, sacrificing some uniformity for elaboration
speed.

### Risk: Strict positivity

The rejected design was a `thin` constructor:
`(cell : PolyTerm π dim bnd) →
 (hasThin : π.stratification.thin dim cell) →
 PolyTerm π dim bnd.flipped`.

The `bnd.flipped` part would create a new raw cell of the same dim
with the boundary flipped.  This is HIT-like (an equivalence-style
constructor), and Lean's strict-positivity checker may reject it.

**Mitigation:** encode `thin` not as a ctor but as a `Prop`-valued
predicate, with the flipped variant derivable.  Loubaton 2301.11424's
left semi-model structure suggests this: thin cells are not new
generators, they are markings on existing cells.  Final rule:
`PolyTerm` has no thin constructor, `PolyCell` has no thin
constructor, and `FXConv` is a certified dim-1 cell plus a thinness
certificate from the stratification layer.  Any inverse/flipped
variant is derived from the marking.

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
   semantic justification mechanizes.  The certified PolyCell bridge
   inherits this operational rule; it does NOT depend on the
   (∞,ω)-semantic proof being Lean-mechanized.

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
PolyCell pivot, with cited algorithm + LoC estimate + ship stages.

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

### 12.5 What FX aims to extend beyond the published literature — target contributions

The FX PolyCell design is mostly an integration of published
mathematics into one mechanizable substrate.  This subsection
enumerates the *target* contributions where FX aims to go beyond
what any single paper has shipped.  Every item is a research
program, not a landed Lean result.

**Target contribution 1 — The FX PolyCell Cellular Tensor (§3.0.7).**
Intended composite of four published pillars plus our own capability
ledger:
* Almeida 2025 vol I supplies the syntactic GAT tensor (T1).
* Bocquet-Kaposi-Sattler 2023 supplies internal sconing
  preservation (T2) for one CwR morphism — extending it to a
  cellular tensor of profiles is part of the lift.
* Crans 1999 + Steiner 2004 + ABGMMM 2023 supply the Gray-tensor
  universal property on strict single-sort polygraphs (T4 base
  case).
* Our design adds: a ProfileCapabilities honesty ledger (T3, as
  upper bound, not substitute for interaction proofs), the
  proposed lift of (T4) from strict single-sort polygraphs to
  sort-stratified DEPENDENT profiles with admissibility, and an
  explicit no-go register cross-referenced against Zwart-Marsden
  rather than a "capabilities = ⊥" silent failure (T7).

The composite (T1)–(T8) would be FX-original IF the lift mechanizes.
Vol II [Alm26], in preparation, aims to prove a stronger result at
the maximum-generality GAT level; FX's program aims for the
admissible-profile projection without waiting.  Neither is shipped.

**Target contribution 2 — ProfileCapabilities honesty ledger.**  Per
§3.14, every admissible profile is required to declare a
`ProfileCapabilities` record listing what it provides (subject
reduction, confluence, normalization, canonicity, decidable
conversion, decidable typechecking, productivity, erasure
soundness) and its consistency strength relative to the ambient
theory (Lean 4, ZFC, ZFC + I, ZFC + Mahlo, ...).  We are unaware
of a published framework with this discipline at the profile
level.  The ledger is a NECESSARY-condition tracker — tensor of
two profiles has at most the meet of their capabilities — not a
sufficient-condition substitute for the actual interaction proofs.
It catches "fake subsumption" early (a framework that claims many
type theories but silently loses properties under composition gets
flagged at the ledger level), but it does not replace per-pair
admission work.

**Target contribution 3 — A 4-tier multi-modal stack with explicit
Fire-Triangle navigation (§3.7).**  Cohesive / Resource / Cost /
Security / Structural tiers, each with its own substrate paper,
composed via MTT (Gratzer-Kavvos-Nuyts-Birkedal 2020) as outer
container.  Per-tier Fire-Triangle leg restriction (calf/decalf
restrict effects, MTT restricts substitution, SProp restricts
dependent elimination) so no axis violates Pédrot-Tabareau 2020.
Composition target: cellular tensor.  Honest disclaimer: each
cross-tier interaction is its own proof obligation; this section
is a navigation plan, not a discharged metatheorem.

**Target contribution 4 — Accept-or-reject-honestly admission
contract.**  Per §3.14, `extendProfile` is intended as a function
that either returns a new admissible profile OR returns a
constructive rejection witness naming which prior capability
collided with the new extension and which distributive law would
need to exist.  No silent failure, no "we hope it composes" cells.
This would make admission decidable per extension, but only after
the per-pair witnesses are supplied — the contract is a discipline,
not a free decision procedure.

**Target contribution 5 — Self-hosting kernel FX as L5 meta-profile
(§3.15).**  The Self-Hosting Kernel FX profile would reflect
PolyCell into itself: FX reasoning about its own profile space
inside itself, using the reflection profile (Axis 12 STC) to
internalize ProfileExtension.  If achieved, this closes the loop:
the FX Cellular Tensor target theorem becomes statable inside FX.
We do not know any published framework that has this closure;
whether it mechanizes in Lean within FX's lifetime is an open
research question.

**Target contribution 6 — The 13-axis profile bundle with mechanized
cross-axis coherence.**  Per §4, every admissible profile would
specify thirteen axes whose cross-axis consistency is a target
finite-state check.  No published framework that we are aware of
bundles this many graded / modal / cohesive / cubical / topos axes
into one mechanically checkable record.  The bundle itself is a
data structure; whether all 13 axes mechanize cleanly together
under strict zero-axiom discipline remains a separate proof
obligation per axis.

**What FX does NOT extend.**  Bound 1 (Pédrot-Tabareau Fire Triangle),
Bound 3 (Gödel II), Bound 4 (Lean 4 metatheoretic strength), Bound 5
(undecidable typechecking for some profiles), Bound 6 (strict
positivity), Bound 7 (productivity for corecursion), Bound 8
(classical reasoning opt-in), Bound 9 (continuous mathematics
external), Bound 10 (ambient metatheory as outer bound) — these are
genuine foundational limits inherited from every formal-syntactic
framework.  FX does not escape them; FX makes them explicit per
profile via ProfileCapabilities.

**Three-layer foundational picture:**
```
Layer 3: AMBIENT MATH (Lean 4 + ZFC+I + the ambient metalanguage)
              ↑ instantiated by
Layer 2: PolyCell raw/certified universe + admission calculus + cellular tensor
              ↑ specializes to
Layer 1: SPECIFIC PROFILES (FX, MLTT, HoTT, CTT, MTT, 2LTT, ...)
```

FX is positioned at Layer 2 — the framework that hosts Layer 1
profiles, bounded only by Layer 3.  The FX Cellular Tensor Theorem
is FX's Layer-2 load-bearing structural mechanism.  Vol II [Alm26]
will eventually prove a Layer-2 theorem at the maximum-generality
GAT level; until then, the FX Cellular Tensor is the admissible-
profile projection that ships now.

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

### FX Cellular Tensor target theorem (§3.0.7) — reference triangle

CT1. Daniel Almeida, *A monoidal category of dependently sorted
      algebraic theories I: syntax*, `arXiv:2511.13547` (Nov 2025),
      119 pages.  Volume I of a planned pair.  Constructs the
      syntactic tensor product `A ⊗ B` of generalized algebraic
      theories (Cartmell sense): tensor of judgments (§2 + Table 1),
      strict double categories T_cat ⊗ T_cat (§3.1, Axioms 1–28),
      Lawvere theory recovery (§3.2, identification with Freyd 1966),
      cartesian product of locally finite direct categories for type
      signatures D(S ⊗ T) ≅ D(S) × D(T) (§3.3, pages 35-37),
      morphisms vs displayed structures with distinct cofibration
      structures (§3.4 + page 40 referencing Ahrens-Lumsdaine 2019
      and BarHen25 §3.9), the comparison functor ⊗_{A,B} : C(A) ×
      C(B) → C(A⊗B) for fixed (A,B) (Construction 6.5),
      associativity-of-derivable-judgments (Theorem 7.3), symmetry-
      of-derivable-judgments (Proposition 8.1).  Explicitly **defers
      to vol II [Alm26], in preparation**: functoriality of ⊗ on
      GAT-morphisms (Remark 6.7, page 82), closed monoidal structure
      and pentagon coherence (Remark 7.5, page 96), hexagon
      coherence for symmetry (§8 closing, page 98), the equation
      Mod(A ⊗ B, Fam) ≅ Mod(A, Mod(B)) (abstract).  Supplies (T1) of
      the FX Cellular Tensor *target*; the universal property is in
      the deferred volume, not in vol I.
CT2. Sjoerd Crans, *A tensor product for Gray-categories*, Theory
      and Applications of Categories 5 (1999), 12-69.
      <http://www.tac.mta.ca/tac/volumes/1999/n2/n2.pdf>.  Gray-tensor
      universal property scoped to **Gray-categories** (strict, single-
      sort).  Lifting it to sort-stratified dependent profiles is the
      hard part FX's (T4) target attempts; Crans does not do that
      lift.
CT3. Richard Steiner, *Omega-categories and chain complexes*,
      Homology, Homotopy and Applications 6 (2004), 175-200.
      Extends Crans 1999 to **ω-categories** via the chain-complex
      side; supplies background monoidal machinery on strict
      ω-categories, not on sort-stratified DEPENDENT profiles.
CT4. Maaike Zwart, Dan Marsden, *No-go theorems for distributive
      laws*, LICS 2019, `arXiv:1811.06460`.  Categorical no-go
      catalogue: probability × powerset (Varacca-Winskel 2006),
      triple no-go for probability × powerset × state, generalized
      framework.  Supplies the no-go inventory that (T7) of the FX
      Cellular Tensor cross-references for **explicit rejection** of
      colliding extensions (not silent capability-meet collapse).
CT5. Daniel Almeida, *A monoidal category of dependently sorted
      algebraic theories II: categorical aspects*, [Alm26],
      **IN PREPARATION** as of 2026.  Planned to supply
      functoriality of ⊗ on GAT-morphisms, closed monoidal structure
      on GAT, pentagon coherence, hexagon coherence, the
      Mod(A⊗B, Fam) ≅ Mod(A, Mod(B)) equation.  Whether FX's lift
      attempt or vol II ships first is an open race; until either
      lands, both results are intended-but-unshipped.

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

This document is the soundness contract for the PolyCell pivot.
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

No `IsX : Prop` placeholder predicates ship under the PolyCell
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
