# PolyCell — Raw Input + Certified Universal Substrate for FX Kernel Cells

> **Status:** committed design contract — the maximal-power apex
> kernel FX targets.  Computability-hardened.
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
> **Costed:** ~270K gross zero-axiom Lean LoC for the FULL
> maximal-power apex kernel (~207K thirteen-axis + Tier-0 (∞,ω)
> substrate + ~63K Phase-Z typed/cubical/HIIRT/21-dim apex; ~230K net
> after the §7/§8 cascade-obsolescence + migration deletions), over
> 2–4 years.  **~25K is already in place** — the PolyCell substrate
> (RawTerm / RawCell / PolyCell + 194-`Generator` table + certifier +
> Allais fold) plus the reducibility + strengthening foundation.
> Delivered in full, this is simultaneously the FIRST
> mechanization of (∞,ω)-categories in any proof assistant AND the
> strongest sound type theory with decidable typechecking ever
> shipped.  See [§9](#9-loc-budget) for the canonical accounting and
> [§11.8](#118-the-maximal-power-computable-kernel) for the apex
> commitment.
>
> **Slogan:** *permissive raw cells, intrinsic certified cells.*  Raw
> input is the **scope-indexed, dimension-computed** `RawTerm` /
> `RawCell` layer (shipped, all V2 suffixes dropped per V2-mig.11–14)
> and may represent nonsense — including dim-mismatched composites —
> so the checker can reject it.  Certified `PolyCell π sort dim scope
> boundary raw` is the kernel layer and has constructors only for
> sorted, scoped, boundary-compatible cells, collapsed to one generic
> `gen` constructor over the 194-entry generator table (expanding to
> ~400–500 entries at MILESTONE D per §3.16).  FX kernel objects
> become projections of certified cells over one `PolyProfile π`; raw
> nonsense must map to `none` / `rejected reason`, never to a
> certificate.
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

* **Tier 1 — POLYCELL CORE** (~15K LoC, §4) — **SHIPPED**.
  A two-layer core: permissive raw `RawTerm` + `RawCell` (scope-
  indexed, dimension computed) for input data, plus intrinsic certified
  `PolyCell` indexed by sort, dimension, scope, boundary, and raw
  syntax, with one generic `gen` constructor over the 194-entry
  generator table.  All V2 suffixes dropped per V2-mig.11–14.  Each
  axis is one Tier-0 obligation witness attached to the profile, not
  a new raw constructor family.  See §3.16 for the apex generator
  inventory (~400–500 entries at MILESTONE D).

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

**Above all three tiers — the apex commitment.**  Tiers 0/1/2 give
the STRUCTURAL substrate (RMC + sconing + Fire Triangle / raw +
certified cell layer / 13 profile axes + extension calculus).  On
TOP of that substrate sits the **maximal-power computable kernel
target** (§11.8): the strongest currently-known sound type theory
that admits decidable typechecking — 2LTT 4-mode universes + the full
categorical structural-reflection-degree ladder (Mahlo → Πⁿ →
accessible-category → sequential ESR up to the `kunenI0` apex; NOT
set-theoretic embeddings) + K-free dependent
elimination with motive children + definitional eta + HIIRT + HITs +
QIITs + multi-clock guarded type theory + internal parametricity +
rewriting rules as first-class kernel feature + cubical pattern
matching + Equations + `dProp` internal computational reflection +
full CCHM cubical primitives + typed `HasType` + 21-dim integration
+ MTT + cohesion + differential cohesion + linear-nonlinear +
algebraic effects + synthetic-math layer.  Closed-system mandate:
**no user-level tactics** (only `calc` + type-directed elaboration),
**no external SMT** (verified internal deciders only, with Phase Z₉
holding a fully-verified internal SMT engine in reserve), **no LLM
in the kernel** (LLM-driven work lives outside via the agent
protocol).  See §11.8 for the full apex commitment and §11.8.7 for
the decidability + mechanized-complexity matrix.

The hard rules this design holds:

* No "rzk-prototyped" claims where rzk does not implement the system.
* No "21 cohesive focuses" where only 4 are cohesive.
* No groupoid-hypothesis-violating theorems applied to non-groupoid
  polygraphs.
* No Coverage Semantics for univalent FX (Eremondi-Kammar §7.2 says
  incompatible with univalent theories — substitute Cockx-Devriese-
  Piessens "Pattern matching without K", ICFP 2014, DOI
  10.1145/2628136.2628139).
* No `--type-in-type` even as a flag.  No external SMT even with a
  "trust" annotation.  No LLM-driven proof generation INSIDE the
  kernel even with "verification gates" (per §11.8.11 closed-system
  mandate).

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
    * 3.10 [Univalent universe — 2LTT 4-mode universes + Setzer-Rathjen flag hierarchy](#310-univalent-universe)
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
    * 11.5 [Computability + decidability discipline summary](#115-computability--decidability-discipline-summary)
    * 11.6 [Metatheory obligations on the v2 substrate](#116-metatheory-obligations-on-the-v2-substrate)
    * 11.7 [Foundational boundaries — Gödel, Turing, openness as design constraints](#117-foundational-boundaries--godel-turing-and-controlled-openness-as-polycell-design-constraints)
    * 11.8 [**The Maximal-Power Computable Kernel** — the apex commitment](#118-the-maximal-power-computable-kernel)
    * 11.9 [**The Internalization Program** — frontier & beyond-frontier extensions](#119-the-internalization-program--frontier-and-beyond-frontier-extensions)
12. [Risks + open research questions](#12-risks-and-open-questions)
13. [References](#13-references)

**Reader's path to the apex.**  For the strongest summary of what FX
is targeting, read §1 (manifesto) then jump to §11.8 (maximal-power
kernel), then §11.8.7 (decidability + complexity matrix) and §11.8.9
(nine-phase rollout).  §3 is the structural substrate; §11.8 is the
operational apex; §4 + §10 + §11 + §13 are the implementation
contract + phasing + discipline + provenance.

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

The v2 structural re-foundation is **SHIPPED** as of 2026-05-27.
`RawTerm scope` + `RawCell scope` (un-indexed by dimension, dimension
computed via `RawCell.dim`) are the canonical raw layer.  The
194-entry `Generator` enum + `binderShifts` + `payload` family +
`generatorChildSpecs` table is the Allais universe-of-syntaxes
descriptor over which the certifier, fold (`rename` + `subst` as
ONE generic instance each per V2-L2.4/L2.6), `cd_lemma`, and
`Conv` recurse uniformly.  The certified `PolyCell` collapses to
ONE generic `gen` constructor (V2-L1c.4 headline) plus the four
cell-layer constructors (`gen` / `generatingCell` /
`verticalComposite` / `identityCell`), with `horizontalComposite`
staged per §11.6.5 pending Gray-tensor admission.

All earlier K11.x / K12.x / K13.x cascade-tax framing has been
SUPERSEDED: the cascade is structurally dead at the substrate
level.  Adding a new feature is one Generator entry + admission
witness per §3.16, not a 78-arm pattern-match cascade across 13+
files.

This document specifies the **apex categorical-and-computable
substrate** for FX — the union of TWO co-maximal ambitions, neither
of which a proof assistant has ever shipped, and whose intersection
is FX's first-in-class delivery:

**(A) The full (∞,ω)-categorical universe internalized in a proof
assistant.**  Not (∞,1), not strict ω-cat, not weak ω-groupoid —
the FULL (∞,ω) categorical universe parameterized by **thirteen
profile axes** (SSC, STC, MTT-norm extend an earlier ten-axis core;
the Tier-0 universal meta-framework binds them all) plus a profile-
extension calculus (§3.14).  Hadzihasanovic regular directed
complexes (Axis 1) supply the shape catalogue; Awodey-Newstead
polynomial pseudomonads + Aberlé-Spivak polynomial universes (Axis
2) supply the algebraic theory; Verity stratification (Axis 3) +
Malbos-Massacrier-Struth cubical coherent confluence (Axis 4)
supply the marking + saturation discipline; Loubaton 2207.08504
§3.1.4 Gray module (Axis 6) supplies the bidirectional composition;
Loubaton 2307.11931 §6.1.4.2 functorial Grothendieck construction +
Aberlé-Spivak subterminality (Axis 10) supplies the univalent
universe at (∞,ω); HLOR ωcE polygraph (Axis 9) supplies the
universal coherent walking ω-equivalence; Uemura representable map
categories + BKS internal sconing (Tier 0) bind every axis under
one universal substrate.  Every axis grounded in published
literature, every axis Lean-mechanizable at zero axioms, every
axis giving FX a capability no other proof assistant has.  The
(∞,ω)-categorical universe is FX's SEMANTIC ambition: this would be
the first mechanization of (∞,ω)-categories in any proof assistant
if shipped.

**(B) The apex maximal-power computable kernel — the strongest
currently-known sound type theory that admits decidable
typechecking.**  Not just decidable Conv, but DECIDABLE typed
checking + DECIDABLE typed conversion + MECHANIZED complexity
bounds for every decision procedure (§11.8.7), under the zero-
axiom + closed-system discipline (§11.8.11).  The apex commitments
(§11.8): 2LTT skeleton with FOUR universe modes (inner univalent /
outer strict / directed / (∞,ω)-directed); the categorical
structural-reflection-degree flag hierarchy as universe-strength
payload (apex `kunenI0` = I0-strength via sequential ESR, stated as a
reflection principle, not an embedding j:V→V); K-free
dependent elimination with motive children + definitional eta;
full HIIRT (standard IR + indexed IR + higher IR + QIR + the
combined Forsberg-Setzer HIIRT beast); HITs + QIITs with cubical
Kan eliminator computation; multi-clock guarded type theory (BMV
2017); internal parametricity (Bernardy-Coquand-Moulin 2015);
rewriting rules as first-class kernel feature (Cockx-Tabareau
2021) with confluence + termination + linearity admission;
cubical pattern matching + Equations-style dependent pattern
matching; `dProp` internal computational reflection (Pédrot-
Tabareau 2018); full CCHM cubical computational univalence;
typed `HasType` judgment with typed subject reduction; 21-
dimensional integration over MTT + cohesive triple + differential
cohesion + n-truncations + linear-nonlinear adjoint modality +
algebraic effects + handlers; 10-profile synthetic mathematics
layer (∞-topos / synthetic spectra / synthetic smooth manifolds /
synthetic algebraic geometry / synthetic quantum / synthetic
measure + probability + Markov / synthetic differential cohomology
/ synthetic computability / synthetic stable ∞-categories);
optional Phase Z₉ fully-verified internal SMT engine built natively
inside FX as the closed-system alternative to delegating to
external Z3/CVC5.  The apex computable kernel is FX's OPERATIONAL
ambition: this would be the strongest sound type theory with
decidable typechecking ever shipped.

**The intersection — (A) ∩ (B) — is what makes FX first-in-class.**
The (∞,ω)-categorical substrate gives the semantic depth; the apex
computable kernel gives the operational depth; together they make
FX simultaneously a programming language kernel AND a
categorical-foundations research artifact, with every component
sound by published theory and every decision procedure verified
internally.  No precedent for either axis alone in any proof
assistant; FX delivers their union.

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
At the end you have the raw input layer (`RawTerm scope` +
`RawCell scope`, dimension computed not type-indexed) as the input
format and certified `PolyCell π sort dim scope boundary raw` as the
kernel inhabitant type, with the certified layer parameterized by a
thirteen-field `PolyProfile π`.  FX is one specific profile, reached and grown by the extension
calculus, not assembled by hand.

Eating all the cakes — universe layer:
- **Two-Level Type Theory (2LTT) skeleton** (Annenkov-Capriotti-Kraus-
  Sattler MSCS 2023): inner univalent universes (`gen_universeU`) for
  objects, outer strict universes (`gen_universeS`) for metatheory +
  computational reflection, with explicit lift / lower bridges.
- **Four universe modes total**: inner univalent, outer strict
  (strict reduction calculus + strict large-elim; univalence STILL
  applies per §11.8.13 — diverges from 2LTT orthodoxy), directed
  (Riehl-Shulman synthetic (∞,1)-categories), (∞,ω)-directed
  (Loubaton 2307.11931).
- **Univalence-everywhere discipline** (§11.8.13): univalence holds at
  every mode, level, lift, dimension, and modality with 3-4 independent
  proofs (operational `Step.eqType` + polynomial subterminality +
  polynomial pseudomonad + ∞-topos).  No K-axiom commitment anywhere.
- **Predicative cumulative hierarchy + impredicative bottom**
  (`SProp` definitional proof irrelevance + `Type₀` System-F-style
  polymorphism); strictly predicative `Type 1+`.
- **Full universe polymorphism** over `LevelExpr` (`lzero` / `lsucc` /
  `lmax` / `limax` / `lvar`); polynomial-time level-equality
  normalization (Mörtberg-Sterling 2024) + first-class bounded
  quantification (Chan-Weirich 2502.20485).
- **Structural-reflection-degree hierarchy as universe flags**
  (categorical, NOT set-theoretic — no V, no AC, no embeddings j:V→V;
  §11.8.2): universe-closure (`inaccessible`) → Mahlo reflection
  (`mahlo` → `hyperMahlo`) → higher-order Πⁿ-reflection
  (`weaklyCompact` → `reflecting`) → single-structure accessible-category
  reflection (`ramsey` → `vopenka` = SR for all classes) → **sequential
  Exact Structural Reflection** (`huge` → **`kunenI0`**, the
  rank-into-rank region; Bagaria-Lücke "Huge Reflection") → the 2024 SR
  frontier (`exacting`, `ultraexacting`; Aguilera-Bagaria-Lücke,
  ZFC-consistent rel I0).  **FX's committed categorical apex is
  `kunenI0`** — I0-strength self-similarity stated as a reflection
  principle, not `j : V → V`.  Each flag names a degree of structural
  reflection (Bagaria; Adámek-Rosický; Bagaria-Casacuberta-Mathias-
  Rosický; Bagaria-Lücke), decidable as a stricter admission predicate.
  Above that sits the open frontier (`schlutzenbergVLambdaPlus2`
  choiceless ceiling; `reinhardtDirected` FX-native) — honest catalogue
  entries, not objects FX asserts; see §11.8.2.1.
- **First-class universe codes**: `LevelExpr` and `UniverseFlag` live
  in the outer universe; declarations quantify over and pattern-match
  on them.

Eating all the cakes — elimination + computation layer:
- **K-free / univalence-compatible** identity types (cubical paths,
  Cockx-Devriese-Piessens "Pattern matching without K" ICFP 2014).
- **Dependent large elimination with motive children**: eliminator
  spines carry the motive as a typed child (per §11.8.3 fix to the 16
  current SR-iota arms).
- **Definitional eta** for functions, pairs, dependent pairs, unit,
  records.
- **Higher induction-recursion (HIIRT)**: standard IR (Dybjer-Setzer
  2003) + indexed IR + higher IR (Setzer 2008) + quotient IR + the
  combined HIIRT beast (Forsberg-Setzer 2012).
- **Higher Inductive Types (HITs)** + **Quotient Inductive-Inductive
  Types (QIITs)** with cubical Kan eliminator computation
  (Cavallo-Mörtberg, Altenkirch-Capriotti-Dijkstra-Forsberg).
- **Multi-clock guarded type theory** (Bizjak-Møgelberg-Vezzosi LICS
  2017): clock types, clock variables, clock-dependent later modalities,
  guarded fixed points — strictly more expressive than single-clock
  Nakano or sized types.
- **Internal parametricity** (Bernardy-Coquand-Moulin ICFP 2015 +
  Cavallo-Harper LICS 2020): the kernel proves its own free theorems
  without external metatheory.
- **Rewriting rules as a first-class kernel feature** (Cockx-Tabareau
  ICFP 2021): user-declared rewrite rules admitted on confluence +
  termination + linearity witnesses, joining the kernel's definitional
  equality per profile.
- **Cubical pattern matching** + **Equations-style dependent pattern
  matching** (Sozeau-Mangin ICFP 2019) — deep dependent matching with
  automatic recursion equations.
- **Internal computational reflection via `dProp`** (Pédrot-Tabareau
  LICS 2018): decidable-propositions universe carrying its own
  decision procedure; Markov's principle internally, no global
  classical commitment.

Eating all the cakes — cubical, modal, synthetic-math layer:
- **Full CCHM cubical computational univalence**: `gen_path` /
  `gen_pathLam` / `gen_pathApp` / `gen_transp` / `gen_hcomp` /
  `gen_glue` / `gen_unglue` / `gen_face` / `gen_dimI`.  Univalence is
  COMPUTATIONAL, not just an operational shortcut on universe-Id.
- **Multi-Modal Type Theory (MTT) outer container**
  (Gratzer-Sterling-Sterling LICS 2020) with dependent right adjoints
  between modes.
- **Cohesive modalities** ♭ ⊣ ◇ ⊣ □ ⊣ ♯ per cohesive focus
  (Myers-Riley `arXiv:2301.13780`).
- **Differential cohesion** Π ⊣ ♭_inf ⊣ ♯_inf ⊣ ʃ_inf (Schreiber
  `arXiv:1310.7930`) for synthetic differential / algebraic geometry.
- **n-truncations as profile features** (Capriotti-Kraus 2018).
- **Linear / non-linear adjoint modality** (Benton's LNL).
- **Algebraic effects + handlers** as first-class kernel feature
  (Plotkin-Pretnar ESOP 2009).
- **Synthetic mathematics layer** as profile capabilities: ∞-topos
  internal language, synthetic spectra, synthetic smooth manifolds /
  Lie groups, synthetic algebraic geometry, synthetic quantum types,
  synthetic measure + probability + Markov, synthetic differential
  cohomology, synthetic computability, synthetic stable ∞-categories.

Eating all the cakes — structural substrate + discipline:
- **Graded** (Atkey 2018 + Wood-Atkey 2022 corrected Lam rule),
  parametric over a quantale Q.
- **Polarized** (Levy CBPV + Pédrot-Tabareau ∂CBPV) with explicit
  Fire-Triangle navigation per §3.0.3.
- **Synthetic-Tait metatheory at (∞,ω)** via complicial nerve.
- **Allais universe-of-syntaxes** generic traversals (one structural
  `fold` ⇒ `rename` + `subst` as single instances).
- Presented as a **complicial-stratified globular-cubical-opetopic
  polygraph** with Gray-tensor compatible composition and tropical
  optimal reduction.
- **Mechanized in Lean 4 at strict zero axioms** — no `axiom`, no
  `sorry`, no `noncomputable`, no `propext`, no `Quot.sound`, no
  `Classical.choice`, no `@[implemented_by]`, no `@[extern]`, no
  `omega`, no hypothesis-as-postulate (per lean-fx-2/CLAUDE.md +
  AXIOMS.md).
- **Decidable typechecking at every admissible dimension** with
  MECHANIZED complexity bounds.  Polynomial-time first-order core
  (Lensing 2025); cubical-NbE dependent core (Mörtberg 2023).
- **Closed-system mandate** (§11.8.11): NO user-level tactics (only
  `calc` chains + type-directed elaboration), NO external SMT (every
  decider INTERNAL and verified — Phase Z₉ ships a fully-verified
  internal SMT engine if one ever becomes necessary), NO LLM in the
  kernel (LLM-driven workflows live OUTSIDE via the agent protocol,
  proposing terms the kernel verifies under its ordinary rules).

This is the **maximal-power computable kernel** — the strongest
currently-known sound type theory that admits decidable typechecking,
constrained only by (1) per-feature soundness in published theory,
(2) decidable typechecking under cubical NbE, and (3) zero-axiom
closed-system discipline.  See **§11.8** for the full apex
commitment, **§11.8.7** for the decidability + complexity matrix,
**§11.8.9** for the nine-phase Z₀–Z₈ rollout, **§11.8.10** for the
soundness composition (every component sound by published theory;
the JOINT soundness of the combination is open research), and
**§11.8.0** for the obligations ledger that tracks that joint
metatheory honestly (O-NORM / O-CONF / O-CANON et al.).

This is the "quantale-enriched (∞,∞)-category of types" Object the
`20_05_2026.md` dossier §14 hand-waves toward; this document makes it
mechanizable AND — through §11.8 — pushes it to the apex of what
mathematics currently knows how to mechanize soundly.

The cost is honest: ~270K gross zero-axiom Lean 4 LoC (~230K net),
~245K still to write after the ~25K shipped foundation, 2–4 years of
focused work, and the **first mechanization of (∞,ω)-categories
internalized in any proof assistant** AND the **strongest sound type
theory with decidable typechecking ever shipped** if all committed
stages land.  FX simultaneously becomes a programming language kernel
AND a categorical-foundations research artifact.  No precedent for
either; FX commits to their union.

**The method, and a third identity.**  Behind both ambitions is one
*method* the rest of this document applies relentlessly — the
**internalization principle** (§11.9.0): take a quantity normally
external, meta, or semantic and make it an internal, typed, certified,
*computable* cell.  Dimension is computed (`RawCell.dim`, §4), not an
a-priori index; equality is the saturation marking (§3.3–§3.4), not a
primitive; complexity is a grade (§3.7); consistency strength (§11.7.1)
and decidability (§11.7.4) are computable data.  Applied past the apex
(§11.9) the same move internalizes proof-simplicity (Squier homology =
Hilbert's 24th, §11.9.1.2), algorithmic information (FX0 as a fixed
`K`-machine, §11.9.2.1), entropy (SN = a Second Law, §11.9.2.2), and
ordinal strength (a GLP reflection algebra, §11.9.3 OP7).  And it points
at a **third identity** beyond language-kernel and foundations-artifact:
FX as an *instrument for generating novel verified mathematics* — the
discovery engine (§11.9.4) that produces theorems which provably do not
restate or compress what is already known.  This is not a separate
project bolted on; it is what the apex is FOR.  Univalence-everywhere
(§11.8.13) is the canonical dedup oracle; decidable Conv (MILESTONE A)
makes "is this the same idea?" computable; FX0 (§12.6) pins the
reference machine; the reflection ladder (§11.8.2) guarantees the supply
of genuinely-harder problems never runs dry (§11.7.1).  The apex is
independently justified — but it is *also*, exactly, the precondition
stack for that engine.  (Per the §11.9.0 firewall, the engine is
beyond-apex and never on the MILESTONE A–D critical path; the apex ships
first.)

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
  `RawCell` input).
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

**Apex extension (§11.8 commitment).**  Under the maximal-power
kernel commitment, raw-reduction Conv decidability (the original
MILESTONE A target) is **a sub-result of typed Conv decidability**,
not the endpoint.  The revised milestone scale (§11.8.12):

* **MILESTONE A (revised)** = decidable typed conversion + decidable
  typed checking for the ~30-generator semantic core, via cubical
  NbE + bidirectional typechecking (Phase Z₁ + Z₂ + Z₃ of §11.8.9).
* **MILESTONE A+** adds the full CCHM cubical primitives
  (Phase Z₄).
* **MILESTONE A++** adds HITs + QIITs (Phase Z₅).
* **MILESTONES B / C / D** add HIIRT + Mahlo, guarded recursion, and
  full 21-dim integration respectively.

Every decision procedure invoked at any milestone is INTERNAL and
fully verified — no external SMT, no LLM oracle, no `Classical.dec`
escape hatch.  §11.8.7 catalogs each decider with its complexity
bound; the strict harness's `STRICT-COMPLEXITY` gate verifies the
bound on every decidable kernel theorem (closing the "decidable
but EXP-tower" loophole).  Path A's NbE engine generalizes to the
typed cubical setting (Mörtberg 2023); Path B's Makkai/Forest word
equality remains available as semantic cross-check on the typed
polygraph projection.

### 2.4 Concurrency / distribution wait on certified `compH`

The `20_05_2026.md` dossier §2.7 conjectures that K11.5 (horizontal
composition) + K11.6 (interchange / Eckmann-Hilton) IS the separation
logic frame rule at the polygraph level.  The conjecture is *correct
in structure but loses typing* in the current K11 design because the
typed Term is separate from the polygraph.

The raw layer does **not** fix this.  Raw
`RawCell.horizontalComposite` is input syntax only: it can represent a
proposed horizontal composition, but
it does not certify disjoint footprints, Gray-boundary matching, or a
typed frame rule.

The certified layer fixes this only after Axis 6 is real.  A future
certified `PolyCell` horizontal-composite constructor must take two
certified cells, a
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

**Apex modal stack (§11.8.6 commitment).**  Under the maximal-power
kernel, "one kernel hosts every type theory we'd ever want" is not
slogan but mechanism: the modal layer is the FULL **MTT outer
container** (Gratzer-Sterling-Sterling LICS 2020) with dependent right
adjoints, hosting:

* The **cohesive adjoint triple** ♭ ⊣ ◇ ⊣ □ ⊣ ♯ per Myers-Riley
  cohesive focus (`gen_shape` / `gen_flat` / `gen_sharp`).
* **Differential cohesion** Π ⊣ ♭_inf ⊣ ♯_inf ⊣ ʃ_inf for synthetic
  differential / algebraic geometry (`gen_reduced` /
  `gen_infinitesimal` / `gen_etale`, Schreiber 2013).
* **Multi-clock guarded type theory** (BMV LICS 2017): `gen_clock` /
  `gen_laterCl` / `gen_forceCl` / `gen_clockAbs` / `gen_clockApp` /
  `gen_fixedPoint` — strictly more expressive than single-clock
  Nakano (clock quantification + clock-dependent constructions).
* **Internal parametricity** (Bernardy-Coquand-Moulin 2015):
  `gen_param` / `gen_paramAbs` — free theorems internalized.
* **Linear / non-linear adjoint modality** (Benton's LNL): `gen_F` /
  `gen_G` — linear types as a modal sub-theory.
* **n-truncations** `gen_truncN n` (Capriotti-Kraus 2018).
* **Algebraic effects + handlers** (Plotkin-Pretnar ESOP 2009) as
  first-class kernel feature: `gen_effectOp` / `gen_effectHandler` /
  `gen_effectScope`.

**One kernel hosts every type theory we'd ever want.**  Different FX
deployments pick different profiles; all coexist.  Adding a new
modality is one Generator-table entry plus an MTT mode-theory
extension witness — never a `Term` constructor, never a per-modality
adjunction-by-hand proof.

### 2.6 The categorical universe internal to FX

Loubaton's PhD thesis §6.1.4.2 proves:

> Hom^⊖(I, ω) ≃ LCart^c_U(I)

where `ω` is the (∞,ω)-category of (∞,ω)-categories.  This is the
(∞,ω) statement of univalence + Grothendieck construction simultaneously.

For FX, this means: the universe `Ty.universe` in the current kernel
becomes a certified universe `PolyCell` over a dim-0 `RawCell`
(`termBase`) input, and its
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
`RawCell` raw syntax.
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
constructions.  The barrier is engineering scale (~270K LoC), not
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

**How §3 relates to §11.8.**  The thirteen axes here describe the
PROFILE SHAPE — what data a profile bundles and what categorical
laws it must satisfy.  §11.8 then commits the *kernel itself* to the
**maximal-power computable target**: 2LTT 4-mode universes (§11.8.2),
HIIRT + multi-clock guarded + internal parametricity + rewriting rules
+ pure type-directed elaboration (§11.8.3), full CCHM cubical
(§11.8.4), typed `HasType` judgment with typed SR (§11.8.5), full
21-dim integration + MTT + cohesive + differential cohesion + linear-
nonlinear + algebraic effects + synthetic mathematics layer (§11.8.6),
and a decidability matrix with mechanized complexity bounds (§11.8.7).
The closed-system mandate (§11.8.11) — no user tactics, no external
SMT, no LLM — applies UNIFORMLY across every axis below.  Read §3 as
the categorical SHAPE, §11.8 as the operational APEX both must
realize together.

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

- A fixed inductive of typed `Term` constructors makes every new
  former an inductive extension with a per-constructor cascade across
  rename / subst / cd_lemma / Conv.  FX instead carries operations as
  entries in the unified 194-entry `Generator` table (§4 / §3.16).

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
* **The Squier 3-cells are also computable proof-data, not only a
  coherence guarantee (O-HOMOLOGY, §11.9.1.2).**  A convergent
  presentation's critical-pair fillers present a free polygraphic
  resolution (Guiraud-Malbos); its homology `Hₙ` measures proof
  essential-uniqueness — a theorem's proof-cell is contractible iff it
  has a canonically-simplest proof, the first non-zero `Hₙ` is the
  obstruction, and high homological dimension *lower-bounds* proof
  complexity (Squier FDT).  This is a concrete candidate answer to
  **Hilbert's lost 24th problem** (proof simplicity, recovered by
  Thiele 2003); `H₁` on the β/ι/η term polygraph is shippable now from
  the cd / critical-pair table this axis already builds (§11.9.1.2).
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
  universe cell over raw `RawCell` classify `fxProfile`
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

- For FX: the fxProfile's free ω-cat is generated by the unified
  194-entry `Generator` table (dimension computed by `RawCell.dim`,
  not a per-dim enum split) plus the cd-pair-indexed dim-2 confluence
  fillers.  This is a finite polygraph.  K12 reducibility + cd_lemma confluence gives the
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

**Apex commitment (§11.8.2).**  Under the maximal-power kernel, this
axis ships not as a single univalent universe but as a **2LTT
4-mode universe stack** with the **full Setzer + Rathjen large-
cardinal hierarchy** as a `UniverseFlag` payload.  The four modes:

* `gen_universeU n` — inner univalent (cubical Kan reduction);
  objects live here.
* `gen_universeS n` — outer strict (strict normalization + strict
  large-elimination discipline); **univalence still applies** per
  §11.8.13 univalence-everywhere discipline (FX diverges from 2LTT
  orthodoxy here — no K-axiom commitment); metatheory + computational
  reflection live here.
* `gen_universeD n` — directed universe (Riehl-Shulman synthetic
  (∞,1)-categories `arXiv:1705.07442`); directed univalence as theorem
  per Gratzer-Weinberger-Buchholtz 2407.09146.
* `gen_universeOmega n` — (∞,ω)-directed (Loubaton 2307.11931).

Plus `gen_sprop` for definitional proof irrelevance,
`gen_univLift` / `gen_univLower` for mode bridges (Hofmann-Streicher
natural transformations), and `LevelExpr` for full universe
polymorphism (decidable in polynomial time per Mörtberg-Sterling
2024 normalization).

The `UniverseFlag` enum runs the structural-reflection-degree ladder
per §11.8.2 — a CATEGORICAL hierarchy (no V, no AC, no embeddings
j:V→V): universe-closure (`standard`, `inaccessible`) → Mahlo
reflection (`mahlo` → `hyperMahlo`) → higher-order Πⁿ-reflection
(`weaklyCompact` → `reflecting`) → single-structure accessible-category
reflection (`ramsey` … `extendible`, `vopenka` = SR for all classes) →
**sequential Exact Structural Reflection** (`huge`, `nHuge`,
`kunenI3`…**`kunenI0`**, the rank-into-rank region; Bagaria-Lücke "Huge
Reflection") → the 2024 SR frontier (`exacting`, `ultraexacting`;
Aguilera-Bagaria-Lücke, ZFC-consistent rel I0).  Each flag names a
degree of structural reflection (Bagaria; Adámek-Rosický; Bagaria-
Casacuberta-Mathias-Rosický; Bagaria-Lücke), decidable as a strictly
stronger admission predicate (O(flag enum position)).  Above the
frontier sits the open tail (`schlutzenbergVLambdaPlus2` choiceless
ceiling; `reinhardtDirected` FX-native) — catalogue entries, not
asserted (§11.8.2.1).  Implementation schedule: `standard` first
(Phase Z₆ kickoff); Mahlo + higher-order reflection ship Phase Z₆
proper; single-structure then sequential-ESR degrees up to `kunenI0`
ship over the following months as Phase Z₆+.  **FX's committed
categorical apex — I0-strength self-similarity via sequential ESR
(`kunenI0`) — lands at ★ MILESTONE B (§11.8.12) within 6 months of
Phase Z₆ kickoff**, with `exacting`/`ultraexacting` as same-phase
stretch targets.

**Operational reference:** `Step.eqType` reduction rule in FX
kernel (per lean-fx-2/CLAUDE.md mandate).  Univalence ships as a
**definitional reduction**, not an axiom: `Step.eqType : Step
(Ty.id (Ty.universe l) A B) (Ty.equiv A B)`.  The theorem
`Univalence : Conv (Ty.id Univ A B) (Ty.equiv A B) := Conv.fromStep
Step.eqType` is a real body, zero-axiom under
`#assert_no_axioms`.  Under the apex commitment this generalizes
to full CCHM cubical operations (Phase Z₄): `gen_path` / `gen_transp`
/ `gen_hcomp` / `gen_glue` / `gen_unglue` / `gen_face` / `gen_dimI`
make univalence COMPUTATIONAL, not just an operational shortcut on
universe-Id terms.  See §11.8.4 for the full cubical generator
inventory.

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

**Extension to full cubical primitives (Phase Z₄ commitment).**
Per §11.8.4, the long-term kernel target is the **full Cubical Type
Theory primitive set**: `gen_path` / `gen_pathLam` / `gen_pathApp`
/ `gen_transp` / `gen_hcomp` / `gen_glue` / `gen_unglue` / `gen_face`
/ `gen_dimI` — not just the `Step.eqType` reduction.  This makes
univalence COMPUTATIONAL in the full CCHM sense rather than just an
operational shortcut on universe-Id terms.  The current
`Step.eqType` rule is the operational entry point; Phase Z₄
extends to full Kan cubical structure.

---

### 3.11 Single-Substitution Calculus backbone

**Reference:** Kaposi-Xie *Type Theory with Single
Substitutions* `arXiv:2510.12303` (Oct 2025); Altenkirch-Burke-
Wadler *Substitution Without Copy and Paste* `arXiv:2510.12304`
(Oct 2025).

**Why FX needs it:**

* A fixed-inductive `Term` with one constructor per former forces the
  rename / substitution / cd_lemma cascades to carry one arm per
  constructor; FX's single Allais fold over the 194-`Generator` table
  collapses each to one generic instance.  Per
  `feedback_perf_antipatterns.md` profile
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

**Two substitution calculi, one bridge (O-SUBST-BRIDGE, §11.8.0).**
FX carries two substitution presentations and must name which is
canonical: the §4 Allais universe-of-syntaxes PARALLEL fold (one
generic rename / subst traversal over the 194-`Generator` table —
the operational backbone the kernel computes with) and the Kaposi-Xie
SINGLE-substitution calculus above (8 equations, isomorphic to CwF
syntax — the metatheory backbone that collapses the 78-arm commute
proofs).  FX commits to the Allais parallel fold as the OPERATIONAL
canonical form and treats SSC as the metatheory VIEW; their
equivalence — `sscIsomCwF` composed with the Allais fold's
correctness — is OBLIGATION O-SUBST-BRIDGE (specifiable now: a Lean
isomorphism, not new mathematics).  Until it is proved, a theorem
stated in one calculus does not transfer to the other for free, so
neither presentation may silently borrow the other's lemmas.

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

**The extension calculus is the tangent structure of theory-space
(O-TSPACE, §11.9.2.3).**  Reading `extendProfile` geometrically: the
admissible `ProfileExtension`s at a profile form its **tangent cone**
(the directions mathematics can grow); the Fire-Triangle / Zwart-Marsden
no-gos are the **boundary singularities**; and the lax-3-cell
**associator (T5) is the curvature** — flat exactly when concept-order
is irrelevant, curved where the order of adding features is forced.
With the `Hardness` metric (§11.9.1.3) this makes "where can mathematics
go from here" a *computable* question (enumerate the tangent cone, score,
follow the high-`Hardness` geodesic), and the obstruction-cohomology of
the cross-pair laws (§11.9.1.1 O-OBSTRUCT) is the curvature's
de-Rham-style classification.  So §3.14 is not only the feature-admission
mechanism — it is the differential geometry on which the §11.9 frontier
program navigates.

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
   discharge erasure soundness automatically.  The field is a NAMED
   placeholder, not a theorem: the §1.5 premise — all 21 dimensions
   erased to zero runtime cost — needs an erasure-correctness
   metatheorem (the erasure map commutes with reduction on the runtime
   fragment, and erased programs compute the same observable values as
   their typed sources).  That theorem is OBLIGATION O-ERASE
   (§11.8.0, specifiable now), gating MILESTONE D; supplying
   `erasureWitness` per feature is how the obligation is discharged
   incrementally, never a substitute for stating it.

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

### 3.16 Apex Generator Inventory — what §11.8 commits the table to ship

The 194-generator surface in `GeneratorCore.lean` (`gen_var` →
`gen_processCalc`) is the **current** table.  The apex commitment
in §11.8 expands the table substantially.  This section is the
concrete inventory of what Phase Z₀ through Z₈ + Z₉ commit the
Generator table to admit, with explicit `ChildSpec` lists, binder
shifts, payload types, totality classes, and Phase-Z stage tags.

Where §11.8 lays out the THEORETICAL apex commitments, §3.16
catalogs them as **table data** — the same shape (`Generator
enum + arity + binderShifts + payload + childSpecs + cellSort +
totalityClass + consistencyStrength + siteOpenness`) the current
194-entry table uses.  No new inductive ctors at the `PolyCell`
level; only new `Generator` enum values + their metadata + their
`SemanticallySupportedGenerator` admission witnesses.

This is the **cascade-death principle made concrete at apex
scale**: even at MILESTONE D (~21-dim integration + full synthetic
math layer + verified SMT engine + every cubical/HIT/HIIRT/guarded
/parametricity/rewriting/cohesion/MTT/effect feature), every new
capability remains a new Generator entry plus its admission
witness — never a new `RawTerm` ctor, never a new `PolyCell` ctor,
never a per-feature cascade across rename/subst/cd/Conv.  The
194-entry table grows to ~400-500 entries at MILESTONE D; the
inductive surface area at the `PolyCell` level stays fixed.

#### 3.16.1 Why a §3.16 inventory section exists

Three audiences need this section:

1. **Implementation warriors.**  When Phase Z₀ kicks off, the
   warrior implementing `gen_universeU` / `gen_universeS` /
   `gen_universeD` / `gen_universeOmega` doesn't want to re-derive
   the apex commitments by re-reading §11.8.2.  They want a single
   table with `ChildSpec` lists, binder shifts, and payload types
   they can paste into `GeneratorCore.lean` extension.  §3.16
   delivers that table.

2. **Reviewers + ledger auditors.**  When a commit adds (e.g.) the
   `gen_clockAbs` Generator entry, the reviewer needs to confirm
   the entry's metadata matches the published theory (BMV 2017
   multi-clock).  §3.16 provides the reference target so the
   review is a comparison against table data, not a re-read of
   §11.8.3.

3. **Future-FX warriors.**  When MILESTONE C is reached and someone
   wants to add (e.g.) a new HIT to the catalog, §3.16 documents
   the discipline: emit a new `gen_<feature>Ctor` + `gen_<feature>
   PathCtor` + `gen_<feature>Rec` triple, with the standard child-
   spec template per the HIT's signature.  No bespoke design
   decisions per HIT — the template is fixed.

#### 3.16.2 Generator family taxonomy at the apex

The apex Generator table partitions into TWELVE major families,
each gated by a Phase Z stage and admitted under specific
`SemanticallySupportedGenerator` predicates:

| Family | Apex generators | Phase | Reference |
|---|---|---|---|
| §3.16.3 Universe modes | 4 mode codes + `gen_sprop` + 2 lifts | Z₀ + Z₆ | §11.8.2 + Setzer 1998 / Rathjen 1998 |
| §3.16.4 Cubical CCHM primitives | 9 generators (path / pathLam / pathApp / transp / hcomp / glue / unglue / face / dimI) | Z₄ | CCHM JFP 2018 |
| §3.16.5 HIT + QIIT path constructors | 7 templates (quotMk / quotEq / circle / pushout / trunc / coequalizer / generalHIT) | Z₅ | Cavallo-Mörtberg 2020 |
| §3.16.6 HIIRT eliminators | 30+ refactored eliminator spines with motive children | Z₆ | Dybjer-Setzer 2003 + Setzer 2008 |
| §3.16.7 Multi-clock guarded | 6 generators (clock / laterCl / forceCl / clockAbs / clockApp / fixedPoint) | Z₇ | BMV 2017 |
| §3.16.8 Internal parametricity | 2 generators (param / paramAbs) + bridges | Z₈ | Bernardy-Coquand-Moulin 2015 |
| §3.16.9 First-class rewriting | 1 generator (rewriteRule) + admission triple | Z₈ | Cockx-Tabareau 2021 |
| §3.16.10 dProp + reflection | 2 generators (dProp / dPropDec) | Z₈ | Pédrot-Tabareau 2018 |
| §3.16.11 MTT mode generators | 3 generators per mode (mode / modIntro / modElim) + adjunction witnesses | Z₈ | Gratzer-Sterling-Sterling 2020 |
| §3.16.12 Cohesion + diff cohesion | 7 generators (shape / flat / sharp / reduced / infinitesimal / etale + reduce) | Z₈ | Shulman 2018 + Schreiber 2013 |
| §3.16.13 Algebraic effects | 3 generators (effectOp / effectHandler / effectScope) | Z₈ | Plotkin-Pretnar 2009 |
| §3.16.14 Synthetic math | 10 profile capabilities (no kernel gen — profile-level) | Z₈+ | per §11.8.6 |
| §3.16.15 Verified SMT engine | 6 generators (smtSatCert / smtTheoryCert / smtNelsonOppen / + 3 supporting) | Z₉ | optional, per §11.8.7 |

Each subsection below specifies the family's generators in detail.
The cascade-death property holds uniformly: adding a Generator entry
to the table never adds a `RawTerm` or `PolyCell` constructor.

#### 3.16.3 Universe-mode generators (Z₀ + Z₆)

The current `gen_universeCode` has payload `Unit` — the Codex audit
(`feedback_polycell_structural_vs_semantic`) flagged this as the
seven-gap audit's gap #1 (universe-mode under-specification ⇒
Type-in-Type at the admission level).  §11.8.2 commits to **4
universe modes** with a `LevelExpr × UniverseFlag` payload + SProp
+ 2 lifting directions.

Apex universe generators:

```
| .gen_universeU       => LevelExpr × UniverseFlag   -- inner univalent (cubical Kan reduction)
| .gen_universeS       => LevelExpr × UniverseFlag   -- outer strict (strict reduction + strict large-elim);
                                                     -- univalence STILL applies per §11.8.13
| .gen_universeD       => LevelExpr × UniverseFlag   -- directed (∞,1)-cat synthetic, directed univalence theorem
| .gen_universeOmega   => LevelExpr × UniverseFlag   -- (∞,ω)-directed (Loubaton)
| .gen_sprop           => Unit                        -- SProp (definitional proof irrelevance,
                                                     --        univalence trivial-by-collapse)
| .gen_univLift        => LiftDirection              -- Inner→Outer / Outer→Inner / Directed lift,
                                                     --   univalence-preserving per §11.8.13
| .gen_univLower       => LiftDirection              -- inverse lift (where defined), univalence-preserving
```

`LevelExpr` carries the universe-polymorphism payload:

```
inductive LevelExpr where
  | lzero : LevelExpr
  | lsucc : LevelExpr → LevelExpr
  | lmax  : LevelExpr → LevelExpr → LevelExpr
  | limax : LevelExpr → LevelExpr → LevelExpr  -- impredicative max
  | lvar  : Nat → LevelExpr                    -- universe variable
```

Equality of `LevelExpr` up to algebra (`lmax e e = e`, `lmax lzero
e = e`, …) is decidable in **polynomial time** via the Mörtberg-
Sterling 2024 normalization algorithm — one of the deciders
listed in §11.8.7's matrix.

`UniverseFlag` carries the structural-reflection-degree ladder per
§11.8.2 — a CATEGORICAL hierarchy, not a set-theoretic one (no V, no
AC, no embeddings j:V→V): universe-closure (`standard`,
`inaccessible`) → Mahlo reflection (`mahlo`, `superMahlo`, `nMahlo`,
`hyperMahlo`) → higher-order Πⁿ-reflection (`weaklyCompact`,
`indescribable`, `reflecting`) → single-structure accessible-category
reflection (`ramsey`, `measurable`, `strong`, `woodin`, `supercompact`,
`extendible`, `vopenka` = SR for all classes) → **sequential Exact
Structural Reflection** (`huge`, `nHuge`, `kunenI3`…**`kunenI0`**, the
rank-into-rank region; Bagaria-Lücke) → 2024 SR frontier (`exacting`,
`ultraexacting`).  **`kunenI0` is FX's committed categorical apex** —
I0-strength self-similarity as a reflection principle.  The open tail
(`schlutzenbergVLambdaPlus2`, `reinhardtDirected`) is catalogue-only,
not asserted.  See §11.8.2 + §11.8.2.1 for the canonical enum body, the
ESR ladder, the "Why reflection, not embeddings" rationale, and the
Reinhardt frontier (b)/(c) split.

Each flag is a strictly stronger admission predicate.  Admission is
decidable in `O(flag enum position)`.  Implementation schedule per
§11.8.9: `standard` + `inaccessible` ship Phase Z₆ kickoff; Mahlo +
higher-order reflection ship Phase Z₆ proper; single-structure then
sequential-ESR reflection degrees up to `kunenI0` (+ the
`exacting`/`ultraexacting` frontier) ship over the following months as
Phase Z₆+.  **The committed categorical apex `kunenI0` (I0-strength via
sequential ESR) lands at MILESTONE B within 6 months of Phase Z₆
kickoff** per §11.8.12; the open-frontier tail
(`schlutzenbergVLambdaPlus2`, `reinhardtDirected`) is catalogue-only.

`ChildSpec` lists for universe-mode generators:

| Generator | Arity | ChildSpecs | binderShifts |
|---|---|---|---|
| `gen_universeU` / `gen_universeS` / `gen_universeD` / `gen_universeOmega` | 0 | `[]` | `[]` |
| `gen_sprop` | 0 | `[]` | `[]` |
| `gen_univLift` / `gen_univLower` | 1 | `[{ .type, 0, 0 }]` | `[0]` |

Each universe generator is `cellSort := .type`, `cellDimension := 0`,
`totalityClass := .total`.  ConsistencyStrength varies per flag.

#### 3.16.4 Cubical CCHM primitives (Phase Z₄)

§11.8.4 commits to the full CCHM cubical primitive set, generalizing
the current `gen_interval0` / `gen_interval1` / `gen_intervalOpp` /
`gen_intervalMeet` / `gen_intervalJoin` / `gen_pathLam` / `gen_pathApp`
/ `gen_transp` / `gen_hcomp` / `gen_glueIntro` / `gen_glueElim` to a
coherent CCHM-compatible cubical core.

Apex cubical generators (extending what's already in the 194 table):

```
| .gen_path        => Unit  -- Path type former: Path A x y as a Generator
                            -- (type-level; the term-level pathLam already exists)
| .gen_face        => FaceFormula  -- Face formulas: i = 0, i = 1, i ∧ j, i ∨ j, ...
| .gen_dimI        => Unit  -- The interval pre-type (interval semantics)
| .gen_compFill    => Unit  -- Composition filling (Kan structure)
| .gen_glueType    => Unit  -- Glue type former (Glue A φ T e at type level)
```

The current `gen_glueIntro` / `gen_glueElim` are term-level glue
introduction / elimination; the apex commitment adds `gen_glueType`
at type level.  Similarly `gen_path` adds the type former alongside
the existing `gen_pathLam` (term-level path lambda).

`FaceFormula` is a finite presentation of dim-interval face
constraints:

```
inductive FaceFormula where
  | dimIs0 (dimVar : Nat) : FaceFormula                    -- i = 0
  | dimIs1 (dimVar : Nat) : FaceFormula                    -- i = 1
  | meet   (left right : FaceFormula) : FaceFormula        -- i ∧ j
  | join   (left right : FaceFormula) : FaceFormula        -- i ∨ j
  | empty  : FaceFormula                                    -- 0_F (always false)
  | full   : FaceFormula                                    -- 1_F (always true)
```

`DecidableEq FaceFormula` is structural.  Face-formula equality
modulo distributivity of meet over join is decidable in polynomial
time (a normal-form approach: disjunctive normal form per
Mörtberg-Sterling).

`ChildSpec` lists for apex cubical generators:

| Generator | Arity | ChildSpecs | binderShifts |
|---|---|---|---|
| `gen_path` | 3 | `[{ .type, 0, 0 }, { .term, 0, 0 }, { .term, 0, 0 }]` | `[0, 0, 0]` |
| `gen_face` | 0 | `[]` | `[]` |
| `gen_dimI` | 0 | `[]` | `[]` |
| `gen_compFill` | 4 | `[{ .type, 0, 1 }, { .term, 0, 0 }, { .term, 0, 0 }, { .term, 0, 0 }]` | `[1, 0, 0, 0]` |
| `gen_glueType` | 4 | `[{ .type, 0, 0 }, { .term, 0, 0 }, { .type, 0, 0 }, { .term, 0, 0 }]` | `[0, 0, 0, 0]` |

All apex cubical generators are `cellSort := .term` or `.type`,
`cellDimension := 0`, `totalityClass := .total` (cubical Kan ops
are Tot-by-construction in CCHM), `consistencyStrength :=
.predicative` (CCHM lives below ZFC + inaccessibility).

#### 3.16.5 HIT + QIIT path constructors (Phase Z₅)

§11.8.3 commits to Higher Inductive Types via path-constructor
Generators carrying a `kind : Generator.Kind` tag:

```
inductive Generator.Kind where
  | termCtor            -- ordinary constructor
  | pathCtor            -- path constructor (Path A x y inhabitant)
  | higherPathCtor      -- 2-cell / higher path constructor
  | recursorCtor        -- eliminator (gets motive)
```

Each HIT instance ships THREE Generators: a term constructor, one
or more path constructors, and an eliminator.  The HIT eliminator's
iota rule respects path constructors via cubical Kan operations
(per §11.8.4 generators above).

Apex HIT generator families (one row per HIT):

| HIT | Term ctor | Path ctor(s) | Recursor |
|---|---|---|---|
| Quotient | `gen_quotMk` (existing) | `gen_quotEq` (existing) | `gen_quotRec` (existing) |
| Circle (S¹) | `gen_circleBase` (existing) | `gen_circleLoop` (existing) | `gen_circleRec` (existing) |
| Pushout | `gen_pushInl` / `gen_pushInr` (existing) | `gen_pushGlue` (existing) | `gen_pushRec` (existing) |
| n-truncation | `gen_truncIntro` (existing) | `gen_truncCoh` (existing) | `gen_truncRec` (existing) |
| Suspension (apex add) | `gen_suspNorth` / `gen_suspSouth` | `gen_suspMerid` | `gen_suspRec` |
| Coequalizer (apex add) | `gen_coeqIn` | `gen_coeqEq` | `gen_coeqRec` |
| General-HIT framework (apex add) | `gen_hitCtor (signature : HITSignature)` | `gen_hitPath (path : HITPathDecl)` | `gen_hitRec` |

`HITSignature` and `HITPathDecl` are profile-level data: a HIT's
shape is described by lists of constructor arities + path
boundaries, admitted via `SemanticallySupportedGenerator` with a
Cavallo-Mörtberg-2020 well-formedness witness.

QIITs (Quotient Inductive-Inductive Types per Altenkirch-Capriotti-
Dijkstra-Forsberg FoSSaCS 2018) share the same template but with
the constraint that the type former and value former are mutually
inductive at the Generator level (via the `mutual` keyword in the
Generator table — admissible because Generator is a finite enum, not
a recursive inductive).

**The induction-induction tension is real and not closed by the
finite enum (O-II, §11.8.0).**  A QIIT *is* induction-induction: a
type mutually defined with a family indexed by it.  The v2 substrate
deliberately UN-indexed `RawCell` (dimension computed, not a type
index) precisely to dodge Lean's mutual-index rule, which rejects the
`Ctx ⇄ Ty ⇄ Term` mutual block.  That the `Generator` enum is finite
does NOT discharge QIIT well-formedness — the induction-induction
lives at the TYPED layer (the mutual type/family dependency in
`HasType`), not in the enum.  Reconciling QIIT typed certification
with the substrate's un-indexing (the live path: well-scoped `Term` +
extrinsic `HasType` carrying the II dependency, per Kaposi-Kovács-
Lafont-Altenkirch QII) is OBLIGATION **O-II** (specifiable now), not
a property of the enum being finite.

`ChildSpec` lists for the apex HIT additions follow the template:
term ctors have payload-shape children; path ctors have Path-type
endpoints as children at scope-shift 0; recursors have a motive
child at scope-shift 1, base case at 0, recursive case at the
binder count of the HIT.

#### 3.16.6 HIIRT eliminators (Phase Z₆ refactor)

§11.8.3 commits to **dependent large elimination with motive
children**.  The current 16 SR-iota arms (per memory
`project_polycell_v2_progress`) all assume non-dependent
eliminators (no motive in the child spine).  Phase Z₀ refactors
this.

**Eliminator spine template (post-Z₀):**

```
gen_<typename>Elim spec:
  ChildSpec list := [
    { .type, 0, 1 },           -- motive : <typename> → Type
    { .term, 0, 0 },           -- base case (or first variant)
    { .term, 0, <binder count> }, -- recursive case (with binders for
                                      predecessor, induction hypothesis,
                                      result of induction, ...)
    ...
    { .term, 0, 0 }            -- scrutinee
  ]
  binderShifts := [1, 0, <binder count>, ..., 0]
```

Concrete refactored eliminators (Phase Z₀):

| Generator | Pre-Z₀ shape | Post-Z₀ shape |
|---|---|---|
| `gen_natElim` | `[0, 0, 0]` (zero, succ, scrutinee, NO motive) | `[1, 0, 2, 0]` (motive, zero, succ-with-IH, scrutinee) |
| `gen_natRec` | `[0, 0, 0]` (iterator form, no motive) | `[1, 0, 2, 0]` |
| `gen_boolElim` | `[0, 0, 0]` | `[1, 0, 0, 0]` (motive, true, false, scrutinee) |
| `gen_listElim` | `[0, 0, 0]` | `[1, 0, 3, 0]` (motive, nil, cons-with-IH, scrutinee) |
| `gen_optionMatch` | `[0, 0, 0]` | `[1, 0, 1, 0]` (motive, none, some, scrutinee) |
| `gen_eitherMatch` | `[0, 0, 0]` | `[1, 1, 1, 0]` (motive, inlBranch, inrBranch, scrutinee) |
| `gen_idJ` | `[0, 0]` | `[2, 0, 0]` (motive at shift 2, refl case, witness) |
| `gen_idStrictRec` | `[0, 0]` | `[2, 0, 0]` |

Phase Z₀ is ~2K LoC of refactor work (the 33+ structural decls
this affects, per §11.8.9).  The downstream SR-iota arms refactor
to match the new shapes.  The arms shipped today (16/18 per
`project_polycell_v2_progress`) are SOUND for the pre-Z₀ shapes;
the post-Z₀ shapes get fresh SR proofs as part of Z₁ (Typed core).

#### 3.16.7 Multi-clock guarded recursion (Phase Z₇)

§11.8.3 + §2.5 commit to **multi-clock guarded type theory**
(Bizjak-Møgelberg-Vezzosi LICS 2017 + Møgelberg-Veltri-Vezzosi
JFP 2020).  Beyond single-clock Nakano `▷`, multi-clock supports
clock quantification + clock-dependent constructions.

Apex multi-clock generators:

```
| .gen_clock         => Unit  -- clock-type former (a clock is a "rate")
| .gen_laterCl       => Unit  -- ▸_κ later modality at clock κ
| .gen_forceCl       => Unit  -- force_κ : ▸_κ A → A (under clock binding)
| .gen_clockAbs      => Unit  -- ∀κ. A — universal clock abstraction
| .gen_clockApp      => Unit  -- A[κ] — clock application
| .gen_fixedPoint    => Unit  -- gfix : (▸_κ A → A) → A — guarded fixed point
```

`ChildSpec` lists:

| Generator | Arity | ChildSpecs | binderShifts |
|---|---|---|---|
| `gen_clock` | 0 | `[]` | `[]` |
| `gen_laterCl` | 1 | `[{ .type, 0, 0 }]` | `[0]` |
| `gen_forceCl` | 1 | `[{ .term, 0, 0 }]` | `[0]` |
| `gen_clockAbs` | 1 | `[{ .type, 0, 1 }]` (body under a clock binder) | `[1]` |
| `gen_clockApp` | 2 | `[{ .term, 0, 0 }, { .term, 0, 0 }]` | `[0, 0]` |
| `gen_fixedPoint` | 1 | `[{ .term, 0, 1 }]` | `[1]` |

All multi-clock generators: `cellSort := .term` or `.type`,
`cellDimension := 0`, `totalityClass := .productive` (multi-clock
programs are productive-by-construction per BMV's productivity
proof), `consistencyStrength := .predicative`.

The shift-1 binders in `gen_clockAbs` and `gen_fixedPoint` exercise
the fold engine's binder-lift discipline — covered by V2-fix-8's
shift > 1 smoke (uncommitted on disk, to ship next iteration).

#### 3.16.8 Internal parametricity bridge (Phase Z₈)

§11.8.3 commits to **internal parametricity**: the kernel proves
its own free theorems without external metatheory (Bernardy-Coquand-
Moulin ICFP 2015 + Cavallo-Harper LICS 2020).

Apex internal-parametricity generators:

```
| .gen_param         => Unit  -- parametricity bridge: BridgeA : A ≅ Param A
| .gen_paramAbs      => Unit  -- parametric universal abstraction
| .gen_paramApp      => Unit  -- parametric application
| .gen_paramRel      => Unit  -- relational interpretation extraction
```

`ChildSpec` lists:

| Generator | Arity | ChildSpecs | binderShifts |
|---|---|---|---|
| `gen_param` | 1 | `[{ .type, 0, 0 }]` | `[0]` |
| `gen_paramAbs` | 1 | `[{ .term, 0, 1 }]` (body under parametric binder) | `[1]` |
| `gen_paramApp` | 2 | `[{ .term, 0, 0 }, { .term, 0, 0 }]` | `[0, 0]` |
| `gen_paramRel` | 2 | `[{ .term, 0, 0 }, { .term, 0, 0 }]` | `[0, 0]` |

Adds ~3K LoC to the kernel (per §11.8.3).  Decidable typechecking
preserved (Bernardy-Moulin 2013).  `cellSort := .term`,
`cellDimension := 0`, `totalityClass := .total`,
`consistencyStrength := .predicative`.

#### 3.16.9 First-class rewriting rules (Phase Z₈)

§11.8.3 commits to **rewriting rules as first-class kernel
feature** (Cockx-Tabareau ICFP 2021).  Users declare rewrite rules
that extend definitional equality, admitted on confluence +
termination + linearity witnesses.

Apex rewriting generators:

```
| .gen_rewriteRule => RewriteRuleData
                      -- payload: pair of patterns (lhs, rhs) + linearity witness
```

`RewriteRuleData` carries:

```
structure RewriteRuleData where
  lhsPattern : Pattern
  rhsPattern : Pattern
  linearityWitness : IsLinear lhsPattern
  confluenceWitness : ProfileConfluent (extendWith lhs rhs)
  terminationWitness : ProfileTerminating (extendWith lhs rhs)
```

Each rule's admission requires:

* **Confluence witness** — the new TRS remains confluent.
* **Termination witness** — the new TRS remains terminating (per
  §11.7.2's `TotalityClass` constraint).
* **Linearity witness** — patterns are linear (Cockx-Tabareau §3).

When admitted, the rule joins the kernel's definitional equality.
Strictly more powerful than fixed reduction rules: users extend
the kernel's notion of computation per-profile, with decidable
admission (each witness is decidable per §11.8.7).

`gen_rewriteRule` is `cellSort := .term`, `cellDimension := 0`,
`totalityClass := .total` (rules must witness termination),
`consistencyStrength := inherited from base profile`.

#### 3.16.10 dProp + internal computational reflection (Phase Z₈)

§11.8.3 commits to **decidable propositions universe** `dProp`
where every inhabitant carries its own decision procedure (Pédrot-
Tabareau LICS 2018).  Markov's principle holds internally; outside
`dProp` the system remains constructive.

Apex `dProp` generators:

```
| .gen_dProp     => Unit                   -- universe of decidable propositions
| .gen_dPropDec  => Unit                   -- the embedded decider: dProp → Bool
| .gen_dPropOfDecidable => Unit            -- inject Decidable P into dProp
```

`ChildSpec` lists:

| Generator | Arity | ChildSpecs | binderShifts |
|---|---|---|---|
| `gen_dProp` | 0 | `[]` | `[]` |
| `gen_dPropDec` | 1 | `[{ .term, 0, 0 }]` | `[0]` |
| `gen_dPropOfDecidable` | 1 | `[{ .term, 0, 0 }]` | `[0]` |

`cellSort := .type` for `gen_dProp`, `.term` for the others.
`totalityClass := .total`.  `consistencyStrength := .predicative`.

#### 3.16.11 MTT mode-theory generators (Phase Z₈)

§11.8.6 commits to **Multi-Modal Type Theory (MTT)** at the apex
modal layer (Gratzer-Sterling-Sterling LICS 2020).  Modes form a
2-category; modalities are 1-cells; modal types `⟨μ | A⟩` shift
types between modes.

Apex MTT generators (per mode):

```
-- One Generator per admitted mode in the mode theory
| .gen_mode (modeTag : ModeTag) => Unit          -- mode declaration
-- Modal intro/elim, parameterized by modality
| .gen_modIntro (mu : Modality) => Unit          -- ⟨μ | A⟩ introduction
| .gen_modElim  (mu : Modality) => Unit          -- ⟨μ | A⟩ elimination
| .gen_modCompose => Unit                         -- modality composition: μ ⊕ ν
| .gen_modAdjUnit (adj : AdjunctionWitness) => Unit -- η of an adjunction
| .gen_modAdjCounit (adj : AdjunctionWitness) => Unit -- ε of an adjunction
| .gen_modDRAEval => Unit                         -- dependent right adjoint eval
```

`ChildSpec` lists vary per modality (different modalities have
different arities — a left adjoint takes 1 child, a right adjoint
takes 1, a triple `♭ ⊣ ◇ ⊣ ♯` takes 3 components).  The template:

| Generator | Typical arity | ChildSpec template |
|---|---|---|
| `gen_modIntro μ` | 1 | `[{ .term, 0, <mode-shift> }]` |
| `gen_modElim μ` | 1 | `[{ .term, 0, 0 }]` |
| `gen_modCompose` | 2 | `[{ .term, 0, 0 }, { .term, 0, 0 }]` |

The mode-theory's 2-category itself is **rigid** (no non-trivial
2-isomorphisms between 1-cells, per §3.13's three restrictions),
which makes MTT conversion decidable in polynomial time by
Gratzer's universal recipe.  Decidability witness lives in §11.8.7
as `Decidable (MTTModalityCompose mod1 mod2)`.

#### 3.16.12 Cohesion + differential cohesion (Phase Z₈)

§11.8.6 commits to the full **cohesive adjoint triple** ♭ ⊣ ◇ ⊣ □
⊣ ♯ (Shulman 2018, Myers-Riley) plus **differential cohesion**
Π ⊣ ♭_inf ⊣ ♯_inf ⊣ ʃ_inf (Schreiber 2013).

Apex cohesion generators:

```
-- Cohesive modalities
| .gen_shape         => Unit  -- ʃ (shape): ∫ ⊣ ♭
| .gen_flat          => Unit  -- ♭ (flat / discrete)
| .gen_sharp         => Unit  -- ♯ (sharp / codiscrete)
| .gen_cohesiveUnit  => Unit  -- adjunction unit per cohesive focus
-- Differential cohesion
| .gen_reduced       => Unit  -- ℜ (reduced / underlying)
| .gen_infinitesimal => Unit  -- ℑ (infinitesimal shape)
| .gen_etale         => Unit  -- &  (étale / formally étale)
```

`ChildSpec` lists: each cohesive / differential modality is
unary, accepting one term-child at the parent scope.

| Generator | Arity | ChildSpecs | binderShifts |
|---|---|---|---|
| `gen_shape` | 1 | `[{ .type, 0, 0 }]` | `[0]` |
| `gen_flat` | 1 | `[{ .type, 0, 0 }]` | `[0]` |
| `gen_sharp` | 1 | `[{ .type, 0, 0 }]` | `[0]` |
| `gen_cohesiveUnit` | 1 | `[{ .term, 0, 0 }]` | `[0]` |
| `gen_reduced` | 1 | `[{ .type, 0, 0 }]` | `[0]` |
| `gen_infinitesimal` | 1 | `[{ .type, 0, 0 }]` | `[0]` |
| `gen_etale` | 1 | `[{ .type, 0, 0 }]` | `[0]` |

All cohesion / differential-cohesion generators: `cellSort :=
.type`, `cellDimension := 0`, `totalityClass := .total`,
`consistencyStrength := .predicative`.

#### 3.16.13 Algebraic effects + handlers (Phase Z₈)

§11.8.6 commits to **algebraic effects with handlers** as first-
class kernel feature (Plotkin-Pretnar ESOP 2009).

Apex algebraic-effect generators:

```
| .gen_effectOp      => EffectOpSignature   -- algebraic effect operation
| .gen_effectHandler => HandlerData          -- handler implementing an effect
| .gen_effectScope   => Unit                 -- delimited continuation scope
| .gen_effectResume  => Unit                 -- continuation resumption
| .gen_effectFinally => Unit                 -- handler finally-clause
```

`EffectOpSignature`:

```
structure EffectOpSignature where
  opName       : Name
  paramTypes   : List Ty
  returnType   : Ty
  effectLabel  : EffectLabel
```

`ChildSpec` lists:

| Generator | Arity | ChildSpecs | binderShifts |
|---|---|---|---|
| `gen_effectOp` | <varies by op signature> | per-op | per-op |
| `gen_effectHandler` | 2 + #ops | `[{ .term, 0, 0 }, { .term, 0, 1 }, ...]` | `[0, 1, ...]` |
| `gen_effectScope` | 1 | `[{ .term, 0, 0 }]` | `[0]` |
| `gen_effectResume` | 1 | `[{ .term, 0, 0 }]` | `[0]` |
| `gen_effectFinally` | 2 | `[{ .term, 0, 0 }, { .term, 0, 1 }]` | `[0, 1]` |

Sound by Plotkin-Pretnar + Bauer-Pretnar.  Decidable typechecking
preserved.  Adds ~5K LoC.  `cellSort := .term`, `cellDimension :=
0`, `totalityClass := varies per effect`, `consistencyStrength
:= .predicative`.

#### 3.16.14 Synthetic mathematics layer (Phase Z₈+, profile-level)

§11.8.6 commits to **synthetic mathematics frameworks** as PROFILE-
LEVEL capabilities, NOT kernel-level Generators.  Each synthetic-math
framework is a `ProfileExtension` (§3.14) admitted with a `Bilax
Compatible` witness and a `ProfileCapabilities` record:

| Framework | Profile capability | Reference | LoC est |
|---|---|---|---|
| ∞-topos internal language | `fxInfinityToposProfile` | Shulman 2019 + Lurie HTT | ~30K |
| Stable homotopy / synthetic spectra | `fxSpectraProfile` | Krause 2025 | ~15K |
| Synthetic Lie groups + smooth manifolds | `fxSmoothProfile` | Kock SDG | ~10K |
| Synthetic algebraic geometry | `fxAlgGeomProfile` | Cherubini-Coquand-Geuvers-Hou-Mörtberg 2024 | ~20K |
| Synthetic quantum types | `fxQuantumProfile` | Coecke-Selinger / Heunen-Vicary | ~15K |
| Synthetic measure + probability | `fxMeasureProfile` | synthetic-probability literature | ~12K |
| Synthetic Markov categories | `fxMarkovProfile` | Fritz 2020 | ~8K |
| Synthetic differential cohomology | `fxDiffCohomologyProfile` | Schreiber 2013 | ~25K |
| Synthetic computability theory | `fxComputabilityProfile` | Bauer 2006 (effective topos as profile) | ~10K |
| Synthetic stable ∞-categories | `fxStableInfinityProfile` | Riehl-Verity ∞-cosmoi | ~20K |

Each profile uses the SAME `PolyCell` substrate but with a profile-
specific `SemanticallySupportedGenerator` admission table — the
generators are kernel-level but their admission predicates are
profile-level.  Profiles form a 2-category (geometric morphisms
between profiles), and profile-of-profiles is admissible (§3.8
self-referential profiles via Uemura ∞-type theories).

#### 3.16.15 Z₉ verified internal SMT engine generators (optional, deferred)

§11.8.11 commits to building a **fully-verified internal SMT
engine** as Phase Z₉ if and when a concrete profile-level need
emerges.  Z₉ is OPTIONAL — the per-theory internal deciders of
§11.8.7 cover most needs.  When Z₉ ships, it adds the following
generators:

```
| .gen_smtSatCert       => SATCertificate
                          -- verified DRAT certificate for a SAT instance
| .gen_smtTheoryCert (theoryTag : TheoryTag) => TheoryCertificate
                          -- per-theory certificate (linear arithmetic, BV,
                          --  congruence closure, ...)
| .gen_smtNelsonOppen   => CombinationCertificate
                          -- Nelson-Oppen combination certificate
| .gen_smtUnsatCore     => UnsatCoreData
                          -- minimal unsatisfiability core
| .gen_smtModel         => ModelData
                          -- explicit model when SAT
| .gen_smtProofTerm     => ProofTerm
                          -- replayable proof term in the kernel
```

Each generator carries a CERTIFICATE that the kernel verifies — no
trust placed in the SMT engine beyond the verifier's check.  ~10K
LoC.  `cellSort := .term`, `cellDimension := 0`, `totalityClass :=
.total`, `consistencyStrength := inherited from base profile`.

This is the **closed-system mandate** (§11.8.11) operationalized:
SMT-level reasoning happens INSIDE FX with verified deciders; no
external Z3 / CVC5 calls; no trust on external software.

#### 3.16.16 ChildSpec extensions: motive / dependent / interval children

The current `ChildSpec` record is:

```
structure ChildSpec where
  cellSort : CellSort
  cellDimension : CellDim
  scopeShift : Nat
  deriving DecidableEq
```

The apex commitments require three extensions to this template,
captured as `ChildSpec` field options or as separate ChildSpec
variants:

* **Motive children.**  Dependent eliminators carry a motive child
  whose `cellSort := .type`, `cellDimension := 0`, `scopeShift := <
  binder-count-of-the-eliminated-type >`.  No new field — motive
  children are just ChildSpec values with `.type` sort and the
  appropriate binder shift.  Pure refactor.

* **Cubical interval children.**  Cubical Kan ops (transp, hcomp,
  glue) bind interval variables `i : 𝕀`, not term variables.
  Modeled as `ChildSpec { .term, 0, intervalShift }` where
  `intervalShift` is the interval-variable count, with the
  interpretation handled at admission time (the typechecker treats
  these binders as living in the interval pre-type per CCHM).

* **Clock children.**  Multi-clock guarded generators bind clock
  variables.  Modeled as `ChildSpec { .term, 0, clockShift }` with
  clock-context interpretation at admission time.

No structural change to `ChildSpec` itself — the apex commitments
reuse the existing record by interpreting `scopeShift` polymorphically
across term / interval / clock binders.  The `binderShifts` list per
generator stays a `List Nat` (just `scopeShift` values).

#### 3.16.17 Payload type extensions

Current `Generator.payload : Generator → Nat → Type` maps each
Generator to its payload type at a given scope.  The apex
commitments add the following payload types:

* `LevelExpr` (universe-mode generators, §3.16.3).
* `UniverseFlag` (universe-mode generators, §3.16.3).
* `LiftDirection` (lift / lower generators, §3.16.3).
* `FaceFormula` (cubical face generators, §3.16.4).
* `Generator.Kind` (HIT kind tag, §3.16.5).
* `HITSignature` / `HITPathDecl` (general-HIT framework, §3.16.5).
* `RewriteRuleData` (first-class rewriting, §3.16.9).
* `ModeTag` / `Modality` / `AdjunctionWitness` (MTT, §3.16.11).
* `EffectOpSignature` / `HandlerData` (algebraic effects, §3.16.13).
* `SATCertificate` / `TheoryCertificate` / etc. (Z₉ SMT engine,
  §3.16.15).

Each payload type ships with:

* `DecidableEq` (structural).
* A `Generator.payloadValid` predicate (decidable) that checks the
  payload's well-formedness at admission time.
* Serialization to `List Nat` (for the FX0-PolyCell certificate
  format, §12.6.4) via a per-payload serializer.

The closed-enum payload types (`UniverseFlag`, `Generator.Kind`,
`LiftDirection`) auto-derive `DecidableEq`.  The structural ones
(`LevelExpr`, `FaceFormula`, `RewriteRuleData`, `EffectOpSignature`)
need hand-rolled propext-free `DecidableEq` per the project
`feedback_lean_zero_axiom_match` discipline.

#### 3.16.18 Trust stratification per generator

Per §11.7's foundational-boundary mechanisms, each Generator
carries three additional metadata fields:

* `totalityClass : TotalityClass` (§11.7.2: `total` / `productive`
  / `partial`).
* `consistencyStrength : ConsistencyStrength` (§11.7.1:
  `finitistic` / `predicative` / `impredicative` / `inaccessible`
  / `mahlo` / `custom`).
* `siteOpenness : SiteOpenness` (§11.7.3: `sealed` / `extensible`
  / `reflective` / `oracle`).

For the apex generator additions:

| Family | `totalityClass` | `consistencyStrength` | `siteOpenness` |
|---|---|---|---|
| Universe modes (§3.16.3) | `.total` | per-flag reflection degree (predicative → `kunenI0` ESR apex; `reinhardtOpen` for the open tail) | `.sealed` |
| Cubical CCHM (§3.16.4) | `.total` | `.predicative` | `.sealed` |
| HIT + QIIT (§3.16.5) | `.total` (for ctors), `.total` (for recs) | `.predicative` | `.sealed` |
| HIIRT eliminators (§3.16.6) | `.total` | per-type-former | `.sealed` |
| Multi-clock guarded (§3.16.7) | `.productive` | `.predicative` | `.sealed` |
| Internal parametricity (§3.16.8) | `.total` | `.predicative` | `.sealed` |
| Rewriting rules (§3.16.9) | `.total` (admission requires termination witness) | inherited | `.extensible` |
| dProp (§3.16.10) | `.total` | `.predicative` | `.sealed` |
| MTT modal (§3.16.11) | varies per mode | `.predicative` | `.sealed` |
| Cohesion (§3.16.12) | `.total` | `.predicative` | `.sealed` |
| Algebraic effects (§3.16.13) | varies per effect | `.predicative` | `.sealed` |
| Synthetic math (§3.16.14) | varies per framework | varies per framework | `.sealed` |
| Verified SMT (§3.16.15) | `.total` | inherited | `.sealed` |

These three metadata fields enforce the structural soundness
contracts at admission time — a `partial` Generator cannot be the
child of a `total` parent; a `vopenka`-strength Generator cannot
ship in a profile claiming `predicative` strength; an `oracle`
Generator cannot ship in a `sealed` profile.

#### 3.16.19 Migration discipline: how the table grows without cascade

The 194-entry table grows to ~400-500 entries by MILESTONE D.  The
discipline that keeps cascade-tax at zero:

1. **No new `RawTerm` constructors.**  Every apex addition is a
   new Generator enum value plus its metadata.  `RawTerm` stays
   the one-`mkGen`-ctor inductive shipped at V2-L0.6.
2. **No new `PolyCell` constructors** (except `horizontalComposite`
   under §11.6.5's staged Gray-tensor admission).  The certified
   inductive stays the four-ctor shape (`gen` / `generatingCell` /
   `verticalComposite` / `identityCell`) shipped at V2-L1c.4-7.
3. **No new traversal operations.**  `rename` + `subst` (and
   future ops like `eval`, `nbe`, `quote`) remain ONE-line `fold`
   instantiations.  The fold engine's shift-polymorphism (V2-fix-8
   smoke) handles any binder shape.
4. **Per-generator admission proofs.**  Each new Generator's
   `SemanticallySupportedGenerator` arm ships a constructive
   admission witness — typically a few lines per generator citing
   the published theory.
5. **Per-family metatheory inheritance.**  When a family closes
   (e.g., HITs at Z₅), the family's metatheory (canonicity for
   HIT-introduced types, eta-equivalence for HIT eliminators,
   cubical Kan-fillness for HIT path constructors) ships ONCE as
   a family-level theorem, NOT per-generator.

This discipline is the **cascade-death principle** at apex scale:
the engine grows linearly in Generator count, not quadratically in
(Generator × consumer) pairs.

#### 3.16.20 Audit gates for each apex phase

Each phase Zₙ adds audit gates that verify the family's
zero-axiom + closed-system + complexity-bound discipline.

| Phase | Audit gates added | What they verify |
|---|---|---|
| Z₀ | `STRICT-Z0-MOTIVE` | Every eliminator's spine carries a motive child at the correct binder shift; pre-Z₀ shapes flagged. |
| Z₁ | `STRICT-Z1-TYPED` | Every typed-core generator has a `HasType` rule with proper inversion lemmas. |
| Z₂ | `STRICT-Z2-CANONICITY` | Every closed inhabitant of a canonical type reduces to a constructor. |
| Z₃ | `STRICT-Z3-DECIDABLE-CONV` | Typed Conv decision procedure ships with a `Complexity` witness. |
| Z₄ | `STRICT-Z4-CUBICAL` | Every cubical Kan op has a defining reduction rule. |
| Z₅ | `STRICT-Z5-HIT` | Every HIT family ships path constructor + recursor + iota rule + cubical Kan witness. |
| Z₆ | `STRICT-Z6-HIIRT` | Every IR / HIIRT family has a Setzer-form admission witness with proof-theoretic strength tag. |
| Z₇ | `STRICT-Z7-GUARDED` | Every multi-clock generator has a productivity witness. |
| Z₈ | `STRICT-Z8-21DIM` | Every dimension d ∈ {2,…,21} ships a typing judgment with decidable typechecking. |
| Z₉ | `STRICT-Z9-SMT` | Every SMT certificate has an in-kernel verifier that accepts iff the certificate is sound. |

Plus uniform gates that span all phases:

* `STRICT-TC` (per §11.7.5) — TotalityClass constraints on
  Generator children.
* `STRICT-CS` (per §11.7.5) — ConsistencyStrength monotone through
  ProfileExtension chain.
* `STRICT-SO` (per §11.7.5) — SiteOpenness compatibility on
  extension admission.
* `STRICT-COMPLEXITY` (per §11.8.7) — every `Decidable` instance
  ships with a verified complexity bound.

These gates LIVE under `LeanFX2/Tools/AuditAll/AuditPolyCell.lean`
+ family-specific audit files (per the existing AuditPolyCell
convention).  Each new Generator addition adds its
`#assert_no_axioms` entry; each new admission witness adds its
`STRICT-*` family gate entry; each new complexity bound adds its
`STRICT-COMPLEXITY` entry.

The audit harness is the **mechanized enforcement** of the apex
commitments: a Generator addition that violates any of these gates
is REJECTED by the build — not as a warning, as a hard fail.

---

## 4. The raw/certified PolyCell signature

After the thirteen profile axes are defined, the trusted kernel surface
has two layers.  The **v2 structural re-foundation** (shipped 2026-05-27
per V2-mig.18 final audit + ef079829 v1 retirement) fixes their shape;
v1's dim-indexed `PolyTerm` (sentinel-payload atoms + per-fixture
certified constructors) is **DELETED** — what remains is the v2
substrate as the SOLE canonical kernel surface.  Historical v1 work
(TCB.4–TCB.8) survives only as commit-log entries in §10's POLY-TCB
ledger.

1.  Raw syntax is **un-indexed by dimension** and split in two:
    `RawTerm scope` (the term layer — one `mkGen generator payload
    children` constructor, scope-indexed, with structural children) and
    `RawCell scope` (the categorical cell layer — `termBase`,
    `generatingCell`, `verticalComposite`, `horizontalComposite`,
    `identityCell`).  Dimension is a **computed** function
    `RawCell.dim`, never a type index.  The layer is deliberately
    permissive: imported data, broken generator ids, wrong arity, bad
    sort choices, dim-mismatched composites, and future `compH`
    experiments are all representable so the checker can say
    `false` / `none` / `rejected reason`.
2.  `PolyCell π sort dim scope boundary raw` is certified syntax.  It
    is indexed by the raw cell it certifies, and its constructors are
    the only trusted introduction rules.  Ill-sorted, ill-scoped, or
    boundary-incompatible cells are unconstructable at this layer.  The
    per-feature term constructors collapse to **one** generic `gen`
    constructor parameterized by the generator table.

**Why un-indexed raw is the keystone (the highest-ROI decision).**  A
*permissive* raw layer must not enforce dimension at the type level —
its whole job is to represent nonsense the checker rejects.  Every
propext-leak fought through TCB.7/TCB.8 (the dual `(dim, rawCell)`
match, the partial constructor enum at `dim + 1`, the dim-1 dispatcher)
traces to dim being a type index.  Computing dim instead of indexing it
dissolves the entire leak class, and lets the raw layer represent (and
the checker reject) a dim-mismatched `verticalComposite` that the v1
type made unconstructable.  Indexing stays where it belongs: the
certified `PolyCell`.

**Why one generic `gen` constructor is the cascade-death mechanism.**
`Generator` + `binderShifts` is an Allais "universe of syntaxes with
binding" descriptor (U20, `arXiv:2001.11001`).  ONE structural fold
`RawTerm.fold` over that descriptor yields `rename` and `subst` as
single generic instances — collapsing the 5–8K-LoC per-constructor
rename/subst commute cascade (§3.11) to instances of three monad laws.
The certifier, `cd_lemma`, and decidable `Conv` recurse once over the
same structure, so adding a feature is one `Generator` value plus one
`SupportedGenerator` arm — never a new raw constructor and never a
per-ctor proof cascade.  This is the concrete mechanism behind §2.1's
"feature constructors move into generator metadata."

This mirrors the existing kernel pattern:

```lean
RawTerm scope                         -- permissive-ish syntax
Term ctx type raw                     -- intrinsic typed certificate

RawTerm scope                       -- permissive term layer (scope-indexed)
RawCell scope                       -- permissive cell layer (dim COMPUTED)
PolyCell profile sort dim scope b raw -- intrinsic certified cell
```

The profile-extension calculus (§3.14) lives over admissible profiles;
it is not another constructor family inside the raw layer.

The Lean block below shows the SHIPPED v2 substrate shape (modulo
late-binding axis-7 / axis-9 / etc. structures still under construction
per §10 phasing).  Each invariant is audited; the dim-indexed v1
`PolyTerm` proving ground (sentinel-payload atoms + five per-fixture
certified constructors) is **DELETED** per commit ef079829 (V2-mig.18
final audit), its convergence theorems were ported to v2 before
deletion, and its commit history lives in §10's POLY-TCB ledger as
historical record only.

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

/-- Raw term layer (v2).  Scope-indexed, NOT dim-indexed.  One generic
`mkGen` constructor over the `Generator` enum — an Allais
universe-of-syntaxes descriptor (`arXiv:2001.11001`): `payload` carries
only local scalar data (a `Fin scope` de Bruijn index for `var`, a level
`Nat` for the universe code, `Unit` otherwise), and `children` are
STRUCTURAL sub-terms whose binders are tracked by
`generator.binderShifts` (a binder child's head lives at
`scope + shift`).  Nested terms are representable directly; there are no
sentinel payloads and no hand-written child decoders. -/
mutual
  inductive RawTerm : Nat → Type where
    | mkGen :
        {scope : Nat} →
        (generator : Generator) →
        (payload : generator.payload scope) →
        (children : RawTermChildren generator.binderShifts scope) →
        RawTerm scope
  inductive RawTermChildren : List Nat → Nat → Type where
    | childNil :
        {scope : Nat} → RawTermChildren [] scope
    | childCons :
        {scope shift : Nat} → {restShifts : List Nat} →
        RawTerm (scope + shift) →
        RawTermChildren restShifts scope →
        RawTermChildren (shift :: restShifts) scope
end

/-- Raw cell layer (v2).  Scope-indexed only; dimension is COMPUTED by
`RawCell.dim`, never a type index.  This is the keystone: a permissive
raw layer must not enforce dim at the type level, and removing the index
dissolves the propext-leak class fought through TCB.7/TCB.8 (the dual
`(dim, rawCell)` match, the partial ctor enum at `dim + 1`, the dim-1
dispatcher).  The term layer embeds at dimension 0 via `termBase`; a
dim-mismatched `verticalComposite` is now representable (and rejected by
the certifier) rather than unconstructable. -/
inductive RawCell : Nat → Type where
  | termBase :
      {scope : Nat} → RawTerm scope → RawCell scope
  | generatingCell :
      {scope : Nat} → (ruleId : Nat) →
      RawCell scope → RawCell scope → RawCell scope
  | verticalComposite :
      {scope : Nat} → RawCell scope → RawCell scope → RawCell scope
  | horizontalComposite :
      {scope : Nat} → RawCell scope → RawCell scope → RawCell scope
  | identityCell :
      {scope : Nat} → RawCell scope → RawCell scope

/-- Dimension recovered structurally (matches the cell ALONE, the
propext-clean shape; total; no `termination_by`). -/
def RawCell.dim {scope : Nat} : RawCell scope → CellDim
  | .termBase _                 => 0
  | .generatingCell _ source _  => source.dim + 1
  | .verticalComposite first _  => first.dim
  | .horizontalComposite left _ => left.dim
  | .identityCell base          => base.dim + 1

-- v1 PolyTerm proving ground RETIRED 2026-05-27 (ef079829).  The
-- dim-indexed `PolyTerm profile : Nat -> Type` with sentinel-payload
-- atoms is DELETED; its convergence theorems were ported to v2 before
-- removal.  Historical record in §10's POLY-TCB ledger (TCB.4–TCB.8).

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
Higher boundaries are raw source/target endpoint cells; constructors and
the checker separately require endpoint certificates before producing a
`PolyCell` over those raw endpoints. -/
def CellBoundary (profile : PolyProfile) :
    CellSort → CellDim → Nat → Type
  | _, 0, _ => Unit
  | _, _ + 1, scope =>
      RawCell scope × RawCell scope

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

/-- Raw child descriptor used by the certifier's child-spine
reconciliation.

This records the shape claimed for a child.  It does not certify the
child: the stored raw cell is only a permissive `RawCell` at the
declared scope. -/
structure RawChildDescriptor (profile : PolyProfile)
    (cellSort : CellSort) (cellDimension : CellDim) (scope : Nat) where
  rawCell : RawCell scope

/-- Decoder output for a generator is a child spine whose carrier is raw
descriptors, not certified cells. -/
def RawChildDescriptors (profile : PolyProfile) (parentScope : Nat)
    (childSpecs : List ChildSpec) : Type :=
  CellChildren (RawChildDescriptor profile) parentScope childSpecs

/-- Generic generator metadata (shipped V2-L1.1–L1.9).  `SupportedGenerator
(generator : Generator)` admits a generator to the certified layer — ONE
arm per supported feature, never a new `PolyCell` constructor;
`generatorCellSort : Generator → CellSort` and `generatorChildSpecs :
Generator → List ChildSpec` derive the cell sort and child-spine spec
(scope shifts = `generator.binderShifts`); `GenPayloadEvidence generator
scope payload` discharges the local payload (`var`'s `index < scope` is
structural via the `Fin scope` payload); `CertifiedTermSpine
profile specs scope children` is the certified child spine (the
carrier-parametric `CellChildren` / `CertifiedChildSpineForRawDescriptors`
instantiated to certified cells); `HasEqualDim source target` is the
value-level endpoint-dimension reconciliation, decided by `Nat.decEq` on
the computed `RawCell.dim`.

The v1 sentinel-payload tables (`SupportedGeneratorSpec`,
`SupportedRuleSpec`, `AtomPayloadEvidence`, plus the
`lambdaUnitTypeBodyVarZeroPayload` / `applicationVarZeroVarOnePayload` /
`piTypeUnitCodomainUnitPayload` Nat constants used as fixture sentinels)
were DELETED with v1 in commit ef079829.  They are not listed here.
The 194-Generator table (`Generator.binderShifts`, `Generator.payload`,
`Generator.arity`) plus `SupportedGenerator` / `GenPayloadEvidence`
above subsumes the entire v1 per-fixture admission surface. -/

/-- Certified cell syntax.  The trusted layer, indexed by the raw
`RawCell` it certifies, so erasure back to raw is definitional.  Per-
feature term constructors collapse to ONE generic `gen` constructor
over the 194-Generator table.

There is deliberately no certified `horizontalComposite` constructor
until the Gray tensor boundary formula and disjoint-footprint/matching
condition are mechanized.  Raw `RawCell.horizontalComposite` remains
available as input data; the checker rejects it as `unsupportedCompH`. -/
inductive PolyCell (profile : PolyProfile) :
    (sort : CellSort) →
    (dim : CellDim) →
    (scope : Nat) →
    CellBoundary profile sort dim scope →
    RawCell scope →
    Type where

  -- ONE generic certified term-generator constructor.  `supported`
  -- admits the generator (a `SupportedGenerator` arm — adding a
  -- feature is one new arm); `payloadEvidence` discharges the local
  -- payload; `childSpine` certifies the structural children against the
  -- generator's `childSpecs` (scope shifts = `binderShifts`).  Subsumes
  -- every v1 per-fixture term constructor.
  | gen :
      {scope : Nat} → {generator : Generator} →
      {payload : generator.payload scope} →
      {children : RawTermChildren generator.binderShifts scope} →
      SupportedGenerator generator →
      GenPayloadEvidence generator scope payload →
      CertifiedTermSpine profile (generatorChildSpecs generator) scope children →
      PolyCell profile (generatorCellSort generator) 0 scope ()
        (.termBase (.mkGen generator payload children))

  -- Certified generating cell (dim n+1) over two certified endpoints of
  -- EQUAL computed dimension, reconciled against a supported rule.
  | generatingCell :
      {scope : Nat} → (rule : RuleSpec) →
      SupportedRuleSpec rule →
      {source target : RawCell scope} →
      {sourceBoundary targetBoundary :
        CellBoundary profile rule.cellSort source.dim scope} →
      HasEqualDim source target →
      PolyCell profile rule.cellSort source.dim scope sourceBoundary source →
      PolyCell profile rule.cellSort source.dim scope targetBoundary target →
      PolyCell profile rule.cellSort (source.dim + 1) scope
        (source, target)
        (.generatingCell rule.ruleId source target)

  -- Certified vertical composite: same sort, shared middle endpoint
  -- decided by the propext-free `DecidableEq (RawCell)`.
  | verticalComposite :
      {sort : CellSort} → {dim scope : Nat} →
      {source middle target : RawCell scope} →
      {firstRaw secondRaw : RawCell scope} →
      PolyCell profile sort (dim + 1) scope (source, middle) firstRaw →
      PolyCell profile sort (dim + 1) scope (middle, target) secondRaw →
      PolyCell profile sort (dim + 1) scope
        (source, target)
        (.verticalComposite firstRaw secondRaw)

  -- Certified identity (degenerate) over any certified base.
  | identityCell :
      {sort : CellSort} → {dim scope : Nat} →
      {boundary : CellBoundary profile sort dim scope} →
      {baseRaw : RawCell scope} →
      PolyCell profile sort dim scope boundary baseRaw →
      PolyCell profile sort (dim + 1) scope
        (baseRaw, baseRaw)
        (.identityCell baseRaw)
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
  | fuelExhausted

/-- Infer a certified package from raw input.

The v2 certifier is `certifyRawCellExact?` (raw-indexed, returning a
certificate over the EXACT input `RawCell`) with `inferRawCellGeneral?`
its existential wrapper.  ONE structural recursion over `RawCell`
certifies the entire non-`horizontalComposite` fragment at every
dimension; `horizontalComposite` rejects as `unsupportedCompH` pending
Gray semantics.  The propext-leak that blocked the dim-indexed v1
dispatcher (TCB.7d/7f) is gone by construction: there is no dim type
index to force a `(dim, rawCell)` match, and endpoint-dimension
reconciliation is value-level (`Nat.decEq` on `RawCell.dim`).

v1 `inferRawCell?` / `checkRawCellAs?` over the dim-indexed `PolyTerm`
(TCB.6j–TCB.8) were RETIRED with v1 in commit ef079829.  The TCB.8
convergence theorems established v1↔general-certifier agreement on the
shared fragment BEFORE deletion; no coverage was lost at the cutover. -/
structure CertifiedRawCellResult (profile : PolyProfile) (scope : Nat) where
  cellDimension : CellDim
  inputCode : List Nat
  rawCell : RawCell scope
  cellSort : CellSort
  cellBoundary : CellBoundary profile cellSort cellDimension scope
  certifiedCell :
    PolyCell profile cellSort cellDimension scope cellBoundary rawCell
  hasInputCode :
    hasSameNatList inputCode (rawCellCode rawCell) = true

def certifyRawCellExact? {profile : PolyProfile} (scope : Nat)
    (raw : RawCell scope) :
    Except CellCheckRejection
      (CertifiedRawCell profile scope raw) := ...

def inferRawCellGeneral? {profile : PolyProfile} (scope : Nat)
    (raw : RawCell scope) :
    Except CellCheckRejection
      (CertifiedRawCellResult profile scope) := ...

/-- Check raw input against an expected certified shape.

`wrongSort` is a rejection of this expected-shape checker.  Bare inference
has no external sort expectation, so it fails with generator, payload, child,
boundary, or unsupported-certification reasons instead. -/
def checkRawCellAs? {profile : PolyProfile}
    (expectedSort : CellSort) (expectedScope : Nat)
    (raw : RawCell expectedScope) :
    Except CellCheckRejection
      (CertifiedRawCellResult profile expectedScope) := ...

end LeanFX2.Foundation.PolyCell.Core
```

Feature operations are **not** raw constructors.  Universe
cells, cumulativity, Π/Σ, modalities, cubical paths, `transp`, `hcomp`,
HIT eliminators, probability, quantum, SDG, and every future feature
are entries in `π.algebra.bases` with payload/output/compatibility
tables.  Thinness is also **not** a constructor.  `FXConv` is a
certified dim-1 cell plus a decidable/Prop thinness certificate on that
certified cell's raw erasure; raw thinness facts are usable only under
an existing certified step/cell.

The raw layer is two inductives: `RawTerm` (one generic `mkGen`
constructor over the `Generator` table, structural children) and
`RawCell` (five structural constructors `termBase`, `generatingCell`,
`verticalComposite`, `horizontalComposite`, `identityCell`, dimension
computed not indexed).  The certified `PolyCell` layer exposes ONE
generic `gen` term constructor plus `generatingCell`,
`verticalComposite`, and `identityCell`; certified `horizontalComposite`
is blocked until Axis 6 has real Gray boundary semantics.  Compared to
the current 75-ctor `Term` + 100+-ctor `Step` + 100+-ctor `cd_lemma`,
this is a ~50× reduction in inductive surface area and, more
importantly, new features add one `Generator` value, never a raw or
certified constructor.

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
| fuelled checker recursion budget is exhausted | reject `fuelExhausted` |

**Negative probes.**  The checker must be developed against a concrete
catalog of malformed raw inputs, not only against positive examples:

- unknown atom ids must reject as `unknownGenerator`;
- variable atoms whose payload is outside the expected scope must reject
  as `badPayload`;
- known generators with reserved malformed payloads must reject as
  `badPayload`, `wrongArity`, or `wrongChildShape`;
- supported-but-uncertified pi-type and context-extension generator
  sentinels must reject as `badPayload`, `wrongArity`, or
  `wrongChildShape` until their decoders have certified child spines;
- nullary type/context/mode atoms with nonzero payloads must reject as
  `badPayload`;
- finite non-nullary payload decoders must first return
  `RawChildDescriptors`, then recursively screen each decoded child
  against the generator's declared child shape; for the first
  application fixture, `app(var 0, var 1)` may screen as a term shape,
  while applications whose function or argument child decodes to a
  type/context/mode cell, or whose decoded argument is outside scope,
  must reject as `wrongChildShape`;
- application payload sentinels must exercise the application decoder
  branch itself: undecodable payloads reject as `badPayload`,
  wrong-arity sentinels as `wrongArity`, and wrong-child-shape
  sentinels as `wrongChildShape`;
- current certified ingress accepts the structurally screened
  `app(var 0, var 1)` fixture only after the payload decoder and generic
  child-shape screen succeed and only when `var 0` and `var 1` are both
  certifiable in the same scope; scope 0 and scope 1 reject as
  `wrongChildShape`, and malformed application payloads preserve the
  specific decoder rejection they trigger;
- the first certified dim-1 fixture is the structural term cell
  `termStep(var 0, var 1)` only, built directly from certified endpoints
  after endpoint screening; the arbitrary positive-dimensional raw
  dispatcher is not part of the TCB until it can be implemented without a
  trust escape;
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
- screened positive-dimensional raw cells outside the current certified
  constructor domain must remain uncertified and reject through the
  certification-stage policy as `unsupportedCertification`;
- raw vertical composites of identity cells over seed term/type/context/mode
  cells must screen successfully with their respective sort, but still
  reject through certification-stage policy as `unsupportedCertification`;
  the derived certified vertical-composition helper is the only certified
  path for those shapes until a real raw `compV` ingress dispatcher exists;
- derived certified identity cells are allowed only from an already
  certified base package; raw identity over a malformed base must reject
  through the base screen and raw identity ingress remains unsupported
  unless a later exact constructor path is added;
- raw horizontal composites must reject as `unsupportedCompH` until
  Axis 6 supplies certified Gray-boundary semantics, including
  `compH` over otherwise well-screened operands;
- a fuelled checker call with an exhausted recursion budget must reject
  as `fuelExhausted`, not as malformed payload data; these probes live in
  their own fuel-budget family because ordinary negative probes use the
  default checker fuel;
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
The hostile probe catalog is now maintained through rejection-family
partitions with audited headline theorems: all bad-payload probes reject
as `badPayload`, all wrong-arity probes as `wrongArity`, all
wrong-child-shape probes as `wrongChildShape`, all bad-endpoint probes as
`badBoundaryEndpoint`, all unsupported-Gray probes as
`unsupportedCompH`, and all screen-passing but uncertified
positive-dimensional probes as `unsupportedCertification`.  Fuel-budget
probes form a separate exact family that rejects as `fuelExhausted`.
These headline theorems are derived from the existing executable screen and
certification-policy checks; they do not replace the hostile fixtures or
weaken per-probe diagnostics.

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
    -- The polynomial monad whose generators ARE the unified 194-entry
    -- `Generator` table (`GeneratorCore.lean`, gen_var →
    -- gen_processCalc) — ONE enum the certifier / fold / cd_lemma /
    -- Conv recurse over uniformly, growing to ~400–500 entries at
    -- MILESTONE D (§3.16) by entry addition, never by inductive
    -- cascade.  Dimension is structural (`RawCell.dim`), not a
    -- constructor partition:
    -- dim 0: term/type/context/mode generators (var, lam, app, lamPi,
    --        pair, fst, snd, boolElim, natElim, …, transp, hcomp,
    --        idJ, idStrictRec, modIntro, modElim, subsume, the
    --        universe-code + type-code family, …)
    -- dim 1: generating cells (β, η, ι, cubical-β, modal-β, …)
    -- dim 2: cd_lemma confluence fillers (ONE generic theorem, §11.6.1)
    -- dim 3: Squier coherence cells (critical-pair quadruples)
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

/-- Raw FX cell input (v2): the scope-indexed `RawCell` layer.  This is
not a kernel certificate.  `RawCell` is profile-agnostic — the
generator table lives in the certified `PolyCell` over `fxProfile`. -/
def FXRawCell := RawCell

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
def FXContext (scope : Nat) (raw : FXRawCell scope) :=
  PolyCell fxProfile .context 0 scope () raw

/-- Certified type cell. -/
def FXType (scope : Nat) (raw : FXRawCell scope) :=
  PolyCell fxProfile .type 0 scope () raw

/-- Certified term cell.  The eventual typed bridge refines this with a
context cell and a type cell, exactly like `Term ctx type raw`. -/
def FXTerm (scope : Nat) (raw : FXRawCell scope) :=
  PolyCell fxProfile .term 0 scope () raw

/-- Certified generating step or vertical composite over one sort.
Raw horizontal composition is rejected until Axis 6 certifies it.  Raw
endpoints and the dim-1 raw cell are all `RawCell scope`; dimension is
the certified index, not a raw type index. -/
def FXStep (sort : CellSort) (scope : Nat)
    (source target : FXRawCell scope) (raw : FXRawCell scope) :=
  PolyCell fxProfile sort 1 scope (source, target) raw

/-- Certified conversion is a certified dim-1 cell plus a thinness
certificate on that certified cell's raw erasure. -/
def FXConv (sort : CellSort) (scope : Nat)
    (source target : FXRawCell scope) (raw : FXRawCell scope) :=
  { cell : FXStep sort scope source target raw //
      fxProfile.stratification.thin 1 raw = true }

/-- Certified confluence filler. -/
def FXCdLemma (sort : CellSort) (scope : Nat)
    (source target : FXRawCell scope) (raw : FXRawCell scope) :=
  PolyCell fxProfile sort 2 scope (source, target) raw

end LeanFX2
```

**The foundational reading — every structural rule is a morphism, at
its sort.**  `FXStep`, `FXConv`, and `FXCdLemma` are each parameterized
by `sort : CellSort`, so a *morphism* (a dim-1 cell) is generic over all
seven sorts at once.  This is not incidental — it is the statement that
**the structural rules of all 21 dimensions ARE cells**: a dim-1 cell at
`.term` is a β/ι/η reduction; at `.type` it is a univalence /
cumulativity path (DIRECTED — the universe is an (∞,ω)-category, §5.1
c=1, not a groupoid); at `.context` it is a substitution / weakening
(the CwF base-category morphism, §3.11); at `.grade` it is a subgrading
`r ≤ s`; at `.mode` an MTT modality (§3.13); at `.protocol` session
subtyping / duality (§11.2).  Three structural facts follow, and they are
the seat of the §11.9 Internalization Program:

* **Equality is the marking, uniformly.**  `FXConv sort` is exactly *a
  dim-1 cell whose raw erasure is thin* (the saturation, §3.3–§3.4).  So
  Conv (terms), univalence (types), bisimulation (protocols), and
  contextual equivalence are the *same construction* — "a thin cell at
  that sort" — the sameness-unification conjecture (§11.9.3 OP3).
* **Substitution is a 1-cell; the substitution lemma is whiskering.**  A
  `.context` morphism horizontally composed (Gray, §3.6) with a `.term`
  morphism IS "the substitution acts on the reduction"
  (`t[σ] ↝ t'[σ]`); the cell-level substitution obligation (§11.6.2) is
  exactly this whiskering.  The frame rule (§2.4) is the same
  `horizontalComposite` on disjoint footprints.
* **The cross-sort interaction laws are fillers, and their obstructions
  are computable.**  Where two sorts' cells fail to admit an interchange
  filler is a soundness collision; the cohomology of those obstructions
  classifies which dimension subsets compose (§11.9.1.1 O-OBSTRUCT).

This is the load-bearing conceptual link from the cell substrate to the
internalization program: the kernel does not *encode* the 21 dimensions
beside a term calculus — each dimension's structural relation is a
morphism in one polygraph, and §11.9 internalizes the *meta*-quantities
(complexity, proof-simplicity, entropy, ordinal strength) the same way.

This means the existing 80+ kernel files become **view definitions**
over the certified cell layer, not independent inductives and not raw
subtypes of Nat-coded cells.  All cascade work disappears only after
the certified checker and the legacy round-trip bridge are real.

### 5.1 Profile restriction & scope boundaries

FX is ONE profile, grown by the extension calculus (§3.14).  The
inverse direction — and the deliberate non-goals — are recorded here
so they are conscious decisions, not silent gaps.

* **Restriction / slicing (the FX0 minimal-trust dial).**  A
  `ProfileLens.forget` (§3.14) drops generators, yielding *sub*-profiles:
  an MLTT slice (Π/Σ/Id, no cubical/modal/graded), a cubical-only
  slice, a constant-time-only slice.  Library authors and the
  FX0-PolyCell verifier (§12.6) pick the **lowest sufficient**
  sub-profile — the smallest sound kernel for a workload — rather
  than carrying the whole apex.  This is the surviving, honest form of
  the old "(n,p,k,c) parameter dial": restriction by lens-forget, not
  by a parameter record.

* **Categorification depth — two levels committed; only the
  open-ended tower is out of scope.**  Categorification level (the
  old `c`) is NOT a user-facing dial like n/p/k — but it is not
  vacuous either, and "drop it entirely" was wrong.  FX commits to,
  and already USES, two levels:
  - **c = 1 — object theory:** types as (∞,ω)-categories
    (`gen_universeOmega`, directed univalence).  Directedness is
    itself a categorification commitment — the universe is an
    (∞,ω)-CATEGORY, not a symmetric ∞-groupoid.
  - **c = 2 — metatheory:** FX's own metatheory provably lives one
    level up, in the 2-category of models / profiles.  Load-bearing
    and already in use, merely unnamed: Tier 0's bi-initial model
    (§3.0.1), the cellular tensor universal property (§3.0.7), the
    profile fibration (§3.8), BKS sconing in the presheaf topos
    (§11.8.0), and profile-of-profiles (§3.16.14) are all c = 2.
    Today c = 2 is AMBIENT (proven in Lean about FX); INTERNALIZING it
    (FX reasoning about its own profiles inside FX) is the
    Self-Hosting Kernel FX meta-profile (§3.15).  So the
    categorification ladder is the formal measure of **self-hosting /
    metatheory-internalization depth**, not idle tower-climbing.
  Out of scope (genuinely): the open-ended `c → ω` tower as a SINGLE
  Lean object (predicativity blocks a universe of all categorification
  levels at once), and `c` as a user-facing dial — users do not pick a
  categorification level, it is an architecture fact.  What survives as
  the committed core: a fixed object level + a fixed metatheory level
  (ambient now, self-hosted later).

  **A door left open — c ≥ 3 (meta-metatheory) is not empty, and we
  decline to close it.**  Tagging it "speculative" would be the same
  glib error as dismissing c = 2: two pieces of structure FX already
  commits to live one level higher than c = 2.
  - The structural-reflection ladder (§11.8.2) is, strictly, a c = 3
    phenomenon.  Bagaria structural reflection is a property OF the
    c = 2 category of models — "every proper class of structures has a
    small reflecting subfamily" quantifies over that whole category, so
    the statement lives one level up.  The apex's `kunenI0`-via-ESR is
    thus a c = 3 commitment wearing a c = 2 admission predicate; the
    door is already ajar.
  - The Gödel-climbing tower (§11.7.1: rung n+1 proves `Con`(rung n))
    is an iterated meta-hierarchy — FX-metatheory about FX-metatheory
    about … — the meta-metatheory tower under another name.

  The examination-worthy question (the funny space): are the
  categorification-depth tower (`c`) and the consistency-strength
  ladder (§11.8.2) the SAME tower seen two ways?  Iterating "internalize
  my own metatheory" cannot reach a fixed point at or below FX's
  strength ceiling — Gödel II forbids a kernel that fully describes its
  own metatheory at its own strength — so the c-tower, exactly like the
  reflection ladder, must climb strictly rather than collapse.  Whether
  it converges (a stabilization-hypothesis-style question — does
  categorifying enough times stop producing genuinely-new structure?)
  or climbs to `kunenI0` and halts, is open.  Left open for
  examination, not closed: a fixed object level and a fixed metatheory
  level are what the kernel BUILDS; c ≥ 3 is where the kernel's own
  reflection apex already secretly reasons, kept on the books as an
  honest frontier rather than erased.

* **Incrementality is a daemon concern, not a kernel dimension.**
  Incremental re-checking (re-verify only edited regions — load-bearing
  for the agentic-LLM iteration loop) lives in the compiler daemon
  (fx_design §24's warm-recheck), NOT as a kernel grade dimension.  The
  earlier dim-24 ILC change-calculus (`ΔA` / `Df`) is out of the 21-dim
  kernel; the 21 dims are canonical (§11.8.6).

* **E-graphs are outside-kernel search.**  Equality saturation (egg)
  is the canonical search strategy for the agent / optimizer layer —
  it *proposes* rewrites that the kernel *verifies* via `Conv`.  It is
  the operational dual of the kernel's congruence closure (`Conv` +
  `Conv.ofChildren` + cd_lemma), not a kernel encoding column.

* **Hardware / physics verticals.**  RTL/Verilog, multi-level
  Maxwell→μArch, side-channel typing beyond the Security+Observability
  dims + CT effect, synthetic physics — all live as §3.15
  `ProfileExtension`s with their own future product docs, never as
  kernel obligations here.

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
| P0.1 Step.eta | **Committed in two layers**: raw structural eta will ship in the current M8 cascade as a sibling relation `Step.eta`, with binder eta guarded by `RawTerm.strengthen`; typed eta remains the type-directed eta-long NbE/readback layer.  Long-term, eta rules are still profile metadata, but the current SN/CR route must see raw eta explicitly before the master theorem closes. |
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

**Eta correction (May 2026):** the previous "Step.eta is only a
Generator value" wording was too aggressive for the current proof
frontier.  We are now committed to BOTH flavors:

* raw `Step.eta` as a sibling relation beside the existing step
  relation, for structural eta rules that can be recognized without
  typing (`lam/app`, `pair/fst/snd`, path/modal/clock/param/glue cases
  as their generators land);
* typed eta-long NbE/readback for genuinely type-directed eta,
  especially Unit eta, which is incoherent as an untyped raw rewrite.

The task ledger records this as `#350`-`#358` for the raw eta cascade
(`RawTerm.strengthen`, `Step.eta`, SR/CR/SN/audit gates) and
`#359`-`#364` for typed eta-long NbE and typed beta+eta conversion.
This placement is intentional: raw eta lands before the final SN/CR
closure so the master theorem covers beta+iota+eta from the start.
The raw `Step.eta` module only declares constructors for generators
that exist in the current `Generator` enum.  Clock and parametricity
eta remain reserved until Phase Z7/Z8 extends the generator table with
`gen_clockAbs`/`gen_clockApp` and `gen_paramAbs`/`gen_paramApp`;
those slots must not be simulated by unrelated generators.

Current shipped eta slice: `#350` adds the raw strengthening
substrate, `#351` adds the current-generator raw `Step.eta` sibling
relation, and `#352` adds audited subject-reduction arms for the
structural eta sources that need no freshness side condition:
`pair (fst p) (snd p)`, `modIntro (modElim m)`, and
`glueIntro (glueElim g) g`.  `#353` adds audited
subject-reduction arms for the current binder eta sources:
`lam (app (weaken f) newestVar)` and
`pathLam (pathApp (weaken p) newestVar)`.  The binder proof projects
the certified weakened child, then cancels the weakening by singleton
substitution (`weaken_subst_singleton`), avoiding any inverse-renamer
assumption.  `#354` adds the beta+iota/eta subject-reduction umbrella:
`Step.eta.preservesShape` dispatches over the five current eta
constructors, and `Step.betaEta.preservesShape` keeps the legacy
beta+iota `Step.preservesShape` theorem unchanged while exposing the
opt-in union needed by the upcoming CR/SN eta tasks.  The first `#355`
slice adds the betaEta local-join target and embeds the shipped
beta+iota `cd_lemma` into it.  It also records a formal frontier fact:
current root eta heads are `gen_lam`, `gen_pair`, `gen_pathLam`,
`gen_modIntro`, and `gen_glueIntro`, while beta's root head is
`gen_app`; therefore the current one-step relation has no same-root
beta/eta overlap.  The same slice starts the real eta-root versus
beta+iota-congruence work with audited eta-pair diamonds for reducing
inside the `fst p` or `snd p` occurrence before contracting
`pair (fst p) (snd p)`.  The next #355 slice extends that same
current-generator family to `modIntro (modElim m)` and both Glue
occurrences in `glueIntro (glueElim g) g`, again as explicit audited
betaEta joins.  The next binder slice adds a one-step weakening replay
lemma and audited `lam`/`pathLam` joins for congruence steps that come
from an actual source-level step in the underlying function/path term.
It also adds resolver-facing strengthened variants: if an arbitrary
under-binder reduct strengthens back to a source-scope reduct and the
corresponding source-level step is supplied, the betaEta join follows.
The latest #355 slice proves the source-step half of that inversion:
`Step.weaken_substTarget` replays any step out of `weaken source` at
source scope by substituting canonical `unit` for the fresh variable.
The `lam` and `pathLam` strengthened resolver wrappers now need only
the freshness/strengthening witness for the arbitrary under-binder
reduct; the corresponding source-level step is derived internally.
The next lifted-binder substrate slice adds
`RawTerm.strengthen_iterateLiftRaw_weaken`,
`RawTerm.strengthen_iterateLiftRaw_sound`, children-spine
strengthening siblings, lifted singleton-substitution cancellation
for terms and children, and `StepChildren.weaken_substTarget`.  This
is the binder-depth substrate needed for the congruence case of the
freshness inversion, where the target step may occur inside a child
spine under additional binders.  The following root-case subslice
isolates `RawTerm.weaken_subst0` and
`RawTerm.strengthen_weakened_subst0`: a beta contractum of a weakened
redex is itself a weakening, and strengthening it recovers the
source-scope contractum.  The latest #355 slice folds the root-case and
child-spine ingredients into the freshness inversion:
`Step.preserves_isFreshFor` proves every beta+iota step preserves an
arbitrary substitution/renaming retraction, and
`Step.weaken_strengthenTarget` specializes it to arbitrary reducts of
`weaken source`.  The binder betaEta resolver wrappers
`etaLamArbitraryUnderBinderCong` and
`etaPathLamArbitraryUnderBinderCong` now consume only the under-binder
step; strengthening and the source-level replay step are derived
internally.  The next #355 slice closes the eta-pair projection-iota
overlaps explicitly: `etaPairFirstProjectionIota` and
`etaPairSecondProjectionIota` join
`pair (fst (pair a b)) (snd (pair a b))` against root eta-pair, and
`etaPairLeftStep` / `etaPairRightStep` package every beta+iota `Step`
leaving an eta-pair source into one resolver-facing arm.  The following
#355 slice does the same packaging for the remaining structural
non-binder eta roots: `etaModIntroLeftStep` / `etaModIntroRightStep`
and `etaGlueIntroLeftStep` / `etaGlueIntroRightStep` cover every
beta+iota `Step` leaving the current modal and Glue eta sources.
The final #355 slice wires the binder roots and mixed dispatcher:
`RawTerm.weaken_lam`,
`RawTerm.weaken_eq_lam_implies_source_lam`, and
`RawTerm.subst0_lift_weaken_newestVar` isolate the eta-lambda root
beta overlap, `etaLamLeftStep` / `etaLamRightStep` and
`etaPathLamLeftStep` / `etaPathLamRightStep` package every beta+iota
`Step` leaving the current binder eta sources, and
`cd_lemma_step_eta` / `cd_lemma_eta_step` prove the mixed
beta+iota-vs-root-eta local Church-Rosser quadrants for every current
eta constructor.  This completes #355's honest boundary.  #356 then
closes the eta-vs-eta quadrant in
`StepEtaEtaCriticalPairs.lean`: because the current `Step.eta`
relation is root-only and has no eta congruence constructor, nested
eta examples are not one-step branchings yet.  The shipped theorem
`Step.eta.deterministic` proves two root eta steps from the same source
have the same reduct, `cd_lemma_eta_eta` closes the eta/eta local join,
and `cd_lemma_betaEta` now inhabits the full
`CdLemmaStatementBetaEta` for the current beta+iota+root-eta relation.
The first #357 slice adds the honest conditional Newman bridge in
`StepBetaEtaConfluence.lean`: `Step.betaEtaStar.Join`,
`Step.betaEtaStar.HasConfluence`,
`Step.betaEtaStar.IsStronglyNormalizing`, and
`Step.betaEtaStar.confluence_of_strongNormalization` mirror the
beta+iota-only bridge but consume the shipped `cd_lemma_betaEta`
dispatcher.  This is deliberately not a claim of global beta+eta SN:
the theorem is conditional on a future
`Step.betaEtaStar.HasStrongNormalization` witness, and the actual SN
accessibility lifts remain blocked behind #258's unfinished master SN
work.  The second #357 slice adds the eta-only SN substrate in
`StrongNormalizationEta.lean`: renaming and weakening preserve
`RawTerm.size`, every current root eta constructor strictly decreases
that size, and `Step.etaStar.hasStrongNormalization` follows by
well-foundedness of the size measure.  This closes eta-only
accessibility; it still does not prove the beta+iota-to-betaEta SN
transfer needed for unconditional beta+eta confluence.  Record, clock,
and parametricity eta remain generator-frontier work, not placeholders
in the current raw relation.

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
| P2.4 PolyTerm intrinsic mirror | **Reframed**: the raw layer (`RawTerm`/`RawCell`) stays permissive; certified `PolyCell` is the intrinsic mirror. |
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
| P3.4 PolyStep dim-1 generators | **Subsumed**: dim-1 certified cells over raw `RawCell` endpoints. |
| P3.5 PolyStep.cd / cd_lemma generic | **Subsumed after proof**: cd_lemma is the per-profile theorem at dim 2 once saturation supplies the certified fillers. |
| P3.6/P3.7 RawValueTerm / ValueTerm | **Subsumed**: values are normal-form predicates on `RawTerm`. |
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
| P5.2 EGraph extraction | **Subsumed after certification**: quotient certified cells by generated congruence; raw `RawCell` alone is not enough. |

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
| `Foundation/Polygraph/RawPolyTermFlat.lean` | 316 | Revived as `RawTerm` — the canonical scope-indexed structural raw term layer (v2); `RawCell` wraps it for the categorical cell structure at all dims |

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

Plus the ~207K thirteen-axis + Tier-0 substrate (§9) and the ~63K
Phase-Z apex, minus the ~40K of deleted existing code: the net code
base after PolyCell migration lands near **~230K LoC** (§9) — larger
than the ~140K current kernel, but with **drastically better
extensibility**, structural soundness, and capability surface, and
with the per-ctor cascade tax structurally eliminated.

---

## 9. LoC budget

Honest accounting per axis:

Per-axis figures track each §3.x section's estimate; the budget spans
all thirteen axes + the Tier-0 meta-framework + the extension calculus
(§3.14) + the §11.8 maximal-power apex layer.

| Axis / layer | Lean LoC (gross) | Has Lean precedent? |
|---|---|---|
| 0 — Tier-0 meta-framework (Uemura RMC + BKS sconing + Fire Triangle) | ~12K | None — first Lean port |
| 0 — §3.0.7 PolyCell Cellular Tensor (FX-original target) | ~5K | None — FX-original |
| 1 — Shape category catalogue (Hadzihasanovic RDC) | ~8K | Partial: globular yes; opetopic/Steiner no |
| 2 — Polynomial-universe algebra | ~6K | Agda (Aberlé-Spivak); not for Glob_∞ |
| 3 — Verity stratification | ~5K | None |
| 4 — Saturation (cubical coherent confluence) | ~7K | None |
| 5 — Enrichment ladder (synthetic Segal/Rezk) | ~3K | Partial Segal in Mathlib |
| 6 — Complicial Gray module (Stage 1 shipped + Stage 2) | ~16K | Coq (Maltsiniotis-Métayer, strict only) |
| 7 — ∞-Topos base (Dugger presentation + doctrine stack) | ~30K | Lurie HTT not Lean-formalized |
| 8 — Profile fibration (Cisinski ω-loc via Beke-Smith) | ~10K | None |
| 9 — ωcE classifier + Makkai/Forest word problem | ~5K | None |
| 10 — Univalent universe (poly-universe + Step.eqType) | ~6K | Cubical Agda (∞,1); (∞,ω) no |
| 11 — Single-substitution calculus backbone | ~7K | Agda (Kaposi-Xie); none in Lean |
| 12 — Synthetic Tait computability classifier | ~8K | Istari only; none in Lean |
| 13 — MTT normalization gateway | ~12K | None (Menkar prototype only) |
| 14 — Profile extension calculus (§3.14) | ~7K | Agda (Aberlé); none in Lean |
| — PolyCell raw/certified core | ~15K | None for this design |
| — fxProfile instance | ~20K | — |
| — FX kernel migration | ~25K | — |
| **THIRTEEN-AXIS + TIER-0 SUBSTRATE** | **~207K gross** | **First-ever (∞,ω) mechanization** |
| Phase-Z maximal-power apex (Z₀–Z₈, §11.8.9) | ~53K | None |
| Phase Z₉ verified internal SMT (optional) | ~10K | None |
| **FULL MAXIMAL-POWER APEX KERNEL** | **~270K gross / ~230K net** | **Strongest decidable-typechecking kernel ever attempted** |

Net of the §8 migration deletions (~40K) and the §7 cascade-
obsolescence collapse, the full apex kernel lands near **~230K net**,
matching the §11.8.9 apex figure.  Of this, **~25K is already in
place**: the PolyCell substrate (RawTerm / RawCell / PolyCell +
194-`Generator` table + certifier + Allais fold) plus the reducibility
+ strengthening foundation.

Comparison points:
- Current FX kernel (Lean): ~140K LoC — the v2 substrate is folded in
- Lean 4 stdlib: ~280K LoC
- Mathlib4: ~1.5M LoC (a LIBRARY of theorems, not one sound kernel)
- HoTT-Coq library: ~30K LoC of Coq (mostly (∞,1))
- Cubical Agda library: ~50K LoC of Agda

No prior artifact is simultaneously a SINGLE sound kernel, at this
scope, AND at this expressive ceiling.  The ~270K is a 2–4 year
project (faster with collaborators), and it is the FULL commitment —
not a tradeoff to weigh.  It buys, together, the first mechanization
of (∞,ω)-categories in any proof assistant AND the strongest sound
type theory with decidable typechecking ever shipped (§11.8).

For comparison with the abandoned path:
- Old accelerate-* cascade roadmap: ~135K LoC over ~12 months — and it
  scaled LINEARLY per new ctor; the cascade tax never amortized.
- PolyCell apex: ~270K LoC over ~24–48 months — but the substrate is a
  ONE-TIME cost, after which every future feature (probability, SDG,
  quantum, distributed, …) is ONE Generator entry + admission witness.
  The break-even crosses early; thereafter expansion is unbounded.

---

## 10. Phased rollout

Realistic ship plan in dependency order.

### Phase POLY-TCB — raw/certified trust boundary (immediate, ~4K NEW LoC)

**Goal:** stop treating Nat-coded raw cells as trusted kernel
inhabitants.  Keep the raw layer permissive, then introduce a
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
| TCB.3c negative probes | `a3b729bb` | Hostile raw fixtures cover the current rejection reasons and are audited as data before checker theorems claim anything. |
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
| TCB.7f first certified dim-1 term cell | `d4829833` | The first positive-dimensional certified inhabitant is the structural term cell `termStep(var 0, var 1)`, built only from certified `var 0` and `var 1` endpoints after endpoint screening.  A dimension-polymorphic dispatcher over arbitrary raw dim-1 cells was tried and rejected because it pulled in `propext`; the committed path keeps only the direct fixture ingress plus certification-stage negative probes. |
| TCB.7g derived certified identity cells | `1b346406` | Certified identity cells are now derived from already certified base packages and exposed through certified FX views for seed term/type/context/mode cells plus the seed dim-1 term-step.  No raw identity dispatcher is added. |
| TCB.7h expanded hostile rejection probes | `d647fada` | The negative catalog now covers application decoder sentinels, pi/context-cons sentinels, malformed identity bases, unsupported term-step variants, and well-screened `compH`.  Probe counts are ratcheted and every new rejection is audited. |
| TCB.7i headline negative-probe theorems | `178b3cfa` | The negative catalog is partitioned by rejection family, with audited headline theorems for each inference, expected-shape, and certification-policy family.  Global probe counts are still ratcheted through the family lists. |
| TCB.7j derived certified vertical composites | `3875a56b` | Certified vertical composition is now exposed only over already certified cells whose middle endpoint is definitionally shared.  A seed term-identity composite is available as a certified FX dim-1 term view; arbitrary raw `compV` ingress remains unsupported. |
| TCB.7k certified endpoint projections | `0a98af8d` | Certified positive-dimensional FX cells now expose source and target raw endpoints through their intrinsic boundary index.  Seed step, identity, and vertical-composite endpoint theorems are audited and definitional. |
| TCB.7l structural thinness seed | `b3e745f3` | Certified thinness is now an intrinsic predicate generated only by identity cells and vertical composition of already thin cells.  Thin FX views exist for seed identities and the seed identity composite; arbitrary generating steps are not thin. |
| TCB.7m endpoint-indexed certified arrows | `6d666e98` | Certified positive-dimensional FX arrows now carry source and target endpoints in the view type itself.  Vertical composition requires a definitionally shared middle endpoint, and thin arrows preserve the same endpoint discipline.  This is still structural: no legacy `Step`/`Conv` bridge, no raw dispatcher, and no generating-step thinness. |
| TCB.7n arrow endpoint theorem heads | `4673b627` | Certified and certified-thin arrows now have generic audited source/target theorems for identity and vertical composition.  These are theorem heads over already certified data, not new raw ingress or new thinness power. |
| TCB.7o multi-sort thin identity arrows | `b7b203f6` | Endpoint-indexed thin identity arrows are now exposed for the seed type, context, and mode cells, matching the existing term identity arrow discipline.  This confirms the certified view layer is not term-only; type/context/mode cells use the same endpoint-indexed substrate without any new raw ingress. |
| TCB.7p multi-sort thin identity composites | `bee8d7f1` | Endpoint-indexed thin composites of seed identity arrows are now exposed for type, context, and mode cells.  This mirrors the term identity composite through the generic thin-arrow `compV`, proving the multi-sort views share the same structural vertical-composition discipline. |
| TCB.7q derived application child spine | `0f6f3098` | The accepted `app(var 0, var 1)` child package no longer stores an independent certified child spine.  It derives the spine from the certified function and argument children and exposes a raw-descriptor erasure theorem showing the certified spine matches the decoded raw child descriptors.  No accepted raw inputs are broadened. |
| TCB.7r application child erasure theorems | `ef939560` | Certified child-spine erasure now preserves declared arity, and the certified `app(var 0, var 1)` child package is theorem-linked to the payload decoder output.  Certification followed by child-spine erasure returns the same raw descriptor spine as decoding for every scope where both variables are in scope. |
| TCB.7s descriptor-indexed certified child spines | `e97831e1` | `CertifiedChildForRawDescriptor` and `CertifiedChildSpineForRawDescriptors` index certified child evidence by the raw descriptor spine it certifies.  The first application child package now exposes a descriptor-indexed spine over the decoder output and forgets back to the ordinary certified child spine.  No equality-field trust, new constructor family, raw dispatcher, or new accepted payload is added. |
| TCB.7t descriptor spine erasure | `9c935bef` | Descriptor-indexed certified child evidence now erases back to exactly the raw descriptor it certifies, and descriptor-indexed certified spines erase back to exactly the raw descriptor spine they certify.  This is generic theorem-level glue only: no new raw dispatcher, constructor family, or accepted payload is added. |
| TCB.7u certified operational names | `1b87a346` | Certified generating term steps now have an endpoint-indexed view requiring raw erasure to be a single generating dim-1 cell, and structural conversions are named as the current certified-thin term arrows.  This adds operational names over existing certified arrows/thin arrows only: no raw dispatcher, no legacy `Step`/`Conv` bridge, no cd/coherence view, and no new accepted payload is added. |
| TCB.7v exact rejection family heads | `ca2b66bc` | Negative-probe headline theorems now bind each finite family to one exact rejection reason, instead of only checking each probe's stored expected reason.  This is a computable Bool-level theorem layer over the existing screens and certification policy; it adds no raw ingress, no new probes, no logical non-inhabitation claim, and no accepted payload. |
| TCB.7w certified result erasure | `456191da` | Certified raw-cell/result packages now expose audited theorem heads showing the carried `PolyCell` erases to the raw cell it certifies, and result input-code evidence is projected without trusting it for construction.  No raw ingress, no new probes, no new logical non-inhabitation claim, and no accepted payload is added. |
| TCB.7x exact probe-family coverage | `0b30c9fb` | Exact-reason negative-probe families now pass only when the family is nonempty and every probe rejects with the named reason.  This prevents empty-family theorem heads from passing vacuously while staying at the executable Bool-checker layer: no `False` theorem, no raw ingress, no new probes, and no accepted payload is added. |
| TCB.7y dim-two seed term arrow | `493ecacf` | The identity over the seed dim-1 term step is now exposed as endpoint-indexed dim-2 term arrow and thin-arrow views, with audited definitional raw/source/target theorems.  No checker change, raw ingress, new probe, certified constructor, or accepted payload is added. |
| TCB.7z rejection-reason coverage matrix | `aa34f94f` | Every `CellCheckRejection` constructor is now mapped to the exact nonempty negative-probe family or families that cover it, with an audited headline theorem over `CellCheckRejection.all`.  This is still executable checker coverage, not a `False` theorem or certified-cell non-inhabitation claim. |
| TCB.7aa accepted-ingress coverage matrix | `c4858ea1` | The current finite accepted ingress fixtures now have audited shape-coverage headlines: seed term/type/context/mode atoms, `app(var 0, var 1)`, and the direct `termStep(var 0, var 1)` path.  This adds no raw ingress, no accepted payload, no probe, no dispatcher, and no non-inhabitation claim. |
| TCB.7ab application expected-shape probes | `75d6d741` | Expected-shape hostile probes now cover the accepted application checked as type/context/mode, and preserve malformed application `badPayload`, `wrongArity`, and `wrongChildShape` rejections through `checkRawCellAs?`.  The rejection-reason coverage matrix now requires these expected-shape families where they exist. |
| TCB.7ac raw vertical identity probes | `a6d177b8` | Raw `compV` over two identity cells for seed term/type/context/mode now screens successfully by sort but rejects through certification policy as `unsupportedCertification`.  This pins the raw-ingress boundary: derived certified vertical composition over already certified identities remains valid, but no raw `compV` dispatcher, new certified constructor, accepted payload, or non-inhabitation claim is added. |
| TCB.7ad generator-spec ingress dispatch | `6b6386da` | `inferRawAtom?` now dispatches accepted atom ids through the audited generator-spec constants rather than magic numeric pattern arms, and nearby accepted-ingress theorem targets name the same constants.  This is a TCB readability/shrink refactor only: accepted raw inputs, rejected raw inputs, certified constructors, probe counts, and audit budgets are unchanged. |
| TCB.7ae fuel exhaustion rejection | `7b418b9b` | Fuel budget exhaustion is now its own structured checker rejection, `fuelExhausted`, instead of being conflated with `badPayload`.  A nonempty fuel-budget probe family and exact coverage matrix branch pin `screenRawCellWithFuel? 0`; no accepted raw inputs, certified constructors, or raw ingress paths are added. |
| TCB.7af supported generator lookup ratchet | `ab7b5d06` | Every currently supported dim-0 generator now has an audited definitional `lookupGeneratorSpec?` success theorem, including unsupported-but-screened lambda, pi-type, and context-cons generators.  This is table-coverage evidence only: no accepted raw inputs, certified constructors, or checker branches are added. |
| TCB.7ag accepted ingress screen coverage | `ef259a8d` | Every current finite accepted ingress fixture now has audited executable coverage that the accepted result shape agrees with the expected structural screen.  This adds no raw ingress, accepted payload, certified constructor, non-inhabitation theorem, or raw-code preservation claim beyond the separate generic erasure/input-code evidence. |
| TCB.7ah term-step input-code coverage | `25b890c7` | The direct positive-dimensional `termStep(var 0, var 1)` accepted ingress now has an audited executable prefix-code coverage theorem tying the successful result's stored input code back to its raw input.  The generic certified-result theorem separately links stored input code to the returned raw cell.  This is fixture-level regression coverage only: it does not prove raw-code injectivity and does not add any dispatcher, accepted raw input, or certified constructor. |
| TCB.7ai accepted input-code coverage matrix | `5e71abad` | Input-code coverage now spans the current finite accepted fixture frontier: seed term/type/context/mode ingress, the accepted application certified package, and the direct term-step ingress.  The application case intentionally avoids full dispatcher normalization; existing accepted-ingress coverage still pins that the checker accepts the application fixture.  No raw ingress, payload, constructor, dispatcher, injectivity theorem, or non-inhabitation claim is added. |
| TCB.7bd lambda decoder staging | `d8ee29f8` | Lambda now has a decoder-only payload staging table with one well-shaped unit/body child spine and hostile context-domain, type-body, and binder-shifted out-of-scope body fixtures.  The child descriptor screen is audited, while raw ingress still rejects the staged lambda payload as `badPayload`; no certified lambda constructor or new accepted input is added. |
| TCB.7be pi-type decoder staging | `12ce9a88` | Pi-type now has a decoder-only payload staging table with one well-shaped unit-domain/unit-codomain child spine and hostile context-domain and term-codomain fixtures.  The child descriptor screen is audited, while raw ingress still rejects the staged pi-type payload as `badPayload`; no certified pi-type constructor or new accepted input is added. |
| TCB.7bf first certified pi-type payload | `99d659c7` | `Pi (_ : Unit). Unit` is the first non-nullary dim-0 type payload admitted to the certified layer.  It is built only from certified unit-type children at the parent scope and binder-extended scope.  Hostile pi-type payloads with context-domain or term-codomain children still reject by computation, and checking the accepted pi-type as term/context/mode rejects as `wrongSort`.  This is not general pi-type certification. |
| TCB.7bg first certified lambda payload | `6778dece` | `lam (_ : Unit). var 0` is the first non-nullary lambda term payload admitted to the certified layer.  It is built only from a certified unit-type domain at the parent scope and a certified `var 0` body under the binder-extended scope.  Hostile lambda payloads with context-domain, type-body, or out-of-scope body children still reject by computation, and checking the accepted lambda as type/context/mode rejects as `wrongSort`.  This is not general lambda typing, beta, substitution, or context extension. |
| TCB.7bh certified lambda/pi FX views | `b2a5c8ea` | The FX-profile view layer now exposes certified views for the first lambda term payload and first pi-type payload, with audited raw-erasure theorem heads.  This is only naming over existing certified packages: no new payload, checker branch, raw dispatcher, operational typing theorem, or non-inhabitation theorem is added. |
| TCB.7bi lambda child decoder erasure links | `447fabcb` | The first certified lambda child package now has audited package raw-erasure, child-spine arity, raw-descriptor, and decoder-link theorem heads matching the application/pi pattern.  This is theorem-level regression coverage only: no new payload, checker branch, raw dispatcher, operational typing theorem, or non-inhabitation theorem is added. |
| TCB.7bj descriptor-indexed decoder erasure links | `dec2a809` | The descriptor-indexed application, lambda, and pi-type child spines now have audited theorem heads linking their erased raw descriptors to the corresponding payload decoder outputs.  This is theorem-level glue over existing certified packages only: no new payload, checker branch, raw dispatcher, operational typing theorem, or non-inhabitation theorem is added. |
| TCB.7bk pi input-code coverage name | `ffa5d018` | Pi-type input-code coverage now has the same named audited helper shape as application and lambda, and the stale atom-ingress comment now lists the current finite accepted fixtures.  This is proof/readability parity only: no new payload, checker branch, raw dispatcher, operational typing theorem, or non-inhabitation theorem is added. |
| TCB.7bl first certified context-extension payload | `c73494ac` | `ctxCons(empty, Unit, linear)` is the first non-nullary dim-0 context payload admitted to the certified layer.  It is built only from certified empty-context, unit-type, and linear-mode children at the parent scope.  Hostile context-extension payloads whose context/type/mode child has the wrong sort reject as `wrongChildShape`, and checking the accepted context extension as term/type/mode rejects as `wrongSort`.  This is not general context typing, weakening, substitution, raw context dispatch, or a non-inhabitation theorem. |
| TCB.8a general polymorphic raw-indexed certifier | `9ce59dfa` | `Foundation/PolyCell/Core/CertifyExact.lean`: `certifyRawCellExact?` is the first dimension-polymorphic recursive certifier — one function recursing over every `PolyTerm profile dim` and returning a certificate indexed by the EXACT input.  Covers all payload-evidenced atoms (via `certifyRawAtomExact?` with `cast`/`Eq.rec` id transport) plus iterated identities at every dimension; `inferRawCellGeneral?` wraps it into the existential result API.  **Resolves the long-standing propext blocker** of TCB.7d/7f: the leak was the dual `(dim, rawCell)` / partial-index match, not polymorphic recursion — matching on `rawCell` only (dim inferred) is the clean `retargetProfile` shape.  All `#assert_no_axioms` clean. |
| TCB.8b certify generating cells | `1aef8b31` | `certifyRawCellExact?` recurses on both endpoints of a raw `.cell` and reconciles against the term-step rule via `buildTermStepCellExact?` (`by_cases` Decidable + `subst`/`Eq.rec`, never a Nat-index match; the dim-0 `Unit` boundary makes the sort transport obligation-free). |
| TCB.8c propext-free `DecidableEq (PolyTerm)` | `9632db28` | `Foundation/PolyCell/Core/PolyTermDecEq.lean`: adapts the deprecated Burroni-`PolyCell` recipe (#1747) — `SuccShape` decomposition via pure `casesOn` + index-equality-witness motive, `.atom` discharged by `Nat.noConfusion`, transport casts in standalone `cast_*` lemmas.  Two `PolyTerm`-specific wrinkles: `compV`/`compH` compose same-dimension children so `decEq` recurses on `PolyTerm.size` (well-founded, not dim); and the size bounds use core `Nat` lemmas because `omega` itself pulled `propext`+`Quot.sound` into the decreasing proof.  `succShape`, `decEq`, `instDecidableEqPolyTerm` all `#assert_no_axioms` clean. |
| TCB.8d certify vertical composites | `6446a0aa` | `buildVerticalCompositeExact?` reconciles two certified positive-dim cells into a certified `compV`: same sort, and first-target = second-source decided via the propext-free `PolyTerm` `DecidableEq`; the boundary-pair transport is `▸` + structure eta.  `certifyRawCellExact?` now recurses on both `compV` operands.  The certifier is therefore **total on the entire non-`compH` raw fragment**; only `compH` rejects (`unsupportedCompH`), pending Gray semantics.  (compV result theorems are `#eval`-verified, not `rfl`, since `decEq` is well-founded; the defs are `#assert_no_axioms` clean.) |
| TCB.8e soundness + general FX ingress | `08e8edb5` | `certifyRawCellExact?_sound`: every accepted certification erases EXACTLY to its raw input (guaranteed by the raw-indexed type — no false positive is expressible).  `certifyRawCellExact?_compH_rejects` pins the only rejection class.  `FXProfile/CertifiedViews.lean` exposes the canonical general FX ingress `certifyFXCellExact?` (raw-indexed) / `certifyFXCell?` (existential), plus FX-level soundness and `compH`-rejection theorems. |

**Deliverables (NEW only):**

| Task | File(s) | Content | Acceptance |
|---|---|---|---|
| TCB.1 sort vocabulary | `Foundation/PolyCell/Core/CellSort.lean` | `CellSort` enum for `context`, `type`, `term`, `mode`, `effect`, `grade`, `protocol`; decidable equality; no semantics. | `#assert_no_axioms CellSort`; no `Inhabited`/`Classical`; audit gate added. |
| TCB.2 generator child specs | `Foundation/PolyCell/Core/GeneratorSpec.lean` | `ChildSpec`, `GeneratorSpec`, `RuleSpec`; scope shift separated from arity; first concrete specs for `var`, `lam`, `app`, `unitType`, `piTy`, `ctxEmpty`, `ctxCons`, `linearMode`, and the current dim-1 step-generator shell. | `lam` child table has type child at scope+0 and term body at scope+1; `piTy` codomain is type at scope+1; all facts are definitional or simple cases. |
| TCB.3 heterogeneous children | `Foundation/PolyCell/Core/CellChildren.lean` | `CellChildren (ChildCarrier : CellSort -> CellDim -> Nat -> Type) (parentScope : Nat) : List ChildSpec -> Type`; constructors force child sort/dim/scope from the spec list without depending on full `PolyCell` yet. | It is impossible to build a lambda body child at `.type` or at the wrong scope without a Lean type error; audit gate added. |
| TCB.3b raw child descriptors | `Foundation/PolyCell/Core/RawChildren.lean` | `RawChildDescriptor` and `RawChildDescriptors`; payload decoders can return shape-indexed raw children without certifying them. | Decoder output can record lambda/pi/context child shapes, but the carrier stores only permissive raw cells; no `PolyCell` is produced. |
| TCB.3c negative probes | `Foundation/PolyCell/Core/NegativeProbes.lean` | Concrete malformed raw cells plus expected rejection labels for the current `CellCheckRejection` cases. | Probe catalog is audited and nonempty; executable rejection claims live in `Check.lean`, not in the fixture file. |
| TCB.4 certified boundary layer | `Foundation/PolyCell/Core/Certified.lean` | `CellBoundary` and `PolyCell profile sort dim scope boundary raw` with constructors `atom`, `cell`, `compV`, `identity`; **no certified `compH`**; atom payload evidence currently certifies only in-scope variables, unit type, empty context, and linear mode. | Bad `compV` with mismatched middle endpoint has no constructor; raw `compH` has no certified introduction rule; out-of-scope variable payloads and nonzero unit/context/mode payloads have no `AtomPayloadEvidence` constructor. |
| TCB.5 raw rejection result | `Foundation/PolyCell/Core/CheckResult.lean` | Structured rejection enum, not just `Option`, so the checker can say which invariant failed. | Rejections distinguish unknown generator, wrong sort, bad payload, wrong arity, wrong child shape, bad boundary endpoint, bad vertical boundary, unsupported `compH`, unsupported certification, and fuel exhaustion. |
| TCB.6a executable rejection screen | `Foundation/PolyCell/Core/Check.lean` | Computable recursive screen over the supported generator/rule tables; rejects unknown ids, malformed payloads, wrong arity/child-shape sentinels, wrong expected sort, bad endpoints, bad vertical boundaries, and unsupported raw `compH`. | Every executable theorem is audited axiom-free; the catalog runner proves all current inference and expected-shape negative probes are rejected. |
| TCB.6h certified seed packages | `Foundation/PolyCell/Core/Check.lean` | `CertifiedRawCell` dependent package plus concrete packages for the payload-evidenced seed atoms only. | Each package erases definitionally to its named raw fixture; no application, lambda, pi, context-cons, generated cell, vertical composite, or raw `compH` is certified by this task. |
| TCB.6i expanded malformed probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean` | More hostile fixtures for application argument position, child scope failure, rule dimension misuse, and cross-sort expected-shape checks. | Probe counts are ratcheted; each new malformed input has a definitional rejection theorem and an audit harness assertion. |
| TCB.6j dim-0 certified ingress | `Foundation/PolyCell/Core/Check.lean` | Computable `inferRawCell?` and expected-shape `checkRawCellAs?` returning `CertifiedRawCellResult` or a rejection reason for dim-0 raw atoms, implemented without `propext`, `Classical`, `Inhabited`, or `Nonempty`. | Every accepted result contains a `PolyCell`; at this stage accepted witnesses were only in-scope variables, unit type, empty context, and linear mode.  Application certification starts later at TCB.7b. |
| TCB.7a certified seed views | `Foundation/PolyCell/FXProfile/CertifiedViews.lean` | `CertifiedFXCell` plus certified seed projections for context/type/term/mode over the current dim-0 ingress subset. | Every view carries an actual `PolyCell`; raw-erasure theorems are definitional; conversion/thinness and full step/coherence views remain unimplemented. |
| TCB.7b first certified application payload | `Foundation/PolyCell/Core/GeneratorSpec.lean`, `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean` | The finite payload `9100` is admitted as `app(var 0, var 1)` only through certified `var 0` and `var 1` child witnesses. | Scope 0/1 reject as `wrongChildShape`; type-as-function, type-as-argument, and out-of-scope application fixtures still reject; the accepted result and FX view erase definitionally to the raw fixture; all declarations are in `AuditPolyCell`. |
| TCB.7c certified application child decoder | `Foundation/PolyCell/Core/Check.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | `CertifiedApplicationVarZeroVarOneChildren` records the certified function child, certified argument child, and application child spine; `certifyApplicationVarZeroVarOneChildren?` is the computable ingress used by `inferRawAtom?`. | The app parent is built only from the certified child package; scope 0/1 reject before parent construction; expected-shape scope-1 rejection and child-spine arity are audited axiom-free. |
| TCB.7d screen-gated certified application ingress | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | The certified application ingress runs the payload decoder and generic `screenRawChildDescriptorsWith?` child-shape screen before building the parent certificate. | `LeanFX2.Tools.AuditAll` is green; no accepted payload is broadened; the direct dependent certified-child-spine route remains blocked until it can be implemented without `propext`. |
| TCB.7e hostile application child probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds mode/context-as-function and mode/context-as-argument malformed application payloads. | Probe count ratchets to 21 inference probes; each new malformed payload has decoder and rejection theorems under `AuditPolyCell`; `LeanFX2.Tools.AuditAll` is green. |
| TCB.7f first certified dim-1 term cell | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a direct certified package and FX view for the structural `termStep(var 0, var 1)` fixture; adds certification-stage negative probes for bad endpoints, unsupported raw `compH`, a screened but unsupported term step, and a screened but unsupported vertical composite. | The accepted dim-1 result carries an actual `PolyCell`; scope 1 rejects before endpoint construction; unsupported screen-passing dim-1 shapes reject as `unsupportedCertification`; no arbitrary dim-1 dispatcher is committed; `LeanFX2.Tools.AuditAll` is green. |
| TCB.7g derived certified identity cells | `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `identityCell` and `certifiedIdentityPackage`, deriving identity certificates only from already certified base cells. | Seed identity views erase definitionally to raw identity cells; malformed raw identity bases still reject through the screen; no raw identity ingress dispatcher is committed; `AuditPolyCell` keeps zero axiom and anti-vacuity budgets. |
| TCB.7h expanded hostile rejection probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds hostile application decoder sentinel probes, pi/context-cons payload sentinel probes, raw identity over malformed base, extra unsupported term-step variants, and `compH` over well-screened operands. | Inference probes ratchet to 32 and certification probes to 6; every new fixture has a definitional rejection theorem and an audit entry; malformed application sentinels preserve `badPayload`, `wrongArity`, or `wrongChildShape` precisely. |
| TCB.7i headline negative-probe theorems | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Groups inference, expected-shape, and certification probes by rejection family and adds audited headline theorems for each family. | Family counts plus global counts are ratcheted; the headline theorems are computable consequences of the existing checker runners and keep all hostile fixtures as regression data. |
| TCB.7j derived certified vertical composites | `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a certified vertical-composite helper and package over already certified cells whose shared middle endpoint is part of the type. | Raw erasure is definitional; the seed term identity composed with itself is exposed as a certified dim-1 term view; no equality casts or raw `compV` dispatcher are introduced. |
| TCB.7k certified endpoint projections | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `sourceRaw` and `targetRaw` projections for certified positive-dimensional FX cells. | Endpoint access reads only the existing `CellBoundary`; seed term-step, seed identities, dim-2 step identity, and seed vertical composite have audited definitional source/target theorems. |
| TCB.7l structural thinness seed | `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `PolyCell.ThinCell` with exactly two constructors: identity and vertical composition of thin cells.  Adds certified thin FX views for seed identities and the seed term identity composite. | No arbitrary generating step is classified thin; thin views still carry the underlying certified cell and audited definitional raw/source/target theorems. |
| TCB.7m endpoint-indexed certified arrows | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `CertifiedFXArrow` and `CertifiedFXThinArrow`, where the source and target endpoints are parameters of the view type. | Arrow identity and vertical composition erase definitionally to raw identity and raw `compV`; vertical composition type-checks only when the middle endpoint is shared; thin arrows compose only from thin arrows. |
| TCB.7n arrow endpoint theorem heads | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds generic theorem heads for source and target endpoints of certified-arrow identity and vertical composition, mirrored for certified thin arrows. | Every theorem is definitional and audit-gated; no new certified constructors, raw dispatchers, or operational classifications are added. |
| TCB.7o multi-sort thin identity arrows | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds type/context/mode endpoint-indexed arrow aliases and seed thin identity arrows with definitional raw/source/target theorems. | The new arrows are derived only from already certified seed cells and structural identity thinness; no checker acceptance domain changes. |
| TCB.7p multi-sort thin identity composites | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds type/context/mode endpoint-indexed thin composites by composing the corresponding seed thin identity arrows. | Raw/source/target theorems are definitional and audited; no raw `compV` dispatcher, checker broadening, or operational conversion predicate is added. |
| TCB.7q derived application child spine | `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Removes the stored `applicationChildSpine` field from the first certified application child package and derives it from `functionCell` and `argumentCell`.  Adds certified-child-spine erasure to `RawChildDescriptors`. | The package cannot carry certified children together with an unrelated child spine; the erasure theorem is definitional and audited; no new application payloads are accepted. |
| TCB.7r application child erasure theorems | `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds generic arity preservation for certified-child-spine erasure and theorem-level glue showing the accepted application child certificate erases back to the payload decoder's raw descriptors. | All theorems are audit-gated and definitional; this is not a new decoder, raw dispatcher, certified constructor, or accepted payload. |
| TCB.7s descriptor-indexed certified child spines | `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds descriptor-indexed certified children/spines where the certified cell raw index is the descriptor's raw cell.  The first application child package exposes this descriptor-indexed spine over the current decoder output. | The indexed spine forgets to ordinary certified children and preserves arity; it does not store a raw-equality proof field and does not broaden application ingress. |
| TCB.7t descriptor spine erasure | `Foundation/PolyCell/Core/Certified.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds generic erasure theorems for `CertifiedChildForRawDescriptor` and `CertifiedChildSpineForRawDescriptors`: forgetting descriptor-indexed evidence to ordinary certified children and then to raw descriptors returns the descriptor spine in the index. | Both theorems are audit-gated and structural; no equality-field trust, raw dispatcher, certified constructor, or accepted payload is added. |
| TCB.7u certified operational names | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `CertifiedFXGeneratingStep` over endpoint-indexed certified term arrows plus `CertifiedFXStructuralConv` as the current structural-thin term-arrow name.  Seed generating-step and structural-reflexivity fixtures expose audited raw/source/target theorems. | The generating-step view requires `isGeneratingStepCell = true`; structural conversion is only identity/thin-vertical-composite thinness.  This is not the legacy `Step`/`Conv` bridge and adds no new raw ingress, certified constructors, cd fillers, or accepted payloads. |
| TCB.7v exact rejection family heads | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds exact-reason family runners and audited theorem heads for inference, expected-shape, and certification-policy negative families. | Each finite family is checked against one named `CellCheckRejection`; this remains executable screen/policy evidence, not a theorem that no `PolyCell` inhabitant exists.  No new raw cells are admitted. |
| TCB.7w certified result erasure | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds generic erasure and input-code projection theorems for `CertifiedRawCell` and `CertifiedRawCellResult`. | Definitional and audit-gated; does not prove raw-code injectivity, does not broaden checker acceptance, and does not promote negative probes to non-inhabitation claims. |
| TCB.7x exact probe-family coverage | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds exact-coverage predicates and headlines for inference, expected-shape, certification-policy, and all current negative-probe families. | A family must be nonempty and must reject with its named reason to pass.  This is still executable checker evidence, not a constructor-index impossibility theorem. |
| TCB.7y dim-two seed term arrow | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds dim-2 endpoint-indexed term arrow/thin-arrow aliases and seed identity-over-step views. | All raw/source/target theorems are definitional and audit-gated; no new certified constructors, checker acceptance, raw ingress, or negative-probe theorem shape is added. |
| TCB.7z rejection-reason coverage matrix | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds per-`CellCheckRejection` coverage dispatch plus a headline over `CellCheckRejection.all`. | Adding a rejection constructor forces a new coverage branch; reasons with both inference and certification probes require both exact families.  No probe, checker acceptance, raw ingress, or non-inhabitation theorem is added. |
| TCB.7aa accepted-ingress coverage matrix | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds accepted-ingress shape coverage for the current finite positive domain: four seed dim-0 atoms, the accepted application fixture, and the direct dim-1 term-step fixture. | Coverage checks acceptance, dimension, and sort; generic raw-erasure theorem heads remain separate.  No raw dispatcher, accepted payload, negative probe, or non-inhabitation theorem is added. |
| TCB.7ab application expected-shape probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds three application wrong-sort expected-shape probes plus three malformed-application expected-shape pass-through probes. | Expected-shape probe count ratchets to 15; wrong-sort expected-shape probes ratchet to 12; bad-payload, wrong-arity, and wrong-child-shape expected-shape families are nonempty and exact-reason audited.  No accepted raw input or certified constructor is added. |
| TCB.7ac raw vertical identity probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds raw `compV(identity seed, identity seed)` certification probes for term/type/context/mode seeds, plus executable screen-success and certification-policy rejection theorems. | Certification probes ratchet to 10 and unsupported-certification probes ratchet to 8; each raw vertical identity composite screens as its own sort but rejects as `unsupportedCertification` at raw certification policy.  No raw `compV` ingress dispatcher or non-inhabitation theorem is added. |
| TCB.7ad generator-spec ingress dispatch | `Foundation/PolyCell/Core/Check.lean` | Replaces magic numeric accepted-id pattern arms in `inferRawAtom?` with `Nat.beq` dispatch against the generator-spec cell ids, and rewrites visible theorem targets to those constants. | `AuditPolyCell` and full `AuditAll` remain green; the accepted/rejected fixture set is unchanged.  This reduces the local trusted reading burden without changing checker power. |
| TCB.7ae fuel exhaustion rejection | `Foundation/PolyCell/Core/CheckResult.lean`, `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `CellCheckRejection.fuelExhausted`, a separate fuel-budget probe family, exact-family runners, and a coverage-matrix branch for the new rejection constructor. | `screenRawCellWithFuel? 0` rejects definitionally as `fuelExhausted`; `AuditPolyCell` and full `AuditAll` are green; no accepted raw input, certified constructor, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7af supported generator lookup ratchet | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds audited lookup-success theorem heads for lambda, application, pi-type, and context-cons, completing the existing success ratchets for all currently supported dim-0 generator metadata. | All new theorems are `rfl` over the existing lookup table; `AuditPolyCell` and full `AuditAll` are green; no checker behavior or accepted domain changes. |
| TCB.7ag accepted ingress screen coverage | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds executable screen-coverage predicates and audited theorem heads for the accepted seed term/type/context/mode atoms, accepted application fixture, and direct term-step fixture. | Coverage says accepted shape and expected structural screen agree for the current finite accepted domain only.  Raw-code preservation remains the separate generic erasure/input-code theorem layer; no raw ingress, accepted payload, certified constructor, or non-inhabitation theorem is added. |
| TCB.7ah term-step input-code coverage | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `hasCertifiedResultInputCodeCoverage` and applies it to the already accepted direct dim-1 term-step fixture. | The theorem checks the successful result's stored input code against `termStep(var 0, var 1)`; generic `CertifiedRawCellResult.inputCode_matches_rawCellCode` remains the returned-raw-cell link.  It is prefix-code regression evidence only; no raw-code injectivity, raw dispatcher, new accepted input, or non-inhabitation claim is added. |
| TCB.7ai accepted input-code coverage matrix | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds accepted dim-0 input-code coverage for the four seed atom ingress paths, package-level application input-code coverage, and a current accepted input-code matrix spanning those plus the direct term-step ingress. | Application input-code coverage is package-level to avoid normalizing the whole application dispatcher through payload `9100`; the separate accepted-ingress coverage matrix still proves checker acceptance.  `AuditPolyCell` and full `AuditAll` are green; no accepted-domain or constructor change. |
| TCB.7aj raw identity certification probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds raw `identity(seed)` certification probes for term/type/context/mode seeds, plus executable certification-policy rejection theorems. | Certification probes ratchet to 14 and unsupported-certification probes ratchet to 12; each raw identity screens through its base sort but rejects as `unsupportedCertification` at raw certification policy.  This is distinct from the TCB.7ac raw `compV(identity, identity)` probes and adds no raw identity ingress dispatcher, accepted input, or non-inhabitation theorem. |
| TCB.7ak accepted dim-0 frontier fixture list | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `AcceptedDimZeroFixture`, a five-entry `acceptedDimZeroFixtures` frontier, a length ratchet, and rewires dim-0 ingress/screen/input-code coverage through that shared frontier. | The fixture list reduces omission risk across the three accepted dim-0 coverage matrices.  The application still uses raw ingress for shape/screen coverage and the existing package-level result for input-code coverage; no accepted raw input, payload, certified constructor, dispatcher, injectivity theorem, or non-inhabitation claim is added. |
| TCB.7al raw term-step unit-composite probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds raw `compV(identity(var 0), termStep(var 0, var 1))` and `compV(termStep(var 0, var 1), identity(var 1))` certification probes, plus screen-success and certification-policy rejection theorem heads. | Certification probes ratchet to 16 and unsupported-certification probes ratchet to 14; both unit composites pass the structural screen as term cells but reject as `unsupportedCertification` at raw certification policy.  No raw `compV` ingress dispatcher, vertical-composition law, accepted input, or non-inhabitation theorem is added. |
| TCB.7am low-scope term-step rejection probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds scope-0 and scope-1 bad-boundary probes for the raw `termStep(var 0, var 1)` shape, plus direct screen and direct ingress rejection theorem heads. | Inference probes ratchet to 34 and the `badBoundaryEndpoint` inference subfamily ratchets to 6.  Both low-scope probes reject as `badBoundaryEndpoint` before certified endpoint construction; no new accepted scope, raw dispatcher, semantic term-step theorem, or non-inhabitation theorem is added. |
| TCB.7an positive-fuel identity exhaustion probe | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a fuel-budget probe for `screenRawCellWithFuel? 1` over raw `identity(var 0)`, plus an audited executable rejection theorem. | Fuel-budget probes ratchet to 2; the nested identity probe rejects as `fuelExhausted` after one descent rather than collapsing into payload or certification policy.  No accepted raw input, raw identity ingress, certified constructor, or non-inhabitation theorem is added. |
| TCB.7ao hostile application child-screen ratchet | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds direct audited theorem heads that the mode/context-as-function and mode/context-as-argument application payload sentinels reject at the decoded-child screen and at the direct dim-0 screen. | The existing malformed payloads remain rejection fixtures only; no probe count changes, accepted payloads, raw ingress paths, certified constructors, or non-inhabitation theorems are added. |
| TCB.7ap pi/context expected-shape probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds expected-shape pass-through probes for malformed pi-type and context-extension bad-payload, wrong-arity, and wrong-child-shape sentinels. | Expected-shape probes ratchet to 21, with bad-payload / wrong-arity / wrong-child-shape expected-shape families each ratcheting to 3.  These are executable rejection checks for supported-but-uncertified generator metadata; no lambda/pi/context certified payload family, accepted input, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7aq derived certified package coverage | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a six-entry `DerivedCertifiedFixture` frontier for the current certified-layer derived packages: term/type/context/mode identities, identity over the seed term-step, and the seed term-identity vertical composite. | The new matrix gives audited shape, structural-screen, and input-code coverage for derived packages only.  Raw identity and raw `compV` ingress remain unsupported certification paths; no accepted raw input, certified constructor, dispatcher, injectivity theorem, or non-inhabitation theorem is added. |
| TCB.7ar metadata ratchet completion | `Foundation/PolyCell/Core/GeneratorSpec.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Completes the current generator arity ratchet for `variable` and `contextEmpty`, pins raw ids for variable/lambda/application, and pins the seed term-step rule id and sort. | These are definitional table drift checks only.  No generator metadata, checker branch, accepted raw input, certified constructor, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7as lambda expected-shape probes | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds expected-shape pass-through probes for malformed lambda bad-payload, wrong-arity, and wrong-child-shape sentinels. | Expected-shape probes ratchet to 24, with bad-payload / wrong-arity / wrong-child-shape expected-shape families each ratcheting to 4.  This is pre-acceptance negative coverage for lambda metadata only; no lambda certified payload family, accepted input, checker branch, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7at application function-scope probe | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a hostile application payload whose decoded function child is out of scope, symmetric to the existing out-of-scope argument probe. | The new payload rejects through decoded-child screening, dim-0 screening, and raw-ingress policy as `wrongChildShape`; inference probes ratchet to 35 and the wrong-child-shape family ratchets to 12.  No accepted payload, certified constructor, checker broadening, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7au application payload frontier ratchets | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Separates the singleton accepted application payload frontier from hostile decoded application payload fixtures, and ratchets both finite lists. | The accepted certified application frontier remains exactly `app(var 0, var 1)`.  The hostile decoded frontier has eight fixtures and the finite decoder recognizes nine fixture payloads before sentinel/default rejection.  No accepted payload, certified constructor, checker branch, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7av raw identity screen coverage | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds direct executable screen-success theorem heads for raw `identity(seed)` over term/type/context/mode seeds. | These theorems pin the distinction between structural screening and certification: the identities screen as their own sorts, while the existing certification-policy theorems still reject raw identity ingress as `unsupportedCertification`.  No raw identity dispatcher, accepted input, certified constructor, or non-inhabitation theorem is added. |
| TCB.7aw multi-sort derived identity composites | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Extends the derived certified package frontier with type/context/mode identity-twice composites, matching the multi-sort thin-arrow view layer. | `derivedCertifiedFixtures` ratchets from six to nine entries and the existing shape/screen/input-code coverage matrices now include term/type/context/mode identities, identity over the seed term-step, and term/type/context/mode identity-twice composites.  These are derived certified packages only; raw `compV` ingress remains unsupported. |
| TCB.7ax application payload code distinctness | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a finite Bool-level distinctness checker for Nat-code frontiers and applies it to accepted, hostile decoded, decoded, sentinel, and sentinel-inclusive application payload lists. | This prevents accidental payload-code collisions in the finite application fixture table.  The sentinel-inclusive frontier has twelve distinct codes.  No decoder branch, accepted payload, certified constructor, raw dispatcher, semantic injectivity theorem, or non-inhabitation theorem is added. |
| TCB.7ay metadata id distinctness | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds finite supported-generator and supported-rule id frontiers plus length and distinctness ratchets. | The current supported generator metadata table has eight distinct ids and the supported rule metadata table has one id.  This is lookup-table drift protection only; no generator metadata, checker behavior, accepted input, certified constructor, raw dispatcher, or semantic injectivity theorem is added. |
| TCB.7az unsupported metadata lookup ratchets | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds audited negative lookup theorem heads around unsupported generator ids and the first unsupported rule id after the seed term-step rule. | Positive lookup coverage is now paired with nearby failure coverage, reducing table-boundary drift risk.  This changes no lookup implementation, generator metadata, checker behavior, accepted input, certified constructor, raw dispatcher, or semantic injectivity theorem. |
| TCB.7ba higher endpoint rule misuse probe | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a second wrong-endpoint-dimension raw rule probe using the seed term-step rule at endpoint dimension two. | Unknown-generator inference probes ratchet from two to three and total inference probes ratchet from 35 to 36.  The rule table remains pinned to the seed dim-0 endpoint rule only; no rule metadata, accepted input, certified constructor, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7bb unsupported rule-id probe | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a raw dim-1 cell using the first unsupported rule id over otherwise screenable term endpoints. | Unknown-generator inference probes ratchet from three to four and total inference probes ratchet from 36 to 37.  This pins rule-id lookup failure separately from endpoint failure; no rule metadata, accepted input, certified constructor, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7bc accepted seed expected-sort successes | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `checkRawCellAs?` success theorem heads for accepted seed type/context/mode cells, matching the existing seed term success theorem. | Caller-facing expected-sort success coverage now spans the four accepted seed sorts.  This adds no accepted input, certified constructor, checker branch, raw dispatcher, or non-inhabitation theorem. |
| TCB.7bd lambda decoder staging | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a decoder-only lambda payload frontier: one well-shaped unit/body child spine and hostile context-domain, type-body, and binder-shifted out-of-scope body fixtures. | The child-descriptor screen distinguishes the well-shaped lambda spine from each hostile child shape, and `checkRawCellAs?` still rejects the staged lambda payload as `badPayload`.  This adds no lambda raw ingress, certified lambda constructor, accepted payload, raw dispatcher, or non-inhabitation theorem. |
| TCB.7be pi-type decoder staging | `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds a decoder-only pi-type payload frontier: one well-shaped unit-domain/unit-codomain child spine and hostile context-domain and term-codomain fixtures. | The child-descriptor screen distinguishes the well-shaped pi-type spine from each hostile child shape, and `checkRawCellAs?` still rejects the staged pi-type payload as `badPayload`.  This adds no pi-type raw ingress, certified pi-type constructor, accepted payload, raw dispatcher, or non-inhabitation theorem. |
| TCB.7bf first certified pi-type payload | `Foundation/PolyCell/Core/GeneratorSpec.lean`, `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds the core payload code and certified child package for `Pi (_ : Unit). Unit`, plus raw ingress, accepted-fixture coverage, raw-code coverage, and hostile expected-shape probes. | `inferRawCell?` now accepts this one pi-type payload as `.type`; `checkRawCellAs?` rejects it as term/context/mode; context-domain and term-codomain pi payloads still reject as `wrongChildShape`; no general pi binder typing, raw dispatcher, conversion rule, or non-inhabitation theorem is added. |
| TCB.7bg first certified lambda payload | `Foundation/PolyCell/Core/GeneratorSpec.lean`, `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds the core payload code and certified child package for `lam (_ : Unit). var 0`, plus raw ingress, accepted-fixture coverage, raw-code coverage, and hostile expected-shape probes. | `inferRawCell?` now accepts this one lambda payload as `.term`; `checkRawCellAs?` rejects it as type/context/mode; context-domain, type-body, and out-of-scope-body lambda payloads still reject as `wrongChildShape`; no general lambda typing, beta, substitution, context extension, raw dispatcher, or non-inhabitation theorem is added. |
| TCB.7bh certified lambda/pi FX views | `Foundation/PolyCell/FXProfile/CertifiedViews.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `certifiedLambdaUnitTypeBodyVarZero` and `certifiedPiTypeUnitCodomainUnit` as FX-profile views over already certified raw-cell packages, plus raw-erasure theorem heads. | The views erase definitionally to the accepted lambda and pi raw fixtures and are covered by `AuditPolyCell`; no raw ingress, accepted payload, certified constructor, checker branch, operational typing theorem, or non-inhabitation theorem is added. |
| TCB.7bi lambda child decoder erasure links | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds audited theorem heads linking the first certified lambda child package and its child-spine erasure to the lambda payload decoder output. | The theorem heads are definitional and mirror the application/pi pattern; no accepted raw input, payload, certified constructor, checker branch, raw dispatcher, operational typing theorem, or non-inhabitation theorem is added. |
| TCB.7bj descriptor-indexed decoder erasure links | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds audited theorem heads for descriptor-indexed application, lambda, and pi-type child-spine erasure against their payload decoders. | The theorem heads route through existing descriptor-indexed spines and ordinary decoder-erasure links; no accepted raw input, payload, certified constructor, checker branch, raw dispatcher, operational typing theorem, or non-inhabitation theorem is added. |
| TCB.7bk pi input-code coverage name | `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds `hasAcceptedPiTypeUnitCodomainUnitInputCodeCoverage` beside the existing application/lambda coverage helpers and routes the pi-type input-code theorems through it. | `AuditPolyCell` covers the new helper; this is naming/readability parity only, with no accepted raw input, payload, certified constructor, checker branch, raw dispatcher, operational typing theorem, or non-inhabitation theorem added. |
| TCB.7bl first certified context-extension payload | `Foundation/PolyCell/Core/GeneratorSpec.lean`, `Foundation/PolyCell/Core/NegativeProbes.lean`, `Foundation/PolyCell/Core/Certified.lean`, `Foundation/PolyCell/Core/Check.lean`, `Tools/AuditAll/AuditPolyCell.lean` | Adds the payload code and certified child package for `ctxCons(empty, Unit, linear)`, plus raw ingress, accepted-fixture coverage, raw-code coverage, decoder-erasure links, and hostile wrong-child-sort probes. | `inferRawCell?` now accepts this one context-extension payload as `.context`; `checkRawCellAs?` rejects it as term/type/mode; type-as-context, term-as-type, and context-as-mode context-extension payloads still reject as `wrongChildShape`; no general context typing, weakening, substitution, raw context dispatcher, or non-inhabitation theorem is added. |

**Implementation order after TCB.7bg:**

> **Largely superseded by TCB.8 (general certifier landed).**  The
> dimension-polymorphic recursive certifier `certifyRawCellExact?` now
> exists and is total on the entire non-`compH` raw fragment (TCB.8a–8e).
> The propext obstruction this section repeatedly cited was diagnosed and
> removed: it was the dual `(dim, rawCell)` / partial-index match, NOT
> polymorphic recursion.  Items below are retained as the historical
> pre-TCB.8 guidance; where they say "blocked by propext," read "resolved
> by TCB.8."

1.  Do not broaden lambda/application/pi by adding more one-off parent
    constructors unless the slice is intentionally finite and explicitly
    probed.  Descriptor-indexed child spines over `RawChildDescriptors` are
    live for the first application, lambda, and pi-type payloads and erase
    exactly to their descriptor indexes.  The next non-nullary slice must
    either generalize that indexed shape without weakening `AuditPolyCell`,
    or stop at the current finite payload frontier.  No new payload is
    accepted merely because its raw descriptor screen passes.  (The
    "dimension-polymorphic dependent pattern route is not acceptable" note
    here is OBSOLETE — TCB.8a found the clean route: match on `rawCell`
    only, transport ids via `cast`/`Eq.rec`, never the equation compiler.)
2.  If the reusable certified-child spine cannot be made audit-clean,
    keep using the decoder plus generic screen gate and move to
    positive-dimensional certification instead of weakening the TCB.
3.  Continue positive-dimensional certification without broadening raw
    ingress.  A propext-free raw dispatcher for the already certified
    `.cell` fixture is now LANDED (TCB.8): `certifyRawCellExact?` certifies
    arbitrary `.cell`/`.compV`/identity/atom inputs (term-step rule), so
    this is no longer blocked.  Derived identity and derived vertical
    composition are complete for already certified inputs, the current
    derived-package frontier has audited shape/screen/input-code coverage, and the
    identity over the seed dim-1 term step is exposed as a dim-2
    endpoint-indexed arrow/thin-arrow view.  Raw identity and raw `compV`
    ingress remain untrusted; TCB.7aj explicitly probes raw identities
    for term/type/context/mode, and TCB.7ac explicitly probes raw
    identity composites for term/type/context/mode, as screen-successful
    but certification-policy rejected.  Certified `compH` remains
    blocked on real Gray-boundary semantics.
4.  Thinness is structural and intentionally narrow: identities are thin,
    and vertical composites of thin cells are thin.  Do not classify
    generating term steps as thin until an operational conversion
    predicate exists and is audited.
5.  Keep the propext-free boundary-screen discipline: no `propext`,
    `Quot.sound`, `Classical`, `Inhabited`, `Nonempty`, hidden `False`
    equation dependents, or weakened audit budgets.  The failed
    direct-dependent-pattern route is not acceptable.
6.  Add negative probes before each new accepted family: malformed
    payload sentinel, wrong arity, wrong child sort/dimension/scope,
    expected-shape sort confusion, bad endpoint, and bad vertical
    boundary where the family can participate in positive-dimensional
    cells.  Raw nonsense must remain representable and the certified
    layer must reject it by computation.  Any new probe family must be
    added to the rejection-family partitions and covered by the matching
    audited headline theorem, while keeping the individual probes as
    regression fixtures.  The rejection-reason coverage matrix must also
    name which exact family covers any new `CellCheckRejection`
    constructor, and multi-phase reasons must list every phase-family that
    currently exercises that reason.
7.  Extend `CertifiedViews.lean` only as the checker gains real
    certified inhabitants: context/type/term/mode seed views,
    positive-dimensional endpoint projections, endpoint-indexed arrows,
    multi-sort identity thin arrows, multi-sort identity thin composites,
    structural thin views, the certified generating-step name, and the
    structural-conversion alias are live.  Final legacy `Step`/`Conv`
    bridges, cd fillers, and coherence views must wait for broader
    positive-dimensional certification plus operational data.  Keep old raw
    subtype views as compatibility shims.
8.  Legacy bridge: connect the existing intrinsic kernel judgments to
    certified views only after the checker has nonempty accepted
    witnesses and the audit proves every new declaration axiom-free.
9.  For each new negative-probe family, keep both theorem layers:
    (a) the existing "stored expected reason rejects" headline and
    (b) the TCB.7v exact-reason headline saying the whole finite family
    rejects as one named `CellCheckRejection`.  TCB.7x adds the executable
    coverage layer: each named family must be nonempty and must reject with
    its named reason.  TCB.7z adds the constructor-level rejection-reason
    coverage matrix over `CellCheckRejection.all`; this matrix is only an
    anti-omission gate for executable probes and must not be read as
    certified-cell non-inhabitation.  Over time, fold those executable
    families under
    well-scoped PolyCell theorem heads only when the scope is exact.
    Acceptable future headline shapes include:
    `inferProbeFamily_rejected_with_<reason>`,
    `expectedShapeProbeFamily_rejected_with_<reason>`,
    `certificationProbeFamily_rejected_with_<reason>`,
    `probeFamily_hasNoCertifiedCell_of_childShapeMismatch`,
    `probeFamily_hasNoCertifiedArrow_of_boundaryMismatch`, and
    `probeFamily_hasNoConstructorIndex_of_<obstruction>`.  The first three
    are executable checker theorems; the last three are genuine
    constructor-index or certified-boundary impossibility theorems and must
    be grounded in an explicit finite probe list or a real constructor-index
    obstruction.  Do not headline "no certified inhabitant" merely because
    a raw checker currently returns a rejection code.  Stronger
    non-inhabitation theorems are allowed only when they follow from
    certified constructors and indices without excluded middle, `propext`,
    `Classical`, `Inhabited`, `Nonempty`, or empty-domain tricks.  Keep the
    theorem name scoped to the actual obstruction: infer-screen rejection,
    expected-shape rejection, certification-policy rejection,
    child-descriptor mismatch, boundary mismatch, or constructor-index
    non-inhabitation.

**TCB.9 — v2 structural re-foundation LANDED 2026-05-27:**

The six-stage v2 re-foundation is **SHIPPED + AUDITED**.  v1's
dim-indexed `PolyTerm` (sentinel-payload atoms + per-fixture certified
constructors) is **DELETED** (commit ef079829).  `RawTerm scope` +
`RawCell scope` + `PolyCell profile sort dim scope boundary raw` is the
SOLE canonical kernel surface.  The 194-Generator table + `binderShifts`
+ `payload` family + `SupportedGenerator` admission + `GenPayloadEvidence`
+ `CertifiedTermSpine` substrate carries the entire former v1 admission
surface — no v1 sentinel constants, no v1 per-fixture inductives, no
v1 hand-written child decoders survive.  All V2 suffixes dropped per
V2-mig.11–14 + final V2-mig.18 audit.

What landed at each stage:

| Stage | Content | Commits |
|---|---|---|
| **Stage 0** | `RawTerm` + `RawCell` un-indexed inductives + `RawCell.dim` computed function | V2-L0.6/0.8/0.9 |
| **Stage 1** | Generator metadata (`generatorCellSort`, `generatorChildSpecs`, `SupportedGenerator`, `GenPayloadEvidence`, `HasEqualDim`) + binderShifts coherence | V2-L1.1–L1.9 |
| **Stage 2** | Certified `PolyCell` + `CertifiedTermSpine` + 4 certified constructors (`gen` / `generatingCell` / `verticalComposite` / `identityCell`) gated by SPIKE-1 zero-axiom dim transport | V2-L1c.1–L1c.10 |
| **Stage 3** | `certifyRawCellExact?` (mutual with `certifyTermSpine?`) + existential wrapper + soundness theorems (no false positives) + coverage suite | V2-L1cert.1–L1cert.19 |
| **Stage 4** | Allais ops: `RawTerm.fold` over `Foundation/Action.lean` ⇒ `rename` / `subst` as ONE instance each + Action laws (apply_ext / compose_assoc / identity_apply) | V2-L2.1–L2.11 |
| **Stage 5** | v1↔v2 bridge + per-fixture agreement | gated by SPIKE-2, completed before v1 retirement |
| **Stage 6** | Re-point `inferRawCell?` / `checkRawCellAs?` / FX views to v2 + DELETE v1 | commit ef079829 |

Both linchpin spikes returned zero-axiom: **SPIKE-1** value-level dim
transport in the certified `generatingCell` (`Nat.decEq` on `RawCell.dim`
+ `▸`) shipped at V2-L1c.5; **SPIKE-2** v1↔v2 agreement on the dim-
erased existential shipped at V2-SPIKE-2.  The generic children-spine
recursion (`certifyChildSpine?`) was always axiom-free.

The v2 substrate is now the cascade-death lever in operation: the
194-Generator table grows by one entry per new feature (per §3.16
inventory); the `RawTerm` / `RawCell` / `PolyCell` inductive surface
stays fixed at four certified constructors.  Adding `gen_universeU` /
`gen_path` / `gen_clock` / `gen_param` / `gen_rewriteRule` / `gen_dProp`
/ `gen_mode` / `gen_shape` / `gen_effectOp` / `gen_smtSatCert` per
Phase Z₀–Z₉ commitments is one-Generator-entry-per-feature work, not
a cascade.

**POLY-TCB anti-vacuity gate (HISTORICAL — TCB.4 LANDED + RETIRED with
v1 in commit ef079829).**  The anti-vacuity gate prevented the v1 TCB
from shipping a soundness theorem whose supported-generator domain was
empty.  Under v2, the gate is structurally absorbed: the 194-Generator
table is non-empty by construction, `SupportedGenerator` is a fully
populated inductive (one arm per admitted generator, expanding to
~400–500 arms by MILESTONE D per §3.16), and every `CellCheckRejection`
constructor has its named exact-family probe ratchet (V2-L1cert.16).

**Non-goals in POLY-TCB (HISTORICAL — v1-era constraints):**

- Raw input layer retained — `RawTerm` / `RawCell` (v2) ARE the input
  format AND rejection target.  v1's `PolyTerm` is **DELETED**.
- Certified `horizontalComposite` remains BLOCKED until Axis 6 supplies
  a real Gray tensor boundary formula and disjoint-footprint/matching
  condition.  Raw `RawCell.horizontalComposite` is admissible as input
  syntax; the certifier rejects it with `unsupportedCompH`.
- Typed legacy equivalence + subject reduction + confluence + decidable
  conversion live in Phase POLY-Z (§10's POLY-Z table + §11.8 apex
  commitments).  TCB itself certifies shape/sort/scope and vertical
  boundary structure only — that floor is reached.

**Verification gate (in force on every PolyCell commit):** every new
declaration added to `LeanFX2/Tools/AuditAll/AuditPolyCell.lean`;
`lake build LeanFX2.Foundation.PolyCell.*` kernel green; `lake build
LeanFX2 LeanFX2Audit` full-strict zero-axiom sweep green;
forbidden-token scan (no `axiom` / `sorry` / `noncomputable` /
`propext` / `Quot.sound` / `Classical.choice` / `@[extern]` /
`@[implemented_by]`) over touched PolyCell files.

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
- `Foundation/PolyCell/Core/RawTerm.lean` + `RawCell.lean` —
  permissive raw layer (scope-indexed, dimension computed)
- `Foundation/Polygraph/PolyCell.lean` — certified cell type
- `LeanFX2/FxProfile.lean` — FX as a profile instance
- `LeanFX2/FxCellViews.lean` — FXType, FXTerm, FXStep, FXConv as views

**Acceptance:** raw `RawTerm` / `RawCell` and certified `PolyCell`
typecheck zero-axiom; fxProfile satisfies consistency conditions; view
definitions agree with current types through the checked bridge.

### Phase POLY-Z — Typed Layer + Decidable Typechecking (months 24-60, ~53K LoC)

The maximal-power computable kernel commitment from §11.8.  Eight
sub-phases delivering the typed layer, cubical primitives, HITs,
IR/Mahlo, guarded recursion, and 21-dim integration on top of the
structural substrate that POLY-ζ ships.

| Sub-phase | Content | LoC est | Months |
|---|---|---|---|
| Z₀ | Foundational refactors: `gen_universe` payload → `LevelExpr × UniverseFlag`; motive children in eliminator spines; `SupportedGenerator` split into `Syntactically~` + `Semantically~`; rename 33+ structural decls under new names | ~2K | 1 |
| Z₁ | Typed core: `TypingContext` + `HasType` for ~30-generator semantic core (var, unit, universe, Π, λ, app, Σ, pair, fst, snd, bool, nat, list, option, either, identity, refl, J) | ~5K | 2-3 |
| Z₂ | Canonicity + consistency for the semantic core; honesty probes refreshed | ~3K | 1-2 |
| Z₃ | Decidable typechecking via cubical NbE for the semantic core; bidirectional algorithm | ~6K | 2-3 |
| Z₄ | Cubical primitives: `gen_path` / `transp` / `hcomp` / `glue` / `unglue` / `face` / `dimI`; Kan structure proofs for each generator | ~8K | 3-4 |
| Z₅ | HITs as profile-level generators with path-constructor support; HIT eliminators with cubical Kan computation; QIITs | ~5K | 2-3 |
| Z₆ | Induction-recursion: Tarski universes internally; Mahlo reflection degrees (mahlo → hyperMahlo) + higher-order Πⁿ-reflection (weaklyCompact → reflecting) | ~3K (IR) + ~5K (Mahlo + Πⁿ) | 3-4 |
| Z₆+ | Single-structure accessible-category reflection (ramsey → vopenka; Adámek-Rosický/Bagaria) + **sequential Exact Structural Reflection** (huge → **kunenI0**, the rank-into-rank region; Bagaria-Lücke) + the 2024 SR frontier (exacting/ultraexacting; Aguilera-Bagaria-Lücke, ZFC-consistent rel I0). Categorical reflection degrees, NOT embeddings j:V→V; leverages polynomial-universe + HIIRT + (∞,ω) substrate. Apex `kunenI0` lands ★ MILESTONE B (§11.8.12); open tail (schlutzenberg/reinhardtDirected) catalogue-only. | ~8K (ESR) + ~3K (frontier) | 2-3 |
| Z₇ | Guarded recursion (Nakano modality) + coinduction with productivity; codata generators | ~4K | 2-3 |
| Z₈ | 21-dim integration: usage, effect, security, refinement, lifetime, provenance, trust, repr, observability, clock, complexity, precision, space, overflow, FP order, mutation, reentrancy, size, version | ~15K | 6-12 |
| Z₉ | **Optional, only-if-needed**: fully-verified internal SMT engine (verified SAT + verified theory deciders + verified Nelson-Oppen) — built natively inside FX per §11.8.11's closed-system mandate.  Deferred until a concrete profile-level need emerges that the individual decision procedures (§11.8.7) cannot serve. | ~10K | 6-9 |

**Total for POLY-Z: ~53K LoC core + ~10K LoC Z₉-if-needed over
~24-36 months focused work**, running in parallel with POLY-η's
migration cleanup from month 24 onward.  Combined with the ~170K
substrate LoC, the full kernel arrives at ~220K-230K LoC and
**MILESTONE D (full FX kernel)** at ~month 60.

Per §11.8.12 the milestone scale is revised:

* MILESTONE A    = Z₁ + Z₂ + Z₃ — decidable typed checking for semantic core (~month 30).
* MILESTONE A+   = + Z₄ — cubical primitives (~month 34).
* MILESTONE A++  = + Z₅ — HITs (~month 37).
* MILESTONE B    = + Z₆ — IR + Mahlo (~month 41).
* MILESTONE C    = + Z₇ — guarded recursion (~month 44).
* MILESTONE D    = + Z₈ — full 21-dim FX kernel (~month 56).

Each sub-phase composes published per-feature theory; the JOINT
soundness of the accumulating union is the open obligation
O-NORM / O-CONF / O-CANON (§11.8.0), discharged via BKS sconing on the
full signature.  Per-feature: assembly.  The joint metatheory:
research.

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

**The umbrella rule.**  Every shipped declaration MUST be `theorem`,
`lemma`, `def`, `inductive`, `structure`, or `instance` with a real
body.  No `axiom`.  No `sorry`.  No `noncomputable` for kernel
theorems.  No `propext` / `Quot.sound` / `Classical.choice` in any
kernel transitively.  No `@[implemented_by]` / `@[extern]` for kernel
theorems.  No hypothesis-as-postulate (`theorem foo (univ :
Univalence) : ...` is BANNED — it ships the conclusion conditionally
on an unprovable input, semantically equivalent to an axiom).  No
`IsX : Prop` placeholder predicates.  No `Inhabited X` for
unconstructible X.  See lean-fx-2/CLAUDE.md for the full discipline
and the strict-harness gates that enforce it.

**Closed-system mandate (§11.8.11 lifted here as headline).**  The
kernel is a CLOSED SELF-CONTAINED SYSTEM.  Three NON-NEGOTIABLE bans
apply to every axis below, every Phase Zₙ, and every profile
extension:

* **No user-level tactics.**  Proofs are TERMS, not scripts.  `calc`
  chains are the only proof-script construct at user level.  All
  other proof construction happens via type-directed elaboration
  (§11.8.3).  There is no `by` block, no `apply`, no `intro`, no
  `rewrite`, no `simp`, no `tauto`, no `decide` exposed as a
  user-facing tactic language.  If a goal needs more than `calc`
  chains + refinement synthesis to inhabit, the user refines the
  SPECIFICATION (more refinements, more equations, more
  definitional structure) — not the proof script.
* **No external SMT.**  The kernel never calls Z3, CVC5, or any
  external solver.  Every decision procedure invoked during
  elaboration is INTERNAL and fully verified in Lean (and eventually
  in FX itself, per the self-hosting target §3.15).  Internal
  deciders ship per §11.8.7's matrix with their published-algorithm
  basis.  If higher SMT-level power becomes necessary, the response
  is to build a **fully-verified internal SMT engine** natively
  inside FX as Phase Z₉ — never to delegate to an external untrusted
  oracle.
* **No LLM in the kernel.**  LLM-driven workflows live OUTSIDE the
  kernel via the agent protocol (fx_design.md §24).  LLMs propose
  TERMS that the kernel verifies under its ordinary rules; inside
  the kernel there is no LLM-aware operation, no synthesis-by-
  language-model primitive, no oracle fallback.

These three bans preserve: (a) soundness independence from external
software, (b) single-grammar proof representation, (c) deterministic
reproducible builds, (d) zero-trust composition.  Anything that
cannot be implemented cleanly within the zero-axiom + closed-system
discipline is **de-scoped** — `--type-in-type` is absolutely banned
even as a flag; external SMT is absolutely banned even with a
"trust" annotation; LLM-driven proof generation INSIDE the kernel is
absolutely banned even with "verification gates."

Per-axis discipline rules follow.  Each axis stays zero-axiom under
the specific patterns named below, with the umbrella + closed-system
rules applying uniformly throughout:

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

**v2 un-indexes the raw layer, which removes the dim-parameter trap at
its source.**  `RawTerm` is scope-indexed and `RawCell` carries no
dim index (dimension is the computed `RawCell.dim`), so the certifier
never matches a `(dim, ctor)` pair — the structural cause of the propext
leaks fought through TCB.7/TCB.8.  The remaining certified indexed layer
still observes the traps documented in `feedback_lean_zero_axiom_match`
+ `feedback_lean_indexed_partial_match`:
- Match the raw cell ALONE (index inferred); never the `(dim, cell)`
  pair or a partial ctor enum at a restricted index
- Endpoint-dimension reconciliation is value-level (`Nat.decEq` on
  `RawCell.dim` + `▸`), never the equation compiler on a Nat index
- `Nat` facts use core lemmas, never `omega` (which pulls `propext` +
  `Quot.sound`)
- Boundary destructuring uses explicit pattern + `nomatch` for
  impossible-by-index cases
- Thinness is a stratification predicate / marking, not a certified
  constructor.  Any inverse/flipped-boundary operation must be a
  derived theorem over marked cells, not an `Eq.rec` shortcut.

This is the riskiest design point — the recipe in `feedback_lean_match_propext_recipe`
(8 concrete patterns for propext-clean match) applies throughout, and the
v2 generic certifier `certifyRawCellExact?` plus `DecidableEq
(RawCell)` are the load-bearing zero-axiom declarations.

---

## 11.5 Computability + decidability discipline summary

The 2026-05-24 revision audited every load-bearing computability /
decidability claim in this document.  This section is the index for
the STRUCTURAL substrate's decidability claims.  **For the full
maximal-power kernel's decidability matrix (typed Conv, typed
checking, cubical primitives, IR, HITs, guarded recursion, Mahlo
universes, 21-dim integration), see §11.8.7.**  The two sections
are complementary: §11.5 is the substrate; §11.8.7 is the apex
target.

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

## 11.6 Metatheory obligations on the v2 substrate

The v2 structural re-foundation (§4, TCB.9) gives the SUBSTRATE for
the four-property computability quartet (`computability-rules.md` §1).
This section pins what must be proved ON the v2 substrate for the
quartet to hold, identifies the subtle interactions the v2 design must
get right, and reserves the Div-fragment integration point for later.

### 11.6.1 The quartet restated for PolyCell

| Property | v2 statement | What must be shipped |
|---|---|---|
| **Subject Reduction (SR)** | If `PolyCell profile sort 0 scope () raw` (a certified dim-0 cell = typed term) and a dim-1 generating cell certifies a step from `raw` to `raw'`, then `PolyCell profile sort 0 scope () raw'` (the target is also certified at the same sort). | The **substitution lemma at every dimension**: applying subst σ to a dim-1 cell preserves its source/target boundary. For `generatingCell ruleId source target`, `(generatingCell ruleId source target).subst σ` must be `generatingCell ruleId (source.subst σ) (target.subst σ)` with the HasEqualDim and SupportedRuleSpec witnesses preserved through the substitution. This is the cell-level analog of the v1 `Step.par.Compat` cascade (~3K LoC) — the Allais fold (V2-L2.8) replaces the cascade, but the boundary-preservation property must still be PROVED as a theorem over `fold`, not merely assumed. |
| **Confluence (CR)** | If `raw →* raw₁` and `raw →* raw₂` (via chains of dim-1 cells), then ∃ `raw₃` with `raw₁ →* raw₃` and `raw₂ →* raw₃`. | Generic cd_lemma as ONE theorem per profile (the §2.2 collapse): for every pair of dim-1 generating cells with the same source (a critical pair), a dim-2 cell (confluence filler) exists. The MMS cubical coherent confluence substrate (arXiv:2511.16852 §4 Newman + Church-Rosser) supplies the machinery; the Generator table supplies the critical-pair enumeration. The proof is ONE structural induction over the Generator table, not a per-constructor cascade. |
| **Strong Normalization (SN)** | Every certified dim-0 cell reduces to a normal form in finitely many dim-1 steps under any reduction strategy. | Tait reducibility over `RawTerm` (a Prop-valued `RC : CellSort → RawCell scope → Prop` with one arm per Generator, per Era S Day 41–43 of the extended-roadmap). The v2 substrate simplifies the argument: the Allais fold gives eval (NbE), the generic `Gen` constructor means the fundamental theorem is ONE induction over Generators rather than a per-Term-constructor 75-arm proof. BUT: the RC predicate must be defined over `RawTerm`, not legacy `Term` — either re-prove on v2 or lift through the bridge (V2-bridge.4). |
| **Decidable Type-Checking** | `Decidable (certifyRawCellExact? scope raw = Except.ok _)` for all raw cells; and for the Tot fragment, `Decidable (Conv a b)` via NF equality. | The certifier `certifyRawCellExact?` is ALREADY a computable decision procedure returning `Except.ok` or `Except.error` — so decidability of certification is STRUCTURAL (it's a computable function; it always terminates by structural recursion). Decidable Conv requires SN (terms normalize) + CR (NFs unique) + the comparison `DecidableEq` on NFs. The comparison is shipped (V2-L0.11/12); SN + CR are the metatheory obligations above. Path A (NbE via `fold` + quote + DecidableEq on NFs) or Path B (Makkai word equality on the finite Generator-presented polygraph) gives the procedure. |

**The quartet has a thermodynamic reading (O-THERMO, §11.9.2.2).**  SN
is not merely "terminates": assign each cell a free energy
`cost − T·(information it discards)` (cost grade, §3.7 — a projection or
non-injective rewrite discards information, i.e. produces logical
entropy, Landauer 1961).  Then **SN is a Second Law** (free energy is
bounded below and strictly descends along directed, non-thin cells, so
every certified cell relaxes to a normal form), **CR is ergodicity**
(the equilibrium is unique), and the **Tot/Div boundary (§11.7.2) is a
phase transition**.  A temperature parameter unifies kernel reduction
(`T→0`, Lévy-optimal) with the §11.9.4 agent search (high `T`,
annealing).  This is a *geometric* route to the same O-NORM / O-CONF
obligations — a frontier alternative to the syntactic sconing route, and
the foothold for the discrete-Ricci-flow normalization proof of §11.9.3
OP5.

### 11.6.2 The substitution lemma at the cell level (the subtle obligation)

The Allais fold (V2-L2.3 `fold`) gives rename/subst on `RawTerm`
and the Action laws (V2-L2.7) prove compose/identity/extensionality
on terms.  V2-L2.8 lifts rename/subst to `RawCell`.  But the
load-bearing property is:

```
RawCell.subst σ (generatingCell ruleId source target)
  = generatingCell ruleId (source.subst σ) (target.subst σ)

RawCell.subst σ (verticalComposite first second)
  = verticalComposite (first.subst σ) (second.subst σ)

(and analogously for identityCell)
```

— i.e., substitution COMMUTES with the cell-layer constructors and
PRESERVES boundaries.  For `verticalComposite`, the shared middle
`target(first) = source(second)` must survive substitution:
`target(first.subst σ) = source(second.subst σ)`.  This follows from
the term-layer Action laws applied pointwise to the endpoints, but it
must be STATED and PROVED explicitly as a cell-layer theorem.

Without this, the certified layer's `PolyCell.verticalComposite`
cannot have a substitution operation (you can't substitute into a
certificate if substitution breaks the shared-middle invariant).
Subject reduction at dim ≥ 1 depends on this.

### 11.6.3 Scope-shift coherence under the fold (the de Bruijn trap)

When `fold` recurses into a child under a binder (a `childCons`
with `shift > 0`), it LIFTS the environment by `shift`.  The
certifier (`certifyTermSpine?`) expects each child at
`scope + shift`.  These must agree: the fold's lift must produce a
term at the same scope the certifier expects.

The coherence lemma V2-L1.3 (generatorChildSpecs shifts =
binderShifts) ties the two metadata views.  But the operational
agreement — "applying rename ρ via `fold` to a term that certifies
at scope `s` produces a term that certifies at scope `ρ(s)`" — is a
separate property: **rename-equivariance of the certifier**.

```
certifyRawCellExact? scope (RawTerm.rename ρ term) = Except.ok _
  ↔
certifyRawCellExact? (ρ scope) term = Except.ok _
```

(informally: renaming a well-formed term by a scope-compatible
renaming yields a well-formed term).  This is the operational
glue between "the fold is correct" and "the certifier agrees."
Off-by-one in the lift-by-shift vs the certifier's scope+shift
creates a silent scope mismatch that passes on closed terms and
fails on open terms under binders — the classic de Bruijn bug.

### 11.6.4 Generator table validation (TCB boundary)

The Generator table (`Generator.arity`, `binderShifts`, `payload`,
`generatorCellSort`, `generatorChildSpecs`) is TRUSTED DATA in the
FX0-PolyCell design (§12.6.9): the verifier consumes it, does not
validate it.  Table correctness — "each Generator entry faithfully
represents the intended type former" — is established by:

1. **Per-Generator round-trip witnesses** (in the bridge, V2-bridge.1
   / FX0-PC.7 `encodeCellSound`): encoding a legacy `Term.var` /
   `Term.lam` / `Term.app` / ... via the Generator table and
   decoding back recovers the original.  Each round-trip theorem
   ties one Generator entry to the legacy constructor it represents.
2. **Cross-implementation agreement** (FX0-PC.8): the Lean and
   external verifiers consume the SAME table and produce the SAME
   verdicts.  If either table is wrong, the two disagree on some
   fixture.
3. **Coverage + negative probes** (V2-L1cert.15/16): the test
   corpus exercises every admitted Generator with accepted fixtures
   AND hostile fixtures, pinning the table's accept/reject boundary
   per-entry.

These three together form the table-validation argument.  NO SINGLE
mechanism suffices: round-trips catch semantic bugs (wrong arity),
cross-implementation catches implementation bugs (wrong code), and
probes catch boundary bugs (accepting what should reject or vice
versa).  The table is still trusted data (not self-validating), but
the trust surface is ~300 lines of lookup tables audited by three
independent mechanisms.

### 11.6.5 horizontalComposite admission staging (inductive extension discipline)

Every other feature addition is a GENERATOR TABLE extension (one
`SupportedGenerator` arm — the inductive `PolyCell` doesn't
change).  `horizontalComposite` is the exception: admitting it
requires adding a NEW CONSTRUCTOR to `PolyCell` (a certified
`horizontalComposite` constructor with a Gray-boundary witness),
which is an INDUCTIVE EXTENSION.

Inductive extension means every theorem that matches on `PolyCell`
(soundness proofs, erasure lemmas, the fold, the FX0 verifier) must
be EXTENDED with a new case.  This is a mini-cascade — much smaller
than the v1 78-arm cascade but still non-trivial (~10–15 theorems
need a new arm).

**Staging discipline:**
- The `horizontalComposite` tag is RESERVED in the FX0-PolyCell
  certificate format (§12.6.4, tag byte = 3) with a "must reject"
  rule that the specification can later upgrade to "check Gray
  boundary condition" without breaking the binary format.
- The `PolyCell` inductive is designed with a PLACEHOLDER comment
  at the position where the certified `horizontalComposite`
  constructor will go, listing the fields it will need (Gray-boundary
  formula + disjoint-footprint witness + marking compatibility per
  Axis 6 Stage 2).
- When Axis 6 lands, the admission is ONE commit that: adds the
  constructor, extends the ~10–15 theorems with the new case,
  upgrades the FX0 verifier from "reject tag 3" to "check Gray
  boundary on tag 3", and re-runs the full cross-check corpus
  (FX0-PC.8) with horizontalComposite fixtures added.

This is the ONE place the inductive grows after the v2 re-foundation
stabilizes.  All other feature growth is table-only.

### 11.6.6 Div-fragment integration point (reserved, not designed)

FX's `with Div` effect (fx_design.md §9.4) permits possibly-divergent
computation.  Under the v2 substrate, a Div program is an infinite
chain of individually-certified dim-1 cells (each step well-formed,
the chain potentially non-terminating).  Productivity checking
(fx_design.md §3.5 `with Productive`) ensures every observation on a
codata stream eventually produces a value.

The four-property quartet does NOT hold for the Div fragment (SN
fails by definition; decidable typechecking requires fuel-bounding or
coinductive techniques).  The v2 substrate must accommodate Div
programs without compromising the Tot fragment's guarantees:

- **Effect isolation:** the Tot/Div boundary is enforced by the
  graded effect system (dimension 4).  A `Tot` cell cannot reference
  a `Div` cell without an explicit `with Div` annotation.  The
  certifier checks this via the `generatorCellSort` + effect-grade
  metadata — a `Tot`-sorted Generator cannot have a `Div`-sorted
  child.
- **Per-step soundness:** each individual dim-1 cell in a Div chain
  IS certified (SR holds per-step).  The chain's non-termination is
  an EFFECT, not a soundness violation.
- **Fuel-bounded verification:** for the FX0-PolyCell verifier, Div
  programs are verified up to a fuel bound (the certificate carries a
  finite prefix of the chain; the verifier checks each step in the
  prefix).  The `fuelExhausted` rejection (TCB.7ae) is the
  mechanism.

Detailed design for Div-fragment coinduction / productivity checking /
Delay-monad integration is DEFERRED — the Tot fragment's metatheory
is the critical path.  This subsection reserves the integration point
so future work knows where Div enters the v2 architecture.

---

## 11.7 Foundational boundaries — Gödel, Turing, and controlled openness as PolyCell design constraints

The PolyCell substrate sits inside three absolute ceilings (Gödel
incompleteness, Turing undecidability, Rice's theorem). This section
captures how each ceiling translates into a CONCRETE design constraint
on the v2 substrate and the profile-extension calculus — not as
abstract philosophy but as actionable mechanisms with specific Lean
signatures, verification gates, and FX0-PolyCell implications.

### 11.7.1 Gödel's ceiling → ConsistencyStrength as computable data

**The constraint:** any consistent profile `π` cannot prove `Con(π)`
(Gödel II).  Every profile-extension `π → π'` that adds a new axiom
(a new Generator entry with no reduction rule — a bare declaration)
potentially increases consistency strength.  If the extension is
inconsistent with existing axioms, the system must REJECT, not
silently accept.

**Actionable mechanism — the `ConsistencyStrength` ledger:**

```lean
/-- Ordinal approximation of the profile's consistency strength.
    Not a formal ordinal — a computable tag tracking relative strength
    for the admission contract's use.  The tag is a LOWER BOUND on
    what the profile can prove about weaker systems.  Buckets follow
    the §11.8.2 apex hierarchy (precise flag = `UniverseFlag`; this
    enum is the coarse summary used by `ProfileExtension.strengthAfter`). -/
inductive ConsistencyStrength where
  | finitistic            -- PRA / bounded arithmetic
  | predicative           -- PA / predicative analysis
  | impredicative         -- power-set-style closure
  | inaccessible          -- universe-closure reflection (Grothendieck universe)
  | setzerHierarchy       -- Mahlo reflection degrees (Setzer 1998, 2008)
  | reflectingHierarchy   -- higher-order Pi^n reflection (Rathjen 1998, 2014, 2017)
  | embeddingCardinal     -- single-structure accessible-category reflection
                          --   (ramsey → vopenka; Adamek-Rosicky, Bagaria)
  | kunenRankIntoRank     -- sequential Exact Structural Reflection degrees
                          --   (huge → kunenI0; Bagaria-Lucke "Huge Reflection")
  | exactingFrontier      -- SR-defined 2024 frontier (exacting / ultraexacting;
                          --   Aguilera-Bagaria-Lucke); ZFC-consistent rel I0
  | reinhardtOpen         -- OPEN: ambient self-similarity above ESR
                          --   (schlutzenbergVLambdaPlus2 choiceless ceiling;
                          --   reinhardtDirected FX-native).  Postulate-only / open;
                          --   NOT a strength FX derives — see §11.8.2.1
  | custom (tag : Name)   -- user-declared with explicit witness
  deriving DecidableEq
```

**Integration into ProfileExtension (§3.14):**

Every `ProfileExtension` carries:
- `strengthBefore : ConsistencyStrength` — the base profile's tag.
- `strengthAfter : ConsistencyStrength` — the extended profile's tag.
- `strengthWitness` — a checked justification that `strengthAfter`
  is an honest upper bound: the extension's new axioms do not exceed
  the claimed strength.  For Generator entries that are DEFINITIONS
  (conservative extensions), `strengthAfter = strengthBefore`
  automatically.  For bare declarations (non-conservative),
  `strengthAfter ≥ strengthBefore` and the gap must be named.

**FX0-PolyCell implication:** the `.fx0c` certificate header carries
the `ConsistencyStrength` tag.  The external verifier checks that the
tag is MONOTONE through the certificate chain (extensions never
decrease strength) but does NOT verify the tag is correct (that's a
Layer 2 Lean proof).  A certificate claiming `finitistic` strength
while using a Generator entry that requires `inaccessible` is caught
by the Lean proof, not by the verifier — the verifier's job is
structural cell checking, not ordinal analysis.

**The Gödel-climbing mechanism (D.10 of extended-roadmap.md):**
adding `Con(S_n)` as a new Generator entry is a ProfileExtension
with `strengthBefore = strength(S_n)` and `strengthAfter =
strength(S_n) + 1` (informally — the ordinal arithmetic is tracked
by the tag, not formalized as real ordinals).  STRICT-35 checks the
extension's critical pairs; the ConsistencyStrength tag tracks the
resulting position.  Each climb is one verified commit.

**Gödel is the engine of the apex ladder, not its ceiling.**  FX
never proves `Con(FX)` — but for every WEAKER flag it does: FX at
reflection degree *n+1* proves `Con(FX` at degree *n*`)` (Gentzen-
style: `Con(PA)` is provable, just not *in* PA — it needs ε₀-induction,
i.e. a stronger reflection degree).  The structural-reflection ladder
(`inaccessible → mahlo → … → kunenI0 → exacting → …`, §11.8.2) IS this
tower of "prove the consistency of your previous self."  So
incompleteness is generative here: **if FX could prove its own
consistency, the ladder would collapse to a fixed point and the supply
of genuinely new problems would run dry; because no degree proves its
own `Con`, there is ALWAYS a strictly stronger reflection degree to
climb to.**  The boundary is also un-cheatable from inside: the Gödel-II
hypotheses (consistency, decidable proof-checking, arithmetic strength)
are each load-bearing FX commitments, and the only known escapes break
one of them — true arithmetic drops decidability, Presburger drops
strength, Willard self-verifying theories drop the *provable totality*
that FX's SN + decidable-Conv discipline (§11.7.2) requires.  FX is
therefore squarely Gödel-bound by design, and re-representing `Nat`
cannot change this (the homotopical dressing is orthogonal to the
arithmetic content that triggers coding).  The response is never escape
but *climb* — which is exactly why the apex is unbounded.  See §11.8.2.1
for how this interacts with the Reinhardt frontier.

**The climbing ladder IS the Chaitin incompressibility ladder (O-AIT,
§11.9.2.1).**  With FX0 as a *fixed* reference machine (§12.6),
`K_FX0(x) := size of the smallest FX cell producing x` is a concrete
Kolmogorov measure (no floating additive constant).  Chaitin's
incompleteness: a theory proves `K_FX0(x) > c` only up to `c ≈ K(theory)`.
So the **provable-incompressibility ceiling rises strictly with reflection
degree** — the same tower that proves `Con` of its previous self unlocks
strictly higher provable-incompressibility bounds, and *consistency
strength = the provable-`K`-ceiling*.  Two consequences feed the §11.9
program: the ladder's own ordinal analysis (O-ORD) is dischargeable as a
mechanized **Beklemishev GLP reflection algebra** (§11.9.3 OP7), turning
"rung *n+1* ⊢ Con(rung *n*)" from calibration prose into a theorem read
off the GLP Worm; and "an idea feels already-stated" is the *signed*
statement that its conditional `K_FX0(· ∣ corpus)` is low (§11.9.1.3
O-HARD), i.e. it lives below the current reflection degree's `K`-ceiling.

**This is what makes the §11.9.4 discovery engine provably
open-ended.**  A Kolmogorov-driven search that minimizes the certified
description length `L` while maximizing `Hardness` would, on a *fixed*
reflection degree, eventually exhaust the supply of high-`Hardness` facts
(everything compressible at that strength gets found, and `Hardness → 0`).
But because the provable-`K`-ceiling rises *strictly* with reflection
degree and no degree proves its own `Con`, climbing one rung (the
Gödel-climbing ProfileExtension above) always unlocks a fresh frontier of
facts that were *certifiably* incompressible below it.  So the discovery
engine never runs dry — and engine open-endedness is not a separate
property to be engineered but the SAME theorem as the apex ladder's
unboundedness.  Incompleteness is the engine's fuel (`O-ENGINE`, §11.9.4).

### 11.7.2 Turing's ceiling → Tot/Div/Productive as Generator-level effect grades

**The constraint:** a Turing-complete language has undecidable
properties (halting, equivalence, Rice's theorem).  FX resolves this
by partitioning programs into three computability classes, each
tracked by the graded effect system (dimension 4) and enforced at
the Generator table level.

**Actionable mechanism — per-Generator totality classification:**

```lean
/-- Every Generator carries a totality class that the certifier
    enforces through child-sort constraints. -/
inductive TotalityClass where
  | total       -- always terminates; SN + CR + SR + decidable Conv hold
  | productive  -- non-terminating but every observation terminates
                -- (codata streams, servers, reactive systems)
  | partial     -- may diverge; per-step SR holds, chain may be infinite
  deriving DecidableEq
```

Each Generator's metadata includes `totalityClass : TotalityClass`.
The certifier enforces the following child constraint:
- A `total` Generator's children must ALL be `total` (no Div child
  in a Tot parent).
- A `productive` Generator may have `total` or `productive` children
  (but not `partial`).
- A `partial` Generator may have children of any class.

This is checked COMPUTABLY by the certifier (a comparison on the
TotalityClass enum per child — ~3 lines of logic in the
per-child reconciliation V2-L1cert.2).  The FX0-PolyCell verifier
checks the same constraint from the serialized Generator table.

**What this buys:**
- The Tot fragment is a DECIDABLE sub-language: SN holds (every
  total Generator's children are total → structural induction gives
  termination), so NbE terminates, so Conv is decidable.
- The Productive fragment supports verified reactive systems: every
  observation on a codata cell reaches a value (productivity =
  every `productive` Generator's observations are guarded by a
  decreasing measure on the observation index).
- The Partial fragment is Turing-complete: any computable function
  expressible, but the metatheory quartet does NOT hold for it.
  Verification is per-step (each dim-1 cell certifies), not
  per-chain (the chain may diverge).

**Rice's theorem implication:** no computable property of the
Partial fragment's input-output behavior is decidable in general.
BUT: properties of INDIVIDUAL STEPS are decidable (the certifier
checks each step).  Properties of FINITE PREFIXES are decidable
(fuel-bounded verification).  Properties of the TOTAL subfragment
are decidable.  The boundary between "decidable" and "undecidable"
is the Tot/Partial effect grade — a TYPED, CHECKED boundary, not
an invisible runtime hazard.

### 11.7.3 The open/closed spectrum → SiteOpenness as a profile parameter

**The constraint:** closed formal systems (fixed axioms) have strong
internal reasoning but cannot grow; open systems (arbitrary axiom
addition) can grow but lose internal guarantees.  Traditional proof
assistants are fully closed (the type theory is fixed at compile
time).

**Actionable mechanism — `SiteOpenness` as a profile field:**

```lean
/-- How open the profile is to external content.  Each level is
    strictly weaker in internal guarantees and strictly stronger in
    expressivity. -/
inductive SiteOpenness where
  | sealed          -- no extensions admitted; strongest internal reasoning
                    -- (fixed Generator table; full quartet provable)
  | extensible      -- extensions via ProfileExtension with admission contract
                    -- (new Generators admitted if STRICT-35/36/37 pass;
                    --  quartet holds for the Tot fragment of each extension)
  | reflective      -- extensions + self-reference via Era R ReflTerm
                    -- (the kernel can manipulate its own terms as data;
                    --  Tarski hierarchy prevents paradox via partiality
                    --  of ReflTerm.elaborate)
  | oracle          -- external oracle calls (SMT, ML model, hardware RNG)
                    -- with explicit trust boundaries
                    -- (oracle results are NOT certified; they enter as
                    --  `partial` Generator entries with explicit fallibility)
  deriving DecidableEq
```

The `fxProfile` default is `extensible` — new features enter via
`ProfileExtension` with verified admission.  Moving to `reflective`
requires Era R (Day 88.5+).  Moving to `oracle` requires explicit
trust boundaries (the oracle's output is wrapped in a `partial`
Generator with `ConsistencyStrength` capped at `finitistic` unless
the oracle provides its own soundness certificate).

**ProfileExtension integration:**

```lean
structure ProfileExtension (base : AdmissibleProfile) where
  -- ... existing fields from §3.14 ...

  /-- The extension's openness must not exceed the base's. -/
  opennessCompatible :
    extension.openness ≤ base.openness

  /-- The extension's consistency strength is tracked. -/
  strengthAfter : ConsistencyStrength
  strengthMonotone : base.consistencyStrength ≤ strengthAfter
```

A `sealed` profile cannot admit ANY extension (the strongest
guarantee — useful for deployed production kernels where the type
theory must not change).  An `extensible` profile admits extensions
that pass STRICT-35/36/37.  A `reflective` profile additionally
permits self-referential programs.  An `oracle` profile additionally
permits external calls with explicit trust boundaries.

**FX0-PolyCell implication:** the `.fx0c` certificate header carries
the `SiteOpenness` tag.  The external verifier checks that the tag
is consistent with the Generator table (a `sealed` certificate
cannot reference Generators not in the original table; an `oracle`
certificate must mark oracle-derived cells with a trust boundary
tag).

### 11.7.4 The decidability frontier as a computable function

The three ceilings (Gödel, Turing, Rice) define a FRONTIER between
decidable and undecidable properties.  Under the PolyCell design,
this frontier is itself COMPUTABLE — the certifier can TELL YOU where
the frontier is for your current profile.  The §11.9 program targets a
concrete *certified undecidability locus* here: in the protocol sort
(§11.2) under the quantum profile (§3.15), **MIP\*=RE** (Ji-Natarajan-
Vidick-Wright-Yuen 2020, refuting Connes embedding) forces `Conv` on
certain nonlocal-game `.protocol` cells to be UNDECIDABLE — so
`isDecidableInProfile?` returns a *certified* `undecidable` with a
quantum-information reduction witness, pinning the exact boundary of the
decidable-typechecking guarantee per sort (§11.9.3 OP6).  This is the
positive use of the frontier: not every sort's `Conv` is decidable, and
FX names *where* it stops, with a witness.

**Actionable mechanism — `isDecidableInProfile?`:**

```lean
/-- Given a property (expressed as a predicate on certified cells),
    determine whether it is decidable in the current profile.
    Returns:
    - `decidable decider` if the profile's Tot fragment + Generator
      table + completed metatheory gives a terminating decision
      procedure
    - `undecidable witness` if the property reduces to a known
      undecidable problem (halting, Rice, Post correspondence, ...)
      with an explicit reduction witness
    - `unknown` if neither decidability nor undecidability is
      established (the honest "I don't know")
-/
inductive DecidabilityStatus where
  | decidable (decider : RawCell scope → Bool)
  | undecidable (reductionWitness : ReductionToHalting)
  | unknown
```

This is NOT a universal decidability oracle (that's impossible by
Rice's theorem).  It is a FINITE, CONSERVATIVE classifier that
knows about the specific decidability witnesses in the profile's
metatheory (the 24-dimensional decidability matrix from §11.5, the
TotalityClass per Generator, the SiteOpenness level).  It says
"decidable" only when it has a concrete decider; "undecidable" only
when it has a concrete reduction; "unknown" otherwise.

**Integration with the compiler agent protocol (fx_design.md §24):**

```text
GET /decidability?property=Conv(a,b)
  → { status: "decidable", decider: "NbE-NF-equality",
      complexity: "O(size(a) + size(b))" }

GET /decidability?property=Halts(program)
  → { status: "undecidable",
      reduction: "reduction to halting problem via Rice" }

GET /decidability?property=HasType(ctx,term,ty)
  → { status: "decidable", decider: "certifyRawCellExact?",
      complexity: "O(size(term) * max_child_arity)" }
```

An agentic LLM working inside FX can QUERY the decidability frontier
before attempting a proof: if the property is undecidable, the agent
knows to either (a) restrict to a decidable subfragment, (b) propose
a site extension that makes it decidable, or (c) report "this
requires a stronger axiom" with the minimum ConsistencyStrength
increase.  This is the "Gödel becomes boring" mechanism from §12.5
made computationally concrete.

### 11.7.5 Cross-cutting verification gates

The mechanisms above integrate into the existing strict harness:

| Gate | What it checks | Where |
|---|---|---|
| **STRICT-CS** | ConsistencyStrength monotone through ProfileExtension chain | Profile admission |
| **STRICT-TC** | TotalityClass constraints on Generator children | certifyRawCellExact? per-child check |
| **STRICT-SO** | SiteOpenness compatibility on extension admission | ProfileExtension.opennessCompatible |
| **STRICT-DF** | DecidabilityStatus conservative (never claims decidable without a concrete decider) | isDecidableInProfile? |

These are COMPUTABLE checks — each is a finite comparison on an enum
or a table lookup.  The FX0-PolyCell verifier checks STRICT-TC
(the child totality constraint, ~3 lines of code in the per-child
reconciliation); the others are Layer 2 Lean proofs that the
verifier trusts via the certificate header tags.

---

## 11.8 The Maximal-Power Computable Kernel

This section pins FX's foundational ambition: **target the strongest
currently-known sound type theory that admits decidable
typechecking**.  Codex audit M-2026-05-27 (project memory
`feedback_polycell_structural_vs_semantic`) flagged that the current
PolyCell substrate provides STRUCTURAL admission only.  This section
commits to the typed, decidable, maximally-powerful kernel that will
sit on top of it.

**The directive: every feature, fully decidable, all at once** — no
"undecidable corner" of the type theory.  Maximum theoretical power
constrained only by: (1) per-feature soundness in published theory,
(2) decidable typechecking under cubical NbE, and (3) the
zero-axiom discipline from §11.

This is multi-year work.  Every component is **sound in isolation**
by known theory — but the **soundness of the COMBINATION is a genuine
proof obligation**, not a corollary of the per-feature citations.
§11.8.0 is the obligations ledger that tracks this honestly: the
per-feature work is assembly; the joint metatheory (O-NORM / O-CONF /
O-CANON) is research.

### 11.8.0 Apex metatheory obligations — the combination is not free

**Honesty discipline, applied to the apex.**  §3–§4 and §11.6 obey
the manifesto rule: every claim is a constructive definition, a cited
decision procedure with complexity, or an explicit out-of-scope tag.
This subsection extends that discipline to all of §11.8.  Every
feature below (cubical, HIIRT, guarded recursion, internal
parametricity, MTT + cohesion, the 21-dim graded layer, the
structural-reflection ladder) is sound **in isolation** by published
theory.  Their **union is not sound by corollary**: joint
normalization, joint confluence, and joint canonicity of the combined
system are proof obligations, several of them open research.  Naming
the per-feature papers does not discharge the joint obligation;
pretending it does would be exactly the placeholder pattern §1
forbids.

**The obligations ledger.**  Status is one of: **open research** (no
one has done it — naming it precisely is the deliverable) or
**specifiable now** (pinnable with a schema or clause, no new
mathematics required).

| ID | Obligation | Status | Gates |
|---|---|---|---|
| **O-NORM** | Joint normalization of the feature union (cubical + HIIRT + guarded + parametricity + MTT + 21-graded) | open research | decidable typed Conv, MILESTONE A→D |
| **O-CONF** | Joint confluence of the full reduction relation (βηι + cubical Kan + user rewrite rules + commuting conversions + η-everywhere) | open research | generic cd_lemma at apex scale (§11.6.1) |
| **O-CANON** | Canonicity for the union (follows O-NORM) | open research | consistency at apex (§11.8.8) |
| **O-CUBE-PARAM** | Coherence of the path dimension (cubical) with the bridge dimension (internal parametricity) | open (Cavallo-Harper unifies) | Phase Z₄ + Z₈ |
| **O-ORD** | Ordinal-notation / well-ordering substrate establishing each reflection-ladder rung's strength — *discharge route: mechanized Beklemishev GLP reflection algebra, §11.9.3 OP7* | open research | MILESTONE B ladder (§11.8.2) |
| **O-REFL-MODEL** | Construction / relative-consistency justification of the reflection-degree universes inside FX's own (∞,ω)-topos substrate | open research | MILESTONE B |
| **O-FIRE** | Algebraic effects + handlers confined to a Fire-Triangle-safe graded / ∂CBPV fragment (§3.0.3) | specifiable now | §11.8.6 effects soundness |
| **O-IR-SCHEMA** | Codes-for-IR universe + strict-positivity criterion — the actual content of "supporting HIIRT" | specifiable now | Phase Z₆ (§11.8.3) |
| **O-II** | Induction-induction / QIIT well-formedness at the typed layer, reconciled with the v2 substrate's deliberate un-indexing | specifiable now | Phase Z₅ (§3.16.5) |
| **O-ELAB** | Elaborator soundness (emits only kernel-recheckable terms) + completeness for the decidable fragment | specifiable now | MILESTONE A (§11.8.3) |
| **O-ERASE** | Erasure-correctness metatheorem (the §1.5 zero-runtime-cost premise) | specifiable now | MILESTONE D (§3.14) |
| **O-SUBST-BRIDGE** | Equivalence of the Allais parallel-fold substitution (§4) and the Kaposi-Xie single-substitution calculus (§3.11) | specifiable now | — |
| **O-INTERNAL** | The internalization principle as method (external quantity → typed certified computable cell) — the generator of the rows below | meta (§11.9.0) | beyond apex |
| **O-OBSTRUCT** | Obstruction-cohomology of the 21-dim profile: H² over the dimension lattice classifying jointly-sound subsets (the §3.7/§3.14 no-go register as a cochain complex) | specifiable now; sublattice shippable | §11.9.1.1, beyond apex |
| **O-HOMOLOGY** | Squier proof-homology = Hilbert's 24th problem (proof simplicity); the cd/critical-pair resolution's Hₙ | shippable now (H₁, term fragment) | §11.9.1.2, beyond apex |
| **O-HARD** | The Hardness instrument N·D·(1+A)·(1+B) + δ-discrepancy — certified novelty/depth metric over the Conv-deduped FactDAG | D,B shippable now; N specifiable; A open | §11.9.1.3, beyond apex |
| **O-AIT** | Synthetic algorithmic information theory: FX0 as fixed K-machine; Chaitin-ceiling ladder = Gödel-climbing ladder; Kₙ truncation spectrum | specifiable now | §11.9.2.1, beyond apex |
| **O-THERMO** | Synthetic thermodynamics: SN (O-NORM) = Second Law (free-energy descent); Tot/Div = phase transition; temperature unifies reduction & search | open research | §11.9.2.2, beyond apex |
| **O-TSPACE** | Geometry of theory-space: cellular-tensor associator (T5) = curvature; ProfileExtensions = tangent cone; Hardness = metric | open research | §11.9.2.3, beyond apex |
| **O-FIREWALL** | Goodhart-resistant agent loop (the A-term rejects noise) + paraconsistent raw/certified proof firewall (adversarial-proposer-safe) | specifiable now | §11.9.4, §24 |
| **O-ENGINE** | Kolmogorov-driven discovery engine: minimize the certified description-length bound `L(T∣KB)` / maximize `Hardness`; homology-guided abstraction (`H₁`); open-endedness from the reflection ladder | specifiable now | §11.9.4, §24, §11.7.1, beyond apex |

**The committed normalization route (O-NORM / O-CANON).**  FX commits
to ONE technique to carry the joint metatheory: **BKS internal
sconing (Tier 0, §3.0.2) extended to the full kernel signature**,
with Synthetic Tait Computability (Axis 12) and Tait reducibility
(§11.6.1) as independent cross-checks.  Sconing is the only route
known to compose across heterogeneous features — it derives
canonicity / normalization / parametricity from one gluing witness
per signature extension.  O-NORM is precisely the obligation to
construct the sconing witness for the COMBINED signature, not per
isolated feature.  It is the apex's single load-bearing proof
obligation; the §11.8.14 definitional-univalence normalization (its
O3) is one special case.

**Relative-consistency stance (a disclaimer, not an obligation).**
For every reflection-ladder flag, FX@flag is consistent **relative
to** an ambient metatheory of strength ≥ the flag's classical
calibration (§11.8.2) — **assumed, not proven**.  By Gödel II, FX
cannot prove its own consistency at or above its own strength
(§11.7.1).  The ladder is a tower of *relative* consistency
strengths, honestly assumed per rung, never an internal absolute
guarantee.

**How the rest of §11.8 references this ledger.**  Downstream
subsections cite an obligation by ID rather than re-asserting
soundness inline: §11.8.7's decidability matrix gates combined-
fragment entries on O-NORM; §11.8.6's algebraic effects cite O-FIRE;
§3.16.5/6's IR/HIT admission cites O-IR-SCHEMA / O-II; §11.8.2's
ladder cites O-ORD / O-REFL-MODEL.  The **§11.9 Internalization Program**
registers its nine frontier obligations (O-INTERNAL / O-OBSTRUCT /
O-HOMOLOGY / O-HARD / O-AIT / O-THERMO / O-TSPACE / O-FIREWALL /
O-ENGINE) here for
accountability, but they are **beyond-apex** — present in the ledger,
explicitly NOT on the MILESTONE A–D critical path (the firewall of
§11.9.0).  This ledger is the single accountable place tracking the
apex's open frontier AND the post-apex program, in the idiom of §12's
risk register and §11.8.14.1's stated open problems.

### 11.8.1 The seven gaps in the current substrate

Codex audit M-2026-05-27 (second pass, evening) identified seven
foundational gaps relative to the diabolic-apex target:

| # | Gap | Severity | Fix in §11.8 |
|---|-----|----------|--------------|
| 1 | `gen_universe`'s payload is `Unit` ⇒ `Universe : Universe` syntactically (Girard's paradox at the admission level) | SEVERE | §11.8.2 universe-level payload |
| 2 | Eliminators have no motive children ⇒ non-dependent only | BLOCKING | §11.8.3 motive children in spine |
| 3 | `SupportedGenerator` admits all 194 + `GenPayloadEvidence = Unit` | HIGH | §11.8.4 syntactic vs semantic admission |
| 4 | No typing judgment (`HasType` absent) | HIGH | §11.8.5 typed layer |
| 5 | Only dim 1 (type) modeled; 20 other FX dimensions absent | HIGH | §11.8.6 21-dim integration |
| 6 | Consistency unprovable without typed metatheory | FOUNDATIONAL | §11.8.8 canonicity + consistency |
| 7 | `TotalityClass` metadata exists but unenforced | MEDIUM | §11.8.4 admission gating |

### 11.8.2 Universe policy — maximal power

The kernel commits to the following universe design:

**Two-Level Type Theory (2LTT) skeleton.**  Following Shulman 2017
"Brouwer's fixed-point theorem" + Annenkov-Capriotti-Kraus 2017
"Two-level type theory and applications", the kernel ships TWO
parallel universe hierarchies sharing the same syntactic
substrate:

* **Inner univalent universes** (`gen_universeU n` for `n : LevelExpr`):
  cubical Kan, no K-axiom, all univalence machinery.  Objects
  live here.
* **Outer strict universes** (`gen_universeS n` for `n : LevelExpr`):
  strict normalization + strict large-elimination discipline;
  **univalence STILL applies** via `Step.eqType` at the outer mode
  per §11.8.13 univalence-everywhere discipline.  "Strictness" here
  refers to the REDUCTION CALCULUS and ELIMINATION SHAPE, NOT to
  propositional identity.  Metatheory + computational reflection
  live here.  (Diverges from 2LTT orthodoxy which usually puts
  K-axiom + UIP definitional in the outer mode — FX rejects that
  trade in favor of univalence-everywhere, since K + univalence
  ⊢ ⊥ per Hofmann-Streicher 1998 forces a choice, and FX's
  univalence-as-theorem discipline forces univalence to win.)
* **Lifting / lowering**: explicit `gen_univLift` / `gen_univLower`
  generators with Hofmann-Streicher natural transformations that
  PRESERVE univalence across modes (per §11.8.13).

This is **strictly more powerful** than single-level cubical TT
(can prove metatheorems about univalent objects in the outer mode
without losing univalence anywhere) AND strictly more disciplined
than standard 2LTT (which sacrifices outer-mode univalence to get
K).  FX gets univalence-everywhere by keeping the inner/outer
distinction at the REDUCTION-CALCULUS level instead.

**Hierarchy.**  Predicative cumulative hierarchy inside each level:
`Type 0 ⊆ Type 1 ⊆ …` with `Type n : Type (n+1)`.  No universe
collapse, no Type-in-Type, no Russell paradox vector.

**Impredicativity at the bottom.**  Two impredicative universes:
`SProp` (definitional proof irrelevance) and `Type₀` (System-F-style
polymorphism).  Inside 2LTT, both exist at each level.  Higher
universes (`Type 1+`) are strictly predicative.

**Cumulativity.**  `Type m ⊆ Type n` when `m ≤ n` definitionally,
both inside the inner and outer hierarchies.  Plus 2LTT lifting:
`InnerType n ⊆ OuterType n` via `gen_univLift`.

**Universe polymorphism via `LevelExpr`.**  Declarations
parameterized over universe-level expressions in BOTH hierarchies:

```lean
inductive LevelExpr where
  | lzero
  | lsucc (e : LevelExpr)
  | lmax (e1 e2 : LevelExpr)
  | limax (e1 e2 : LevelExpr)  -- impredicative max (collapses to zero if e2 = lzero)
  | lvar (idx : Nat)

def LevelExpr.eval (env : Nat → Nat) : LevelExpr → Nat := ...
```

`DecidableEq LevelExpr` is structural.  Level equality up to algebra
(`lmax e e = e`, `lmax lzero e = e`, …) is also decidable in
**polynomial time** via normalization (per Mörtberg-Sterling
2024 universe-normalization algorithm).

**First-class universe codes.**  Universe levels themselves are
first-class data in the outer universe — declarations can quantify
OVER `LevelExpr`, pattern-match on it, and use it computationally.
Enables "universe-polymorphic universe construction" (a single
declaration producing universes of any level).

**Russell-external / Tarski-internal split.**  Tarski-style
internally for definite reduction rules; Russell-style externally
for ergonomics.  `gen_universeU` / `gen_universeS` payloads ARE
the Tarski codes; `El` is the implicit decoding.

**Directed type theory universes.**  Following Riehl-Shulman 2017
"A type theory for synthetic ∞-categories" + Loubaton 2307.11931,
the kernel ships ADDITIONAL directed universes:

```lean
| .gen_universeD n  -- directed: types-as-(∞,1)-categories
| .gen_universeOmega n  -- directed: types-as-(∞,ω)-categories
```

Directed universes are SEPARATE from undirected.  Inside
`gen_universeD`: morphisms are directed (have source/target),
homs are not symmetric.  This is the kernel-level commitment to
synthetic higher category theory.

**SProp dedicated universe.**  A separate `gen_sprop` Generator for
the strict universe with definitional proof irrelevance.
Eliminating SProp into Type requires subsingleton elimination
(restricted to subsingleton targets, plus `False`).

**Apex structural-reflection hierarchy as universe flags.**  FX's
foundation is CATEGORICAL, not set-theoretic: the kernel is an
(∞,ω)-topos substrate (§3.7), a universe is a classifying object for
small fibrations (Hofmann-Streicher / Shulman, ref U26), and ZF-style
sets are only the 0-truncated discrete view (§3.9).  The `UniverseFlag`
payload therefore does NOT postulate set membership, the cumulative
hierarchy V, the axiom of choice, or elementary embeddings j : V → V.
Each flag names a DEGREE OF STRUCTURAL REFLECTION (Bagaria, "Large
cardinals as principles of structural reflection") — categorically,
how rich a class of structures the universe reflects into a small
(universe-internal) subclass.  Two regimes:

* **Single-structure reflection** (`inaccessible` → `vopenka`): "every
  proper class of structures contains a small one reflecting it."  Has
  a clean category-theoretic form (Adámek-Rosický accessible-category
  theory; Bagaria-Casacuberta-Mathias-Rosický small orthogonality
  classes; Vopěnka = SR for ALL classes = "Ord ↛ Graph fully
  faithfully").
* **Sequential Exact Structural Reflection** (`huge` → `kunenI0`):
  Bagaria-Lücke "Huge Reflection" (arXiv:2106.01462) push structural
  reflection PAST Vopěnka, through huge, to the **rank-into-rank**
  region.  ESR(κ,λ,𝒞): every large 𝒞-structure receives a
  structure-embedding from a small one; sequential (length-ω) ESR over
  Π₁ classes is the categorical form of I1, climbing to I0.  These
  embeddings are MORPHISMS between objects of the category of
  𝒞-structures — not `j : V → V`.  So `kunenI0` is a genuine,
  categorically-stated reflection degree FX TARGETS, not a calibration
  tag.

**FX's committed categorical apex is `kunenI0` via sequential ESR** —
I0-strength self-similarity stated as a reflection principle.  Just
above it sits the 2024 frontier (`exacting`, `ultraexacting`;
Aguilera-Bagaria-Lücke arXiv:2411.11568), structural-reflection-defined
and ZFC-consistent relative to I0.  Above THAT, the ambient
self-embedding (`reinhardt*`) splits into a Gödel-hard ordinal half and
an FX-native higher-cell half — see "The Reinhardt frontier" below.
`schlutzenbergVLambdaPlus2` is the choiceless ZF ceiling (ZF-PROVEN
consistent rel I0, Schlutzenberg-Goldberg).  See "Why reflection, not
embeddings" below.

```lean
inductive UniverseFlag where
  -- Base: universe-as-classifier
  | standard                    -- ordinary universe classifying small fibrations
  | inaccessible                -- universe closed under Pi/Sigma/W containing a
                                --   smaller universe (Grothendieck universe internal
                                --   to the topos); calibration: inaccessible
  -- Mahlo reflection (regular-fixpoint reflection of universe-valued maps)
  | mahlo                       -- universe whose internal normal universe-valued maps
                                --   have a regular fixpoint sub-universe
                                --   (Setzer / Dybjer-Setzer predicative Mahlo);
                                --   calibration: Mahlo
  | superMahlo                  -- Mahlo reflection iterated once; calibration: super-Mahlo
  | nMahlo (n : Nat)            -- Mahlo reflection iterated n times; calibration: n-Mahlo
  | hyperMahlo                  -- limit of the iterated Mahlo reflection tower
  -- Higher-order (Pi^n) reflection
  | weaklyCompact               -- tree-property / Pi^1_1 reflection;
                                --   calibration: weakly compact
  | indescribable (n : Nat)     -- the universe reflects Pi^n formulas (Pi^n-reflection);
                                --   calibration: n-indescribable
  | reflecting                  -- full higher-order structural reflection;
                                --   calibration: reflecting
  -- Accessible-category reflection degrees (Adamek-Rosicky; Bagaria-Casacuberta-
  --   Mathias-Rosicky: definable orthogonality classes in accessible categories
  --   are small)
  | ramsey                      -- partition reflection; calibration: Ramsey
  | measurable                  -- non-trivial accessible endofunctor without a fixpoint;
                                --   calibration: measurable
  | strong (alpha : Nat)        -- alpha-graded accessible reflection;
                                --   calibration: alpha-strong
  | woodin                      -- determinacy-grade reflection; calibration: Woodin
  | supercompact                -- small orthogonality classes for Sigma_2-definable
                                --   classes; calibration: supercompact
  | extendible                  -- small orthogonality classes, unrestricted;
                                --   calibration: extendible
  | vopenka                     -- TOP CLEAN CATEGORICAL DEGREE: structural reflection
                                --   for ALL classes = every colimit-closed full
                                --   subcategory of a locally presentable category is
                                --   coreflective = Ord does not embed fully into Graph
                                --   (Adamek-Rosicky; Bagaria SR-for-all-classes);
                                --   calibration: Vopenka's principle
  -- Sequential Exact Structural Reflection (Bagaria-Lucke "Huge Reflection",
  --   arXiv:2106.01462): the CATEGORICAL form of the rank-into-rank region.
  --   ESR embeddings are morphisms B -> A in the category of C-structures, NOT
  --   j : V -> V.  These are reflection degrees FX TARGETS, not calibration tags.
  | huge                        -- sequential ESR degree; calibration: huge
  | nHuge (n : Nat)             -- sequential ESR degree; calibration: n-huge
  | kunenI3                     -- sequential ESR degree; calibration: I3
  | kunenI2                     -- sequential ESR degree; calibration: I2
  | kunenI1                     -- Pi_1 sequential ESR (<== I1, Bagaria-Lucke);
                                --   calibration: I1
  | kunenI0                     -- ESR rank-into-rank apex; FX's COMMITTED categorical
                                --   apex; calibration: I0
  -- Structural-reflection frontier (Aguilera-Bagaria-Lucke 2024, arXiv:2411.11568):
  --   SR-defined, ZFC-consistent relative to I0, breaks the linear large-cardinal
  --   picture, bears on the HOD / Ultimate-L conjectures.  Never mechanized anywhere.
  | exacting                    -- exacting: V != HOD; SR-defined frontier degree
  | ultraexacting               -- ultraexacting: below a measurable => Con(ZFC +
                                --   proper class of I0); the new problem class
  -- ===== OPEN FRONTIER (postulate-only / open consistency; NOT admitted reflection
  --   degrees; honest catalogue entries, NOT objects FX proves or admits) =====
  | schlutzenbergVLambdaPlus2   -- choiceless ZF ceiling: V_{lambda+2} self-embedding,
                                --   ZF-PROVEN consistent rel I0 (Schlutzenberg-Goldberg
                                --   JML 2024); above ESR, calibration ceiling
  | reinhardtDirected           -- (c) FX-NATIVE OPEN: a non-invertible elementary
                                --   self-endofunctor of gen_universeOmega that FIXES the
                                --   0-truncation and acts on higher directed cells.
                                --   Godel block does NOT obviously apply (no ordinal
                                --   moved => may not imply Con(FX)); consistency /
                                --   constructibility UNKNOWN; unstatable outside directed
                                --   univalence.  THE open frontier FX uniquely poses.
                                --   (The (b) ordinal-critical-point Reinhardt j : V -> V
                                --    is AXIOM-ONLY -- unprovable by Godel, Kunen-blocked
                                --    in ZFC, open in ZF -- and is intentionally NOT a
                                --    flag; see "The Reinhardt frontier".)
```

**Why reflection, not embeddings.**  Set theory phrases universe
self-resemblance as an elementary embedding j : V → V, because ZF is
isomorphism-blind: it cannot say "the universe is equivalent to a part
of itself," so it reaches for an external structure-preserving map.  FX
is the opposite kind of foundation.  Its universe is univalent (§3.10,
§11.8.13): equivalent structures are EQUAL, so a structure-preserving
self-map that genuinely moved things would have to be the identity —
the embedding idiom degenerates.  The univalence-native idiom for
self-resemblance is REFLECTION: every structure on the universe is
already captured by a small sub-universe.  And reflection reaches
HIGH: Adámek-Rosický + Bagaria-Casacuberta-Mathias-Rosický give the
single-structure degrees up to Vopěnka a purely category-theoretic
form (coreflective subcategories, small orthogonality classes,
accessible-endofunctor fixpoints), and Bagaria-Lücke "Huge Reflection"
push **sequential Exact Structural Reflection** PAST Vopěnka, through
huge, to the **rank-into-rank / I0 region** — still as morphisms
between 𝒞-structures, never `j : V → V`.  So FX reaches I0-strength
self-similarity by climbing the reflection ladder, not by asserting an
external automorphism.

Three things make this not just an idiom swap but the RIGHT
foundation for the question.  (1) **No Kunen obstruction is even
expressible.**  Kunen's inconsistency uses the axiom of Foundation
ESSENTIALLY (Daghighi-Golshani-Hamkins-Jeřábek, arXiv:1311.0814 — drop
Foundation and nontrivial elementary self-embeddings exist) AND the
axiom of choice (the ω-Jónsson algebra).  FX's substrate has NEITHER:
it is non-well-founded by construction (coinduction first-class,
§11.7.2) and AC-free (zero-axiom).  (2) **Univalence is pro-rigidity,
not anti-embedding.**  Goldberg (arXiv:2103.13961) proves elementary
embeddings into a fixed target agree on the ordinals and are UNIQUE
above the least extendible — and a unique self-map is exactly what
univalence permits (a contractible space of equivalences).  So
univalence does not forbid high reflection; it forces it to be
canonical, which Goldberg confirms it is.  (3) **Reflection carries
WITNESSES** (a reflected structure comes with the small sub-universe
that captures it), matching FX's constructive zero-axiom discipline,
whereas an embedding is a bare existence claim.  The ambient
self-embedding `j : V → V` itself (the thing FX does NOT reach by
reflection) splits into a Gödel-hard half and an FX-native open half —
see "The Reinhardt frontier" next.

Each flag has its own decidable admission predicate.  Implementation
schedule per §11.8.9: `standard` + `inaccessible` (universe closure)
ship Phase Z₆ kickoff; the Mahlo reflection degrees (`mahlo` →
`hyperMahlo`) + higher-order reflection (`weaklyCompact` →
`reflecting`) ship Phase Z₆ proper; the single-structure
accessible-category degrees (`ramsey` → `vopenka`) then the
**sequential-ESR rank-into-rank degrees (`huge` → `kunenI0`)** ship
over the following months as Phase Z₆+, leveraging the
polynomial-universe + HIIRT + (∞,ω) directed substrate already
committed in §3.10 + §3.16.6.  **FX's committed categorical apex —
I0-strength self-similarity via sequential ESR (`kunenI0`) — lands at
★ MILESTONE B (§11.8.12) within 6 months of Phase Z₆ kickoff.**  The
2024 frontier degrees (`exacting`, `ultraexacting`) are stretch targets
in the same phase — structural-reflection-defined, ZFC-consistent rel
I0, and never mechanized anywhere, so shipping them is genuinely
first-in-class.  The open-frontier entries (`schlutzenbergVLambdaPlus2`,
`reinhardtDirected`) are NOT implementation targets — they are honest
catalogue markers (choiceless ceiling; FX-native open problem) per "The
Reinhardt frontier".

**Reflection-degree ladder.**  Each rung is a degree of structural
reflection.  The "Categorical characterization" column gives the
isomorphism-invariant (category-theoretic) form; the "Classical
calibration" column gives only the consistency-strength marker — a
yardstick, never a postulate.  Through `vopenka` the categorical
column is single-structure structural reflection (Adámek-Rosický /
Bagaria); `huge` → `kunenI0` is **sequential Exact Structural
Reflection** (Bagaria-Lücke), the categorical form of rank-into-rank;
`exacting`/`ultraexacting` is the 2024 SR frontier.  Only the
open-frontier tail (`schlutzenbergVLambdaPlus2`, `reinhardtDirected`)
lacks a categorical characterization FX commits to.

| Flag | Categorical characterization | Classical calibration |
|---|---|---|
| `standard 0` | classifier of finite fibrations | PRA |
| `standard n` (n ≥ 1) | n-fold iterated universe classifier | I-Σⁿ₁ + iterated inductions |
| `inaccessible` | universe closed under Π/Σ/W with a sub-universe (Grothendieck universe in the topos) | inaccessible |
| `mahlo` | regular-fixpoint reflection of universe-valued maps (predicative Mahlo) | Setzer 1998, KPM |
| `superMahlo` | Mahlo reflection iterated once | Setzer 2008, KPM² |
| `nMahlo n` | Mahlo reflection iterated n times | Setzer 2008, KPMⁿ |
| `hyperMahlo` | limit of the Mahlo reflection tower | limit of KPMⁿ |
| `weaklyCompact` | tree-property / Π¹₁-reflection | Rathjen 2014, Π¹₂-CA₀ |
| `indescribable n` | Πⁿ-formula reflection | Rathjen 1998, Π³ₙ-CA₀ |
| `reflecting` | full higher-order structural reflection | Rathjen-Weiermann 2017, Π³₁-CA₀ |
| `ramsey` | partition reflection | between weakly compact and measurable |
| `measurable` | non-trivial accessible endofunctor (no fixpoint) | Scott 1961 |
| `strong α` | α-graded accessible reflection | Kanamori 2003 |
| `woodin` | determinacy-grade reflection | Martin-Steel 1989 (⇒ PD) |
| `supercompact` | small orthogonality classes for Σ₂-definable classes | Bagaria-Casacuberta-Mathias-Rosický 2015 |
| `extendible` | small orthogonality classes, unrestricted (C⁽ⁿ⁾-degrees) | Bagaria 2012 |
| `vopenka` | structural reflection for ALL classes = colimit-closed full subcategories of locally presentable categories are coreflective = Ord ↛ Graph fully faithfully | Adámek-Rosický 1994; Bagaria 2023 |
| `huge`, `nHuge` | sequential ESR degree (𝒞-structure embeddings) | Bagaria-Lücke 2021 |
| `kunenI3`, `kunenI2` | sequential ESR degree | Bagaria-Lücke 2021 |
| `kunenI1` | Π₁ sequential ESR (⟸ I1) | Bagaria-Lücke 2021 |
| **`kunenI0`** | **ESR rank-into-rank apex — FX's committed categorical apex** | Bagaria-Lücke 2021 ≈ I0 |
| `exacting` | SR-defined; V ≠ HOD | Aguilera-Bagaria-Lücke 2024 |
| `ultraexacting` | SR-defined; ⟹ Con(ZFC + proper class of I0) | Aguilera-Bagaria-Lücke 2024, ZFC-consistent rel I0 |
| `schlutzenbergVLambdaPlus2` | *open frontier — choiceless ZF ceiling, no categorical characterization FX commits to* | Schlutzenberg-Goldberg JML 2024 (ZF-proven rel I0) |
| `reinhardtDirected` | *open frontier — FX-native directed self-endofunctor fixing the 0-truncation; consistency UNKNOWN* | none (Gödel block does not apply; never studied) |

Each rung is STRICTLY stronger than those below; each admission
predicate (through the frontier degrees) is decidable in O(flag enum
position).  **FX's committed categorical apex is `kunenI0`** —
I0-strength self-similarity via sequential Exact Structural Reflection,
stated as a reflection principle on the category of structures, never
as `j : V → V`.  `exacting`/`ultraexacting` are reachable stretch
targets in the same phase.  The two open-frontier rows are honest
catalogue entries — not objects FX asserts or builds — per "The
Reinhardt frontier".

**What the ladder commits to, and what it does NOT (O-ORD /
O-REFL-MODEL, §11.8.0).**  The enum + decidable admission predicate
is the *interface*; two foundational components behind it are
obligations, not results:

* **O-ORD — ordinal analysis.**  The rungs are ORDERED by consistency
  strength, and the Gödel-climbing engine (§11.7.1: rung *n+1* proves
  `Con(`rung *n*`)`) is what makes the ladder generative.  For "rung
  *n* has strength X" and "*n+1* proves `Con(n)`" to be THEOREMS
  rather than calibration prose, FX needs an ordinal-notation /
  well-ordering-proof substrate (Rathjen-style proof theory) — the
  literal content of an admitted Mahlo / Πⁿ / ESR strength.  The doc
  commits to the ladder as enum + admission predicate; the ordinal
  analysis establishing each rung's strength is OBLIGATION **O-ORD**
  (open research), currently ABSENT.

* **O-REFL-MODEL — the universe's construction.**  `kunenI0`-via-ESR
  is stated as a reflection principle FX targets.  HOW a universe
  satisfying ESR(κ,λ,𝒞) is CONSTRUCTED — or relatively justified —
  inside FX's own predicative, AC-free, non-well-founded (∞,ω)-topos
  substrate is not built; "the categorical form reaches the strength"
  is the claim, not the construction.  OBLIGATION **O-REFL-MODEL**
  (open research).

* **First-class flag quantification is strength-stratified.**
  Declarations may quantify over `UniverseFlag` (§3.10), up to
  `kunenI0`.  The quantifier's own universe must therefore exceed the
  strength of every flag it ranges over — you cannot quantify over
  `kunenI0`-strength universes from within a `kunenI0`-strength
  universe without a Girard-style strength inflation.  Flag
  quantification is thus stratified: a declaration ranging over flags
  ≤ f lives at strength > f.  This is a design constraint to enforce,
  not yet a mechanized invariant.

Per §11.8.0's relative-consistency stance, FX@flag is consistent
RELATIVE TO an ambient metatheory of strength ≥ calibration(flag),
assumed not proven (Gödel II).

**Refactored `Generator.payload`:**

```lean
def Generator.payload : Generator → Nat → Type
  | .gen_universeU,     _ => LevelExpr × UniverseFlag  -- inner univalent
  | .gen_universeS,     _ => LevelExpr × UniverseFlag  -- outer strict (strict reduction
                                                       --   + strict large-elim; NO K,
                                                       --   univalence still holds, §11.8.13)
  | .gen_universeD,     _ => LevelExpr × UniverseFlag  -- directed
  | .gen_universeOmega, _ => LevelExpr × UniverseFlag  -- (∞,ω)-directed
  | .gen_sprop,         _ => Unit
  | .gen_univLift,      _ => LiftDirection  -- Inner→Outer / Outer→Inner / Directed lift
  | .gen_var,       scope => Fin scope
  | …
```

This breaks the current "everything is Unit" claim — that is the
intended honesty correction.

#### 11.8.2.1 The Reinhardt frontier — what lies above ESR, stated honestly

`kunenI0` (sequential ESR) is the apex FX *builds*.  The genuine
"universe resembles itself" statement — an elementary self-embedding
of the *ambient* universe, classically `j : V → V` (Reinhardt) — lies
above it.  The categorical lens does something set theory cannot: it
**splits** that one statement into two objects with completely
different status.  Set theory blurs them because it has only one `V`.

**(b) Ambient self-embedding with an ordinal critical point** (the
classical Reinhardt).  This is **AXIOM-ONLY, provable nowhere**, and
the "nowhere" is a theorem, not timidity:

* A (b)-morphism moves an ordinal ⟹ its critical point is measurable,
  …, above I0 ⟹ proper class of measurables ⟹ `Con(ZFC)` ⟹
  **`Con(FX)`**.  FX interprets arithmetic, is consistent, and is
  recursively axiomatized (decidable kernel), so by **Gödel II**
  FX ⊬ `Con(FX)`, hence **FX ⊬ (b)**.  This is foundation-independent
  — categories change the idiom, not the strength of *proving* it; a
  Reinhardt-strength self-morphism is an axiom one may add, never a
  theorem one derives, in ZFC / ZF / FX alike.
* Re-representing `Nat` cannot lift this.  The escape routes from
  Gödel II all break a load-bearing FX commitment: dropping decidable
  proof-checking (true arithmetic) kills the kernel; dropping
  arithmetic strength (Presburger) kills foundational power; **dropping
  provable totality of recursion (Willard self-verifying theories,
  which CAN prove their own consistency) kills SN + decidable Conv +
  NbE termination** — the exact thing FX's totality discipline
  (§11.7.2) requires.  Decidable + total + arithmetically-strong ⟹
  Gödel-bound; FX wants all three, so FX is squarely inside Gödel's
  domain and cannot self-certify.  The homotopical/cubical/directed
  *dressing* of `Nat` is orthogonal to its arithmetic content and
  changes nothing.
* Classically (b) is Kunen-blocked in ZFC; in ZF the region just above
  the wall is graded, not uniformly open: `V_{λ+2}` is ZF-PROVEN
  consistent rel I0 (Schlutzenberg-Goldberg), while Reinhardt `V → V`
  and Berkeley remain open and under active 2024 revision.

**(c) Ambient self-endofunctor fixing the 0-truncation** (`reinhardt
Directed`, FX-native).  A non-invertible elementary endofunctor of
`gen_universeOmega` that is the IDENTITY on every set and ordinal (the
0-truncation) but acts on the higher directed cells.  This object is
**unstatable outside a directed-univalent foundation** — set theory
and even (∞,1)-theories cannot express "fix the discrete core, move
only the higher cells."  Its status is genuinely open in a NEW way:

* The Gödel block of (b) runs entirely through the *moved ordinal*.
  Fix every ordinal and the implication (c) ⟹ `Con(FX)` may FAIL — so
  **Gödel does not obviously forbid (c)**.  It might be cheap and
  CONSTRUCTIBLE (directed type theory already has elementary
  endofunctors like `op : S → S`; the open question is a non-invertible
  one fixing objects), or strong-and-open, or refutable.  Nobody has
  asked.  This is the FX-native open problem the apex points at.
* Goldberg rigidity (arXiv:2103.13961: embeddings into a fixed target
  are unique above extendible) says that *if* such a self-map exists it
  is canonical — exactly what univalence wants.  And the Laver-Steel
  **left-distributive algebra** of elementary self-maps is *computable*
  (Laver tables), so FX can internalize and even evaluate the algebraic
  trace of the frontier object while its top-level consistency stays
  open.  Concretely (§11.9.3 OP4): the higher-cell action of a
  (c)-functor is *forced* to be an LD-algebra representation, so the
  Laver-table first-row period `p(n)` — computable and zero-axiom — is an
  FX-internal invariant whose unboundedness is equivalent to an I3
  cardinal (Dougherty-Jech).  FX thereby turns "does this
  large-cardinal-strength self-map exist?" into "does an
  internally-computable sequence obey a forced growth law?" — a
  *decidable shadow* of the frontier, computable now even though the
  consistency question stays open.

**Gödel is the engine, not the ceiling.**  FX never proves `Con(FX)` —
but for every WEAKER flag it does: the reflection ladder is the tower
in which rung *n+1* proves `Con(`rung *n*`)` (Gentzen-style; §11.7.1
Gödel-climbing).  If FX could prove its own consistency the ladder
would collapse to a fixed point and the supply of new problems would
run dry.  **Incompleteness is precisely what guarantees the
`inaccessible → … → kunenI0 → exacting → reinhardtDirected` ascent is
unbounded** — there is always a strictly stronger reflection degree
because no degree proves its own consistency.  FX's move is never
*escape* (impossible, and self-defeating) but *climb* (built-in,
infinite), plus the separate, orthogonal, FX-only question of whether
(c) exists.

### 11.8.3 Elimination policy — maximal power

The kernel commits to the following elimination design:

**K-free / univalence-compatible.**  Identity types are cubical
paths, NOT Streicher-K style.  FORCED by the univalence commitment
(§3.10): univalence + K is inconsistent.  Pattern-matching on
identity witnesses respects Cockx-Devriese-Piessens "Pattern matching
without K" (ICFP 2014) restrictions.

**The equality zoo needs a discipline.**  FX carries FOUR
equality-like notions and they must not be conflated: the **cubical
path** (`gen_path`, §11.8.4 — the computational univalence route),
**strict identity** (`idStrict` — definitionally-UIP equality where
proof-irrelevant), **`SProp`** (definitional proof irrelevance,
§11.8.2), and the **HOTT observational `Id`** of the §11.8.14
research track (definitional univalence — a SEPARATE, no-interval
substrate that §11.8.14 already flags coexists with cubical as an
architectural fork).  Discipline: cubical path is the default
identity at object level; `idStrict` / `SProp` are opt-in for the
proof-irrelevant / strict fragment; HOTT-`Id` is research-track only.
Notably ABSENT and worth a decision: **observational type theory**
(Pujet-Tabareau "Observational Equality Now For Good" / TTobs) — the
established route to definitional funext WITH decidable conversion and
NO interval.  FX currently jumps from cubical straight to the open
HOTT track, skipping OTT as the pragmatic decidable-funext middle; an
OTT outer mode is a candidate (cf. the §11.8.2 outer-strict mode),
left as a stated design choice, not yet committed.

**Dependent large elimination with motive children.**  Eliminators
carry a motive child in their spine:

```lean
-- gen_natElim spec updated:
def Generator.childSpecs : Generator → List ChildSpec
  | .gen_natElim =>
      [ {cellSort := .type, cellDimension := 0, scopeShift := 1}  -- motive : Nat → Type
      , {cellSort := .term, cellDimension := 0, scopeShift := 0}  -- zeroCase
      , {cellSort := .term, cellDimension := 0, scopeShift := 2}  -- succCase
      , {cellSort := .term, cellDimension := 0, scopeShift := 0}  -- scrutinee
      ]
  -- analogous for gen_listElim, gen_optionMatch, gen_eitherMatch,
  -- gen_boolElim, gen_idJ, gen_idStrictRec
```

The motive child has `scopeShift := 1` because the motive binds the
scrutinee variable.  This change is mechanical but breaks the
current 16 SR-iota arms (they all assume no motive); they get
rewritten as part of Phase Z₀.

**Definitional eta** for:
* Functions: `f ≡ fun x => f x` (judgmental).
* Pairs / dependent pairs: `p ≡ (p.fst, p.snd)`.
* Unit: any two `Unit` values are judgmentally equal.
* Records: extended to record types via field projection.

Definitional eta is a reduction-direction choice — adds eta-arms
to the raw `Step.eta` sibling relation where the redex is structurally
recognizable, and to typed eta-long NbE/readback where the rule needs
type information.  Binder eta uses `RawTerm.strengthen` as the
computational side condition; Unit eta is typed-only and must not be
added as a raw eta constructor.

**Induction-recursion + higher induction-recursion (HIIRT).**
Beyond Dybjer-Setzer's standard IR (a mutual inductive + recursive
function pair), the kernel commits to the FULL Setzer 2008 hierarchy:

* **Standard IR** (Dybjer-Setzer APAL 2003) — `(U, El)` Tarski
  universes internally.
* **Indexed IR** (Dybjer-Setzer 2006) — IR families with parameters.
* **Higher IR (HIR)** (Setzer 2008) — IR at every dimension; IR
  families that themselves take IR families as components.
* **Quotient inductive-recursive (QIR)** types — IR with path
  constructors.  Altenkirch et al. 2018 extended.
* **Higher inductive-inductive-recursive types (HIIRT)** — the
  combined beast: simultaneously HIT + induction-induction +
  induction-recursion.  Sound by Forsberg-Setzer 2012 + extensions.

Each is a separate `GeneratorKind` tag.  Decidable typechecking
established by Setzer 1998 for standard IR, extended to HIIRT by
Capriotti-Forsberg 2020 (proof-theoretic upper bound: still
below first inaccessible).

**The admissibility schema is the actual content (O-IR-SCHEMA,
§11.8.0).**  "Supporting IR/HIIRT" foundationally MEANS shipping a
codes-for-IR universe + a strict-positivity criterion that decides
which inductive-recursive declarations are sound — it is NOT
discharged by naming the strength bound.  FX commits to the
Dybjer-Setzer codes universe (APAL 2003) for standard IR, extended
to the Forsberg-Setzer schema (2012) for the HIIRT beast, as the
`SemanticallySupportedGenerator` admission criterion for IR-kind
generators.  Until that codes universe is defined in Lean, the
IR/HIIRT admission is OBLIGATION **O-IR-SCHEMA** (specifiable now —
a schema, not new mathematics), not a discharged result; the
`HITSignature` / well-formedness-witness fields of §3.16.5 are its
placeholder pending the schema.

**Higher Inductive Types (HITs).**  Generators carry a `kind` tag
distinguishing term constructors from path constructors:

```lean
inductive Generator.Kind where
  | termCtor            -- ordinary constructor (existing default)
  | pathCtor            -- path constructor (Path A x y inhabitant)
  | higherPathCtor      -- 2-cell / higher path constructor
  | recursorCtor        -- eliminator (gets motive)

def Generator.kind : Generator → Kind
  | .gen_quotMk    => .termCtor
  | .gen_quotEq    => .pathCtor
  | .gen_circleBase => .termCtor
  | .gen_circleLoop => .pathCtor
  | .gen_natElim   => .recursorCtor
  | …
```

HIT eliminators' iota rules respect path constructors via cubical
Kan operations (see §11.8.4).

**Quotient Inductive-Inductive Types (QIITs).**  HITs combined
with induction-induction.  Sound by Altenkirch-Capriotti-
Dijkstra-Forsberg (FoSSaCS 2018).

**WF recursion + Div effect opt-in.**  Structural by default;
`WellFounded.fix` opt-in for non-structural cases; general
recursion gated by `with Div` effect (fx_design.md §9.4) and
`TotalityClass.Div` admission witness (§11.7.2).

**Strict commuting conversions.**  Eliminator reduces under nested
eliminators:

```
match (match x with .C1 => a | .C2 => b) with .D1 => c | .D2 => d
  ↝ match x with .C1 => (match a with …) | .C2 => (match b with …)
```

Adds reduction rules → more terms in NF → smaller proof terms →
faster decidable Conv.

**Multi-clock guarded recursion.**  Beyond single-clock Nakano:
the kernel commits to **multi-clock guarded type theory**
(Bizjak-Møgelberg-Vezzosi LICS 2017 + Møgelberg-Veltri-Vezzosi
JFP 2020).  Multiple clocks for productivity at different rates,
clock variables, clock quantification, and clock-dependent later
modalities:

```lean
| .gen_clock         -- gen for clock types (a clock is a "rate")
| .gen_laterCl       -- ▸_κ later modality at clock κ
| .gen_forceCl       -- force_κ : ▸_κ A → A (under clock binding)
| .gen_clockAbs      -- ∀κ. A — universal clock abstraction
| .gen_clockApp      -- A[κ] — clock application
| .gen_fixedPoint    -- gfix : (▸_κ A → A) → A — guarded fixed point
```

Sound by Bizjak-Møgelberg-Vezzosi (sized productivity + cofibration
respecting Kan structure).  Strictly more expressive than:
* Sized types (Abel) — single clock, no clock quantification.
* Nakano single-clock — no clock-dependent constructions.

Enables: streams with fairness witnesses, multi-rate dataflow
networks (relevant to FX's clock dimension #12), bisimulation
proofs that distinguish slow vs fast equivalence.

**Internal parametricity.**  Following Bernardy-Coquand-Moulin
ICFP 2015 + Cavallo-Harper LICS 2020, the kernel commits to
**internal parametricity**: the type theory proves its own free
theorems.

```lean
| .gen_param   -- parametricity bridge: `BridgeA : A ≅ Param A`
| .gen_paramAbs -- parametric universal abstraction
```

A function `f : ∀ A. A → A` internally proves `∀ A x. f A x = x`
WITHOUT pattern matching on `A`.  Strictly more powerful than
external parametricity (which lives outside the type theory in
metatheory).  Decidable typechecking preserved (Bernardy-Moulin
2013).  Adds ~3K LoC to the kernel.

**Coherence with the cubical layer (O-CUBE-PARAM, §11.8.0).**  The
kernel then carries TWO interval-like dimensions: the cubical PATH
dimension (§11.8.4, CCHM) and the parametricity BRIDGE dimension
(here).  Their interaction is not free — and §11.8.14 flags that the
interval route is provably blocked from *definitional* univalence, so
this is a genuine coherence question, not a notation choice.  FX
commits to **Cavallo-Harper Internal Parametricity for Cubical Type
Theory** (CSL 2020 / LMCS 2021) as the substrate that unifies path +
bridge in one cubical setting; their joint coherence in FX's combined
kernel is
OBLIGATION **O-CUBE-PARAM**.  This is the kernel-level form of the
OP1 crux (§11.8.14.1).

**Rewriting rules as first-class kernel feature.**  Per Cockx-
Tabareau ICFP 2021, the kernel admits user-declared rewrite rules
that extend definitional equality:

```lean
| .gen_rewriteRule  -- payload: pair of patterns (lhs, rhs) + linearity/confluence witness
```

Each rule's admission requires:
* Confluence witness (the new TRS remains confluent).
* Termination witness (the new TRS remains terminating, per Z₇'s
  totality discipline).
* Linearity witness (patterns are linear, per Cockx-Tabareau §3).

When admitted, the rule joins the kernel's definitional equality.
Strictly more powerful than fixed reduction rules: users can extend
the kernel's notion of computation per-profile.  Decidable
admission (each witness is decidable per §11.8.7).

**Cubical pattern matching.**  Per Cockx-Tabareau ICFP 2021
"Cubical Type Theory: a constructive interpretation of the
univalence axiom" extended pattern matching: dependent pattern
matching respects path constructors automatically.  No K used;
pattern matching on identity types is interpreted as case-analysis
on cubical paths.

**Equations-style dependent pattern matching.**  Per Sozeau-Mangin
ICFP 2019 "Equations Reloaded": deep dependent pattern matching
with automatic recursion equations.  The kernel admits Equations-
form definitions as a desugaring step (the elaborator produces
standard eliminator + iota chains).

**Internal computational reflection.**  Following Pédrot-Tabareau
LICS 2018 "Failure is not an option: an exceptional type theory":
the kernel admits a **decidable propositions universe** `dProp`
where every inhabitant carries its own decision procedure.  Inside
`dProp`, Markov's principle holds; outside it remains constructive.

```lean
| .gen_dProp     -- universe of decidable propositions
| .gen_dPropDec  -- the embedded decider: dProp → Bool
```

Strictly more powerful: decidable reflection inside the type
theory without committing to classical logic globally.

**Pure type-directed elaboration — no user-level tactics.**  The
kernel commits to a STRICT no-tactics discipline at the user-facing
language level.  Proofs are NOT scripts; proofs are TERMS produced
by type-directed elaboration.  The user writes:

* **Types** + **specifications** (refinements, contracts).
* **Equation chains** via `calc` — the ONLY proof-script construct.
  Each `calc` step is a single Conv invocation between consecutive
  terms; the kernel's NbE-based Conv decider validates it.
* **Definitions** that pattern-match on inductive data — the
  elaborator fills dependent equations automatically (Equations-
  style, §11.8.3 above).

There is **no `by` block**, **no `apply`**, **no `intro`**, **no
`rewrite`** at user level.  Behind the scenes, the elaborator
performs unification + type-directed search + refinement synthesis,
but these are NOT exposed as a tactic language.

Justification: tactic languages introduce a SECOND grammar (the
tactic language) parallel to the term grammar.  Eliminating it
means:
* Single canonical proof representation (the term itself).
* No "tactic dialect" maintenance burden.
* No mismatch between tactic and term semantics.
* Synthesis is forced to produce TERMS, not opaque scripts.

The kernel's elaboration is **complete for the decidable
fragment** (§11.8.7).  When the elaborator cannot fill a gap, it
emits a structured `unsolved-goal` error pointing at the precise
type that needs to be inhabited — the agent / user then refines
the SPECIFICATION (adds more refinements, more equations, more
definitional structure) until the elaborator succeeds.

**Elaborator soundness is the load-bearing trust reduction
(O-ELAB, §11.8.0).**  Banning the tactic layer (and the reflection
self-hosting it would otherwise need, §11.8.11) only reduces trust IF
the elaborator emits exclusively kernel-recheckable terms: every term
it synthesizes — including the products of the unification,
type-directed search, and refinement synthesis above — is re-checked
by the trusted NbE kernel, so an elaborator bug can FAIL to find a
proof but cannot forge one.  That re-check property is elaborator
SOUNDNESS; "complete for the decidable fragment" is elaborator
COMPLETENESS.  Both are statements ABOUT the elaborator, not
corollaries of the kernel's own decidability — they are OBLIGATION
O-ELAB (specifiable now), soundness gating MILESTONE A.  The honest
stance: the kernel is the trusted base; the elaborator is an
untrusted oracle whose every output the kernel re-validates.

Refinement-driven synthesis: `{x : A | P x}` triggers automatic
witness search when `A` is finite, `P` is decidable, or `P` is
constructively derivable from the Generator table's iota chain.

**No external SMT — fully-verified internal deciders only.**  The
kernel does NOT call external SMT solvers (Z3, CVC5, etc.).  Every
decision procedure used during elaboration is INTERNAL and
mechanically verified within FX.  Concrete internal deciders
shipped by the kernel:

| Theory | Internal decider | Verification basis |
|---|---|---|
| Linear arithmetic over ℤ / ℚ | Internal Omega / Cooper | Presburger 1929 + Cooper 1972 |
| Ring identities | Internal Buchberger / Gröbner | Buchberger 1965 |
| Propositional logic (SAT) | Internal CDCL with verified certificates | Maric 2010 SatCheck |
| Bit-vectors | Internal BV-bitblasting + verified SAT | Hadarean 2014 |
| Equality + uninterpreted functions | Internal congruence closure | Nieuwenhuis-Oliveras 2005 |
| Theory combination (when needed) | Internal Nelson-Oppen | Nelson-Oppen 1979 |
| Quantifier-free decidable FOL fragments | Combinations of the above | Standard |

Each internal decider's correctness is a Lean theorem (per the
zero-axiom discipline §11).  The decider's OUTPUT is a kernel term
that the typechecker verifies against the original goal — no
trust placed in the decider beyond the verifier's check.

**If higher SMT-like power becomes necessary**, the path forward
is to **build a fully-verified SMT engine natively inside FX**
as Phase Z₉ — NOT to call out to an external untrusted oracle.
This is a major engineering project (~10K LoC for a small verified
SMT core); deferred until a concrete profile-level need emerges.

**No LLM integration in the kernel.**  The kernel is a closed
self-contained system.  LLM-driven workflows live OUTSIDE the
kernel via the agent protocol (fx_design.md §24): the LLM proposes
TERMS via `POST /edit`, and the kernel typechecks them per its
ordinary elaboration rules.  Inside the kernel itself there is
no LLM-aware operation, no synthesis-by-language-model primitive,
no "let the LLM decide" fallback.  Soundness is preserved by
construction: the kernel only accepts terms that pass its own
verified deciders.

### 11.8.4 Cubical computational univalence — operational core

Per §3.10's existing commitment, FX uses cubical-style univalence
via `Step.eqType`.  Under the maximal-power kernel, this
generalizes to FULL cubical Kan operations.  Generator additions:

```lean
inductive Generator
  | …
  | gen_path        -- Path type former: Path A x y
  | gen_pathLam     -- Path lambda: λ i. body
  | gen_pathApp     -- Path application: p @ i
  | gen_transp      -- Transport: transp (i. A) r body
  | gen_hcomp       -- Homogeneous composition: hcomp φ u u0
  | gen_glue        -- Glue type: Glue A φ T e
  | gen_unglue      -- Unglue: unglue u
  | gen_face        -- Face formulas: i = 0, i = 1, i ∧ j, …
  | gen_dimI        -- The interval pre-type
```

These follow Cohen-Coquand-Huber-Mörtberg (CCHM, JFP 2018) +
Angiuli-Brunerie-Coquand-Harper-Hou-Licata (ABCHHL, "Cartesian
cubical computational type theory", 2019).

**Computability.**  Every cubical operation has a defining
reduction rule.  Kan composition reduces structurally over Π, Σ,
U, inductives.  Transport reduces structurally.  Univalence
reduces via the `equiv → Path` rule.

**Decidability.**  Cubical Agda demonstrates decidable typechecking
for the full CCHM system.  Mörtberg's normalizer establishes
termination.

### 11.8.5 Typed layer architecture

```lean
inductive TypingContext (profile : PolyProfile) : Nat → Type where
  | empty : TypingContext profile 0
  | cons (Γ : TypingContext profile n) (T : RawTerm n)
         (TIsType : ∃ level, HasType profile Γ T (universe level)) :
      TypingContext profile (n+1)

def TypingContext.lookup
    (Γ : TypingContext profile scope) (idx : Fin scope) :
    RawTerm scope := …

inductive HasType (profile : PolyProfile) :
    ∀ {scope : Nat}, TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | conv : HasType Γ t T → Conv T T' →
           (∃ level, HasType Γ T' (universe level)) →
           HasType Γ t T'
  | var : ∀ Γ idx, HasType Γ (varTerm idx) (Γ.lookup idx)
  | universe : ∀ Γ e, HasType Γ (universe e) (universe (lsucc e))
  | piType : ∀ Γ A B e1 e2,
      HasType Γ A (universe e1) →
      HasType (Γ.cons A …) B (universe e2) →
      HasType Γ (piType A B) (universe (lmax e1 e2))
  | lam : ∀ Γ A body B,
      HasType (Γ.cons A …) body B →
      HasType Γ (lam body) (piType A B)
  | app : ∀ Γ f a A B,
      HasType Γ f (piType A B) →
      HasType Γ a A →
      HasType Γ (app f a) (B.subst0 a)
  | natElim : ∀ Γ (P : RawTerm (scope+1)) z s n,
      IsType profile (Γ.cons natType …) P →
      HasType Γ z (P.subst0 zeroTerm) →
      HasType Γ s (piType natType (piType P P.shift)) →
      HasType Γ n natType →
      HasType Γ (natElim P z s n) (P.subst0 n)
  -- per-generator rules for the semantic core
  -- cubical primitives have their own rules per §11.8.4
```

`IsType profile Γ T` is `∃ level, HasType profile Γ T (universe
level)`.

**Typed Subject Reduction** — the real theorem:

```lean
theorem HasType.subject_reduction
    {profile : PolyProfile} {scope : Nat}
    {Γ : TypingContext profile scope} {t t' T : RawTerm scope}
    (hT : HasType profile Γ t T)
    (hStep : Step t t') :
    HasType profile Γ t' T
```

Proof: induction on `Step`, using inversion lemmas on `HasType` for
each generator + `conv` rule for type-up-to-Conv.  The structural
SR shipped today (~33 zero-axiom decls) is reused as a syntactic
sub-proof.

### 11.8.6 21-dimensional integration

Per fx_design.md §1.1, FX has 21 graded type dimensions.  PolyCell
currently models dimension 1 (Type) only.  Under the maximal-power
kernel, each of the other 20 dimensions is a SEPARATE typing
judgment, decidable, composed with `HasType`:

| Dim | Judgment | Decidability route |
|-----|----------|---------------------|
| 1 Type | `HasType Γ t T` | Cubical NbE NF equality |
| 2 Refinement | `RefinedHasType Γ t T pred` | SMT discharge (fx_design.md §10) |
| 3 Usage | `HasUsage Γ t u` | Graded semiring (fx_design.md §6.1) |
| 4 Effect | `HasEffect Γ t T eff` | Effect-row lattice |
| 5 Security | `HasSecurity Γ t T sec` | Lattice join check |
| 6 Protocol | `HasProtocol Γ t T proto` | Session-type unfold |
| 7 Lifetime | `HasLifetime Γ t T r` | Region inference |
| 8 Provenance | `HasProvenance Γ t T prov` | Lattice join |
| 9 Trust | `HasTrust Γ t T trust` | Trust-lattice min |
| 10 Representation | `HasRepr Γ t T repr` | Per-type repr lookup |
| 11 Observability | `HasObs Γ t T obs` | Opacity lattice |
| 12 Clock domain | `HasClock Γ t T clk` | Domain check |
| 13 Complexity | `HasCost Γ t T O(...)` | Symbolic cost bound |
| 14 Precision | `HasPrec Γ t T ULP` | Precision tracking |
| 15 Space | `HasSpace Γ t T n` | Allocation bound |
| 16 Overflow | `HasOverflow Γ t T mode` | Per-arith-op mode |
| 17 FP order | `HasFPOrder Γ t T strict` | Strict/reassoc tag |
| 18 Mutation | `HasMutation Γ t T mut` | Mutation lattice |
| 19 Reentrancy | `HasReentrancy Γ t T re` | Tag check |
| 20 Size | `HasSize Γ t T n` | Codata depth |
| 21 Version | `HasVersion Γ t T ver` | Version-lattice migration |

**Composition.**  Each dimension's typing judgment is INDEPENDENT
under the polynomial-monad presentation (§3.2).  Combined typing
is a PRODUCT: `t` is "fully typed" iff it satisfies every
applicable dimension's judgment simultaneously.

**Decidable typechecking of the full 21-dim composition.**  A
finite list of decidable checks, each delivered by its respective
dimension's typing judgment.  Total complexity: `O(#dimensions × NbE
cost)` = `O(21 × NbE cost)` = `O(NbE cost)` asymptotically.

**Modal layer — full MTT + cohesion + differential cohesion.**
Beyond the 21 dimensions above, the kernel commits to **Multi-Modal
Type Theory (MTT)** at the apex modality layer:

* **MTT base (Gratzer-Sterling-Sterling LICS 2020).**  A 2-category
  of modes with dependent right adjoints between them.  The kernel
  ships `gen_mode` Generators per mode + `gen_modIntro` / `gen_modElim`
  for each adjunction.
* **Cohesive modalities (Shulman 2018 + Schreiber 2013).**
  `gen_shape` (♭ → flat), `gen_sharp` (♯ → sharp), `gen_flat` (♭ →
  discrete), forming the cohesive adjoint triple
  `♭ ⊣ ♯ ⊣ ♭`.  Enables synthetic cohomology, synthetic homotopy,
  synthetic differential geometry.
* **Differential cohesion (Schreiber 2013).**  Adds `gen_reduced`,
  `gen_infinitesimal`, `gen_etale` for synthetic differential geometry
  / synthetic algebraic geometry.  The full differential-cohesive
  adjoint quadruple
  `Π ⊣ ♭_inf ⊣ ♯_inf ⊣ ʃ_inf`.
* **n-truncations as profile features.**  Each `gen_truncN n`
  Generator for n-truncation.  Sound by Capriotti-Kraus 2018.
* **Linear / non-linear adjoint modality (Benton's LNL).**
  `gen_F` / `gen_G` for the linear ⊣ non-linear adjunction.
  Enables linear types as a modal sub-theory of FX's type
  dimension.

**Synthetic mathematics layer — voracious math as profile capabilities.**
Beyond the structural dimensions, the kernel commits to admitting
PROFILE-LEVEL synthetic mathematics frameworks:

| Domain | Profile capability | Reference |
|---|---|---|
| ∞-topos internal language | `fxInfinityToposProfile` | Shulman 2019 + Lurie HTT |
| Stable homotopy / synthetic spectra | `fxSpectraProfile` | Krause 2025 |
| Synthetic Lie groups + smooth manifolds | `fxSmoothProfile` | Kock SDG |
| Synthetic algebraic geometry | `fxAlgGeomProfile` | Cherubini-Coquand-Geuvers-Hou-Mörtberg 2024 |
| Synthetic quantum types | `fxQuantumProfile` | Coecke-Selinger / Heunen-Vicary |
| Synthetic measure + probability | `fxMeasureProfile` | Synthetic probability literature |
| Synthetic Markov categories | `fxMarkovProfile` | Fritz 2020 |
| Synthetic differential cohomology | `fxDiffCohomologyProfile` | Schreiber 2013 |
| Synthetic computability theory | `fxComputabilityProfile` | Bauer 2006 (effective topos as profile) |
| Synthetic stable ∞-categories | `fxStableInfinityProfile` | Riehl-Verity ∞-cosmoi |

Each is a PROFILE — uses the same `PolyCell` substrate but with a
profile-specific `SemanticallySupportedGenerator` table.  Profiles
form a 2-category (geometric morphisms between profiles), and
profile-of-profiles is admissible (§3.8 self-referential profiles
via Uemura ∞-type theories).

**Algebraic effects + handlers as first-class kernel feature.**
Beyond `with Effect` annotations: the kernel admits **full algebraic
effects with handlers** as a profile capability (Plotkin-Pretnar
"Handlers of algebraic effects" ESOP 2009 + Pretnar's thesis):

```lean
| .gen_effectOp    -- algebraic effect operation
| .gen_effectHandler -- handler implementing an effect
| .gen_effectScope -- delimited continuation scope
```

Sound by Plotkin-Pretnar + Bauer-Pretnar.  Decidable typechecking
preserved.  Adds ~5K LoC.

**Fire-Triangle confinement (O-FIRE, §11.8.0).**  The Fire Triangle
(Pédrot-Tabareau, Tier 0 §3.0.3) forbids unrestricted *substitution
+ dependent elimination + effects* simultaneously — and FX commits to
full substitution AND full dependent elimination.  So the
algebraic-effect layer is NOT unrestricted: it is confined to the
graded / ∂CBPV fragment of §3.0.3, where effects are bounded by the
resource grades so dependent elimination + substitution stay
unrestricted on the pure part; handlers may not eliminate dependently
into effectful results outside that fragment.  The proof that the
shipped effect layer stays inside the Fire-Triangle-safe fragment is
OBLIGATION **O-FIRE** (specifiable now) — listing the generators here
does not discharge it.

### 11.8.7 The decidability matrix at the apex (with complexity bounds)

Beyond "decidable", the kernel commits to **mechanized complexity
bounds** for every decision procedure.  Complexity is verified by
the strict harness — each `Decidable` instance ships with a
`Complexity` witness proving the bound.

**Every decider in this matrix is INTERNAL and FULLY VERIFIED.**
No external SMT, no external theorem prover, no LLM oracle.  Each
decision procedure's correctness is proved as a Lean theorem under
the zero-axiom discipline (§11).  The "reference" column names the
PUBLISHED ALGORITHM mechanized inside FX — not an external tool
invoked at elaboration time.

**Per-feature truth vs joint decidability (read before the ✓'s).**
Each ✓ below is established FOR ITS FEATURE IN ISOLATION by the cited
algorithm.  The structural and lattice deciders (`DecidableEq`,
grade / effect / repr / clock checks, the certifier) and the
cubical-core Conv / HasType (Cubical Agda) are **unconditional**.
Decidability of the COMBINED system — every feature active at once —
is **gated on O-NORM** (§11.8.0): the joint normalizer must exist for
typed Conv, HasType, and consistency to be decidable at the apex.
Rows marked **†** are the ones whose apex decidability rides on
O-NORM; their ✓ is per-feature, not yet joint.  This matrix does NOT
claim the union is decidable today — it claims each piece is, and
names (§11.8.0) the obligation whose discharge makes the union so.

| Property | Decidable | Complexity bound | Decision procedure | Reference |
|---|---|---|---|---|
| `DecidableEq (RawTerm scope)` | ✓ | O(size(t1) + size(t2)) | Structural, propext-free | V2-L0.11 ✅ |
| `DecidableEq LevelExpr` | ✓ | O(size) | Structural | §11.8.2 |
| `DecidableEq UniverseFlag` | ✓ | O(1) | Closed enum | §11.8.2 |
| `DecidableEq UniverseMode` (Inner/Outer/Directed) | ✓ | O(1) | Closed enum | §11.8.2 (2LTT) |
| `Decidable (HasCertifiedCellDim0 raw)` | ✓ | O(size × max-arity) | Structural certifier | V2-L1cert ✅ |
| `Decidable (SyntacticallySupportedGenerator gen)` | ✓ | O(1) | Closed 194-table | §11.8.4 |
| `Decidable (SemanticallySupportedGenerator gen)` | ✓ | O(log #generators) per profile | Per-profile witness table | §11.8.4 |
| `Decidable (Conv a b)` raw | ✓ | O(NF normalize) | Cubical NbE NF equality | Mörtberg 2023 |
| `Decidable (Conv (Γ ⊢ a : T) (Γ ⊢ b : T))` typed | ✓† | O(NF normalize + type lookup) | Typed cubical NbE | Cubical Agda; joint O-NORM |
| `Decidable (HasType Γ t T)` | ✓† | O(NF normalize × size(t)) | Bidirectional typecheck + NbE | Adjedj et al. 2310.06376; joint O-NORM |
| `Decidable (IsType Γ T)` | ✓ | O(typecheck) | Inferred-universe lookup | — |
| `Decidable (HasUsage Γ t u)` | ✓ | O(size × #dimensions) | Graded semiring multiplication | Wood-Atkey 2022 |
| `Decidable (HasEffect Γ t eff)` | ✓ | O(size × #effects) | Effect-row sub-effect lattice | — |
| `Decidable (consistency profile)` | ✓† | O(canonical-NF check) | Canonicity + SN + CR | §11.8.8; joint O-CANON |
| `Decidable (KanCubicalStructure dim)` | ✓ | O(dim) | Per-dim structure check | CCHM 2018 |
| `Decidable (HITPathCoherence gen)` | ✓ | O(#path-constructors) | Per-HIT path-constructor table | §11.8.3 |
| `Decidable (IRRecursiveDecoding gen)` | ✓ | O(IR depth) | Per-IR family decoding | Dybjer-Setzer 2003 |
| `Decidable (GuardedProductivity term)` | ✓ | O(size × #clocks) | Multi-clock structural check | Bizjak-Møgelberg-Vezzosi 2017 |
| `Decidable (InternalParametricityWitness term)` | ✓ | O(size) | Bridge-coherence check | Bernardy-Coquand-Moulin 2015 |
| `Decidable (RewriteRuleAdmissible rule)` | ✓ | O(rule-size × KB-iteration-bound) | Confluence + termination check | Cockx-Tabareau 2021 |
| `Decidable (CubicalPatternMatch case-tree)` | ✓ | O(case-tree-size) | Cubical case-tree well-formedness | Cockx-Tabareau 2021 |
| `Decidable (MTTModalityCompose mod1 mod2)` | ✓ | O(mode-graph diameter) | 2-category mode lookup | Gratzer-Sterling-Sterling 2020 |
| `Decidable (DependentRightAdjoint exists)` | ✓ | O(profile-mode-table) | Adjunction table lookup | MTT 2020 |
| `Decidable (CohesionAdjunctionApplicable Γ t)` | ✓ | O(profile-cohesion-flag) | Cohesive mode check | Shulman 2018 |
| `Decidable (SyntheticAlgebraicGeometryAdmissible term)` | ✓ | O(infinitesimal-depth) | Differential-cohesion check | Schreiber 2013 |
| Universe admission at full structural-reflection ladder | ✓ (per flag, when implemented) | O(flag enum position) | reflection-degree admission predicate (Mahlo → Πⁿ → accessible-category → sequential ESR) | Phase Z₆ |
| `Decidable (Dimension-N typing)` for each dim 2-21 | ✓ | Per-dimension (table §11.8.6) | Per-dimension procedure | §11.8.6 |
| `Decidable (TypedSubjectReduction t t' T)` | ✓ | O(typecheck × step-size) | Direct application of SR theorem | §11.8.5 |

**Every feature the kernel admits is decidable in isolation, each
with a mechanized complexity bound; the joint decidability of the
union is O-NORM-gated (§11.8.0, rows marked †).**  Properties OUTSIDE
the kernel
(termination of arbitrary general-recursive programs, halting of
FFI calls, the full halting problem, arbitrary first-order logic
provability) remain undecidable by Rice / Gödel / Turing — these
are gated by the `Div` effect and never admitted into the typed
fragment.

**Polynomial-time core.**  For the FIRST-ORDER typed fragment (no
universe quantification, no dependent eliminators, no HITs), full
typechecking is **polynomial time in size(t) × size(T)** per
Lensing 2025.  For the dependent fragment with cubical NbE, the
bound depends on the NBE normalizer's complexity; Mörtberg 2023
establishes EXP-time worst case, polynomial in practice.

**Complexity verification gate.**  Each shipped `Decidable` instance
must include:

```lean
/-- The decision procedure's complexity bound. -/
structure Complexity (P : Prop) [Decidable P] where
  steps : Nat → Nat → Nat  -- f input-sizes
  bound : ∀ args, (decideTime args) ≤ steps args.size
```

The strict harness's `STRICT-COMPLEXITY` gate verifies the bound on
every decidable kernel theorem.  Removes the "yes it's decidable but
might be EXP-tower" loophole.

### 11.8.8 Canonicity and consistency

**Canonicity for closed values.**  Every closed inhabitant of a
canonical inductive type reduces to a constructor application:

```lean
theorem canonicity_bool
    {profile : PolyProfile}
    (t : RawTerm 0) (h : HasType profile .empty t boolType) :
    t = boolTrue ∨ t = boolFalse := by
  -- by SN, t reduces to NF t'
  -- by typed SR (§11.8.5), HasType .empty t' boolType
  -- by inversion of HasType at boolType on closed NF, t' is one of the two
```

Same for `Nat`, `List`, `Option`, `Either`, `Pair`, `Sum`.

**Consistency theorem.**  No closed proof of `False`:

```lean
theorem consistency
    {profile : PolyProfile}
    (t : RawTerm 0) (h : HasType profile .empty t emptyType) : False
```

Proof: by SN, t reduces to NF t'; by typed SR, t' inhabits `Empty`;
by inversion, `Empty` has no constructors; contradiction.

**Universe consistency.**  No Girard-style paradox.  Proof by
standard syntactic model: each universe level interpreted as a
set in the next; impredicative Prop interpreted as the
two-element set (using SProp's irrelevance).

**Cubical canonicity.**  Per Sterling-Angiuli 2021 ("Normalization
for cubical type theory"), CCHM's normalizer establishes
canonicity for closed cubical terms.

### 11.8.9 Implementation phasing — nine phases, multi-year

**The canonical phasing table for the maximal-power kernel lives in
§10 under "Phase POLY-Z — Typed Layer + Decidable Typechecking
(months 24-60, ~53K LoC)"** with sub-phases Z₀ through Z₈ plus an
optional Z₉ (fully-verified internal SMT engine, ~10K LoC, deferred
until a concrete profile-level need emerges).  Read §10 for the full
roadmap context: POLY-TCB → POLY-0 → POLY-α → POLY-β → POLY-γ →
POLY-δ → POLY-ε → POLY-ζ → POLY-Z → POLY-η.  Phase Z runs in parallel
with POLY-ζ + POLY-η from month 24 onward.

The milestone scale §11.8.12 names (MILESTONE A through MILESTONE D)
maps to:

* **MILESTONE A** = Z₁ + Z₂ + Z₃ (~month 30) — decidable typed
  conversion + typechecking for the ~30-generator semantic core.
* **MILESTONE A+** = + Z₄ (~month 34) — full CCHM cubical primitives.
* **MILESTONE A++** = + Z₅ (~month 37) — HITs + QIITs.
* **MILESTONE B** = + Z₆ + Z₆+ (~month 41-44) — HIIRT + the full
  structural-reflection-degree ladder (§11.8.2): Mahlo reflection
  (`mahlo` → `hyperMahlo`) + higher-order Πⁿ-reflection
  (`weaklyCompact` → `reflecting`) + single-structure
  accessible-category reflection (`ramsey` → `vopenka`) + **sequential
  Exact Structural Reflection** (`huge` → **`kunenI0`**, the
  rank-into-rank region; Bagaria-Lücke) + the 2024 SR frontier
  (`exacting`, `ultraexacting`).  **Committed categorical apex =
  `kunenI0`** (I0-strength self-similarity as a reflection principle,
  never `j : V → V`).  Categorical reflection degrees, NOT embeddings;
  the open-frontier tail (`schlutzenbergVLambdaPlus2`,
  `reinhardtDirected`) is catalogue-only (§11.8.2.1).  Six-month
  delivery target from Phase Z₆ kickoff.
* **MILESTONE C** = + Z₇ (~month 44) — multi-clock guarded recursion +
  productivity-checked codata.
* **MILESTONE D** = + Z₈ (~month 56) — full 21-dim integration + the
  MTT + cohesion + differential cohesion + linear-nonlinear +
  algebraic effects + synthetic mathematics layer of §11.8.6.

**Combined LoC**: ~53K Phase Z core + ~10K optional Z₉ verified
internal SMT + ~170K substrate (POLY-α through POLY-ζ) = ~220K-230K
LoC over ~24-36 months focused work, arriving at MILESTONE D
~month 56-60.

### 11.8.10 Soundness composition

Each component is sound by published theory:

* **Cubical Type Theory** — Cohen-Coquand-Huber-Mörtberg JFP 2018;
  Mörtberg 2023 normalization.
* **Universe hierarchy** — Coquand 2018, Sterling-Angiuli 2021.
* **Impredicative Prop / SProp** — Coquand 2018, Gilbert-Cockx-
  Sozeau-Tabareau POPL 2019.
* **Mahlo universes** — Setzer APAL 1998 (sound up to KPM strength).
* **K-free identity** — Cockx-Devriese-Piessens ICFP 2014, Cockx-
  Devriese JFP 2016.
* **Induction-recursion** — Dybjer-Setzer APAL 2003.
* **Higher Inductive Types** — Cavallo-Mörtberg JFP 2020, CCHM
  2018 (path constructors), Coquand-Huber-Mörtberg 2018.
* **QIITs** — Altenkirch-Capriotti-Dijkstra-Forsberg FoSSaCS 2018.
* **Guarded recursion** — Birkedal-Møgelberg-Schwinghammer-
  Støvring LICS 2012, Nakano LICS 2000.
* **Definitional eta** — Abel-Coquand-Pagano TOPLAS 2020.

Several PAIRWISE compatibilities are already established — evidence
the union is plausible, not proof that it holds:

* Cubical + impredicative SProp: Vezzosi's Cubical Agda with `--prop`.
* Cubical + IR: Sterling-Angiuli STC.
* Cubical + HITs: native to CCHM.
* Cubical + universe polymorphism: native to CCHM.
* Mahlo + cubical: Phase Z₆; theoretical compatibility per Setzer's
  framework + CCHM's universe construction.

But pairwise compatibility is NOT joint soundness.  The full union —
cubical AND HIIRT AND guarded AND internal parametricity AND MTT AND
the 21-graded layer, all active at once — has never been normalized by
anyone; its joint normalization / confluence / canonicity are the
open obligations **O-NORM / O-CONF / O-CANON** of §11.8.0.  **The
per-feature work is assembly; the joint metatheory is research.**  The
committed route is BKS sconing extended to the full signature
(§11.8.0): this section lists the components, §11.8.0 owns the
obligation to glue them.

### 11.8.11 Honesty discipline

Per Codex audit (`feedback_polycell_structural_vs_semantic`) and
CLAUDE.md zero-axiom mandate:

* Every shipped typed-layer theorem is `theorem` / `lemma` / `def`
  with a real body.  No axiom.  No `sorry`.  No `noncomputable`.
* Every `Decidable` instance has a real decision-procedure body.
  No `Classical.dec`.
* Every "soundness" claim is qualified: "structural shape" vs
  "type-preserving" vs "semantically certified."
* Honesty probes remain in the kernel and are extended as new
  gaps emerge (e.g., `probe_universe_Type_in_Type_rejected` after
  Phase Z₀).
* Each Phase Zₙ has its own `#assert_no_axioms` gate sweep.
* This section (§11.8) is updated as each phase lands with a
  "delivered" tag — NOT updated to claim "delivered" before ship.

**Closed-system discipline (the "no-external-helpers" mandate).**
The kernel is a CLOSED SELF-CONTAINED SYSTEM.  Three explicit bans:

* **No user-level tactics.**  Proofs are TERMS, not scripts.  The
  only proof-script construct at user level is `calc`.  All other
  proof-construction happens via type-directed elaboration (§11.8.3).
  There is no `by` block, no `apply`, no `intro`, no `rewrite`,
  no `simp`, no `tauto`, no `decide` as user-facing tactics.  If a
  goal needs more than `calc` chains + refinement synthesis to
  inhabit, the user refines the SPECIFICATION — not the proof
  script.
* **No external SMT.**  The kernel does not call Z3, CVC5, or any
  external solver.  Every decision procedure invoked during
  elaboration is INTERNAL and fully verified in Lean.  Internal
  deciders are listed in §11.8.7 with their published-algorithm
  basis.
* **No LLM in the kernel.**  LLM-driven workflows live OUTSIDE the
  kernel via the agent protocol (fx_design.md §24).  LLMs propose
  TERMS that the kernel verifies under its ordinary rules;
  inside the kernel there is no LLM-aware operation, no
  synthesis-by-language-model primitive, no oracle fallback.

These three bans are NON-NEGOTIABLE.  They preserve:
(a) soundness independence from external software,
(b) single-grammar proof representation,
(c) deterministic reproducible builds, and
(d) zero-trust composition (the kernel's correctness depends only
on the kernel's own verified bodies).

If a future profile genuinely needs SMT-level combined-theory
reasoning, the response is to **build a fully-verified SMT engine
natively inside FX as Phase Z₉** — see §11.8.10's reference list
for the assembly components (verified SAT + verified theory
deciders + verified Nelson-Oppen).  Calling an external SMT is
absolutely forbidden under any phasing.

The maximal-power kernel is sound by composition of known-sound
components.  **Anything that cannot be implemented cleanly within
the zero-axiom + closed-system discipline is de-scoped** — e.g.,
`--type-in-type` is absolutely banned even as a flag; external
SMT is absolutely banned even with a "trust" annotation;
LLM-driven proof generation INSIDE the kernel is absolutely
banned even with "verification gates."

### 11.8.12 What "★ MILESTONE A" means under §11.8

The previous milestone target (decidable raw-reduction Conv via
NbE) is REVISED:

* **MILESTONE A (revised)** = **decidable TYPED conversion + decidable
  TYPED checking** for the semantic core (Phase Z₁ + Z₂ + Z₃).
* **MILESTONE A+** = same, plus cubical primitives (Phase Z₄).
* **MILESTONE A++** = same, plus HITs (Phase Z₅).
* **MILESTONE B** = MILESTONE A++ plus IR + the full
  structural-reflection-degree ladder (Phase Z₆ + Z₆+): Mahlo +
  higher-order Πⁿ-reflection + single-structure accessible-category
  reflection (→ `vopenka`) + **sequential Exact Structural Reflection**
  (→ **`kunenI0`**, the committed I0-strength categorical apex) + the
  2024 SR frontier (`exacting`/`ultraexacting`), per §11.8.2.  These are
  categorical reflection degrees, not embeddings j:V→V; the open tail
  (`schlutzenbergVLambdaPlus2`, `reinhardtDirected`) is catalogue-only.
  Six-month delivery target from Phase Z₆ kickoff.
* **MILESTONE C** = MILESTONE B plus guarded recursion (Phase Z₇).
* **MILESTONE D** = MILESTONE C plus 21-dim integration (Phase Z₈)
  — full FX kernel.

Raw-reduction Conv decidability (the old MILESTONE A) is a
**sub-result** of typed Conv decidability — useful as substrate
but insufficient as a typechecker.

### 11.8.13 Univalence-everywhere discipline

The kernel commits to a **univalence-everywhere** discipline: univalence
holds AT EVERY MODE, EVERY LEVEL, EVERY LIFT, EVERY DIMENSION, and EVERY
MODALITY in FX's substrate that admits identity-like structure.  Univalence
is ALWAYS computational (`Conv.fromStep Step.eqType` body, never
`axiom`), ALWAYS a theorem (not a postulate), and ALWAYS justified by
multiple independent proofs.

**Why univalence-everywhere is load-bearing for the §11.9 program — it
is the canonical dedup oracle.**  Univalence makes equivalent structures
*equal* and (propositionally, via `Step.eqProp`) logically-equivalent
statements equal, so deciding "are these two facts the SAME fact?" is
exactly Decidable Conv (MILESTONE A).  That decidable, canonical identity
is the ingredient every classical complexity measure lacked: it lets FX
quotient the space of facts and **count distinct ones**.  Hence
univalence-everywhere is precisely what turns Kolmogorov complexity from
"shortest program" (uncomputable, machine-floating) into "the canonical
prime-factorization size in the deduplicated polygraph" (computable up to
known Conv) — the foundation of `O-HARD` / `O-AIT` (§11.9.1.3 / §11.9.2.1).
The discipline's reach across all 21 dimensions (the cross-dimension
univalence below) is what makes the count *well-defined per sort* rather
than over-counting equivalent-but-syntactically-different facts; and the
*directedness* of the marking turns the count into a **truncation-indexed
spectrum `Kₙ`** (h-prop level = logical complexity; higher = proof-
structural), an invariant no scalar Kolmogorov measure can express.  So
"univalence everywhere" is not only a soundness stance — it is the
measuring instrument's calibration.

**Three (actually four) independent justifications.**  Each is a separate
body, so no single foundational assumption is load-bearing:

| # | Proof view | Body | Reference |
|---|---|---|---|
| 1 | **Operational** | `Univalence := Conv.fromStep Step.eqType` — kernel reduction rule | lean-fx-2 D2.6 + CLAUDE.md mandate |
| 2 | **Polynomial / structural** | universe is subterminal in `Poly^Cart` ⇒ univalence as subterminality theorem | Aberlé-Spivak 2409.19176 |
| 3 | **Polynomial pseudomonad** | natural model with unit + Σ + Π ⇔ polynomial pseudomonad/pseudoalgebra; univalence as algebra coherence | Awodey-Newstead 1802.00997 |
| 4 | **∞-topos / semantic** | every (∞,1)-topos has strict univalent universes; equivariant cartesian cubical gives constructive Quillen presentation | Shulman 1904.07004 + Awodey-Cavallo-Coquand-Riehl-Sattler 2406.18497 |

A fifth view exists when directed mode is in scope: **cubical computational**
via CCHM Kan ops + Sterling-Angiuli 2021 normalization extending `Step.eqType`
to `transp/hcomp/Glue` reductions (per §11.8.4).

**Propagation scopes.**  Standard univalence applies inside a single
homogeneous univalent universe.  The discipline says: extend it
everywhere FX has identity-like structure.

| Scope | Standard treatment | FX univalence-everywhere commitment |
|-------|--------------------|--------------------------------------|
| Inner univalent (`gen_universeU`) | Univalence (cubical) | Univalence (cubical) — baseline |
| **Outer strict (`gen_universeS`)** | K-axiom / UIP definitional | **Univalence WITH strict large-elim discipline** — "strictness" = elim shape + reduction calculus, NOT propositional identity; per §11.8.2 |
| SProp (`gen_sprop`) | Definitional proof irrelevance | Univalence trivially (any two inhabitants equal) — compatible by collapse |
| Directed (`gen_universeD`) | Directed univalence (Riehl-Shulman) | Directed univalence as theorem via triangulated modalities — Gratzer-Weinberger-Buchholtz 2407.09146 |
| (∞,ω)-directed (`gen_universeOmega`) | (∞,ω)-univalence (Loubaton) | (∞,ω)-univalence as derived rule — Loubaton 2307.11931 §6.1.3 |
| Cross-mode lifts (`gen_univLift` / `gen_univLower`) | Hofmann-Streicher natural transformation | **Lifts ARE univalence-preserving** — provable Conv between `lift(equiv)` and the equiv-at-target-mode |
| Cumulativity (`Type i ⊆ Type j`, `i ≤ j`) | Coercion (unstructured) | `cumulUp` is univalence-preserving — equivalences at lower level become equivalences at higher |
| Level polymorphism (`∀ l. ...`) | Per-level instance | One Univalence theorem polymorphic over all `LevelExpr` (universe-polymorphic univalence) |
| 21-dim graded layers (FX dims 2-21) | No univalence at non-Type dims | **Each dimension's "type universe" gets its own univalence** — effect-row equivalences, usage-grade equivalences, lifetime equivalences, ... GENUINELY NOVEL FX-original |

**Why this matters.**  The univalence-everywhere commitment is what makes
FX qualitatively different from prior type theories.  Standard 2LTT
sacrifices univalence at the outer mode to gain K-style UIP for
metatheory.  FX rejects this trade: by separating the inner/outer
distinction at the REDUCTION CALCULUS level (strict vs cubical Kan)
instead of at the IDENTITY structure (K vs univalence), FX keeps
univalence at every mode.  The outer mode loses K-axiom but gains
univalence; FX gets metatheory + computational reflection that respect
univalence rather than violating it.

**Cross-dimension univalence is the most novel commitment.**  FX's 21
graded dimensions each carry their own "type universe" of admissible
grades / labels / effect rows / etc.  Standard treatments give each
dimension its own (often UIP-flavored) equality.  Under univalence-
everywhere, EACH DIMENSION gets a univalence theorem: equivalent
effect-rows are EQUAL effect-rows, equivalent usage grades are EQUAL
usage grades, equivalent lifetimes are EQUAL lifetimes.  This is what
makes FX's 21-dim composition behave coherently across the substrate
— no dimension can "leak" non-univalent equality into another.

**Absorbed frontier (the 12-paper compatible set, 2026-05-28 literature scan).**
The discipline is realized by absorbing twelve frontier 2020-2026 papers
into FX's substrate, with the four-justification chain above as the
load-bearing subset.  The other eight papers contribute foundation,
substrate, and feature machinery that the discipline depends on:

```
                          UNIVALENCE-EVERYWHERE DISCIPLINE
                       (computational, theorem, 3-4 independent proofs)
                                          │
            ┌─────────────────────────────┼─────────────────────────────┐
            ▼                             ▼                             ▼
       FOUNDATION                     SUBSTRATE                     FEATURES
       #3 Alloc effects               T3 Istari STC kernel          #6 Directed univ.
       #5 Bounded levels              T7 Equivariant cubical        #7 Commuting cohesions
       T1 Mahlo just.                 #1 Poly universes             #8 Tiny object √
       T2 Mahlo+Acc                                                 T5 Def functoriality
                                          │
                                          ▼
                                     CONVERSION
                                     #2 Sort poly. (univalence parametric over sort)
```

Mapping table — each row is the SINGLE canonical citation for the paper
in this spec (cross-references back to §11.8.2 / §3.10 / §3.16.12 / etc.
inline avoid repeating the citation):

| # | Paper | arXiv / DOI | FX role |
|---|---|---|---|
| #1 | Aberlé-Spivak, Polynomial Universes in HoTT | 2409.19176 | Substrate. Univalence-as-subterminality (also row 2 of justifications above; §3.10 structural). |
| #2 | Poiret-Gilbert-Maillard-Pédrot-Sozeau-Tabareau-Tanter, All Your Base / Sort Polymorphism | POPL 2025 / 10.1145/3704912 | Conversion. Univalence parametric over sort modes. |
| #3 | Koronkevich-Bowman, Type Universes as Allocation Effects | 2407.06473 | Foundation. Region semantics; unifies FX dim 1 ↔ dim 7 + dim 15. |
| #5 | Chan-Weirich, Bounded First-Class Universe Levels | 2502.20485 | Foundation. LevelExpr with bounded `∀ i<j.` quantifiers; basis for decidable `denoteEquiv` together with Mörtberg-Sterling poly-time (§11.8.2). |
| #6 | Gratzer-Weinberger-Buchholtz, Directed Univalence in Simplicial HoTT | 2407.09146 | Features. `gen_universeD` directed univalence (also §3.10, §11.8.2). |
| #7 | Myers-Riley, Commuting Cohesions | 2301.13780 | Features. 21D composition primitive (also §3.16.12). |
| #8 | Riley, A Type Theory with a Tiny Object | 2403.01939 | Features. Universe operator √ for synthetic infinitesimals / SDG. |
| T1 | Dybjer-Setzer, Extended Predicative Mahlo | J. Log. Comput. 34(6) 2024 | Foundation. Predicative justification for `mahlo` UniverseFlag (§11.8.2). |
| T2 | Takahashi, Inaccessible Sets in MLTT + Mahlo | 2402.15074 / LMCS 2025 | Foundation. UniverseFlag rung collapse design hint. |
| T3 | Li-Yao-Harper, Mechanizing STC in Istari | 2509.11418 / CPP 2026 | Substrate. Verified NbE + STC modality kernel (= reference 7c). |
| T5 | Laurent-Lennon-Bertrand-Maillard, Definitional Functoriality | ESOP 2024 / 2310.14929 | Features. Functor laws as definitional equalities (orthogonal to identity structure). |
| T7 | Awodey-Cavallo-Coquand-Riehl-Sattler, Equivariant Cartesian Cubical Model | 2406.18497 | Substrate. Constructive cubical model (also row 4 of justifications). |

**Decidable `denoteEquiv` on LevelExpr** comes from Mörtberg-Sterling
polynomial-time normalization (§11.8.2) + #5 Chan-Weirich bounded
first-class levels — the canonical-form approach.  This preserves
univalence at every mode (including outer strict via the strict-reduction
discipline of §11.8.2) and avoids any UIP-flavored shortcut that would
break univalence-everywhere by Hofmann-Streicher 1998.

**Honesty discipline.**  Per §11.8.11, each shipped univalence theorem
must have a real body and pass `#assert_no_axioms`.  No
`axiom Univalence : ...`.  No `noncomputable def`.  When a propagation
scope (e.g. cross-dimension univalence at dim 7 Lifetime) lacks a
written body, it is marked as a pending obligation in the per-dim
metatheory ledger, NOT claimed as delivered.

### 11.8.14 Research track: definitional univalence in a synthetic condensed setting

**Status: RESEARCH TRACK — a committed *attempt to prove*, NOT a
milestone and NOT a landed result.**  Per the manifesto's no-handwave
rule, every claim below is one of: (a) a published result with
reference, (b) an on-ramp FX already commits to, (c) an explicit OPEN
obligation tagged as such.  This section commits FX to *attempting* the
combined target; it does not assert the target holds.  No milestone
star; not on the Phase-Z critical path.  Mirrors the discipline of
§3.0.7 (target obligations, not a victory lap).

**The combined target.**  A kernel mode in which BOTH hold:

1. **Identity is definitional (Higher Observational TT).**  Identity
   types compute by recursion on type structure: `Id (A→B) f g ≡
   (x:A) → Id B (f x) (g x)` (funext definitional), `Id 𝒰 A B ≡
   (A ≃ B)` (univalence definitional).  So funext / propext /
   univalence hold by `rfl`, not merely up to a path — the transport
   tax collapses to computation.
2. **Every type is internally condensed.**  A condensed cohesion focus
   (♭ / ♯ / ∫ over the discrete fragment, profinite/Stone test
   objects) makes every type carry condensed structure: all definable
   maps are continuous by construction, and condensed-abelian groups
   form an internal abelian category (so homological algebra of
   "topological" structure — `Ext` / `Tor` — is internal).

**The synthesis — why combine them (the genuinely novel object).**
Under (1)+(2), a continuous equivalence of condensed types is
definitionally an equality: **homeomorphic spaces are definitionally
equal** (the topological structure-identity principle), and the
condensed-abelian homological algebra carries definitional coherence.
This is the topology×algebra instance of univalence-everywhere
(§11.8.13) — applied to the one interface where classical foundations
fail hardest (topological abelian groups are not an abelian category;
condensed fixes this, and definitional identity makes the fix
`rfl`-clean).

**On-ramps FX already commits to (this is not from scratch):**

* **Internal parametricity** (§3.16.8 `gen_param`) IS the "baby HOTT"
  substrate — Altenkirch-Chamoun-Kaposi-Shulman, *Internal
  Parametricity, Without an Interval* (POPL 2024, arXiv:2307.06448),
  ships a presheaf model + canonicity proof for exactly this base.
  FX's parametricity generator is the literal on-ramp.
* **Cohesion modalities** (§3.16.12 `gen_shape` / `gen_flat` /
  `gen_sharp`) are the condensed-cohesion substrate (condensed sets =
  a cohesive topos over Set).
* **Univalence-everywhere** (§11.8.13) is the discipline this extends
  from *computational* (cubical) to *definitional*.
* **Bounded universe levels** (`LevelExpr` + Chan-Weirich §11.8.2)
  parameterize the condensed size-cutoff cardinal κ (κ-condensed
  universes).
* **Reference implementation to track:** Narya (Shulman) — already
  runs parametric + higher observational type theory.

**Proof obligations (what "trying to prove" decomposes into):**

* (O1) Port baby-HOTT (internal parametricity + presheaf model +
  canonicity, ref DU2) onto FX's `gen_param` substrate.  *Substrate
  published; the port is engineering.*
* (O2) Add bridge types (indexed parametricity) ⇒ identity types.
  *Roadmap step; in progress externally.*
* (O3) Add Kan fibrancy ⇒ transport; prove **normalization**.
  **THE open part** — full-HOTT normalization is unproven anywhere as
  of 2026 (algorithm sketched, no proof).
* (O4) Add the condensed cohesion focus + a synthetic Stone/profinite
  test-object axiom.  *Synthetic condensed TT is unbuilt; synthetic
  Stone duality is an emerging 2024-2026 line.*
* (O5) Prove condensed-abelian = internal abelian category; prove
  homeomorphic = definitionally equal (the synthesis SIP).

Each obligation ships `#assert_no_axioms`-clean per §11; nothing is
claimed delivered before its body exists.

**Reachable NOW (independent of the open parts O3/O4) — the
near-term proving ground:**

* **Univalent parametricity** (Tabareau-Tanter-Sozeau, *The Marriage
  of Univalence and Parametricity*, JACM 2021) combines FX's committed
  univalence + internal parametricity to give automatic, computational
  transport across equivalences for a large class of types NOW —
  ~most of the transport-tax reduction on already-shipped machinery,
  without waiting on O3.
* **The `dProp` / Sierpiński split** — synthetic condensed/topology
  predicts and *founds* FX's `dProp` (§3.16.10, the discrete/decidable
  fragment) and a sibling Sierpiński universe `Σ` of semi-decidable
  propositions.  Reachable on synthetic-topology machinery that exists
  (Escardó).
* **Searchable compact types** — decidable quantification
  `∀ (x : 2^ℕ). p x` over profinite/compact types (Escardó), a
  genuinely new decision procedure, reachable independent of full
  HOTT.

**Honest risk register (brutal):**

* **Highest-risk track in the document.**  O3 (definitional-univalence
  normalization) is open everywhere; O4 (synthetic condensed TT) is
  unbuilt; O5 (the combination) is unprecedented.
* The **interval route is provably blocked**: an interval's large
  recursion + definitional iso-types implies *equality reflection*,
  which contradicts univalence.  Therefore FX's committed *cubical*
  univalence (§11.8.4) is the COMPUTATIONAL route and CANNOT go
  definitional — definitional univalence is a SEPARATE, no-interval,
  observational substrate.  The two coexist (cubical for computational
  univalence + cubical Kan features; the HOTT track for definitional
  identity).  This is an architectural fork, stated honestly.
* Decidability is preserved only on scoped fragments
  (searchable-compact, regular session types, the structural-identity
  fragment); the general case stays propositional/computational.
* **Verdict:** pursue as a parallel research track with the three
  reachable-now wins as the proving ground; promote toward a milestone
  only if/when O3 closes (externally or in FX).  See §13's
  "Definitional univalence + synthetic condensed" reference block
  (DU1-DU9).

#### 11.8.14.1 Stated open problems (attackable now)

The research track above is a *program*; this subsection pins the
concrete **open problems** within it — each stated as a
provable/refutable question with its crux, its foothold, and what its
answer settles.  Per the no-handwave rule these are STATED PROBLEMS,
not claimed results; none is a milestone.

**OP1 — Univalent parametricity over the grade discipline.**
*The recommended first attack: genuinely open, FX-uniquely-posed,
standable on a published result, and it de-risks O1.*

> Does univalent parametricity (Tabareau-Tanter-Sozeau, ref DU4) extend
> to **graded modal** dependent type theory (§6)?  I.e. is the
> parametricity logical relation **compatible with the grade
> discipline**, and does it yield **computational transport across
> equivalences that preserves grades**?

* **Crux (why it is open, not routine):** parametricity's logical
  relation relates two sides *and the relation itself* — it wants to
  **use a variable more than once**; linearity/grades **forbid
  double-use**.  Whether parametricity is even *compatible* with
  quantitative typing is unresolved.  Univalent parametricity is
  mechanized for plain MLTT (DU4); the **graded/modal** case is
  unexplored and may require a genuinely new relation.
* **FX-uniquely-posed:** FX is the only setting committing univalence +
  internal parametricity (§3.16.8 `gen_param`, M86) + 21 graded
  dimensions (§6) at once — no other system can even state OP1.
* **Foothold:** stand on DU4 (Coq-mechanized) + graded-TT metatheory
  (Atkey QTT, ref 33; Wood-Atkey, ref 34; Abel-Danielsson-Eriksson,
  ref U14).
* **Milestone 0 (the crux, weeks not years):** the simplest non-trivial
  grade — linearity `{0,1,w}` (Appendix C) — and *one* former
  (functions): state + prove the parametricity relation respecting
  linear usage.  **Settles:** *can a linear variable be related
  parametrically without violating its grade?*  That single yes/no is
  the whole problem in microcosm.
* **Why it matters both ways:** YES ⇒ definitional univalence over FX's
  graded substrate (O1) is plausible and the §11.8.14 track is viable;
  NO ⇒ the obstruction is found cheaply and early.  Down-to-earth
  payoff: free transport across equivalences for resource-tracked code
  (refactor-without-breaking-proofs for graded/effectful programs).

**OP2 — The directed self-endofunctor (the FX-only trophy).**
*Genuinely open, statable nowhere else; gated on the directed-universe
substrate, so NOT the first attack.*

> Is there a non-invertible elementary self-endofunctor of the (∞,ω)
> directed universe (`gen_universeOmega`) that **fixes the 0-truncation**
> (every set, every ordinal) but acts non-trivially on the higher
> directed cells — and is it consistent / constructible?

* **Why open in a new way:** the Gödel block of ambient-Reinhardt runs
  through a *moved ordinal* (§11.8.2.1); fix every ordinal and the
  implication to `Con(FX)` may fail, so Gödel does NOT obviously
  forbid it.  Status: unknown — possibly cheap-and-constructible
  (directed type theory already has elementary endofunctors like
  `op : S → S`; the open case is a non-invertible one fixing objects),
  possibly strong-and-open, possibly refutable.
* **Unstatable outside directed univalence** — needs the ordinals fixed
  *and* somewhere non-trivial (the higher cells) for the functor to
  act; no set-theoretic or (∞,1) foundation can express it.
* **Gate:** requires the directed-universe substrate (Loubaton-level,
  `gen_universeD`/`gen_universeOmega`) built first — hence the trophy,
  not the opening move.

**Guaranteed-deliverable alternatives (application of known machinery,
NOT open problems — pick these if a sure win is wanted before a
might-fail gamble):**

* **Directed Version-univalence** — apply Riehl-Shulman directed
  univalence (committed `gen_universeD`) to the version/migration
  category (objects = versions, morphisms = migrations); makes
  migration coherence (§14-15) a free theorem.  Known machinery, clean
  theorem, immediate systems payoff.
* **Searchable compact types** — port Escardó (ref DU5): decidable
  `∀ (x : 2^ℕ). p x` over profinite/compact types, a new decision
  procedure, zero-axiom.

**Honest framing of "attack with FX."**  FX's *currently shipped*
substrate (PolyCell, LevelExpr, NbE) does not yet contain the apex
layers OP1/OP2 need (parametricity, univalence, directed universe are
pending — M86, §11.8.13, M25).  So "attack now" realistically means
**theory + a small mechanization probe with FX as the home**, not "run
it on FX today."  OP1's Milestone 0 is the one that is genuinely
attackable now — on paper + a small Lean fragment standing on DU4 —
before the full apex exists, which is exactly why it is the
recommended opening move.

---

## 11.9 The Internalization Program — frontier and beyond-frontier extensions

§11.8 commits the *apex* (the strongest decidable kernel).  §11.9
states the *method* that generated it and applies that method past the
apex.  It is a research program, not roadmap: **none of §11.9 is on the
MILESTONE A–D critical path**, and every entry obeys the §1 manifesto
discipline (a cited result, a constructive Lean target, or an explicit
status tag) and the §11.8.0 ledger format.  The firewall is hard — §11.8
ships first; §11.9 is walled off exactly as §11.8.14 / §11.8.2.1 are.

**Status legend** (reused from §11.8.0): **SHIPPABLE-NOW** (decidable,
runs on the current substrate or a fragment) · **SPECIFIABLE-NOW**
(pinnable as an obligation/schema, no new mathematics, apex-gated) ·
**OPEN-RESEARCH** (genuine open problem, attackable, foothold named) ·
**MOONSHOT** (high-risk, concrete first step + flagged speculation).

### 11.9.0 The internalization principle (the generator)

One move recurs throughout this document: **take a quantity that is
normally external / meta / semantic and make it an internal, typed,
certified, computable cell.**  Already done: dimension is *computed*
(`RawCell.dim`, §4) not an a-priori index; equality is the *saturation
marking* (§3.3–§3.4) not a primitive; complexity is a *grade* (§3.7);
consistency strength is *computable data* (`ConsistencyStrength`,
§11.7.1); decidability is *computable data* (`isDecidableInProfile?`,
§11.7.4).  The frontier is the same move applied to quantities not yet
internalized — **proof simplicity, algorithmic information, entropy/time,
ordinal strength, theory-space curvature**.  The principle is a
*generator*: for any external quantity `X`, ask "what is its
internalization as an FX cell, and what becomes computable once it is?"
The subsections below are its first instances.  The internalization
principle itself is OBLIGATION **O-INTERNAL** (meta; discharged
incrementally as each instance lands).

### 11.9.1 New computable internal structures

#### 11.9.1.1 Obstruction-cohomology of the profile — `O-OBSTRUCT` (SHIPPABLE-NOW on sublattices)

The §6.8 cross-dimension soundness collisions are not a list — they are
the **unfillable horns** of cross-sort horizontal composition (§3.6
Gray).  The per-pair `bilaxCompatibility` witnesses (§3.14, scaffolded
at V2-L5.5) are 1-cochains; the cellular-tensor associator/symmetry
coherence (§3.0.7 T5/T6) and the Zwart-Marsden no-go register (T7)
assemble a cochain complex on the 21-dimension lattice.  Its
cohomology **classifies exactly which subsets of the 21 dimensions are
jointly sound** — a non-zero `H²` class is a certified no-go, a
coboundary is a certified distributive law.  Decidable (finite lattice),
so FX emits a **certified periodic table of admissible type theories**.
Anchor: Zwart-Marsden `arXiv:1811.06460` + Myers-Riley §6.4 + §3.0.7
(T7).  Hook: §6.8 + §3.14 `bilaxCompatibility`.  Prototype: `H²` on the
{Usage, Effect, Security} 3-sublattice (must reproduce the known §6.8
entries).  ~2K LoC.

#### 11.9.1.2 Squier proof-homology = Hilbert's 24th problem — `O-HOMOLOGY` (SHIPPABLE-NOW: `H₁`, term fragment)

A proof of `Conv a b` is a path of generating cells; `cd_lemma` 2-cells
join parallel proofs; Squier 3-cells fill critical-pair branchings
(§3.4).  By Squier (FDT) + Guiraud-Malbos polygraphic resolutions, a
*convergent* polygraph yields a free resolution, hence a **proof-homology
`Hₙ(profile)`**: `H₀` = theorems, `H₁` = essentially-distinct proofs,
`H₂` = essentially-distinct proof-equivalences.  This is a concrete
candidate answer to **Hilbert's lost 24th problem** (proof simplicity,
recovered by Thiele 2003): a theorem has a canonically-simplest proof iff
its proof-cell is contractible (thin all the way up); the obstruction to
simplicity is the first non-zero `Hₙ`; and high homological dimension is
a *lower bound* on proof complexity.  Decidable for the FX profile
(finite generators + convergence + Makkai §3.9).  Anchor: Squier 1987
(ref 14) + Guiraud-Malbos + Hilbert/Thiele.  Hook: the cd / critical-pair
enumeration (§3.4, M6/M7).  Prototype: `H₁` of the β/ι/η term-sort
polygraph — **pre-apex**, reuses the shipped critical-pair table.

#### 11.9.1.3 The Hardness instrument — `O-HARD` (D,B SHIPPABLE-NOW; N SPECIFIABLE; A OPEN)

Over the Conv-deduped dependency DAG of a certified theorem (`FactDAG`,
nodes = facts up to Conv, §11.8.13 univalence supplying the dedup), define
`Hardness(T ∣ KB) = N · D · (1 + A) · (1 + B)`:
**N** = conditional novelty (Σ `K_FX0` over the deduped prime facts of
`T` not Conv-equal to anything in `KB`); **D** = logical depth
(critical-path height of the DAG, Bennett); **A** = abstraction gain
(does adding `T`'s machinery compress the rest of the corpus — DreamCoder
library-gain, approximable from below, certified); **B** = bridge rank
(DAG diameter across corpus regions).  Each factor is a known
statistical-model blind spot, so `Hardness` is the **adversarial
complement of an LLM's training objective**.  The **δ-discrepancy**
`δ(T) = perplexity_LLM(T) − N_certified(T)` localizes where a model is
*falsely confident* (`δ ≪ 0` = thinks routine, is deep) — the certified,
signed form of "stumbling on already-stated ideas," and the most novel
mining target.  Anchor: Bennett (logical depth) + Gell-Mann–Lloyd
(effective complexity) + Koppel (sophistication) + Ellis et al.
(DreamCoder, library learning by MDL) + Schmidhuber (compression
progress) + Solomonoff/Levin.  Hook: FX0 as the *fixed* reference machine
(§12.6, kills classical-K's additive-constant float) + Decidable Conv
(MILESTONE A) as the dedup oracle.  `D` and `B` are pure graph algorithms
on the DAG — **pre-apex computable**; `N` is computable modulo *known*
Conv; `A` is the genuine Chaitin residue (approximable, never optimal —
correctly, since it measures true conceptual invention).

### 11.9.2 New synthetic disciplines

#### 11.9.2.1 Synthetic algorithmic information theory — `O-AIT` (SPECIFIABLE-NOW)

FX0 (~600 lines, §12.6) is a *fixed* universal-ish verifier, so
`K_FX0(T) := size of the smallest FX cell whose FX0-certificate produces
T` is a concrete complexity measure with a pinned reference machine — the
thing classical `K` lacks.  Three commitments: (i) a **description-length
grade dimension** making incompressibility a typing obligation; (ii) `K`
as a **truncation-indexed spectrum `Kₙ`** (the Verity marking §3.3
selects the level: `K₀` = logical, higher = proof-structural) — statable
only because the foundation is directed; (iii) the **Chaitin-bound ladder
= the Gödel-climbing ladder** (§11.7.1): provable incompressibility rises
strictly with reflection degree, so consistency strength *is* the
provable-`K`-ceiling.  `K` decomposes as vocabulary-cost + wiring-cost,
and wiring = Squier-homology rank (§11.9.1.2) — the two structures are
one invariant.  Anchor: Chaitin + Kolmogorov + Bennett + Solomonoff.
Hook: §12.6 (FX0) + §3.3 (marking) + §11.7.1 (climbing).

#### 11.9.2.2 Synthetic thermodynamics of the directed polygraph — `O-THERMO` (OPEN-RESEARCH)

Directedness is an asymmetry — a reduction runs one way and is reversible
only when the marking makes it thin — which is the structure of
thermodynamics (spontaneous vs reversible).  A non-thin cell that
*discards information* (a projection, a non-injective rewrite) produces
logical entropy (Landauer cost); a thin cell is adiabatic.  Define a free
energy `cost − T·(info discarded)` (cost grade dims 13/15); then **SN
(`O-NORM`) is the Second Law** (free energy is bounded below and descends
along directed cells → relaxation to a normal form), **confluence is
ergodicity** (unique equilibrium), and the **Tot/Div boundary (§11.7.2)
is a phase transition**.  A *temperature* parameter unifies kernel
reduction (`T→0`, Lévy-optimal/geodesic) with agent search (high `T`,
simulated annealing) as one statistical-mechanical system.  Anchor:
Landauer 1961 + Bennett reversibility (refs 65–66) + Lévy optimality +
Ollivier-Ricci.  Hook: directedness + §3.3 marking + cost grade +
§11.7.2.  The SN-as-Second-Law identity is the sharp conjecture; the
entropy grade is a SHIPPABLE sub-piece.

#### 11.9.2.3 The geometry of theory-space — `O-TSPACE` (OPEN-RESEARCH)

The extension calculus moves through theory-space; the cellular Gray
tensor (§3.0.7) makes it monoidal.  Then: `ProfileExtension`s at a
profile = the **tangent cone** (the directions math can grow); the Fire
Triangle / Zwart-Marsden no-gos = the **boundary singularities**; the
cellular-tensor lax-3-cell **associator (T5) = curvature** (does the
*order* of adding concepts matter — flat ⟺ order-independent); `Hardness`
(§11.9.1.3) = the **metric**; mathematical discovery = a high-`Hardness`
**geodesic flow**.  Makes "where can mathematics go from here" a
*computable* question (enumerate the tangent cone, score, follow the
gradient).  Anchor: Crans 1999 / Steiner 2004 (Gray) + Lawvere doctrines
+ §3.0.7.  Hook: §3.14 extension calculus + T5/T6 coherence.

### 11.9.3 Extended open problems (OP3–OP7, §11.8.14.1 format)

* **OP3 — The sameness-unification theorem.** Are Conv (terms),
  univalence (types), bisimulation (protocols, §13.19), and contextual
  equivalence all *one* construction — "a thin cell at that sort"?  FX is
  the only setting that hosts all four sorts + a single marking, so it is
  the only place this is statable.  *Foothold:* directed Yoneda /
  Structure Identity Principle (Riehl-Shulman directed univalence,
  §3.10) + coalgebraic bisimulation.  *Settles:* observational
  equivalence in every sort is the same phenomenon.  OPEN-RESEARCH.

* **OP4 — Laver-table periodicity as a forced invariant of
  `reinhardtDirected`** (refines OP2, §11.8.2.1).  The higher-cell action
  of the directed self-endofunctor is constrained to a representation of
  the Laver-Steel left-distributive algebra (SR9), whose Laver tables are
  *computable* and whose first-row period `p(n)→∞` is equivalent to an I3
  cardinal (Dougherty-Jech).  So a decidable, zero-axiom FX computation
  (the period) becomes a *shadow of large-cardinal strength*.  *Status:*
  the period computation is SHIPPABLE; the representation-forcing step and
  the I3 bridge are OPEN-RESEARCH.  Hook: `gen_universeOmega` + SR9.

* **OP5 — A geometric proof of `O-NORM` via Ricci/free-energy flow.**
  Define discrete Ollivier-Ricci curvature from the cost-tropical weights
  (§6, §3.1 Reedy); conjecture the curvature-descent flow's fixed points
  are exactly the η-long normal forms, with positive curvature ⟹ local
  confluence ⟹ SN — a *geometric* normalization technique orthogonal to
  the syntactic sconing route, shipping its own complexity bound.
  Anchor: Ollivier + Lévy optimality.  MOONSHOT.

* **OP6 — A certified locus of undecidability via the protocol sort +
  MIP\*=RE.** Encode quantum nonlocal games as `.protocol` cells in the
  Quantum-Linear profile (§3.15); the tensor vs commuting-operator models
  become Gray `horizontalComposite` vs a commuting interchange; MIP\*=RE
  (Ji-Natarajan-Vidick-Wright-Yuen 2020, refuting Connes embedding) then
  forces `Conv` on those cells to be **undecidable** — a *certified*
  `undecidable` verdict from `isDecidableInProfile?` (§11.7.4) with a
  quantum-information witness, pinning the exact boundary of the
  decidable-typechecking guarantee per sort.  OPEN-RESEARCH.

* **OP7 — Discharge `O-ORD` via a mechanized GLP reflection algebra.**
  The reflection ladder (§11.8.2) + Gödel-climbing (§11.7.1) is a
  candidate constructive model of Beklemishev's polymodal provability
  logic **GLP**; its closed fragment (the Worm) yields canonical ordinal
  notations.  Mechanizing the **graded provability (reflection) algebra**
  inside FX turns "rung *n* has strength X" / "*n+1* ⊢ Con(*n*)" from
  calibration prose into *theorems*, discharging the currently-absent
  `O-ORD` (§11.8.0) — and would be the first mechanized GLP-based ordinal
  analysis.  Anchor: Beklemishev GLP + Japaridze + Rathjen (SR11).
  SPECIFIABLE-NOW (the highest-odds real result of §11.9).

### 11.9.4 The discovery engine — Kolmogorov-driven open-ended search (`O-ENGINE`) + proof firewall (`O-FIREWALL`, both SPECIFIABLE-NOW)

§11.9.1–§11.9.3 internalize the *measures* (novelty, proof-simplicity,
ordinal strength); this subsection composes them into the *engine* that
uses those measures to manufacture genuinely-novel verified mathematics —
math that neither restates nor compresses what the corpus already holds.

**The honest reframe — drive on a certified upper bound, not on `K`.**
True Kolmogorov complexity is uncomputable (Chaitin), so no engine can
optimize it directly.  FX has the two ingredients that make a *runnable
surrogate* exact, neither of which classical AIT had: FX0 is a FIXED
reference machine (§12.6 — no additive-constant float, `K_FX0` is a
concrete number, O-AIT §11.9.2.1), and univalence-everywhere (§11.8.13)
makes Decidable Conv (MILESTONE A) a canonical dedup oracle (no
over-counting equivalent-but-syntactically-different facts).  So define
`L(T ∣ KB)` = the size of the smallest FX0-certificate the engine has *so
far found* for `T` relative to the deduped corpus `KB`.  `L` is
computable, monotone-decreasing as better compressions are discovered,
and `L ≥ K_FX0` always; the residue `L − K_FX0` IS the creative frontier
— the compression that exists but has not been found.  The engine
**minimizes `L` of the corpus while maximizing `Hardness` (§11.9.1.3) of
new facts**: this is Solomonoff/Levin induction made runnable, converging
toward `K` forever without ever reaching it.  "Make `K` a driver"
resolves, precisely, to "drive on the certified tightening bound `L`; the
residue is where novel math lives."

**The seven-component co-evolutionary loop.**

1. **Knowledge base `KB`** — the Conv-deduped `FactDAG` (§11.9.1.3):
   nodes = facts up to Conv, edges = dependency.  Canonical because of
   univalence-everywhere (§11.8.13); this is what `L` / `Hardness` are
   measured against.
2. **Proposer (untrusted)** — an LLM / RL / FunSearch-style generator
   living OUTSIDE the kernel (§24 agent protocol; §11.8.11
   no-LLM-in-kernel).  Emits raw candidate cells (theorem + proof
   attempts); may be adversarial.
3. **Verifier (trusted, FX0)** — the ~600-line external checker (§12.6)
   certifies survivors zero-axiom.  Only certified cells enter `KB`.
4. **Hardness scorer** — computes `Hardness(T ∣ KB) = N·D·(1+A)·(1+B)`
   + the `δ`-discrepancy (§11.9.1.3) over the certified `FactDAG`; `δ ≪ 0`
   (proposer thinks routine, certified-deep) localizes the richest mining
   targets — the engine's adversarial complement to the proposer's
   training objective.
5. **Quality-diversity selector** — NOT a scalar maximizer (which
   mode-collapses to one trick); a MAP-Elites / novelty-search archive
   binned by behavioral descriptor (corpus region × sort × depth band),
   keeping the highest-`Hardness` elite per bin (Lehman-Stanley).  This
   is what makes "open-ended" more than a slogan.
6. **Homology-guided compressor** — periodically recomputes Squier
   proof-homology `H₁` (§11.9.1.2, O-HOMOLOGY) over the accumulated
   proofs; **the non-trivial `H₁` classes ARE the candidate abstractions**
   (essentially-distinct proof patterns reused across the corpus).
   Promoting an `H₁` generator to a named lemma / definition is a
   DreamCoder library-learning step and is exactly what turns the `A`
   (abstraction-gain) factor of `Hardness` positive.  Abstraction is
   therefore *principled* (read off homology), not heuristic.
7. **Compression-progress objective (the driver)** — `dA/dt`, the rate at
   which the certified corpus's total description length drops as
   abstractions are promoted (Schmidhuber's curiosity signal), here
   **canonical** (univalent dedup) and **certified** (FX0).  The engine
   is driven to maximize the rate of compression progress of *verified*
   math.

**Two soundness properties (`O-FIREWALL`).**  (i) **Goodhart-resistance**
— a naive novelty-maximizer chases incompressible noise, but the `(1+A)`
factor rejects it (noise compresses nothing, `A = 0`), and the QD archive
resists collapse to a single high-score region; the effective-complexity
term is the anti-gaming guard.  (ii) **Proof firewall** — the
raw/certified split (§4) + the security taint dimension (§12.3) make the
loop *paraconsistent*: provisional, possibly-adversarial proposals live
as taint-tracked raw cells with no explosion, because validity is gated
at certification, so the loop is **safe against an adversarial proposer**.

**Open-endedness is guaranteed by Gödel (the deepest link, → §11.7.1).**
A discovery engine normally runs dry: once everything compressible at its
current strength is found, `Hardness → 0` and it stalls.  FX's engine
*cannot* run dry, for the same reason the apex ladder is unbounded
(§11.7.1): by the Chaitin-bound = Gödel-climbing identity (O-AIT
§11.9.2.1), every consistency strength has facts whose provable-`K`
ceiling exceeds the current degree, and climbing one reflection degree
(adding `Con(current)` as a ProfileExtension, §11.7.1) strictly raises
that ceiling, unlocking a fresh supply of high-`Hardness` facts.  Because
no degree proves its own `Con`, there is *always* a strictly-harder
frontier — engine open-endedness and apex unboundedness are one theorem.

**Why no prior system does this** (DreamCoder / FunSearch / AlphaProof):
each has a proposer + a scorer, but none has all four FX ingredients —
(a) a *canonical* novelty count (univalence-dedup, §11.8.13; DreamCoder's
library is deduped only up to ad-hoc syntactic equality), (b) a
zero-axiom verification firewall that is adversarial-proposer-safe
(O-FIREWALL; FunSearch trusts a sandbox, AlphaProof trusts Lean's full
kernel), (c) a *principled* abstraction loop (`H₁` = the abstractions,
not a heuristic compressor), and (d) a *provable* open-endedness
guarantee (the reflection ladder).  FX is the first setting where all
four coexist.

**Honest limits (manifesto discipline).**  The `A`-factor is the genuine
Chaitin residue — approximable from below, never optimal — which is
*correct*: it measures true conceptual invention, which is uncomputable.
Dedup is only up to *found* Conv; facts equal by an unfound equivalence
are over-counted until an equivalence-search subloop (a proposer task)
closes the hole — asymptotically, not instantly.  And the Verifier is the
bottleneck exactly where `Hardness` is highest (deepest proofs = highest
`D` = costliest to certify): a real verification/novelty Pareto tension,
no free lunch.  The creative singularity stays uncomputable; the engine
converges toward it forever.  `O-ENGINE` is therefore SPECIFIABLE-NOW as
an architecture — every component is a named obligation already in this
ledger (O-HARD scorer, O-HOMOLOGY compressor, O-FIREWALL firewall, FX0
verifier §12.6, §24 proposer) — **beyond-apex**, and never on the
MILESTONE A–D path (§11.9.0 firewall).  This is the operational endgame of
§3.14 + §24 + §12.6 + the whole §11.9 program.

### 11.9.5 Wild frontier (committed research per the moonshot mandate; all MOONSHOT)

* **Holographic FX.** Trust reduces to the *boundary* (FX0 + the
  0-truncation, §12.6); the higher cells are the *bulk*.  The
  `reinhardtDirected` functor (OP2) — non-invertible, fixes the
  0-truncation, moves higher cells — is *literally* a bulk symmetry
  fixing the boundary.  The boundary-determines-bulk pattern is a
  holographic principle for proof.  (AdS/CFT cited as analogy only.)

* **The Galois 2-group of a profile.** A profile has a finite, computable
  automorphism 2-group (session duality §11.2 = a `ℤ/2`); its
  representations on the 21 dimensions = the *internal symmetries* of the
  type theory; a Tannakian reconstruction from sorts-as-fiber-functors.
  Anchor: Tannakian duality + §11.2.

* **Digital-resource physics.** The grades *are* physical resources
  (space = bits, cost = Landauer energy, clock domain §18.7 = causal
  light-cone with `sync(c)` frame-mixing constraints); a physical-grade
  profile makes FX a synthetic language for resource-bounded physical
  computation — **Hilbert's 6th via resources** rather than via geometry
  (complementing Schreiber's synthetic differential cohesion, ref 25).

* **FX0/FX1 as an interactive proof.** The powerful-untrusted-FX1 ⟶
  weak-trusted-FX0 emission (§12.6) modeled as a one-round IP/PCP;
  self-hosting (§3.15) makes FX0 a cell verifying its own verifier, whose
  Gödel-bounded fixed point is exactly the reflection-degree gap.
  Anchor: Shamir IP=PSPACE + PCP.

### 11.9.6 The frontier ledger

| ID | Entry | Status | Prior-art anchor | FX hook | pre-apex? |
|---|---|---|---|---|---|
| O-INTERNAL | internalization principle (meta) | n/a | — | whole doc | — |
| O-OBSTRUCT | 21-dim obstruction-cohomology | SPECIFIABLE (sublattice SHIPPABLE) | Zwart-Marsden 1811.06460 | §6.8, §3.14 | partial |
| O-HOMOLOGY | Squier proof-homology / Hilbert 24 | SHIPPABLE (`H₁`) | Squier 1987; Thiele 2003 | §3.4, M6/M7 | ✅ |
| O-HARD | the Hardness instrument + δ | D,B SHIPPABLE; N SPEC; A OPEN | Bennett; Gell-Mann–Lloyd; DreamCoder; Schmidhuber | §12.6, MILESTONE A | D,B ✅ |
| O-AIT | synthetic algorithmic info theory | SPECIFIABLE | Chaitin; Solomonoff | §12.6, §11.7.1, §3.3 | — |
| O-THERMO | synthetic thermodynamics | OPEN | Landauer; Bennett; Lévy | §3.3, §11.7.2, cost grade | entropy-grade ✅ |
| O-TSPACE | geometry of theory-space | OPEN | Crans/Steiner Gray; Lawvere | §3.0.7, §3.14 | — |
| OP3 | sameness-unification | OPEN | directed Yoneda/SIP; bisimulation | §3.10, §13.19 | — |
| OP4 | Laver period ↔ `reinhardtDirected` | computation SHIPPABLE; bridge OPEN | Laver; Dougherty-Jech; SR9 | §11.8.2.1, `gen_universeOmega` | period ✅ |
| OP5 | Ricci-flow proof of `O-NORM` | MOONSHOT | Ollivier; Lévy | §6, §3.4 | — |
| OP6 | MIP\*=RE undecidability locus | OPEN | JNVWY 2020 | §11.2, §3.15, §11.7.4 | — |
| OP7 | GLP discharge of `O-ORD` | SPECIFIABLE | Beklemishev; Japaridze | §11.7.1, §11.8.2 | — |
| O-FIREWALL | Goodhart-resistant agent loop | SPECIFIABLE | Schmidhuber; Lehman-Stanley | §24, §12.3, §4 | — |
| O-ENGINE | Kolmogorov-driven discovery engine | SPECIFIABLE | Schmidhuber; Lehman-Stanley; DreamCoder; FunSearch | §11.9.4, §11.7.1, §12.6 | — |

**Sequencing.**  Tier 0 (ship as real cells first, pre-apex): `O-HOMOLOGY`
`H₁`, `O-HARD` D/B, `O-OBSTRUCT` on the 3-sublattice.  Tier 1
(specifiable obligations): OP7 GLP/`O-ORD`, full `O-HARD`/`O-AIT`,
`O-FIREWALL`, and `O-ENGINE` (the capstone composing them into the
discovery loop).  Tier 2 (open research): OP3, `O-THERMO`, `O-TSPACE`, OP4
bridge, OP6.  Tier 3 (moonshot): OP5, §11.9.5.  **First brick is
doc-first** (this section); the Lean prototype is deferred and will be
chosen from Tier 0.  Per the firewall, no `O-`/`OP` here gates
MILESTONE A–D — they are the program *beyond* the apex.

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

The rejected design was a `thin` constructor on the raw layer:
`(cell : RawCell scope) →
 (hasThin : π.stratification.thin cell.dim cell) →
 RawCell scope`  (with the boundary flipped).

The flipped-boundary result would create a new raw cell of the same dim
with the boundary flipped.  This is HIT-like (an equivalence-style
constructor), and Lean's strict-positivity checker may reject it.  v2
makes this doubly moot: `RawCell` carries no boundary index at all, so
the flip cannot even be stated on the raw layer.

**Mitigation:** encode `thin` not as a ctor but as a `Prop`-valued
predicate, with the flipped variant derivable.  Loubaton 2301.11424's
left semi-model structure suggests this: thin cells are not new
generators, they are markings on existing cells.  Final rule:
`RawCell` has no thin constructor, `PolyCell` has no thin
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

### 12.6 FX0-PolyCell — first-order external certificate verifier

**Lineage.**  `kernel-metaplan.md` §"FX0 Escape Hatch" defines FX0 as
an MM0-like root certificate checker: sorts, term constructors, theorem
declarations, explicit substitution, explicit definition unfolding,
stack-machine proof checking — no dependent conversion engine, no
elaborator, no tactics, no hidden inference.  The target path is:

```text
FX1 theorem/check trace
  -> FX1 certificate emitter
  -> FX0 certificate
  -> FX0 verifier accepts
```

This subsection adapts FX0 to the PolyCell substrate.  The adaptation
is SIMPLER than the FX1-mediated path because the PolyCell certifier
(`certifyRawCellExact?` / v2 `certifyRawCellExact?`) IS already
MM0-shaped: it takes a serialized raw cell tree, applies the Generator
table as axioms, and returns accept-with-certificate or reject-with-
reason.  No lambda-Pi intermediary (FX1) is needed between the rich
layer and the root verifier — the cell tree IS the certificate.

**Dual role (the §11.9 connection).**  Beyond trust-reduction, FX0 is
load-bearing for the Internalization Program in two further ways, both
flowing from its being a *fixed* ~600-line verifier.  (1) It is the
**reference machine** for algorithmic information: `K_FX0(x)` = the size
of the smallest cell whose FX0 certificate produces `x` is a concrete
Kolmogorov measure with a *pinned* machine — the additive-constant float
that leaves classical `K` defined only "up to a constant" is exactly
what FX0 nails down (O-AIT, §11.9.2.1).  (2) It is the **trusted
verifier** in the discovery engine (O-ENGINE, §11.9.4): an untrusted
proposer emits raw cells, FX0 certifies the survivors, and the trusted
base never grows past these ~600 lines no matter how much mathematics
the engine discovers.  So FX0 is simultaneously the trust floor, the
fixed `K`-reference machine, and the engine's firewall — one artifact,
three roles.

**Why PolyCell needs its own FX0 (the trust argument).**

FX's zero-axiom discipline proves every PolyCell theorem inside Lean 4.
But Lean 4's C++ kernel (~3000 lines of `type_checker.cpp`) IS the
trusted computing base for those proofs — if the C++ has a soundness
bug, every `#assert_no_axioms`-clean theorem is worthless.  FX0-PolyCell
is the escape hatch: a SEPARATE, ~600-line first-order verifier that
checks the same certificates WITHOUT trusting Lean's kernel.  Two
independent implementations agreeing on the same inputs constitutes a
soundness argument that depends on neither implementation's host
language.

The trust stack with FX0-PolyCell:

```text
Layer 3: LEAN 4 C++ KERNEL (~3000 lines C++, current TCB)
    ↑ checks the Lean proofs of
Layer 2: LEAN 4 PROOFS (zero-axiom theorems — sound IFF Layer 3 correct)
    ↑ proves properties of
Layer 1: COMPUTABLE POLYCELL SUBSTRATE (~800 lines core logic)
    ↑ cross-checked by
Layer 0: FX0-POLYCELL VERIFIER (~600 lines C/Rust/Lean-prelude-only)
         independent implementation of Layer 1's decision procedures
```

When Layers 1 and 0 agree on all inputs, the trust reduces to:
"at least one of the two implementations is correct" — a claim about
~600–800 lines of straight-line code that any auditor can read,
independent of Lean, Coq, Agda, or any proof-assistant kernel.

#### 12.6.1 What FX0-PolyCell checks (the core judgment)

One judgment, uniform across all dimensions:

```
  verify : GeneratorTable × RuleTable × RawCell scope
           → ACCEPT(sort, dim, boundary) | REJECT(reason)
```

**Inputs:**
- `GeneratorTable` — a flat array of `{generatorId, arity, binderShifts,
  payloadSpec, childSpecs, cellSort}` records, one per admitted generator
  (currently 194 for fxProfile; grows by extension, never by code change).
- `RuleTable` — a flat array of `{ruleId, cellSort}` records, one per
  admitted generating-cell rule (currently 1: termStep).
- `RawCell scope` — the certificate to verify, serialized as a tree.

**Outputs:**
- `ACCEPT(sort, dim, boundary)` — the cell is well-formed; the verifier
  returns its sort, computed dimension, and boundary (Unit at dim 0;
  source/target raw cell pair at dim ≥ 1).
- `REJECT(reason)` — the cell is malformed, with a named reason from
  `CellCheckRejection` (unknownGenerator / badPayload / wrongChildShape /
  badBoundaryEndpoint / badVerticalBoundary / unsupportedCompH / ...).

**Properties:**
- **ZERO false positives (unconditional).**  If verify returns ACCEPT,
  the cell IS well-formed — its sort/dim/boundary match the Generator +
  Rule tables and all children recursively verify.  Proof: structural
  induction on the verification — the algorithm exactly mirrors the
  PolyCell constructor preconditions, so an accepted cell COULD
  inhabit PolyCell (the Lean proof `certifyRawCellExact?_sound`
  establishes this for the Lean implementation; the external verifier
  is a re-implementation of the same algorithm).
- **ZERO false negatives on normalized certificates.**  If the rich
  layer emits a certificate whose sorts are normalized, whose
  definitional equalities are witnessed by explicit dim-1 conversion
  cells, and whose boundary endpoints are syntactically equal (not
  merely definitionally equal), then verify returns ACCEPT.
  The ONLY source of false negatives is a certificate where the producer
  forgot to normalize or forgot to carry a witness — the verifier
  itself never rejects a valid fully-explicit certificate.

#### 12.6.2 The verification algorithm

```text
verify(cell, scope, genTable, ruleTable) :=
  match cell with

  | termBase(mkGen generator payload children) =>
      -- Step 1: generator lookup
      entry := genTable[generator]
      if entry = none: REJECT(unknownGenerator)

      -- Step 2: payload check
      if not payloadValid(entry.payloadSpec, scope, payload):
        REJECT(badPayload)

      -- Step 3: child spine recursion
      if children.length ≠ entry.arity: REJECT(wrongArity)
      for (child_i, spec_i) in zip(children, entry.childSpecs):
        childScope := scope + spec_i.scopeShift
        result_i := verify(termBase(child_i), childScope, genTable, ruleTable)
        if result_i = REJECT(r): REJECT(r)          -- propagate
        if result_i.sort ≠ spec_i.cellSort: REJECT(wrongChildShape)
        if result_i.dim ≠ spec_i.cellDimension: REJECT(wrongChildShape)

      return ACCEPT(entry.cellSort, 0, ())

  | generatingCell(ruleId, source, target) =>
      -- Step 1: rule lookup
      ruleEntry := ruleTable[ruleId]
      if ruleEntry = none: REJECT(unknownGenerator)

      -- Step 2: verify endpoints
      sourceResult := verify(source, scope, genTable, ruleTable)
      if sourceResult = REJECT(r): REJECT(badBoundaryEndpoint)
      targetResult := verify(target, scope, genTable, ruleTable)
      if targetResult = REJECT(r): REJECT(badBoundaryEndpoint)

      -- Step 3: endpoint reconciliation (value-level dim equality)
      if sourceResult.dim ≠ targetResult.dim: REJECT(badBoundaryEndpoint)
      if sourceResult.sort ≠ ruleEntry.cellSort: REJECT(badBoundaryEndpoint)
      if targetResult.sort ≠ ruleEntry.cellSort: REJECT(badBoundaryEndpoint)

      return ACCEPT(ruleEntry.cellSort, sourceResult.dim + 1, (source, target))

  | verticalComposite(first, second) =>
      firstResult := verify(first, scope, genTable, ruleTable)
      if firstResult = REJECT(r): REJECT(r)
      secondResult := verify(second, scope, genTable, ruleTable)
      if secondResult = REJECT(r): REJECT(r)

      -- same sort, same dim
      if firstResult.sort ≠ secondResult.sort: REJECT(badVerticalBoundary)
      if firstResult.dim ≠ secondResult.dim: REJECT(badVerticalBoundary)
      if firstResult.dim = 0: REJECT(badVerticalBoundary)  -- composites need dim ≥ 1

      -- shared middle: first's target = second's source (STRUCTURAL equality)
      if not structuralEqual(firstResult.boundary.target,
                             secondResult.boundary.source):
        REJECT(badVerticalBoundary)

      return ACCEPT(firstResult.sort, firstResult.dim,
                    (firstResult.boundary.source, secondResult.boundary.target))

  | horizontalComposite(left, right) =>
      REJECT(unsupportedCompH)   -- until Gray boundary semantics land

  | identityCell(base) =>
      baseResult := verify(base, scope, genTable, ruleTable)
      if baseResult = REJECT(r): REJECT(r)
      return ACCEPT(baseResult.sort, baseResult.dim + 1, (base, base))
```

**Structural equality** (`structuralEqual`) is a recursive comparison
of two `RawCell` trees: same constructor tag at each node, same
payload values, same children recursively.  No reduction, no
unification, no delta-unfolding.  ~50 lines of code.

**Payload validation** (`payloadValid`) dispatches on the
`payloadSpec`:
- `finScope` (variable): payload is a natural number < scope.
- `nat` (universe level): payload is any natural number (or bounded
  by a profile limit).
- `unit`: payload = 0.

~15 lines of code.

**Total verification algorithm: ~120 lines of pseudocode.**  The rest
of the ~600-line implementation is serialization parsing + Generator/
Rule table loading + structural equality + error formatting.

#### 12.6.3 Why this handles dim-3 and dim-4 cells correctly

A dim-3 cd_lemma filler is a `generatingCell` whose source and target
are dim-2 cells (themselves `generatingCell`s or `verticalComposite`s
of dim-1 steps).  A dim-4 Squier coherence cell is a
`generatingCell` / `verticalComposite` / `identityCell` over dim-3
cells.  The verification algorithm handles ALL of these uniformly
because:

1. **The algorithm is dimension-uniform.**  The `match cell` dispatch
   does NOT case-split on dimension.  A dim-4 cell hits the same
   `generatingCell` / `verticalComposite` / `identityCell` branches
   as a dim-1 cell — the only difference is the recursion depth.

2. **Boundary matching recurses.**  At dim 3, checking
   `firstResult.boundary.target = secondResult.boundary.source`
   compares two dim-2 cells by structural equality.  At dim 4 it
   compares dim-3 cells.  `structuralEqual` handles all dimensions
   because `RawCell` is un-indexed by dimension — it's the same
   type at every dimension, and structural comparison is just
   recursive tree equality.

3. **∞-topos / Gray / cubical cells are just deeper trees.**  A
   cubical transport cell at dim 2 is a `generatingCell` with a
   transport ruleId and dim-1 endpoint cells.  An ∞-topos descent
   filler at dim 3 is a `verticalComposite` of transport cells.
   The verifier doesn't know what "transport" or "descent" MEAN —
   it only checks that the Generator table admits the ruleId and
   the endpoint sorts/dims/scopes match.  The SEMANTICS are in the
   Generator + Rule tables (the "axioms"); the verifier is
   domain-agnostic.

**Complexity per cell node:** O(1) table lookups + O(1) field
comparisons + O(children) recursive calls.  Total for a certificate
with N nodes: O(N × M) where M is the maximum structural-equality
comparison size (bounded by the largest boundary endpoint tree).
For FX kernel terms at dim ≤ 4 with bounded fan-out per the Generator
arity table, this is effectively linear in certificate size.

#### 12.6.4 The certificate format (serialization)

The binary certificate format mirrors MM0's `.mmb`:

```text
HEADER:
  magic : u32 = 0x46583043  -- "FX0C"
  version : u32 = 1
  numSorts : u32             -- CellSort enum size (currently 7)
  numGenerators : u32        -- Generator table size (currently 194)
  numRules : u32             -- Rule table size (currently 1)

GENERATOR TABLE:
  for each generator:
    generatorId : u32
    arity : u32
    cellSort : u8
    payloadSpec : u8          -- 0=finScope, 1=nat, 2=unit
    binderShifts : u32[]      -- length = arity
    childSorts : u8[]         -- length = arity
    childDims : u32[]         -- length = arity

RULE TABLE:
  for each rule:
    ruleId : u32
    cellSort : u8

CELL TREE (prefix-encoded):
  tag : u8
    0 = termBase(mkGen)
      generatorId : u32
      payload : u64           -- Nat value (Fin for var, level for universe, 0 for unit)
      children follow inline (arity known from generator table)
    1 = generatingCell
      ruleId : u32
      source subtree follows
      target subtree follows
    2 = verticalComposite
      first subtree follows
      second subtree follows
    3 = horizontalComposite
      left subtree follows
      right subtree follows
    4 = identityCell
      base subtree follows
  scope : u32 (at each termBase node)
```

The format is self-contained: the Generator + Rule tables are IN the
certificate file so the verifier needs no external state.  Different
profiles emit different tables; the verifier is profile-agnostic.

#### 12.6.5 Lean implementation under host-minimal policy

The FX0-PolyCell verifier is implemented TWICE:

1. **In Lean 4 under the FX1 host-minimal policy**
   (`kernel-metaplan.md` §"Lean Host Policy"):
   `prelude` + `import Init.Prelude` only.  No `import Lean`, no
   `import Std`, no `Classical`, no `Quot`, no `propext`, no
   `noncomputable`, no `unsafe`, no `partial`, no `opaque`, no
   `@[extern]`, no `@[implemented_by]`, no tactics, no `omega`,
   no `grind`.  Only structurally recursive `def`, explicit pattern
   matching, `Nat`, `Bool`, `Option`, `List`, `Prod`, `Sum`, `Unit`,
   `Empty`, `Eq`, `rfl`, and term-mode proofs.

   This Lean implementation IS `certifyRawCellExact?` (the v2 certifier
   from the PolyCell substrate), constrained to the host-minimal import
   set.  Its soundness theorem `certifyRawCellExact?_sound` is proved
   in Lean 4 under the same constraints.  The Lean proofs give
   confidence; they are NOT the trust base.

2. **In C, Rust, or eventually FX itself** — an independent
   re-implementation of the same ~120-line algorithm, sharing no code
   with the Lean version.  The two implementations are cross-checked:
   run both on the same certificate files and compare outputs.
   Agreement on a large corpus (the full PolyCell fixture set +
   the rich layer's emitted certificates) constitutes the soundness
   argument that does not depend on either host language's kernel.

The Lean implementation is FIRST (it already exists as the v2
certifier).  The external implementation is SECOND (the "sound
metatheory implementation later" that the user's constraint requires).
Until the external implementation ships, the trust base is Lean 4's
kernel + the `#assert_no_axioms` discipline.  After it ships, the
trust base shrinks to "at least one of two ~600-line programs is
correct."

#### 12.6.6 Certificate emission from the rich layer

The bridge from the existing rich LeanFX2 layer
(`Term context type raw` / `Step` / `Conv` / `cd_lemma`) into
FX0-PolyCell certificates:

```text
Rich LeanFX2 judgment
  -> encodeCell : Term/Step/Conv -> RawCell  (translation)
  -> certifyRawCellExact? on the encoded cell   (verification)
  -> serialize the accepted certificate          (emission)
  -> FX0-PolyCell verifier accepts              (cross-check)
```

The load-bearing theorem (mirroring `kernel-metaplan.md`'s
`encode_term_sound`):

```lean
theorem encodeCellSound :
    LeanFX2.Term context typeExpression rawExpression →
    certifyRawCellExact? scope (encodeCell rawExpression) = Except.ok certificate
```

This is added incrementally per `kernel-metaplan.md`'s staged policy:

1. Variables — `Term.var` → `termBase (mkGen gen_var ...)`.
2. Unit / Pi / Lambda / Application — core term formers.
3. Universe codes — the type-code family.
4. Identity / cubical fragment — dim-1 cells.
5. Steps — dim-1 generating cells via the Rule table.
6. cd_lemma fillers — dim-2 cells.
7. Squier coherence — dim-3+ cells.
8. Rich features (modal, graded, session, effect, codata) as declared
   Generator entries with explicit typing/computation certificates.

Each step is gated by `#assert_no_axioms` on the soundness theorem.
No rich feature is counted as FX0-root until its `encodeCellSound`
theorem is shipped AND the external FX0-PolyCell verifier accepts the
emitted certificate.

#### 12.6.7 First milestone

Mirroring `kernel-metaplan.md`'s FX0 milestone:

```text
Rich-layer certified variable (Term.var) at scope 4
  -> encodeCell emits RawCell (termBase (mkGen gen_var (Fin.mk 0 _) childNil))
  -> Lean certifyRawCellExact? accepts
  -> serialized to .fx0c binary
  -> external FX0-PolyCell verifier accepts
```

FX0-PolyCell is not required before the v2 substrate work starts.
It IS required before claiming minimal final TCB for PolyCell — the
same discipline `kernel-metaplan.md` applies to FX0 vs FX1.

#### 12.6.8 Root status labels for PolyCell modules

Every PolyCell module gets one of these labels (extending
`kernel-metaplan.md`'s labels):

```text
FX0-PolyCell-root
  Part of the minimal cell verifier, covered by structural soundness
  AND cross-checked by the external verifier.

PolyCell-substrate
  The computable certifier/fold/DecEq layer in Lean.
  Covered by Lean proofs; eventually cross-checked by FX0-PolyCell.

FX-rich
  Existing expressive LeanFX2 layer (Term/Step/Conv/HoTT/cubical/...).

Bridge
  Translation + soundness connection between the rich layer and
  PolyCell substrate (encodeCell / encodeCellSound).

Scaffold
  Syntax, docs, or interfaces without load-bearing theorem.

Deferred
  Explicitly not claimed.
```

No PolyCell feature is counted as root-trusted unless it is
`FX0-PolyCell-root`.

#### 12.6.9 What FX0-PolyCell does NOT do

- **No conversion engine.**  Definitional equality is checked by
  structural comparison of raw cell trees.  If two cells are
  definitionally equal but syntactically different, the certificate
  must carry an explicit dim-1 conversion cell witnessing the equality.
  The verifier checks the witness; it never searches for one.

- **No elaboration.**  The verifier checks fully explicit certificates.
  Implicit arguments, type inference, tactic-generated proof terms —
  all of that is the rich layer's job.  The verifier sees only the
  output.

- **No reduction.**  No WHNF, no delta-unfolding, no NbE.  Reduction
  happens in the certificate producer.  The verifier checks that the
  produced witnesses are well-formed, not that they are the RIGHT
  witnesses (that's what the Lean soundness proofs establish).

- **No Generator-table generation.**  The verifier CONSUMES tables
  emitted by the rich layer; it does not generate or validate them.
  Table correctness (that the Generator entries faithfully represent
  the intended type theory) is established by the Lean proofs, not
  by the verifier.

- **No profile-extension logic.**  The verifier is profile-agnostic —
  it checks cells against whatever tables it receives.  The admission
  contract (§3.14 `extendProfile_preserves_admissible`) is a Layer 2
  Lean theorem, not a Layer 0 verifier feature.

These are deliberate: every omission SHRINKS the TCB.  The verifier's
only job is to answer "does this tree match these tables?" — a
purely structural, dimension-uniform, first-order check.

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

### Structural reflection + the categorical large-cardinal frontier (§11.8.2 apex)

SR1. Joan Bagaria, "Large cardinals as principles of structural
     reflection", Bulletin of Symbolic Logic 29(1) (2023).  THE
     program: large cardinals = degrees of structural reflection
     (isomorphism-invariant, category-theoretic).  Canonical citation
     for the §11.8.2 reflection-degree ladder.
SR2. Joan Bagaria, "C^(n)-cardinals", Archive for Mathematical Logic 51
     (2012).  C^(n)-extendible / C^(n)-degrees; corrects the `vopenka`
     and `extendible` calibration (Vopěnka = SR for all classes, NOT
     near-Reinhardt).
SR3. Jiří Adámek, Jiří Rosický, "Locally Presentable and Accessible
     Categories", LMS Lecture Note Series 189, CUP 1994.  Vopěnka's
     principle as category theory: "Ord ↛ Graph fully faithfully" /
     colimit-closed full subcategories of locally presentable
     categories are coreflective.
SR4. Joan Bagaria, Carles Casacuberta, A.R.D. Mathias, Jiří Rosický,
     "Definable orthogonality classes in accessible categories are
     small", J. Eur. Math. Soc. 17 (2015), arXiv:1101.2792.  Cardinal
     degrees ⟺ smallness of definable orthogonality classes
     (supercompact ≈ Σ₂, extendible ≈ unrestricted).
SR5. Joan Bagaria, Philipp Lücke, "Huge Reflection", arXiv:2106.01462
     (2021).  Exact Structural Reflection (ESR) extends structural
     reflection PAST Vopěnka, through huge, to the rank-into-rank
     region; sequential ESR over Π₁ classes ⟸ I1.  THE bridge that
     makes `kunenI0` a categorically-stated reflection degree, FX's
     committed apex.
SR6. Juan P. Aguilera, Joan Bagaria, Philipp Lücke, "Large cardinals,
     structural reflection, and the HOD Conjecture", arXiv:2411.11568
     (2024).  Exacting + ultraexacting cardinals: SR-defined,
     ZFC-consistent relative to I0, break the linear large-cardinal
     picture (`Con(ZFC + proper class of I0)` from below a measurable),
     bear on HOD / Ultimate-L.  FX's `exacting`/`ultraexacting`
     frontier; never mechanized anywhere.
SR7. Ali Sadegh Daghighi, Mohammad Golshani, Joel David Hamkins, Emil
     Jeřábek, "The foundation axiom and elementary self-embeddings of
     the universe", arXiv:1311.0814.  Kunen's inconsistency uses
     Foundation ESSENTIALLY; non-well-founded universes admit nontrivial
     elementary self-embeddings.  Why FX's non-well-founded substrate
     evades the Kunen idiom (§11.8.2.1).
SR8. Gabriel Goldberg, "The uniqueness of elementary embeddings",
     arXiv:2103.13961 / JSL.  Elementary embeddings into a fixed target
     agree on the ordinals and are unique above the least extendible —
     rigidity = univalence-compatibility of high reflection.
SR9. Richard Laver, "The left distributive law and the freeness of an
     algebra of elementary embeddings", Advances in Math 91 (1992);
     + "A free two-generated left distributive algebra of elementary
     embeddings", arXiv:2508.02244 (2025).  The (computable) Laver-Steel
     LD-algebra of elementary self-maps — the internalizable algebraic
     trace of the `reinhardtDirected` frontier.
SR10. Farmer Schlutzenberg (with Gabriel Goldberg), "On the consistency
     of ZF with an elementary embedding of V_{λ+2} into V_{λ+2}",
     J. Math. Logic (2024).  ZF-PROVEN consistency rel I0 of the
     above-Kunen-wall `V_{λ+2}` embedding; the choiceless ceiling tag
     `schlutzenbergVLambdaPlus2` (open-frontier, not asserted).
SR11. Michael Rathjen, "The art of ordinal analysis", Proc. ICM 2006;
     "Proof Theory of Reflection", APAL 68 (1994); "An ordinal
     analysis of stability", AML 44 (2005).  The ordinal-notation /
     well-ordering-proof substrate that would establish each ladder
     rung's strength — the content of OBLIGATION O-ORD (§11.8.0,
     §11.8.2), currently absent from FX.

### Definitional univalence + synthetic condensed mathematics (§11.8.14 research track)

DU1. Thorsten Altenkirch, Ambrus Kaposi, Michael Shulman, Elif
     Üsküplü, *Higher Observational Type Theory* (in preparation;
     TYPES 2025 "From parametricity to identity types"; nLab
     `higher+observational+type+theory`).  Identity types defined by
     recursion on type structure; `Id 𝒰 A B ≡ A ≃ B` — univalence,
     funext, propext DEFINITIONAL.  Full HOTT normalization OPEN as
     of 2026 (DU3).
DU2. Thorsten Altenkirch, Yorgo Chamoun, Ambrus Kaposi, Michael
     Shulman, *Internal Parametricity, Without an Interval*, POPL 8
     (2024) 2340-2369, `arXiv:2307.06448`, DOI 10.1145/3632920.  The
     "baby HOTT" substrate: presheaf model + canonicity proof.  IS
     FX's `gen_param` on-ramp (§3.16.8).
DU3. Michael Shulman, *Towards an Implementation of Higher
     Observational Type Theory* (running-hott, NYU Abu Dhabi 2024) +
     the **Narya** proof assistant (parametric + higher observational
     TT, runnable).  NbE + higher-dimensional normalization algorithm
     sketched; full proof pending.
DU4. Nicolas Tabareau, Éric Tanter, Matthieu Sozeau, *The Marriage of
     Univalence and Parametricity*, JACM 68(1) (2021) + *Equivalences
     for Free!*, ICFP 2018.  Coq-implemented automatic computational
     transport across equivalences — combines FX's committed
     univalence + internal parametricity; the reachable-NOW
     transport-tax win.
DU5. Martín Escardó, *Synthetic Topology of Data Types and Classical
     Spaces*, ENTCS 87 (2004); *Infinite Sets that Admit Fast
     Exhaustive Search*, LICS 2007.  Sierpiński object, the `dProp` /
     Σ split, searchable (compact) types ⇒ decidable quantification
     over `2^ℕ`.  Reachable-NOW.
DU6. Dustin Clausen, Peter Scholze, *Condensed Mathematics* (lecture
     notes, Bonn 2019) + *Analytic Geometry* (2020).  Condensed sets =
     sheaves on profinite sets; condensed-abelian groups form an
     abelian category; the cohesive-topos substrate for the §11.8.14
     condensed focus.
DU7. Clark Barwick, Peter Haine, *Pyknotic Objects, I. Basic Notions*
     (2019).  The universe-bounded variant of condensed (size
     bookkeeping); the κ-condensed universe parameter (ties to
     `LevelExpr`).
DU8. Johan Commelin et al., *Liquid Tensor Experiment* (Lean/mathlib,
     2020-2022).  Machine-verified the hardest theorem of the liquid
     theory — condensed mathematics' existing successful encounter
     with a proof assistant.
DU9. Felix Cherubini, Thierry Coquand, Matthias Hutzler, *A Foundation
     for Synthetic Algebraic Geometry* (2024) — the methodological
     template for synthetic internal-language axiomatization; the
     emerging "synthetic Stone duality / synthetic condensed" line
     (DU4 obligation) follows this pattern.  Synthetic condensed TT is
     UNBUILT; this is the nearest established anchor.

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
32a. Evan Cavallo, Robert Harper, "Internal Parametricity for Cubical
    Type Theory", CSL 2020 / LMCS 17(4) 2021.  Unifies the cubical
    PATH dimension with the parametricity BRIDGE dimension in one
    setting — the substrate for O-CUBE-PARAM (§11.8.0, §11.8.6).
32b. Loïc Pujet, Nicolas Tabareau, "Observational Equality: Now For
    Good", POPL 2022 (PACMPL 6); "Impredicative Observational
    Equality", POPL 2023.  Observational type theory (TTobs):
    definitional function extensionality + decidable conversion with
    NO interval — the pragmatic decidable-funext route flagged in
    §11.8.3's equality-zoo discipline as the absent middle between the
    cubical default and the open HOTT track.

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

### Open-ended discovery + library learning + compression progress (§11.9.4 O-ENGINE)

OE1. Jürgen Schmidhuber, *Formal Theory of Creativity, Fun, and
     Intrinsic Motivation (1990–2010)*, IEEE Trans. Autonomous Mental
     Development 2(3) (2010); *PowerPlay: Training an Increasingly
     General Problem Solver by Continually Searching for the Simplest
     Still Unsolvable Problem*, Frontiers in Psychology 4 (2013),
     `arXiv:1112.5309`.  Compression progress (`dA/dt`) as the
     intrinsic-curiosity / open-ended-search objective — the §11.9.4
     driver.
OE2. Joel Lehman, Kenneth O. Stanley, *Abandoning Objectives: Evolution
     Through the Search for Novelty Alone*, Evolutionary Computation
     19(2) (2011); *Why Greatness Cannot Be Planned* (Springer 2015);
     Jean-Baptiste Mouret, Jeff Clune, *Illuminating search spaces by
     mapping elites* (MAP-Elites), `arXiv:1504.04909` (2015).  Novelty
     search + quality-diversity — the §11.9.4 selector that resists
     Goodhart mode-collapse.
OE3. Kevin Ellis, Catherine Wong, Maxwell Nye, Mathias Sablé-Meyer,
     Lucas Morales, Luke Hewitt, Luc Cary, Armando Solar-Lezama, Joshua
     B. Tenenbaum, *DreamCoder: Bootstrapping Inductive Program
     Synthesis with Wake-Sleep Library Learning*, PLDI 2021,
     `arXiv:2006.08381`.  MDL library learning = the §11.9.4
     homology-guided compressor's abstraction step (the `A` factor of
     `Hardness`, §11.9.1.3).
OE4. Bernardino Romera-Paredes, Mohammadamin Barekatain, Alexander
     Novikov, et al., *Mathematical discoveries from program search
     with large language models* (FunSearch), Nature 625 (2024),
     DOI 10.1038/s41586-023-06924-6.  Untrusted-LLM-proposer +
     trusted-evaluator loop — the §11.9.4 architecture WITHOUT FX's
     canonical dedup / zero-axiom verification firewall / open-endedness
     guarantee.
OE5. Google DeepMind, *AlphaProof* + *AlphaGeometry 2* (2024,
     IMO-silver-medal system; technical announcement).  LLM proposer +
     formal (Lean) verifier at competition scale — the closest deployed
     precedent; lacks the certified `Hardness` metric (§11.9.1.3) and
     the reflection-ladder open-endedness (§11.7.1) of O-ENGINE.

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

The ~270K gross / ~230K net LoC budget is realistic per the per-axis
Lean LoC estimates (§9).  The 2–4 year timeline is realistic per the
per-phase deliverable breakdown (§10).  The risk register in §12 names
specific failure modes with mitigations.

**The expand-at-whim multiplier:** each future FX extension
(probability, measure, SDG, reversible compute, quantum,
distributed, …) is a Tier-2 inhabitant of the Tier-0 obligation
type — ~2K LoC per extension after Tier 0 is in place.  Without
Tier 0, each extension costs ~10-15K LoC of bespoke kernel
surgery.  The Tier-0 investment of ~12K LoC pays back after ~3
extensions; the §3.15 catalog already lists ~15 in scope.

**This is the committed direction.**  The PolyCell substrate
(RawTerm / RawCell / PolyCell + 194-`Generator` table + certifier +
Allais fold) is the canonical kernel surface, and the per-ctor cascade
is structurally dead.  The target is the full maximal-power apex
(§11.8): 2LTT 4-mode universes, the categorical structural-reflection
ladder to the `kunenI0` ESR apex, K-free dependent elimination, HIIRT,
HITs/QIITs, multi-clock guarded TT, internal parametricity, first-class
rewriting, full CCHM cubical, typed 21-dim integration, MTT + cohesion
+ differential cohesion + algebraic effects + the synthetic-math layer
— every component sound by published theory, every decider internal +
verified + complexity-bounded, the whole under zero-axiom +
closed-system discipline.  The critical path runs Phase Z₀ (universe-
level normalization → universe payload → typed universe rule) → Z₁
typed core → MILESTONE A (decidable typed checking + typed Conv), with
the Tier-0 meta-framework + remaining substrate axes (§3) in parallel.

Either way, the literature is captured in
`reference_loubaton_papers.md` and
`reference_polyterm_lit_scan_2026_05_24.md` memory entries; the
design rationale is preserved here for future reference.
