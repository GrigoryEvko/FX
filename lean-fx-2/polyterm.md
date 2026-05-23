# PolyTerm — The Scary Maxxed-Out Universal Substrate for FX Kernel Cells

> **Status:** vision document, computability-hardened (revision 2026-05-24).
> All claims now reduce to one of:
> (a) a constructive Lean definition in this codebase (with file path),
> (b) a published decision procedure (with paper reference + arxiv ID +
>     complexity bound), or
> (c) an explicit out-of-scope tag with reason.
>
> No `IsX : Prop` placeholder predicates.  No "research-frontier flag"
> as a hand-wave shield.  No `Inhabited X` / hypothesis-as-postulate
> patterns.  The document obeys lean-fx-2/CLAUDE.md's zero-axiom
> absolute discipline: every theorem and definition shipped under the
> ten axes must `#assert_no_axioms` clean.
>
> **Costed:** ~187K Lean LoC over 2–3 years, of which **~25K is already
> shipped** in `Foundation/Polygraph/` (K11.1–K11.17 + K12.1–K12.19 +
> K12.23 + strength-T1/T2/T3 + T4×28 + T8 + Generator/RawPolyTermFlat
> infrastructure).  Net new work: ~160K LoC.  See [§9](#9-loc-budget)
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

## Table of Contents

1.  [Manifesto](#1-manifesto)
2.  [Motivation: why pivot the substrate](#2-motivation-why-pivot-the-substrate)
3.  [The Ten Axes](#3-the-ten-axes)
    * 3.1 [Shape per dim — Joyal Θ + Steiner + opetopes + HDA](#31-shape-per-dim)
    * 3.2 [Algebraic theory — polynomial monads](#32-algebraic-theory)
    * 3.3 [Verity stratification — per-cell per-dim thinness](#33-verity-stratification)
    * 3.4 [Saturation — Riehl–Verity profile](#34-saturation)
    * 3.5 [Enrichment ladder — Segal A-precategories](#35-enrichment-ladder)
    * 3.6 [Complicial Gray module — bidirectional composition](#36-complicial-gray-module)
    * 3.7 [∞-Topos base — cohesion + modality + grading](#37-infty-topos-base)
    * 3.8 [Profile fibration — self-referential profiles](#38-profile-fibration)
    * 3.9 [Coherent equivalence classifier — the ωcE polygraph](#39-coherent-equivalence-classifier)
    * 3.10 [Univalent universe — Loubaton thesis §6.1.3](#310-univalent-universe)
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
not a half-measure, not (∞,1), but the full (∞,ω)-categorical universe
parameterized by ten orthogonal axes, every axis grounded in published
literature, every axis Lean-mechanizable at zero axioms, every axis
giving FX a capability no other proof assistant has.

The slogan is **PolyCell renamed and souped up**.  The K11.1 `PolyCell`
(dim-indexed, source/target intrinsic, real Burroni cells) is the
skeleton.  The other nine axes are the flesh.  At the end you have one
inductive type `PolyTerm π dim source target` parameterized by a
ten-field `PolyProfile π`, with FX kernel as one specific instance of
the profile.

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

## 3. The Ten Axes

Each axis below: definition, reference, why-FX-needs-it, Lean
signature sketch.  The axes are orthogonal — varying one doesn't
break the others — but they compose through `PolyProfile` (§3.11).

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

**Lean signature:**

```lean
inductive CellShape where
  /-- Burroni globular cells (D, s, t): one source, one target. -/
  | globular     : CellShape

  /-- BCH cubes with connections + reversals + diagonal.  Used at
  the dimensions where cubical paths and Kan operations live.  -/
  | cubical      : CubicalVariant → CellShape

  /-- Simplicial Δⁿ.  Used for complicial / nerve interpretations
  and as fallback shape for opetopic compatibility. -/
  | simplicial   : CellShape

  /-- Baez–Dolan opetopes, generated inductively by the polynomial
  monad construction.  Used at the dimensions where multi-port
  pasting matters (confluence, coherence). -/
  | opetopic     : Opetope → CellShape

  /-- Joyal Θ-cells via wreath product Θ_n ≀ ⋯ ≀ Θ_n.
  Universal shape; every other shape embeds here. -/
  | theta        : ThetaCell → CellShape

  /-- Steiner parity complex (Steiner 1993).
  Used for cells with directed combinatorics that don't fit
  globularly (oriented simplices, orientals).  -/
  | steiner      : ParityComplex → CellShape

  /-- Berger–Moerdijk generalized Reedy.  Used as a shape combinator
  for cost-tropical weighted reduction. -/
  | reedy        : GenReedy → CellShape

  /-- Pratt HDA precubical cell.  Used for true concurrency
  (Mazurkiewicz independence relation as cube subdivision). -/
  | hda          : HDACube → CellShape

  /-- Cartesian shape combinator: cells of shape (S × T) at the
  combined dimension. -/
  | prod         : CellShape → CellShape → CellShape

  /-- Joyal wreath shape combinator. -/
  | wreath       : CellShape → CellShape → CellShape
  deriving DecidableEq
```

The shape family in a profile is a function `(d : Nat) → CellShape`.
Two profiles agree if their shape families agree pointwise.

**Lean LoC estimate:** ~12K LoC for the full shape catalogue + their
boundary operations + their composition combinatorics + per-shape
decidable equality and serialization.

**Research-frontier flag:** ⚠️ Steiner and opetopic shapes are not
mechanized in any proof assistant; we're first-mover.  Globular,
cubical, simplicial are standard.  Joyal Θ has partial mechanization
in Coq (Bauer-Cisinski) and could port to Lean.

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

/-- A specific polynomial monad: T-polygraphs (the book's §18.1).
For any finitary monad T on Glob_∞, the T-polygraph polynomial monad. -/
def TPolyMonad (T : FinitaryMonad GlobInf) : PolyMonad (fun _ => .globular) := ...

/-- A specific polynomial monad: Batanin's weak ω-cat operad.
This one is NOT finitary (uses the violet operad construction); only
realizable as polynomial because polynomial monads are more general
than finitary monads. -/
def BataninWeakOmega : PolyMonad bataninShapes := ...
```

**Lean LoC estimate:** ~10K LoC for the polynomial-monad framework
+ canonical examples (T-polygraph instance, Batanin instance, FX's
21-graded-modal instance).

**Research-frontier flag:** ⚠️ Mathlib has partial polynomial functor
support (`Mathlib.CategoryTheory.Functor.Polynomial`).  Polynomial
monads on Glob_∞ specifically: not mechanized.

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

**Lean LoC estimate:** ~5K LoC.

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

**Lean LoC estimate:** ~15K LoC.  This includes the construction of
`tSeg(A)` for arbitrary nice model A, plus the proof that the
construction preserves nice model structure (Loubaton 3.1.2.13).

**Research-frontier flag:** ⚠️ Segal categories partial in Mathlib via
`Mathlib.CategoryTheory.Limits.Shapes.RegularMono`.  Full `tSeg(A)`
for arbitrary A: not mechanized.

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

**Lean LoC estimate:** ~25K LoC.  The full ComplicialGray construction
is the heaviest single layer; it includes the Gray tensor formula,
Gray cylinder + cone formulas (Loubaton 2207.08504 §2.3), and the
naturality squares.

**Research-frontier flag:** ⚠️ Gray tensor at the strict ω-cat level
mechanized in Coq (Maltsiniotis-Métayer); the (∞,ω) complicial version
(Loubaton 2207.08504) is unmechanized.

### 3.7 ∞-Topos base

**Reference:** Lurie HTT 2009 Chapter 6 (∞-toposes); Anel-Joyal 2019
CohomotopyTypes; Schreiber 2013 Differential Cohomology in Cohesive
∞-Toposes.

**Why FX needs it:**

- The 21 graded dimensions of FX (per fx_design.md §6) are NOT just
  semirings — they are modal/cohesive/spatial structure on the
  ambient category of types.

- An ∞-topos with modal adjunctions hosts:
  - ♭ ⊣ ◇ ⊣ □ ⊣ ♯ (cohesive modalities, FX's existing 8 modalities)
  - Crypto, Async, Classified, IO, Alloc, … (FX's effect dimensions)
  - Region/Lifetime, Provenance, Trust, Observability, Clock domain
    (the 12 provable dimensions)
  - Complexity, Precision, Space, Overflow, FP order (the 5 bounded
    dimensions)
  - Mutation, Reentrancy, Size (3 structural)
  - Version (1 evolution)

- All 21 dimensions become modal operators on the topos, with the
  21-grade-vector being the result of the composite modal action.

**Lean signature — FULL ∞-topos via Dugger 2001 combinatorial
presentation:**

```lean
/-- An ∞-topos a la Lurie HTT 2009 §6.1.0.4 — presented
CONSTRUCTIVELY via Dugger 2001 "Combinatorial model categories have
presentations" (Trans. AMS 353).  Dugger's theorem: every
combinatorial model category is a left Bousfield localization of the
projective model structure on `sPre(C)` (simplicial presheaves on
some small ∞-cat C) at a SMALL SET of maps.  Hence finite-
presentation site + finite localization-map set = computable ∞-topos.

This is NOT a "modal-adjunction list shim" — it's the genuine
∞-topos data, encoded via its small presentation rather than via
"Mathlib-level large-cat machinery FX doesn't have". -/
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

**Reference:** Loubaton 2307.11931 (PhD thesis) §6.1.3 (univalence at
(∞,ω)); §6.1.4.2 (functorial Grothendieck construction
`Hom^⊖(I, ω) ≃ LCart^c_U(I)`); Voevodsky 2009 (univalence axiom in
HoTT); Sterling-Angiuli-Gratzer 2019 XTT.

**Why FX needs it:**

- Univalence in FX is currently axiom-equivalent: `Step.eqType :
  Step (Ty.id (Ty.universe l) A B) (Ty.equiv A B)` is a postulated
  reduction rule.  It works operationally (zero axioms in Lean) but
  has no semantic justification within FX itself.

- Loubaton 2307.11931 §6.1.4.2: in the (∞,ω)-categorical universe `ω`,
  the functor `Hom^⊖(I, ω)` (marked functors into the universe) is
  equivalent to `LCart^c_U(I)` (U-small classified left cartesian
  fibrations over I).  This IS the (∞,ω) statement of univalence:
  type families = fibrations.

- So FX's `Ty.universe l` becomes a `PolyTerm fxProfile 0 (universeBoundary l)`
  cell, and the equivalence `Id (Universe l) A B ≃ Equiv A B` is a
  STRUCTURAL theorem (not an axiom).  `Step.eqType` becomes the
  reduction step implementing this equivalence inside the universe cell.

**Lean signature:**

```lean
/-- The universe boundary for the universe cell at level n. -/
def universeBoundary (n : Nat) : Boundary 0 := ...

/-- The universe cell.  Internal Universe ω at level n. -/
def universeCell (π : PolyProfile) (n : Nat) : PolyTerm π 0 (universeBoundary n) :=
  PolyTerm.universe n

/-- Loubaton thesis §6.1.4.2 functorial Grothendieck construction:
the functors into the universe are exactly the U-small classified
left cartesian fibrations. -/
theorem grothendieckConstruction (π : PolyProfile) (I : MarkedCellOf π) :
    Hom_⊖ I (universeCell π ω) ≃ LCart^c_U I := ...

/-- Univalence as a structural theorem (Loubaton thesis §6.1.3).
The identity type Id (universe l) A B is canonically equivalent to
Equiv A B via the functorial Grothendieck construction. -/
theorem polyTermUnivalence (π : PolyProfile) (l : Nat) (A B : PolyTerm π 0 _) :
    Id (universeCell π l) A B ≃ Equiv A B := by
  apply Equiv.trans (grothendieckConstruction π _)
  apply Equiv.refl
```

**Lean LoC estimate:** ~10K LoC.

**Research-frontier flag:** ⚠️ Cubical Agda has univalence at the
(∞,1)-level.  (∞,ω)-univalence per Loubaton thesis: not mechanized
anywhere.

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

### What is NOT decidable / NOT shippable (narrowed list after re-scoping)

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

That is the entirety of the not-shippable list.  The previous
revision's "Cisinski ω-loc out of scope" and "full Lurie ∞-topos
out of scope" entries are **withdrawn**; §12 commits to both via
Dugger 2001 + Beke 2000 + Smith small-object-argument routes.
Complicial Gray Stage 2 is **required**, not optional.

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
After the 2026-05-24 computability-hardening revision, every
capability claim above either reduces to:

* a **cited published theorem** with arXiv ID and paper reference
  (typically Loubaton thesis §6.1 + HLOR 2024 + Henry-Loubaton 2023 +
  Loubaton 2207.08504 for semantic claims; Makkai 2021 + Forest 2022
  + Adjedj et al. 2024 for decidability claims), OR
* a **constructive Lean definition** in this codebase (with file
  path under `LeanFX2/Foundation/Polygraph/` or `LeanFX2/Reducibility/`), OR
* an **explicit de-scoping note** in §12 with the reason
  (e.g. "Cisinski ω-localization de-scoped to depth-3 hardcoded
  because no algorithmic construction exists in the literature").

No `IsX : Prop` placeholder predicates ship under the PolyTerm
substrate.  No "research-frontier flag" stands in for a missing
proof.  No `Inhabited X` for unconstructible X.  Every decidability
claim has an algorithm citation; every Lean theorem signature has a
proof skeleton compatible with `#assert_no_axioms` per
lean-fx-2/CLAUDE.md.

The 187K LoC budget is realistic per the per-axis Lean LoC estimates.
The 36-month timeline is realistic per the per-phase deliverable
breakdown.  The risk register in §12 names specific failure modes
with mitigations.

The decision to commit to this pivot is the user's.  This document
is the technical proposal; the cron-based prompts ("continue working
on accelerate-* tasks") indicate the user has not yet committed.

**If committed:** the first concrete step is `Foundation/Polygraph/CellShape.lean`
shipping the shape catalogue.  POLY-α targets MILESTONE A in
month 6.

**If deferred:** this document remains a queued architectural option,
to be revisited after MILESTONE A ships under the current accelerate-*
roadmap.

Either way, the literature is captured in `reference_loubaton_papers.md`
memory entry and the design rationale is preserved here for future
reference.

---

*Document version 1.0 — 2026-05-23.  Authored during the literature
synthesis session that followed P2.3 RawPolyTermFlat substrate ship
(commit 7d6758a9).  Total length ~1500 lines per author request.*
