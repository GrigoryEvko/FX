# FX1Poly Frontiers — the advanced-frontier & open-problem map, with placement

> **What this is.** A dense catalogue of every advanced-frontier topic and open
> problem the FX program engages, each pinned to (a) its mathematical content,
> (b) its honest reachability tier, (c) its FX task IDs, and — the point of this
> file — **exactly where it lives in the `FX1Poly/` tree** (which axis, which
> substrate layer, which new module). It is the companion to `polycell.md` (the
> roadmap) and `Axis/Mode/grade-mode-spectrum.md` (the grade↔mode design). Read
> those for *why*; read this for *what* and *where*.
>
> **Legend.** `[S]` shipped · `[R]` reachable now (T1 engineering, zero-axiom) ·
> `[C]` conditional (T2 — provable relative to a stated hypothesis or a stronger
> metatheory, or an FX conjecture) · `[O]` genuinely open in mathematics/CS
> (T3 / field-open — FX can *contribute*, never *assume*). `★` = keystone.
>
> **The prime directive.** FX's frontier contribution is not "reach higher"; it
> is **being the first foundation where the reach-vs-reality boundary is itself a
> machine-checked, non-forgeable object**, carried by the grade vector the kernel
> already has (Trust dim 9, Cost dim 13, the universe-strength flag). Every entry
> below therefore carries its tier *as data the kernel can propagate*, not as a
> caveat in prose. The honesty ledger is the load-bearing deliverable, not an
> appendix.

---

## 1. The placement rubric — the decision tree

Every frontier module answers six questions in order; the first `yes` fixes its
home. This rubric is the spine of the whole file; the domain sections below just
apply it.

```
Q1  Is it GENERIC (∞,ω)-category theory / rewriting / word-problem, with NO
    dependence on the FX signature, the kernel's RawTerm, or the typing rules?
        → Polygraph/                (zero external deps; imported BY the axes)

Q2  Is it the STANDALONE STRUCTURE OF ONE AXIS (term / type / context / mode)
    as an ω-category — signature-specific, but PRE-gluing (before the four axes
    meet)?
        → Axis/<Axis>/             (each axis its own namespace; meets at Core/Fib)

Q3  Is it a CROSS-AXIS CLASSIFIER or GRADE (the grade↔mode spectrum, the
    universe-strength dial) that every axis instantiates?
        → Axis/Type/Strength/  |  Axis/Mode/GradeAlgebra/
          (a standalone classifier the axes import; NOT under any single axis)

Q4  Is it the SHARED CELL SUBSTRATE, the REDUCTION ENGINE, the REDUCIBILITY
    METATHEORY, or the FOUR-AXIS GLUING?
        → Core/                     (Substrate | Rewriting | Metatheory | Fib)

Q5  Is it a TYPING JUDGMENT, a TYPING-METATHEOREM (SR / SN / FT / canonicity /
    NbE), or one of the 21 GRADED DIMENSIONS?
        → Typed/                    (Engine | Metatheory | Dimensions)

Q6  Is it a STRENGTH / PROFILE / EXTENSION artifact (a consistency-strength flag,
    an admissible profile extension, the reflection ladder)?
        → FXProfile/ | ProfileFibration/ | Core/Substrate/Profile/ | Extension/
```

**Two invariants that never bend.**

- **Namespaces are decoupled from paths.** A file's `namespace` (`FX1Poly.Core`,
  `FX1Poly.Axis`, `FX1Poly.Polygraph`) is independent of its directory. The
  lakefile globs `.submodules`, so *relocating* a file is import-line surgery
  only; consumer references stay valid. This is why the whole Polygraph move-out
  cost nothing semantic. Place by *concept*, not by *namespace*.
- **Every kernel deliverable has a zero-axiom twin** in `FX1PolyAudit/` at the
  mirror path, gated by `#assert_no_axioms` per declaration. A frontier module is
  not "done" until its twin is green. The audit tree is the honesty ledger made
  executable.

**The dependency spine (who may import whom).**

```
Init  ⟶  ComputerAlgebra/  ⟶  Polygraph/  ⟶  Axis/{Term,Type,Context,Mode}
                                                     │
                                                     ▼
                                                  Core/       (Substrate, Rewriting,
                                                     │         Metatheory, Fib)
                                                     ▼
                                                  Typed/      (Engine, Metatheory,
                                                     │         Dimensions)
                                                     ▼
                                        FXProfile / ProfileFibration / Extension
```
Arrows point *may-import*. Nothing above the line imports anything below it.
`ComputerAlgebra/` imports nothing but `Init`; `Polygraph/` nothing but `Init` (+ `ComputerAlgebra/`
where Steiner homology needs it). `Core/Fib/` is the *only* place the four
axes are allowed to meet. The spine is to become a CHECKED artifact (rail 9,
§16) — the 2026-07-02 refactor exposed a silent transitive-import reliance.

---

## 2. Directory skeleton + the new-modules manifest

Current top level: `Core/ Dimensions/ Extension/ FXProfile/ Polygraph/
ProfileFibration/ STC/ Axis/ Typed/`. The frontier work adds directories in
three places; here is the manifest of *new* homes this file proposes (each is
justified in its domain section).

```
Polygraph/                              # generic (∞,ω) cat theory — signature-free
  Category/            [S]              # 1-cats: RawCategory, Pullback
  TwoCategory/         [S]              # RawTwoCategory, GlobularSet, Gray, Semistrict
    FreeTwoCell/       [S]              # signature-generic free-2-cell rewriting tower (18 files, 2026-07-02)
    WalkingAdjunction/ [S]              # seed-instantiated 2-cell word-problem cluster (22 files, 2026-07-02)
    TwoMonad           [S]              # generic 2-monad + EM adjunction + bi-initial model
  OmegaCategory/       [S]              # SquierCoherence, FreeStrictOmega (free ω-cat)
  Marked/              [S]              # MarkedComplicial (HL23 marking seed)
  Invertibility/       [S]              # WitnessClosure, SN = inductive fixpoint
  OmegacE/             [S]              # Makkai free-monoid word engine
  Computad/            [S]              # Signature (the 2-computad carrier), AdjunctionSeed, WordProblem (2026-07-02)
  Steiner/             [R]  ★ NEW       # ADC ≃ free strict ω-cat; decidable cell eq [OurCorollary(Steiner04)]
  Complicial/          [R]     NEW      # horns = equations; Street nerve bridge
  WalkingEquivalence/  [R]     NEW      # the coherent walking ω-equivalence polygraph
  SemiModel/           [R core/O]  NEW  # constructive fibration-cat + enriched WFS
  Homotopy/            [C]     NEW      # the homotopy-language framing (GAT → clan → hyperdoctrine)

ComputerAlgebra/       [S seed / R] ★   # Init-only, certificate-first computational algebra (renamed from
                                        # Exact/ 2026-07-02 — "exact" collides with certifyRawCellExact /
                                        # chainExact and reads as "exact sequence"). Charter subdirs:
                                        # Number/ (structural-fuel gcd + Bezout, divisibility, exact
                                        # rationals, the clean Nat/Int replacement-lemma library — Init's
                                        # Nat.gcd/Int.gcd are WellFounded-based and BANNED; Nat.mul_assoc/
                                        # Nat.add_mul are propext-dirty), LinearAlgebra/ (IntMatrix +
                                        # unimodular alphabet + SNF predicates SHIPPED as brick 1,
                                        # commit 7e85f2ed; SNF checker + fuel driver next), Polynomial/
                                        # (Sturm sequences, root counting), Positivity/ (SOS/PSD checking,
                                        # PerronFrobenius), FloatingPoint/ (radix-generic R-FREE Flocq —
                                        # IEEE ops = round-of-exact on RadixScaledIntegers, div/sqrt
                                        # certificate-first, NO gcd; binary16/32/64 + FP8 E4M3/E5M2 +
                                        # FP4 E2M1 + the spec's dec32/64/128 as ONE format family;
                                        # block-scaled NVFP4/MX quantization certificates = dim-14
                                        # Precision semantics; FLOAT-0..6 #1935-#1941
                                        # [Source(Flocq)]+[OurReformulation]) — one library, four+
                                        # payoffs (Steiner homology,
                                        # Moscow certificates, matroid-Hodge)

Axis/
  Term/ …              [S]              # the reduction axis (Cell, Rewrite, Generator, SSC…)
  Type/                                 # the type/universe axis
    Level/ Universe/   [S]
    Interval/          [R]     NEW      # interval theories, φ columns, cubical Kan ops
    Strength/          [R/C]   NEW      # the reflection-rank-indexed strength dial
  Context/ …           [S]              # the substitution/base axis (RMC, models, directed)
  Mode/                                 # the modality axis
    GradeAlgebra/      [S]              # semiring grades
    Frontier/          [S]              # ModeOmegaWeakGray
    Cohesion*/Transp*  [S/C]            # the modal zoo
    FibrancyMode       [S]              # fibrancy as ONE mode property (2LTT f-e)
  Grade/               [C]     NEW      # the grade↔mode spectrum realized (R1–R7)

Core/
  Substrate/ …         [S]              # RawCell, Cost, Profile, Semantics, Univalence
  Rewriting/ …         [S]              # RuleTables, Reduction, Confluence, Normalize/NbE, Word
  Metatheory/
    Reducibility/ …    [S]              # the Tait candidates (impredicative residual)
    Normalization/     [S]              # Orders (RPO/multiset), StrongNorm, IotaSN
    Sconing/ Canonicity/ [S]
    Reflection/        [R/C]   NEW      # the self-reference ladder, GLP, autonomous progression
    Ordinal/           [R/C]   NEW      # ordinal analysis; Steiner loop-free order as SN measure
  Fib/                 [S/in-flight]    # the four-axis gluing (fib-1..16, THE-ONE-OBJECT)

Typed/
  Engine/ …            [S]              # HasTypeUnion + tables (the live typing engine)
  Metatheory/ …        [S]              # SR, FT, canonicity, Denote, Sconing, STC, Normalizer
  Dimensions/          [S]              # the 21 graded dimensions (Cost, Graded, Parametricity)
    Cost/              [S]              # + the optimization polygraph (COPT/CNOS)
  Rott/                [R]     NEW      # observational logical relations (SRP rows, relativity)
  Complexity/          [R/C]   NEW      # the epistemic-complexity library (LB/barriers/firewall)
  SelfFormalize/       [C]     NEW      # FX@n+1 ⊢ metatheory(FX@n); the bootstrap

FXProfile/ ProfileFibration/ Extension/ [S]  # profiles, strength flags, admissible extensions
```

The rest of this file walks the twelve domains, each concept placed against this
manifest.

---

## 3. Domain I — the higher-categorical substrate (`Polygraph/`)

**Home law.** This entire domain is *signature-free* (∞,ω)-category theory: it
answers Q1, so it lives in `Polygraph/`, imports nothing but `Init` (plus its own
internal `RawCategory`/`Step` substrate), and is imported *by* the four axes. It
is the kernel's reusable pure-math library. The published SOTA here is classical,
on-paper, non-computational (Bousfield-localized semi-model structures); the
`Polygraph/` charter is the **constructive + decidable + zero-axiom** version,
which does not exist anywhere else, so "beyond SOTA" is inherent, not aspirational.

### 3.1 Steiner theory — the free strict ω-category as linear algebra `[R]` ★ {S2, term-GRAY-FULL #1640}

An **augmented directed complex (ADC)** is a chain complex of free abelian groups
`… → C₂ →∂ C₁ →∂ C₀ →ε ℤ` (`∂∂=0`) with, per dimension, a distinguished *positive
cone* `Cₙ⁺` (the ℕ-combinations of basis atoms). Steiner's theorem (Loubaton
thesis §1.2.1, Thm 1.2.1.23): the adjunction `λ ⊣ ν` restricts to an
**equivalence** `(0,ω)-cat_B ≃ ADC_B` between strict ω-categories with a
*loop-free* basis and ADCs with a loop-free basis. Under it: an **n-cell is an
integer vector** over the dimension-n basis; **source/target = the boundary
matrix `∂`** split by positivity (matrix-vector product); **composition
`x *ₖ y = x + y − z`** (`z` = shared k-boundary, i.e. vector arithmetic); and
**two composites are the same cell iff their integer vectors are equal**. The
higher word problem collapses to `DecidableEq (Finsupp basis ℤ)` — no rewriting
search, no completion. The **loop-free order** (`a ⊙ b` = "atom a in `∂b`") is a
well-founded partial order = a *canonical* SN precedence (retires the fib-3-floor
"which LPO?" question). The **Gray tensor** = the chain tensor with the Koszul
sign `∂(x⊗y)=∂x⊗y+(−1)^|x|·x⊗∂y`, which preserves loop-free bases (so `fxMode_nn`
flips reachable-true).

**Home** `Polygraph/Steiner/` — new dir, sibling of `OmegaCategory/`. Modules:
`AugmentedDirectedComplex.lean` (the ADC structure + positivity + loop-free
predicate), `SteinerAdjunction.lean` (`lambdaFunctor`/`nuFunctor` and the
equivalence on the loop-free subcategory), `CellCoordinates.lean` (cell = integer
vector; `sourceMatrix`/`targetMatrix`; `composeAt`), `DecidableCellEq.lean`
(vector equality decider), `LoopFreeOrder.lean` (the well-founded `⊙` order →
exported as an SN measure), `GrayChainTensor.lean` (Koszul tensor). Imports:
`Init` only (ℤ-vectors, `Finsupp`, matrices are all structural, zero-axiom).
**Honesty:** strict ω-cats with a loop-free/free-on-a-polygraph basis; the
*general* strict-ω-cat word problem is undecidable (Novikov–Boone) — FX's
finiteness is the enabler (dovetails HL23 Cor 4.35).

**Provenance (corrected 2026-07-02).** The *representation* is Steiner's
(R. Steiner, "Omega-categories and chain complexes", TAC 11 (2004) 148–184;
restated as Loubaton thesis Thm 1.2.1.23). The **"word problem = linear algebra"
framing is OUR corollary**, not Steiner's claim — he proves an algebraic
equivalence and never states a decidability reading. Tag every use
`[OurCorollary(Steiner04)]`; the zero-axiom mechanization of the corollary is
itself the (modest, genuine) novelty.

**Smith normal form — one engine, five arcs `[R]` ★.** With ADC boundaries as
integer matrices, homology is computed by SNF over ℤ (`ComputerAlgebra/LinearAlgebra/SmithNormalForm`),
making H₁/H₂ of a finite presentation *executable*: (i) the Squier H₁ of
CNOS-0/2/5 + OHOM-1 becomes a decision procedure; (ii) the H² obstruction column
of the periodic table (fib-9 / CFND-5 / O-OBSTRUCT) becomes *computed*, not
conjectured; (iii) ℤ-coefficients see **torsion**, which the shipped 𝔽₂
`F2ChainComplex` cannot — conjecture X2 (§15) reads torsion H₁ as cost-neutral,
erasure-positive strategy monodromy (no rewriting-theoretic interpretation of
torsion exists in the literature we know; even *stating* it machine-checked is a
contribution); (iv–v) the same exact substrate serves the Moscow certificates and
the matroid-Hodge certificates (Domain XI).

**The abelianization reading.** The passage matching-carrier → Steiner
coordinates is precisely *abelianization*: `blockRotate` (the shipped renaming
witness) exists because sequential fresh-id allocation is order-sensitive, while
ℤ-linear combinations forget order — interchange becomes `x + y = y + x`,
definitional. The price of abelianization is exactly the loop-free/free
restriction: relations *need* the order information abelianization destroys.

**The free/relational boundary is machine-witnessed in-tree.** The walking
ω-equivalence is FREE (binary finite-type, `OmegacEFiniteType` proven) — the
Steiner side, decidable by vector equality. The walking *adjunction* is NOT free
— the triangle identities are genuine relations, and the shipped
`WalkingAdjunction/AdjunctionTriangleObstruction` *proves* it — the
completion/matching side (the 22-file cluster relocated 2026-07-02). The two
deciders overlap on the free fragment; `steinerDecide = makkaiDecide` there is
the natural cross-validation theorem (propose **DECIDER-XCHK** — agreement of
independent methods as the horizontal form of the FX0/FX1 trust split).

### 3.2 The free strict ω-category monad `T` over an arbitrary signature `[R strict / O weak]` {SIG-3/5, POLY-CAP #1384, mode-6/7}

Two convergent presentations. Henry–Meadows: *present `T` by its theory Θ* — the
monad⟺theory idempotent adjunction (nervous monads ≃ theories); the free ω-cat
monad is nervous + polynomial/cartesian (the best-behaved class), so you never
build the endofunctor, you present it. Steiner (§3.1): *compute `T(signature)` in
basis coordinates*. FX's 205-generator `fxSignature` IS a pretheory over arities
Θ (Joyal globular sums, an elegant Reedy category); kernel-algebras = Θ-models.

**Home** `Polygraph/OmegaCategory/FreeStrictOmegaMonad.lean` (extends the shipped
`FreeStrictOmega.lean`, currently dim-2 only, `fxMode_nn = false`) + the Steiner
coordinate realization in `Polygraph/Steiner/`. The **weak** ω-cat monad
(Batanin–Leinster globular operad `mode-6`, Simpson semistrictification `mode-7`)
stays a **moonshot** and is honestly marked `[O]` — see §3.7.

### 3.3 Inductive vs coinductive invertibility = SN vs the folk structure `[S]` ★ {Invertibility, DEFUNIV-SN #1647}

HL23's *invertibility set* (Def 4.15) — a cell family closed under "every member
has a reverse + unit/counit witnesses *in the family*" — IS a Tait reducibility
candidate (CR1/CR2/CR3 = the closure). The **least** (inductive) fixpoint of the
witness-closure operator is **strong normalization** (`Acc StepSuccessor`); the
**greatest** (coinductive) fixpoint is the folk/canonical structure. Shipped
theorem: `inductiveClosure_reductWitnessOperator_iff_isStronglyNormalizing`. A key
finding: the *abstract* least fixpoint is impredicative Knaster–Tarski (Lean's
positivity checker can't see through an abstract `apply` field) but **concretizes
to predicative `Acc` at the reduction instance** — the ZF-strength residual,
localized: impredicative-abstract, predicative-concrete.

**Home** `Polygraph/Invertibility/` — shipped (`WitnessClosure.lean`,
`InvertibilitySet.lean`, `StrongNormalizationBridge.lean`, `FiniteNoGap.lean`).
The finite-no-gap corollary (Cor 4.35: a bounded-generator polygraph has no
coinductive-but-not-inductive invertibles) is the *reason* FX's well-typed SN is
structural, not luck.

### 3.4 Marked / complicial structure; the two Gray tensors `[R]` {term-18, term-COMPLICIAL-FULL #1641}

HL23's `m`-marked ω-categories: a marking predicate (which cells are "thin" =
weakly invertible), closed under identity/composition, with `flat`/`sharp`/`eq`
markings. Two Gray tensors: **lax ⊖** (the term-17 Gray tensor) and **pseudo ⊗**
(marks all cross-cells; = cartesian product at the homotopy level). The
globular↔complicial dictionary (Loubaton, HL23 §4.4): **complicial horn = an
equation** (Λᵏ[n]→Δᵏ[n] ≙ the FX rewrite rule / redex), via strictification ⊣
stratified-Street-nerve, a Quillen *equivalence*. So FX's `Step` relation *is* a
complicial horn-filling structure.

**Home** `Polygraph/Marked/` (shipped seed `MarkedComplicial.lean`; add
`Marking.lean` = generic marking over a `RawCategory`, unifying term-18 &
context-36) + `Polygraph/Complicial/` (new: `Horn.lean` = horn=equation,
`StreetNerve.lean` = the nerve bridge). The lax/pseudo distinction goes in
`Polygraph/TwoCategory/GrayTensor.lean`.

### 3.5 The coherent walking ω-equivalence / walking adjunction `[R]` {fib-3, SN-135 #638}

The finite-type polygraph `ωÊ`, self-similar under *marked suspension*
(`Eₖ = α∞(ΣEₖ₋₁) ∪ β∞(ΣEₖ₋₁)`), proven contractible via coinductive
localization = the canonical model structure. This IS the object fib-3 (the
walking adjunction / mode 2-cell word problem) is built on. Bi-invertibility
(separate L/R) = the adjunction; eq = bieq (keystone Prop 1.19) = the coherence
that makes adjoint data essentially unique. The "locality lemma" fib-3 circled =
the weakly-unique-solution property, which HL23 Prop 3.19–3.25 *proves* for
prefibrant objects.

**Home** `Polygraph/WalkingEquivalence/` — new: `WalkingEquivalence.lean` (the
suspension-recursive polygraph), `Contractibility.lean` (the coinductive
contractibility), plus the **decidable word problem the paper never gives**
(`DecidableWalkingWord.lean`) — genuinely beyond SOTA. Consumed by `Core/Fib/`
(fib-3) via the mode axis.

### 3.6 Polygraphic resolution / Squier / higher rewriting `[S dim≤2 / R higher]` {term-4/5, OHOM-1 #1261}

Guiraud–Malbos: a convergent polygraph *has* a resolution — coherence of
coherence, ad infinitum — and its metatheory (SN, CR, coherent presentation) is
the low dimensions of that resolution. Squier's theorem: convergent ⟹ finite
derivation type ⟹ coherent presentation, with the higher syzygies read off the
critical pairs. HL23's *equation with weakly-unique solutions* is exactly
local-confluence + the coherence 2-cell.

**Home** shipped generic core `Polygraph/OmegaCategory/SquierCoherence.lean`
(`RewritePath`, `SquierDiamond`, `RewriteHomotopy`, generic over `Step`); extend
to the (∞,ω) resolution in `Polygraph/OmegaCategory/PolygraphicResolution.lean`.
The **metatheory = resolution** thesis (S3) is realized here + read into
`Core/Metatheory/` per axis. See §8.6.

### 3.7 Semistrictification / Simpson's conjecture / weak (∞,ω) coherence `[O]` {mode-7, term-GRAY-FULL}

★OPEN in mathematics. Not every tricategory strictifies (Gordon–Power–Street:
the obstruction is a braiding, Eckmann–Hilton); the fix is *semistrict* (Gray for
units-strict, Simpson's conjecture for interchange-strict). Above dim 3 the
algebraic coherence explodes (Trimble's tetracategory axioms); the two roads are
(a) drop to geometric models (complicial), (b) semistrictify — **Simpson's
conjecture** (weaken only units) is conjectured to generalize and is **open**.

**Home** `Polygraph/TwoCategory/Semistrictification.lean` (shipped Gray core) →
the weak-ω capstone stays honestly `[O]`. Marked in the audit as `hasNo…=false`.
FX contributes the *decidable convergent-presentation* case, never the general
coherence.

### 3.8 The word problem: decidable ↔ undecidable boundary `[boundary]` {term-20, SN-135}

Decidable for convergent/finite presentations (Steiner linear algebra; the
Makkai `OmegacE` engine; complicial horn-filling); **undecidable** in general
(strict ω-cat word problem contains Novikov–Boone group word problems; Kan/hcomp
filling = f.p.-group word problem — Doré–Cavallo–Mörtberg). This is a *theorem*,
not a gap: it *forces* FX's per-fragment (not joint) decidability and vindicates
the O-NORM honesty rail.

**Home** the decision procedures live across `Polygraph/OmegacE/WordProblem.lean`
(conditional on confluence + a normalizer), `Polygraph/Steiner/DecidableCellEq`,
`Polygraph/WalkingEquivalence/DecidableWalkingWord`; the undecidability boundary
is *documented*, never coded around. Ties `Core/Rewriting/Word/`.

### 3.9 Constructive semi-model structure `[R core / O the ∞-localization]` {SemiModel moonshot}

Gambino–Henry: a model structure on `[Δᵒᵖ, ℰ]` for ℰ merely countably-lextensive
(finite limits + countable van Kampen coproducts) — far weaker than a topos.
Fibrations = maps with *chosen* split-epi sections against horns (fibrancy =
structure); the enriched WFS is over *decidable (complemented)* inclusions with
*chosen* fillers; fibrant replacement = an ω-chain of pushouts. §§1–10,12 are
fully constructive; the *only* non-constructive layer is the ∞-categorical
localization — the exact gap FX's decidable-polygraph program *routes around*
(FX never localizes). Cavallo–Sattler's algebraic-small-object saturation is the
matching engine: the **saturation theorem** ("structure on generators extends
functorially to all cells") IS the S5 "prove metatheory once over the polygraph"
made a categorical theorem; constructive via complemented-mono ω-backdrop +
Pitts–Steenkamp algebraized chains (matches `Acc.rec`).

**Home** `Polygraph/SemiModel/` — new: `FibrationCategory.lean` (finite-limits
only, Thm 1.7), `EnrichedWFS.lean` (decidable inclusions + chosen sections),
`Saturation.lean` (the algebraic-SOA saturation = metatheory-once-over-generators).
Reachable *core*; the Bousfield-localized ∞-cat stays `[O]`, deliberately bypassed.

### 3.10 FX is a homotopy language `[C]` {SIG-5, fib-13}

Bardomiano–Henry: attach to any (semi/weak) model category a first-order
dependent-type *language* with invariance theorems (weakly-equivalent fibrant
objects satisfy the same formulas = language-level univalence). Base = a Cartmell
Generalized Algebraic Theory; the contextual category ℂ_T of a GAT is a *clan*
(category-with-fibrations); the categorical form is the *initial λ-boolean-algebra
over the clan* = a Lawvere hyperdoctrine (∃⊣π*⊣∀ + Beck–Chevalley). FX's
`fxSignature` = a Cartmell GAT; the kernel's context/type/term layer = the clan;
the fibration structure = the clan's fibrations.

**Home** `Polygraph/Homotopy/` — new, the framing modules
(`HomotopyLanguage.lean`, `ClanHyperdoctrine.lean`), imported by `Core/Fib/` and
`Typed/` to certify "FX proves its own invariance theorems zero-axiom." Generalizes
Makkai FOLDS (ties `OmegacE`).

---

## 4. Domain II — identity & fibrancy

**Home law.** "Fibrancy" is the universal question *"what structure do the ≥1-cells
carry?"* — strict / groupoidal(Path) / directed(Hom) / relational(Bridge). It is
**one property of the mode axis** → `Axis/Mode/FibrancyMode` (no standalone
cross-axis classifier). Its **type-level
realizations** (interval theories, universe columns, Kan ops) are the type axis
(Q2) → `Axis/Type/Interval/` + `Axis/Type/Universe/`. Its **computational
content** (def-univalence SN, reify) is metatheory (Q5) → `Typed/Metatheory/` +
`Core/Rewriting/Normalize/NbE/`. The cubical *models* are context-side (Q2/Q4) →
`Axis/Context/`.

### 4.1 Fibrancy as a mode property — strict / Path / Bridge / Hom `[S]` {mode-13, FibrancyMode}

The four fibrancy kinds `{strict, groupoidal, directed, relational} × depth` are
**one property of the mode axis**, indexed by the mode-shape (an interval theory).
2LTT's f/e is the strict-vs-groupoidal *shadow* on the type axis. The property is
read per axis: term (α-eq / Conv / Step / reducibility), type (UIP / Path / Hom /
Bridge), context (raw / univalent / directed / sconing), mode (strict-2cat / equiv
/ adjoint / Galois).

**Home** `Axis/Mode/FibrancyMode.lean` (shipped) — the 2LTT f/e presentation
(`FibrancyKind` + `joinFibrancy`, the f/e 2-category, the non-sharp ι). Fibrancy is
**not** a standalone cross-axis classifier — the earlier `Axis/Fibrancy/` proposal
is dropped; it is just one mode property. Per-axis consumers read the fibrancy kind
off the mode property; "fibred over mode" is a Core/Fib gluing statement, not a
separate folder.

### 4.2 Interval theories & the reversal/twist calculus `[R]` {A1-5 #1792, ZOO-BRAIDED #1926}

An *interval theory* Φ (Cavallo–Sattler "Eliminating Reversals") is a single-sorted
algebraic theory over `{0,1}`: cartesian (trivial), affine (no contraction/no
diagonal), distributive-lattice, De Morgan. *Self-dual* Φ (has an involution)
admits the **twist** `I×I = interval + reversal` — modeling a reversal column
inside a reversal-free base. FX's affine/directed columns are non-self-dual, so
the twist correctly does *not* apply → validates keeping them reversal-free. Each
φ-column = a chosen interval theory (the formal skeleton for the multigrade
universe).

**Home** `Axis/Type/Interval/IntervalTheory.lean` — new: the SOGAT-style
interval-theory data + the self-dual predicate + the twist; `AffineInterval.lean`
(no diagonal — the A1 substrate), `CartesianInterval.lean`, `LatticeInterval.lean`.
Consumed by the universe columns (§4.4) and the mode multiplier (§5.x).

### 4.3 Internal parametricity — Gel, extent, relativity, bridge-discreteness `[R]` {ROTT-RELATIVITY #1901, type-9}

Cavallo–Harper: two intervals in ONE theory (structural Path + affine Bridge;
model = □_c × □_a bicubes). `extent` = bridge-funext *without coe* (affine variable
capture); **Gel-types** = relations→bridges-of-types directly (no V/Glue).
**Relativity** (Thm 2.4): `Bridge_𝒰(A₀,A₁) ≃ (A₀×A₁→𝒰)` — the relational analogue
of univalence. **Bridge-discreteness** (`loosen : Path→Bridge` iso) = the internal
identity-extension lemma (SRP by construction); the universe is *not*
bridge-discrete (`Bridge_𝒰 ≃ relations`, `Path_𝒰 ≃ equivs`); refutes WLEM.

**Home** the *typing rows* (gel/relativity/SRP) go in `Typed/Rott/` — new dir:
`Relativity.lean` (ROTT-RELATIVITY as a kernel theorem), `SrpRows.lean` (the
per-former relational-extensionality rows), `ObservationalDsl.lean` (SRP-by-
construction, param as one inference rule). The relational *candidate* goes in
`Core/Metatheory/Reducibility/Candidates/` (a relational Σ-algebra candidate). The
`Gel` reduction rows are already scaffolded in `Core/Equality/Gel/`.

### 4.4 The φ-three-column universe & the CUA/FE factoring `[C]` {FIBRANCY-THREE-COLUMNS, UNIV-MULTIGRADE #1899}

Path + Bridge + Hom coexisting in one universe (2 columns are SOTA-proven, □_c×□_a;
the 3rd, directed-Hom, is the moonshot but the product-of-cube-categories model is
the concrete route). Cavallo–Höfer: **univalence factors `UA ⟺ CUA ∧ FE`** — CUA =
wild-category (up-to-equality) univalence, computes strictly (the *definitional*
layer, zero-axiom); FE = the graded homotopy layer. CUA ⊬ FE (Von Glehn polynomial
model). Grades univalence-strength: def-categorical-univalence as its own grade.

**Home** `Axis/Type/Universe/MultigradeUniverse.lean` — new: the universe as a
product-graded object `𝒰[ℓ,κ,φ]` + the orthogonality theorems; `CategoricalUnivalence.lean`
(CUA, the computing layer); the FE layer is a graded flag consumed by the
def-univalence row. Imports `Axis/Type/Interval/` + `Axis/Mode/FibrancyMode`.

### 4.5 Definitional univalence — `Id_𝒰 ↝ Equiv` computes `[C]` {type-7 [S], EXT-4 #1373, DEFUNIV-SN #1647}

The oriented equality `Id at universeCode ↝ equivCode` as a *definitional
reduction*, gated by a **type-complexity SN measure** (turns oriented equalities
into reductions without breaking SN) and a **confluence gate** (type-directed-η ×
β/ι orthogonality). Shipped at the context level (context-31) and as type-7; the
kernel row is EXT-4. The SN measure is a genuine FX conjecture in its full form
(DEFUNIV-SN).

**Home** the reduction row in `Core/Rewriting/RuleTables/Iota/` (or a new
`Core/Rewriting/RuleTables/Univalence/`); the SN measure in
`Core/Metatheory/Normalization/StrongNorm/DefunivMeasure.lean`; the confluence gate
in `Core/Rewriting/Confluence/`. The shipped context-level machinery is in
`Core/Substrate/Univalence/`.

### 4.6 Directed type theory / synthetic ∞-categories `[C]` {type-24, context-33/34 [S], DIRECTED-NBE #1907}

Triangulated type theory `TT_□`: a directed interval (bounded distributive lattice,
0≠1, *not* total), synthetic `hom_A(a,b)`, Segal (unique composites)/Rezk (local
univalence). **Directed univalence** `hom_𝒰 ↝ Fun`: FX ships the *space-level*
`hom_S ≃ A→B` (context-34, zero-axiom no-funext); the *category-level*
`hom_Cat ≃ ⟨b|A→B⟩` needs the **flat/cohesion `b` modality**.

**Home** the standalone synthetic ∞-cat of contexts is shipped in
`Axis/Context/ContextSyntheticInfinityCategory.lean` +
`ContextDirectedUniverse.lean` (`hasFullSegalDirectedUA = false` — the honest wall).
The category-level flip needs the `b` modality from `Axis/Mode/Cohesion*`;
directed reify (directed-univalence computes) → `Typed/Metatheory/Normalizer/`
(DIRECTED-NBE). The directed *interval* is a `Axis/Type/Interval/DirectedInterval.lean`.

### 4.7 Cubical Kan operations & the contortion/Kan decidability split `[R ops / O Kan] `{type-23, NBE-DECCONV #1893}

hcomp/transp/coe + cubical canonicity. The **equivariance** condition (Awodey–
Cavallo–…): box-filling over k-cubes + coherence under every automorphism σ∈Σ_k —
what makes a cubical model *present spaces*; realignment/strictness is the axiom
Gel/Glue need. **Boundary-filling** splits sharply: **contortion** (reparameterize
one cube) is *decidable* (P→NP-complete by interval theory; affine = sub-cartesian
= cheapest); **Kan** (paste via fill/hcomp) is **undecidable** for every interval
theory (= f.p.-group word problem). So a *complete* hcomp decider is provably
impossible — route via SMT/search, never claim completeness.

**Home** the Kan-op *generators + rows* → `Axis/Type/Interval/KanOperations.lean`
+ the iota rows in `Core/Rewriting/RuleTables/`. The contortion decider (FX's
sub-cartesian affine advantage) → `Core/Rewriting/Word/ContortionDecider.lean`. FX
keeps its interval **non-fibrant by design** (parametricity + def-univalence, not
full cubical), so the equivariant model is a *donor*, not a port (see §6.x). The
undecidability of Kan is documented as a wall.

### 4.8 Multi-circle & chromatic geometric grades `[O]` {frontier-external}

A type can live over a *product of independent shape-circles* (path × bridge ×
directed × clock) — the honest generalization of "the interval" — giving a vector
geometric grade (Nuyts 2024, internalizable now). Chromatic/motivic height (Morava
K(n)) is the deepest external prize — essentially not internalized in any type
theory; a first synthetic internalization would be genuinely new mathematics.

**Home** the multi-circle product → `Axis/Type/Interval/ShapeProduct.lean`
(reachable). Chromatic height is marked `[O]` and lives (if ever) as a design note
only — no code obligation.

---

## 5. Domain III — modalities & the mode theory (`Axis/Mode/`)

**Home law.** The mode axis is the classifier of *grading shapes* (Q2 for the
axis; Q3 for the grade↔mode spectrum). The whole modal apparatus — MTT/MATT,
transpension, cohesion, the A1 lock — lives in `Axis/Mode/`; the *fibration* over
the mode base (fib-3) lives in `Core/Fib/`.

### 5.1 MTT / MATT & the doctrine `[S mode-1..27]` {mode-0..27}

Multimodal type theory: a mode 2-category 𝓜 (objects = modes, 1-cells =
modalities/locks, 2-cells = transformations); judgments carry positions. MATT =
the modal-annotated variant. The mode theory is a 2-monad (mode-17), with a
bi-initial model. All 27 mode rungs are shipped standalone.

**Home** shipped across `Axis/Mode/Mode.lean`, `TwoMonadDoctrine.lean`, the
modality suite. The generic 2-cat/Gray/ω-cat *cores* were extracted to
`Polygraph/TwoCategory/`; `Axis/Mode/` now holds genuine mode content
(`freeModeCategory` + the modalities).

### 5.2 Transpension — the universal right adjoint `[S/C]` {mode-11 [S], TRANSP-0..4}

The rightmost adjoint in the multiplier's adjoint string; recovers
Gel/Glue/Weld/mill/√/Φ/Ψ/nominal by choosing the shape. Structure-class-gated
admission (the multiplier's affine/cartesian/symmetric class decides which zoo
member is sound). Instances: affine → parametricity (`TRANSP-PARAM-RETIRE #1437`),
clock → guarded `later` + Löb (`TRANSP-3`), cartesian → cohesion √ (`TRANSP-4`).

**Home** `Axis/Mode/Transpension.lean` + `MultiplierStructureClass.lean` +
`MultiplierEndofunctor.lean` (shipped); the admission table `TRANSP-ADMIT` →
`Axis/Mode/TranspensionAdmission.lean`; the gel-boundary iota rows → `Core/Equality/Gel/`.

### 5.3 The A1 lock = context-restriction left adjoint `[R]` ★ {A1-* #1788-1809, fib-3}

**The triply-corroborated keystone.** FX's affine-interval elimination IS the
**context-restriction left adjoint `Γ\r ⊣ −.𝕀`** (Cavallo–Harper §5) — and *that
adjoint is exactly what makes substitution admissible* (`A1-SUBST-OPEN #1807`, the
live blocker). Three independent papers name the same modality: Cavallo–Harper
`Γ\r`, dTT's `△□` display-guard, STC's `●` closed modality. The A1 lock is the
FitchTT right-adjoint lock `Γ/μ_affine†`; the negative bridge `μ_affine◇→A` is its
open form. The affine interval *breaks HITs* (the `line`-HIT reason) — which is the
soundness reason FX's interval is **non-fibrant**.

**Home** the lock former + discipline are shipped/in-flight in
`Axis/Context/` (`lockCons`, the FitchTT accessibility) and the mode modality in
`Axis/Mode/` (`μ_affine`, `μ_affine†`). The **new construction** — realizing the
lock *as* the `Γ\r ⊣ −.𝕀` adjoint — goes in `Axis/Context/DimensionLockAdjoint.lean`
(`A1-CODEXTRIFY`) and the substitution-pushes-under-open metatheory in
`Typed/Metatheory/Strengthening/` (`A1-SUBST-OPEN`). The negative modal *type*
former → `Core/Equality/` or a new `Axis/Type/NegativeModality.lean` (A1-NEG-TRANSPENSION).

### 5.4 Cohesion — ♭/♯/ʃ, real-cohesive, differential `[C]` {type-11, ZOO-COHESION-* #1925-1934}

The adjoint quadruple `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` over the global-sections geometric
morphism `Γ: Psh(W)→Set`; ♭ = Disc∘Γ (flat/discrete comonad), ♯ = coDisc∘Γ
(sharp/codiscrete monad), ʃ = Disc∘Π₀ (shape reflective). The adjoint string
ʃ⊣♭⊣♯ + the cohesion axioms (pieces-have-points, real-cohesive C0–C2). Closes
type-11. The `b` modality here is what category-level directed univalence needs
(§4.6).

**Home** shipped/in-flight across `Axis/Mode/Cohesion*.lean` (the whole
`Cohesion*` family) + `RealCohesion.lean` + `ModalFracture.lean`. The metatheory
(SR/SN/FT/canonicity for the cohesion family) → `Typed/Metatheory/` via the
generic modal arm.

### 5.5 Guarded/clock, linear/BI/LNL, Galois `[S/R]` {mode-15/22/26, ZOO-GALOIS #1928}

Guarded/clock (later, Löb, unique fixpoints — mode-15). Linear/BI exponential
(mode-22) and graded/coeffect (mode-26, the alongside-vs-beneath boundary). The
**LNL polycategory** (Shulman) is the categorical semantics of the linear/nonlinear
split = the grade↔mode crossover: nonlinear objects (cartesian multicat, all
structural rules) + linear (symmetric polycat, exchange only), `F⊣U`, `!=FU`. A
*doctrine* = "one grade-checker parameterized by a semiring/tier"; the sequent
calculus falls out of the free-D-category small-object construction. **Galois
modalities** = each FX lattice-dimension's Galois connection as a ◇/□ adjoint
(FX-native frontier).

**Home** shipped in `Axis/Mode/{GuardedRecursion,Linear,Graded,Session}.lean`;
the LNL-doctrine framing → `Axis/Mode/LnlDoctrine.lean` (new, the entries-only
admissibility predicate = the ASCII sort-discipline); Galois → `Axis/Mode/GaloisModality.lean`.

### 5.6 O-COMBINE — decidable "do great ideas combine" `[R decidable / O the H²]` {mode-18 [S], O-COMBINE #1435, CFND-* #1473-1477}

The decidable pushout of doctrines (mode-18, shipped); `combinesOrthogonally` = the
decidable feature-combination predicate; the extension poset; the join. The **H²
semantic obstruction** (whether two features combine *soundly*, not just
syntactically) is the ★OPEN half.

**Home** shipped `Axis/Mode/CombineAmalgamation.lean`; the decidable
combination-predicate + periodic-table matrix → `Typed/Dimensions/AxisObligation/`
(CFND); the H² obstruction target signature is `[O]`, documented only.

---

## 6. Domain IV — universes, size & proof-theoretic strength (the ℓ axis)

**Home law.** Universe *structure* (Tarski, cumulativity, coherence) is the type
axis (Q2) → `Axis/Type/Universe/`. The *strength dial* (reflection-rank-indexed
flags, the content-vs-flag tags) is a cross-axis grade + a profile artifact (Q3/Q6)
→ `Axis/Type/Strength/` + `FXProfile/`. Ordinal analysis (the SN ordinal = the
resolution height) is metatheory (Q4) → `Core/Metatheory/Ordinal/`.

### 6.1 Tarski universe & strict-universe coherence (Glue/realignment) `[S/R]` {type-0/15/20, TRANSP-GLUE #1438}

The standalone Tarski universe (`Code` + decode, never Russell; `Type@L : Type@(L+1)`;
`grownUniverseCode_notTypedAtSelf`). Strict-universe coherence (Gratzer–Shulman–
Sterling): the **(U8) realignment** axiom = strictly extend a chosen classifier
along a cartesian mono ⟹ strict cumulativity; the internal form is a **`Glue`
type-former** (the *same* connective as cubical), and **U8 ⟺ Glue exists**.
Constructively, realignment holds *exactly for decidable monos* (Orton–Pitts; Swan
sharp) — FX's native home.

**Home** shipped `Axis/Type/TypeAxis.lean` (the Tarski universe) +
`Axis/Type/Universe/` (cumulativity, no-top). The **new** reachable win:
zero-axiom `Glue`-for-decidable-monos → `Axis/Type/Universe/GlueRealignment.lean`
(makes U8 a *theorem*, grounds Tarski coherence, powers STC). The shipped STC
scaffold is in the top-level `STC/`.

### 6.2 Cumulativity, universe polymorphism, impredicativity `[R one sort]` {type-13, UNIV-* #1253-1257}

Universe-polymorphic univalence over `LevelExpr`; cumulativity lifts are
univalence-preserving. **Impredicativity** (`limax`, impredicative Prop `Π(x:Type).Prop
: Prop`) is bounded by **Girard's paradox** — one impredicative sort (CoC-style),
*never a tower* (Type:Type / System-U inconsistent). This is the one object-level
ZF-ish strength; keeping it is the type-13/19/26 design fork.

**Home** `Axis/Type/Level/LevelExpr.lean` (the level algebra incl. `limax`, the
`ne_lsucc_self` no-Type-in-Type guard); the univalence-preservation theorems →
`Axis/Type/Universe/CumulativityUnivalence.lean`. The impredicative-Prop sort is a
*flag* gated in the profile.

### 6.3 Large-cardinal universe operators — the content ceiling `[R]` ★ {type-14, LARGE-CARD-CONTENT #1456}

**The computational-content ceiling is ~external Mahlo / Π₃-reflection**, reachable
*now* via general **induction-recursion** (Setzer's Mahlo universe, `|MLM| =
ψ_Ω₁(Ω_{M+ω}) = KPM`; Dybjer–Setzer IR ≥ KPM). Above this: no proof-theoretic
ordinal has been computed for even *one* inaccessible, so everything higher is a
*posited flag* with no normalizing operator. The **two-ceiling split** — content
(where FX lives) vs consistency-flags (arbitrarily high) — governs everything.

**Home** the reachable IR operator → `Axis/Type/Universe/MahloUniverse.lean`
(new; induction-recursion, zero-axiom). Internal-Mahlo-and-above are flags in the
strength dial (§6.5), kernel-*proven* to add no canonicity.

### 6.4 Choiceless large cardinals & determinacy `[O]` {the honest choiceless axis}

Above I0: the **choiceless** ladder (Reinhardt < super-Reinhardt < Berkeley,
Bagaria–Koellner–Woodin). Choice-freedom lifts the *consistency* ceiling — but only
by *one proven rank* (Schlutzenberg `j:V_{λ+2}→V_{λ+2}+λ-DC`, equiconsistent
ZFC+I0). Reinhardt/Berkeley consistency is **genuinely OPEN under ZF, leaning
possibly-inconsistent** (McCallum's inconsistency proofs retracted/unaccepted). The
honest choiceless strength axis is **determinacy (AD/AD⁺/AD_R)** — T2-believed (= ω
Woodins), with *partial* content (strategies as witnesses). "Past I0 into Berkeley"
is an **overclaim + category error** (the lift is consistency-only, content-null).

**Home** these are *flags* in the strength dial (`FXProfile/` +
`Axis/Type/Strength/`), each carrying a `frontier` tag and kernel-proven
content-null. No operators. The `◇_j` self-embedding modality (j:V→V as a graded
comodality; critical sequence = reflection tower; choice-freedom = the Kunen
loophole) is the wildest moonshot, marked `[O]`, pursued only as a content-null
profile — never a claimed operator.

### 6.5 The reflection-rank-indexed strength dial `[R/C]` ★ {GLP-UNIV-BRIDGE #1449}

The **one rigorously-solid bridge**: Pakhomov–Walsh (reflection rank = proof-
theoretic ordinal; α-iterated Π¹₁-reflection = ε_α) gives each universe level a
*certified ordinal index* and explains *why* natural theories are linearly
well-ordered. **Design correction (cross-corroborated by the reflection ceiling
map):** gate each strength grant on a **reflection-rank / Π¹₁-soundness
certificate, NOT ordinal height** — Feferman–Spector intensionality means height
certifies nothing. Beklemishev worm-notation = the recursive certificate to ε₀/Γ₀.

**Home** `Axis/Type/Strength/StrengthDial.lean` — new: the level = reflection-rank
index; `ReflectionRankCertificate.lean` (the Pakhomov–Walsh gate); the ordinal
machinery it reads from `Core/Metatheory/Ordinal/`. The dial's *tags* (certified /
believed / frontier) ride as profile data in `FXProfile/` + `ProfileFibration/`.
The **novel contribution**: T1 rungs ship IR operators; T2/T3 flags are
kernel-*proven* to add no canonicity (`hasNo…=false`). First foundation
honest-by-construction about where content stops.

### 6.6 Forcing as a modality; independence as profile multiplicity `[R mechanism]` {FORCE-MOD #1450, DUAL-UNIV #1455}

The forcing *translation* (Jaber–Tabareau–Sozeau) is a genuine computational
presheaf/sheaf comonad — a T1 mechanism. Independence statements themselves are
*meta* (about non-provability) → model as **profile multiplicity** (Hamkins
multiverse), not internal theorems. A concrete duality (Stone, Gabriel–Ulmer) as a
univalence between two presented profiles is T1 for the finite/concrete case.

**Home** the forcing comonad → `Axis/Mode/ForcingModality.lean` (new; ties the
shipped context-26 forcing CwF in `Axis/Context/`); profile multiplicity →
`ProfileFibration/`. DUAL-UNIV → `Typed/Dimensions/` (a cross-dimension univalence
instance).

---

## 7. Domain V — grading & the graded-everything unification

**Home law.** The grade↔mode spectrum is the meta-structure over *all* axes (Q3);
its realization goes in `Axis/Grade/` (new) + `Axis/Mode/GradeAlgebra/`; the 21
concrete dimensions are typing-level (Q5) → `Typed/Dimensions/`; the graded
metatheorem (prove once over the product) is a `Typed/Metatheory/` capstone.

### 7.1 The grade↔mode spectrum (R1–R7) `[design-locked / C]` ★ {grade-mode-spectrum.md}

Every grade/mode/stratification is a position on one categorification ladder: a
grade is a 1-cell of a *one-object* 𝓜 (R1–R3, "how much"); a mode is a 0-cell of a
*many-object* 𝓜 (R4–R7, "which place"); the crossover R3→R4 is `grade → mode`. Two
orthogonal dials: beneath↔alongside (mode-26) and static↔value-dependent (the one
genuine break — value-dependent grades cannot be a static 𝓜). The φ/δ/ℓ trinity
sits at R4/R3/R1-2. `categorify ⊣ decategorify`: `grade = π₀(mode)` (CSHD #1483).

**Home** the design lives in `Axis/Mode/grade-mode-spectrum.md` (shipped). The
*realization* (the ladder as a value, the rung classifier `mode-2`/`mode-12`) →
`Axis/Grade/Spectrum.lean` (new) + `Axis/Mode/GradeAlgebra/`. The R7 fixpoint ties
`Core/Fib/` (THE-ONE-OBJECT).

### 7.2 FRONTIER-GRADED-EVERYTHING — the 21 dims as one product-graded object `[C]` {#1872, TYTAB-5 #1399}

Every value carries the 21-dim grade vector *and* the φ/δ/ℓ trinity, each grade a
marking/modality on the polygraph; the metatheory (SN/CR/SR/FT) is proved **once**
over the graded polygraph (S5). The value-dependent break is the one thing that
won't collapse into a static grade.

**Home** the grade-vector premises in the rule tables → `Typed/Dimensions/Graded/`
(TYTAB-5); the graded-metatheorem capstone → `Typed/Metatheory/GradedMetatheory.lean`
(new). The `HasGradeOver R` engine is shipped in `Typed/Dimensions/`.

### 7.3 Decategorification — "a number is the shadow of a category" `[R]` {CSHD-* #1478-1484}

The FinSet-groupoid skeleton; `card` = decategorified cardinality; addition =
disjoint union, multiplication = product, decategorified; the semiring laws from
categorical isos (not `Nat` lemmas); the decategorification functor
`grade = π₀(mode)`; primes as ×-indecomposables (the inverse-categorification
frontier).

**Home** `Axis/Grade/Decategorification.lean` (new; the FinSet-groupoid + `card` +
the functor). Standalone; imported by the spectrum realization.

### 7.4 Equality = indistinguishability under graded observation `[C]` {EQ-OBSERVATION #1652, GRADED-ID #1651, OP3-SAMENESS #1439}

The full observation-lattice unification: SAP = SIP = SRP = NI = CT are one
construction (Conv / univalence / bisimulation / ctx-equiv / constant-time all
"same under graded observation"). Graded identity type / cost-of-transport =
identity as a resource (the HoTT × complexity unification).

**Home** the sameness-unification → `Typed/Metatheory/SamenessUnification.lean`
(ties the shipped `Axis/Mode/SamenessUnification.lean`); graded-Id → a row in
`Typed/Dimensions/` + `Core/Rewriting/RuleTables/`. Relational Σ-algebra candidate
in `Core/Metatheory/Reducibility/Candidates/`.

### 7.5 The quotient grade — axiom-free quotients as a spectrum cross-section `[design-locked 2026-07-02]` {EXT-2 #1371, EXT-3 #1372, EXT-6 #1375, EXT-7 #1376}

"Quotient" is not one type former; it is a **graded family** indexed by a product
of three grades FX already owns: **(mode-26 beneath↔alongside) × (δ truncation) ×
(decidability)**. The named tiers: *setoid* (beneath — the congruence carried as
judgment side-conditions, industrialized by the SR-DSL tables); *definable* (a
computable section/normal form makes the quotient a subtype with definitional
equality — quotient admissibility = word-problem solvability, so the `Polygraph/`
decider library IS the quotient toolkit); *observational* (`Id (quot R) (mk a)
(mk b) ↝ R a b` — `sound` as a computation rule, effectivity free, respect proofs
in SProp; metatheory bill payable against Pujet–Tabareau TT^obs); *classifying*
(δ ≥ 1 — the classifying type IS the quotient, proof-relevant identifications,
the combinatorics case, §12B.1). Collapse maps are theorems: **set quotient =
‖classifying quotient‖₀** (the CSHD-5 seam, `grade = π₀(mode)` applied to
quotients), and normalization collapses observational → definable when a section
exists. Along the ladder, computation and information run in OPPOSITE orders — a
Pareto pair, like time × space (§11.7). The **boldest mechanism**: a user
quotient = *extending the kernel's own presentation* (Conv is already the
quotient of RawTerm by the table) — rewrite rows + a convergence certificate
(Squier machinery) absorb the quotient into Conv (definitional tier); Id-rows
give the observational tier; deny-by-default via a QUOT admission table
mirroring TRANSP-ADMIT, the tier riding as a non-forgeable grade. The HOST never
forms quotients (`Quot.sound` stays banned; fib-5d's up-to-iso boundary is the
one permanent price, already paid).

**Home** the rows via EXT-2/3/6 in `Core/Rewriting/RuleTables/`; the definitional
tier through `Extension/` (EXT-7) + `Polygraph/` convergence certificates; the
admission table → `Typed/Dimensions/QuotientAdmission.lean` (new); the collapse
theorems tie `Axis/Grade/` (CSHD).

---

## 8. Domain VI — metatheory by universal property (dissolution & NbE)

**Home law.** These are typing-metatheorems (Q5) → `Typed/Metatheory/`, riding on
the reducibility substrate (Q4) → `Core/Metatheory/Reducibility/`. The DISSOLVE
arc's thesis: replace case-split metatheory with universal-property arguments.

### 8.1 The reducibility candidate as a Σ-monoid; FT = initial-algebra morphism `[C]` {DISSOLVE-SIG-ALGEBRA #1836}

The impredicative Tait candidate (`RawTerm→Prop`) is the ZF-strength residual (per
the audit); the dissolution is to present it as a Σ-monoid / relational algebra and
the Fundamental Theorem as the *unique initial-algebra morphism* — no per-former
case split. This is simultaneously the "categories over sets" refactor and the NbE
seed (§8.3).

**Home** `Core/Metatheory/Reducibility/Candidates/SigAlgebraCandidate.lean` (new;
the Σ-monoid candidate) + `Typed/Metatheory/Reducibility/Fundamental/` (the initial-
morphism FT). The generic FTGEN engine (shipped) is the reconciliation target
(BRIDGE-FTGEN-SCHEMA #1853).

### 8.2 The data fragment as one polynomial functor; codata as its dual `[C]` {DISSOLVE-POLY-DATA #1837, FRONTIER-COIND-DUAL #1870, FRONTIER-CONTAINER-OMEGA #1869}

The whole data fragment = ONE polynomial functor ⟹ ι-SR + recursor-SN proved once;
the codata/coinductive metatheory = the formal *dual* (proved by duality, no new
cases). The (∞,ω)-container calculus = higher-dimensional polynomial functors for
the higher cells.

**Home** `Core/Metatheory/Reducibility/PolynomialData.lean` (new) +
`Axis/Term/Codata/` (shipped codata) + the container calculus in
`Polygraph/OmegaCategory/ContainerOmega.lean` (the (∞,ω)-generic version, `[O]` at
full strength).

### 8.3 NbE-as-a-functor — the dissolver of the impredicative candidate `[C]` ★ {DISSOLVE-DECCONV-NBE #1842, FRONTIER-NBE-FUNCTOR-FULL #1873, NBE-* #1888-1909}

Build the semantic model *by construction* (no candidate-existential to quantify) —
this is what predicativizes the reducibility metatheory and gives decidable Conv
without rewriting-search or SMT. The full version: NbE-as-a-functor for the
multimodal + cubical kernel, one normalization per fibre. Reify arms: Σ
(surjective-pairing η), modal (μ◇→A η — the A1 negative-modality readback),
universe (carrying the def-univ type data), directed (Segal reify).

**Home** `Core/Rewriting/Normalize/NbE/` (shipped scaffold) + `Typed/Metatheory/Normalizer/`.
New modules: `NfNeClasses.lean` (the Nf/Ne/NfTy mutual normal forms), `ReifySigma.lean`,
`ReifyModal.lean`, `ReifyUniverse.lean`, `DecConvHybrid.lean` (reify ⊕ structural
Nf-equality — the hybrid decision, *not* OmegacE). Ties DISSOLVE-DECCONV-NBE.

### 8.4 FT + canonicity = the Artin-gluing section (STC) `[S/C]` {DISSOLVE-STC-FT #1839, context-11 [S]}

Synthetic Tait computability / Artin gluing: the fundamental theorem + canonicity =
the gluing section, once over the signature. Sterling's open/closed (`○`/`●`)
recollement is the STC substrate; U8 (§6.1) is its basic axiom. "Sconing is enough"
(BKS) is discharged zero-hypothesis on the closed fragment.

**Home** shipped in the top-level `STC/` + `Typed/Metatheory/Sconing/` +
`Core/Metatheory/Sconing/`. The generic gluing section → `Typed/Metatheory/Sconing/ArtinGluingFT.lean`.

### 8.5 Confluence via orthogonality; inversion as no-confusion `[C]` {DISSOLVE-CR-ORTHOGONAL #1851, DISSOLVE-INVERSION-INITIAL #1852}

Confluence once via orthogonality + residuals — no critical-pair enumeration, no
SMT. Inversion lemmas as the initial algebra's no-confusion — no per-former
inversion. Both are "prove-once" replacements for the shipped per-arm machinery.

**Home** `Core/Rewriting/Confluence/OrthogonalCR.lean` (new); the inversion-as-no-
confusion → `Typed/Engine/Union/` (replacing the shipped table-driven inversion,
TYTAB-INV-RETIRE was the first step).

### 8.6 Metatheory = the polygraphic resolution (S3) `[C]` {SCHEMA-META #1650, term-5 [S]}

The unifying thesis: SN = well-foundedness of the (Steiner loop-free / RPO) order;
CR = Squier confluence; SR = typing-preservation of the polygraph rewriting — the
(∞,ω) resolution's dimensions 0–2. Extend term-5's resolution to all four axes; the
honesty ledger (PROVEN/TARGET per theorem) IS the resolution's dimension-by-dimension
completion.

**Home** `Core/Metatheory/Resolution/` (new dir) — `PolygraphicResolution.lean` (the
four-axis resolution), reading the SN order from `Core/Metatheory/Ordinal/`
(§6/§9) and the Squier machinery from `Polygraph/OmegaCategory/`. This is the
design home for the "prove SN/CR/SR once over the parametric row-family" thesis.

### 8.7 The observational-Id table — one row family, three famous rows `[C]` ★ {EXT-3 #1372, EXT-4 #1373, NBE-FUNEXT #1909, OP3-SAMENESS #1439}

The single deepest tracker consolidation available: `Id at T ↝ T's native
sameness` is ONE parametric row family — Π ↝ pointwise (funext), universe ↝ Equiv
(definitional univalence), `quot R` ↝ R (quotient soundness + effectivity, §7.5),
Σ ↝ componentwise, data ↝ structural. **Funext, univalence, and quotient-`sound`
are three rows of one table**, not three features (the OTT/TT^obs design read
through FX's table discipline; the universe is the observational quotient of
codes by equivalence). This subsumes the tripled def-univalence encoding
(HOTT-4 ≡ EXT-4 ≡ FTGEN-5.6) and HOTT-2/3 under EXT-3, and is what OP3-SAMENESS
was groping toward. The per-row admission gate is the same SN/confluence
discipline as every iota row (DEFUNIV-SN's type-complexity measure is the shared
gate).

**Home** one `Core/Rewriting/RuleTables/ObservationalId/` table (new) replacing
the scattered rows; metatheory via the table-generic machinery + the TT^obs
transcription (normalization + canonicity + decidability WITH computing
quotients is proven there).

---

## 9. Domain VII — self-reference, reflection & the bootstrap

**Home law.** The reflection ladder is metatheory + profile (Q4/Q6) →
`Core/Metatheory/Reflection/` + `FXProfile/`; the self-formalization judgment (FX@n+1
⊢ metatheory(FX@n)) is a typing-level bootstrap → `Typed/SelfFormalize/`. **The
hinge:** self-formalization is free (checker = rules); soundness costs exactly one
Gödel-forced strength bump (the universe-strength flag).

### 9.1 The Gödel/Löb/Tarski walls (the tier boundaries) `[settled]`

Gödel-II sharp (Pudlák): no consistent r.e. theory interpreting Robinson Q proves
its own consistency; "interprets Q" = proves ×-totality = arms the diagonal lemma.
Tarski undefinability + Löb: reflective self-access is provability + partial/
stratified reflection only — never truth, never own-Con. The reachable
self-reference budget: local/uniform reflection for bounded formulas + Con of
strictly-weaker subtheories + cut-elimination of fragments.

**Home** documented in `Core/Metatheory/Reflection/GodelBoundary.lean` (the walls as
statements the ladder respects). No code climbs past them.

### 9.2 FX proves its own DISSOLVE metatheory (stratified) `[C]` ★ {FRONTIER-SELF-FORMALIZE #1874}

FX@(n+1) formalizes and proves-normalizing/consistent FX@n — exactly Lean4Lean
(n+1 universes ⊢ Con(n)) + MetaCoq (SN as the one added axiom). The cleanest T2;
never T1 at the same flag (Gödel-II). The `UniverseFlag` is literally the
metacircular ladder rung.

**Home** `Typed/SelfFormalize/` — new dir: `MetatheoryAsTypes.lean` (the DISSOLVE
metatheorems reflected as kernel types), `StratifiedProof.lean` (the n→n+1
interpretation). Reads the strength dial (§6.5) and the reflection ladder (§9.4).

### 9.3 The normalizer as an FX term, proven correct internally `[C at n+1 / T3 same-flag]` {NBE-SELF-REFLECT #1908}

The normalizer-as-a-term is T1 (a total function); soundness/completeness vs Conv
is structural; but *internal totality* of `normalize` for the full theory = internal
SN = Con-strength content, which at the *same* flag violates Gödel-II (T3), provable
at flag n+1 (T2).

**Home** `Typed/SelfFormalize/NormalizerReflected.lean`; the normalizer itself is in
`Core/Rewriting/Normalize/` + `Typed/Metatheory/Normalizer/`.

### 9.4 GLP ordinal analysis; the autonomous progression `[R first-of-kind / C the FX-own form]` ★ {OP7-GLP #1440, mode-23 [S]}

Mechanize Beklemishev's GLP ordinal analysis (worms → ε₀; worm well-ordering +
reduction = decidable-combinatorial). Base camp exists: Lean's
`FormalizedFormalLogic/Foundation` has a sorry-free Solovay arithmetical
completeness of GL. **The novel contribution (triple-confirmed unclaimed):** FX =
the first proof assistant whose strength dial is a **mechanized autonomous
progression** (Turing–Feferman) = the first machine-checked **ordinal analysis of a
theory** = (via worms) the first mechanized **GLP-based** ordinal analysis. FX
uniquely hosts it: the deny-by-default `ConsistencyStrength` dial = the autonomy
condition; the zero-axiom kernel = a hand-auditable climb; the shipped
RPO/multiset machinery = the SN-ordinal.

**Home** `Core/Metatheory/Reflection/GlpAlgebra.lean` (worms, the reflection
calculus RC/GLP) + `Core/Metatheory/Ordinal/` (the ordinal notations, reading the
Steiner loop-free order and the shipped `Normalization/Orders/`). The GLP modality
itself is shipped in `Axis/Mode/Provability.lean` (mode-23). Ties the strength dial
(§6.5).

### 9.5 THE-ONE-OBJECT / the R7 fixpoint `[T1 structural / O semantic]` {THE-ONE-OBJECT #1443, fib-13 #1591}

Structural: the `categorify ⊣ decategorify` fixpoint presented as one product-graded
self-indexed value (SIG-5 bi-initiality) — T1. Semantic reading (an internal
model/truth-predicate of FX in FX) — T3 (Tarski + Gödel-II). The wildest coherent
moonshot fuses this with §9.2 + §9.4: the kernel climbing its own GLP worm, height =
FX's own proof-theoretic ordinal — an unbounded machine-checked Gentzen ladder that
is its own ordinal analysis and the R7 fixpoint. T2 (Gödel forbids *closing*, but
each rung n+1⊢Con(n) is genuinely provable).

**Home** `Core/Fib/TheOneObject.lean` (the structural fixpoint; ties all four axes)
+ `Typed/SelfFormalize/` (the climbing ladder). The design is anchored in
`Axis/Mode/grade-mode-spectrum.md` §6/§7.

### 9.6 Self-extend & the discovery engine `[R orthogonal / C strength-increasing]` {SELF-EXTEND #1834, ENGINE-DISCOVERS #1833, SYNTH-* #1445-1446}

Orthogonal same-strength dimension: the shipped add-a-row mechanism (append rows →
`WfIotaTable` orthogonality → critical-pair admission) — T1, zero new proofs.
Strength-increasing: needs the autonomy certificate (gate on reflection rank, §6.5)
— T2. The discovery loop (Conv-deduped FactDAG, FX0 verifier, Hardness scorer):
architecture specifiable now, driven on `L` (the certified upper bound, computable)
never `K` (uncomputable Chaitin). SYNTH-FUNCTOR (doctrine → kernel-as-value) = T1;
SYNTH-OBSTRUCT (a feature with no admissible classifying extension) = T2.

**Home** self-extend → `Extension/` (the shipped `ProfileExtension` + admission) +
`FXProfile/`; the discovery engine spec → `Typed/SelfFormalize/DiscoveryEngine.lean`
(the loop spec + open-endedness statement); SYNTH → `ProfileFibration/`.

---

## 10. Domain VIII — constructivity & foundations (ZF-strength)

**Home law.** This domain is a *discipline* over the whole tree, not a directory.
Its findings constrain where things go (categories-over-sets, Conv-over-`=`) and
its constructive-model-theory pieces live in `Polygraph/SemiModel/` (§3.9). The
audit twins in `FX1PolyAudit/` are its executable enforcement.

### 10.1 The ZF-strength audit — the one residual `[audited]` {project_zf_strength_audit}

Six-axis verdict: the object theory is predicatively clean; the *one* residual is
the impredicative Tait candidate (`RawTerm→Prop`) + `limax`. Powerset/Replacement/
Infinity are bounded (Tarski codes, ℕ-fuel stratification, no completed totalities);
Choice/Foundation/Extensionality are disciplined (canonical-rep-via-determinism,
`Acc`-not-`WellFounded.fix`, Conv-not-`=`). The residual is dissolved by NbE (§8.3)
— which localizes the impredicativity (impredicative-abstract, predicative-`Acc`-
concrete, per §3.3).

**Home** the discipline is enforced across the tree; the audit gates are in
`FX1PolyAudit/`. The dissolution target is `Core/Rewriting/Normalize/NbE/` (§8.3).

### 10.2 Categories over sets — the refactor direction `[R]` {DISSOLVE-DISPLAY-SUBST #1838}

subset/predicate → display map (mono/fibration), not `X→Prop`; membership `∈` →
generalized element (a morphism into), not `List.Mem`; set-equality `=` on
types/cells → `Conv`/iso; "pick a witness" → canonical structural choice; universe →
classifier/generic-object; type-family-by-recursion → Tarski code + fixed decode.

**Home** substitution/weakening/validity by the display fibration's cartesian lift →
`Core/Fib/DisplaySubstitution.lean` (DISSOLVE-DISPLAY-SUBST); the `List.Mem` →
generalized-element refactor touches `Typed/Engine/Union/` (the premise families) and
`Core/Rewriting/Reduction/Step/` (rule-family membership).

### 10.3 Constructive saturation & effective model theory `[R core]` {§3.9}

Covered under `Polygraph/SemiModel/` (§3.9). The saturation theorem is the
constructive substrate for the polygraph confluence + the semi-model core; the
homotopy-language framing (§3.10) is its semantic mirror.

---

## 11. Domain IX — complexity & meta-algorithmics

**Home law.** These are graded-dimension artifacts (Q5) → `Typed/Dimensions/Cost/`
(the optimization polygraph) + a new `Typed/Complexity/` (the lower-bound library).
**The type-A (complexity) / type-B (rewriting) firewall is the hard rule**: a
type-B result (optimal-among-the-certified-basis) must NEVER be relabeled type-A
(optimal-among-all-algorithms = MCSP / P-vs-NP).

### 11.1 The type-A/type-B firewall `[settled]` ★ {VISION-LEDGER #1274, DEPTH-LEDGER #1653}

type-A = complexity (circuit/time): unconditional+general = T3 (P-vs-NP-adjacent);
conditional (SETH) or restricted-model (monotone/AC⁰/resolution/determinantal) = T1.
type-B = rewriting/proof-theoretic (Squier homology, "optimal among certified
basis", FDT, Lévy-neededness): theorems about the FX polygraph, decidable for the
finite convergent fragment = T1. The firewall is a *typing rule*, carried by the
Trust(dim 9) + Cost(dim 13) grades.

**Home** `Typed/Complexity/Firewall.lean` (new; the type-A/type-B tag as a
propagated grade) — the spine of the epistemic-complexity library.

### 11.2 Machine-checked barriers-as-theorems `[R]` ★ {LB-BARRIERS #1441}

The three barriers as Lean theorems: relativization (Baker–Gill–Solovay), natural
proofs (Razborov–Rudich, conditional on exp-hard PRFs), algebrization (Aaronson–
Wigderson). Each *is* a theorem. **No mechanized barrier library exists** — the
strongest clean first-of-kind in this domain.

**Home** `Typed/Complexity/Barriers/` — new: `Relativization.lean`,
`NaturalProofs.lean`, `Algebrization.lean`. Standalone; the honest P≠NP frame.

### 11.3 Lower bounds — the tiered ladder `[R conditional/restricted, O unconditional]` {LB-0..3, LB-DERIVED/ALGORITHMIC}

LB-0 (Mignon–Ressayre permanent, unconditional but quadratic/restricted) = T1;
LB-1 (OV→Edit-Distance under SETH) = T1-conditional; LB-DERIVED (Razborov monotone /
Håstad AC⁰ / Haken resolution) = T1-restricted-model (they provably don't lift *because*
too weak to hold PRFs — that non-lifting IS the barrier); LB-2 (KW→depth): monotone =
T1, non-monotone super-log = T3 (P vs NC¹, KRW open); LB-ALGORITHMIC (Williams): the
implication = T1, a *new* separation = T3. Unconditional general circuit bounds /
P-vs-NP / NEXP-vs-TC⁰ / MCSP = **T3, field-open**.

**Home** `Typed/Complexity/LowerBounds/` — new: `MignonRessayre.lean`, `SethReductions.lean`,
`RestrictedModel.lean` (monotone/AC⁰/resolution), `KarchmerWigderson.lean`,
`AlgorithmicMethod.lean`. Each bound carries LB-CERT (§11.6). T3 items are documented
walls, never coded.

### 11.4 The two ★ novel bridges `[R / C]` {CNOS-3 #1470, COPT-6 #1463, LB-NATURAL-PARAM #1447}

**No-search = Squier-H₁ / optimality = orthogonality: GENUINE THEOREM (T1)**, not a
category error (Squier FDT + Guiraud–Malbos + Huet–Lévy). Three binding conditions:
(i) type-B — scoped to the certified basis; (ii) pin the degree — the clean statement
is homotopical (FDT/contractibility), "H₁" must be a precise complex; (iii) measure
in the dim-13 **cost grade**, not reduction steps (Lévy-optimal ≠ wall-clock).
**Natural-proofs = internal parametricity: T2 CONJECTURE** with a category-error
trap — genuine *only* as a negative barrier-transfer ("a parametric-definable
separator is RR-natural, hence blocked under exp-hard PRFs"); the load-bearing
unproven lemma is internal-definability ⇒ RR-constructivity; the **forbidden**
direction is "parametricity proves P≠NP internally" (self-defeating, T3-as-T1).

**Home** the Squier-H₁ theorem → `Typed/Dimensions/Cost/NoSearchHomology.lean` +
`Core/Metatheory/Resolution/` (the H₁ of the optimization polygraph); optimality =
orthogonality → `Typed/Dimensions/Cost/OptimalityOrthogonality.lean`. The
natural-proofs bridge → `Typed/Complexity/NaturalParametricity.lean` (stated over
transpension generically — `gen_param` is its affine instance, superseded per §11.9.1.4).

### 11.5 The optimization polygraph (cost as dim-3 rewriting) `[R]` {COPT-* #1457-1466, DIM3-TAB-* #1381-1382, OPT-* }

Optimization schemas as dim-3 rules over `StepOver` with cost certificates: the
`costImprovementTable` (oriented cost-decreasing rows), the orthogonality certificate,
cost-RPO termination, Newman ⇒ unique cost-NF, `IsCostOptimal` as a decidable
orthogonality predicate, the optimizer semantics-preserving by construction. Showcases:
Fibonacci exp→linear (OPT-7), Bird–Meertens MSS cubic→linear (OPT-MSS).

**Home** shipped substrate in `Typed/Dimensions/Cost/` + `Core/Rewriting/RuleTables/`.
New: `Typed/Dimensions/Cost/OptimizationPolygraph.lean` (the dim-3 table + cost-RPO),
`CostNormalForm.lean`, the showcases in `Typed/Corpus/`.

### 11.6 Optimality certificates & algorithmic information `[R]` {LB-CERT #1417, OAIT-* #1258-1260, OHARD-1 #1262}

The triple optimality certificate {upper bound, lower bound, epistemic tag} — the
operationalization of the honesty scale. Algorithmic information: FX0 as a fixed
K-machine (kills the additive constant); bounded K-minimal search (decidable on a
size-bounded Conv-class — resource-K, not uncomputable K); K- vs cost-minimality
Pareto. The Hardness instrument (Bennett logical depth D, bridge rank B, N) = T1; the
Chaitin abstraction-gain A = T2/open. ISO-CONV (graph iso as decidable Conv) = T1
decidability *only* (poly-time GI is a *different* open problem).

**Home** `Typed/Complexity/Certificate.lean` (LB-CERT); OAIT → `Typed/Complexity/AlgorithmicInfo.lean`;
the certificate carries the tier as a Trust(dim 9) + Cost(dim 13) grade — the novel
first-of-kind epistemic-complexity library.

### 11.7 Vector cost, pebbling & zero-copy — the compiler's Pareto substrate `[R]` ★ {COST-SPACETRADE #1267, PHYS-LANDAUER #1453, LEARN-AD #1454}

Cost is not a scalar: Complexity (dim 13) × Space (dim 15) is a PRODUCT semiring,
so the optimizer's target is a **Pareto normal form**, and "memory↔compute trades
must not be awfully asymmetric" is theorem-shaped: admissible rewrites are gated
by a bounded exchange-rate region whose boundary is the **pebbling cliff**
(Hopcroft–Paul–Valiant: the always-available log-space trade; Paul–Tarjan-family
DAGs: superpolynomial time blowup below a space threshold — both consumable
lower-bound certificates on finite DAGs). Black pebbling = rematerialization
(Griewank's REVOLVE = the certified-optimal checkpoint schedule — the exact dual
of OPT-7's memoization); red-blue pebbling (Hong–Kung) = data-movement bounds,
the correct two-level cost model (why FLOP-for-memory trades win wall-clock).
**Reversible pebbling (Bennett) fuses #1453 + #1267**: erasing a pebble =
Landauer dissipation, so the full frontier is a THREE-objective Pareto — time ×
space × erasure — and the erasure grade becomes a third cost axis (no certified
compiler has an energy axis). **Zero-copy is the operational shadow of
linearity**: in the cost-NF of a well-graded program a copy survives iff the
usage grade is genuinely ω — every `memcpy` in the optimum is a *certificate of
real sharing*, and "bloat" gets a definition (allocation/copies above the
grade-forced lower bound; C++ bloat = the price of missing proofs). The two
Pareto endpoints are ALREADY shipped as semantics rungs: term-9 (Lévy/sharing
graphs, max-share) and term-23 (GoI token machine, store-nothing); the certified
optimizer's job is the interior point per target. Also: OPT-56's dim-3 layer is
not greenfield — term-12 (standardization) and term-9 (permutation equivalence)
ARE the 3-cell layer under other names; the new content starts at dim 4.
Conjectures: X1 (memoization ⊣ rematerialization; Pareto frontier = fixed points
of the induced (co)monad) and X2 (torsion H₁ = irreversible search, §3.1).
**Canonicalization**: COPT-0..9 is the canonical optimization-table arc; OPT-2..6
are superseded encodings (keep the OPT showcases 7/MSS/8/CELL/56/ENGINE).

**Home** `Typed/Dimensions/Cost/ParetoNormalForm.lean` + `PebbleGames.lean` (new;
black/red-blue/reversible over finite DAGs) + `InPlaceTheorem.lean` (copy ⟺
ω-certificate, stated at extraction/fib-16); the REVOLVE showcase → `Typed/Corpus/`.

---

## 12. Domain X — the four-axis fibration & the telos (`Core/Fib/`)

**Home law.** `Core/Fib/` is the *only* place the four axes meet (Q4). Everything
here glues Axis/{Term,Type,Context,Mode} into the one kernel. The fib-* arc is the
assembly; THE-ONE-OBJECT is its fixpoint.

### 12.1 The display fibration & the universe reflection `[S/in-flight]` {fib-1/2}

fib-1: types fibred over contexts (the display fibration; `DisplayMapDecidableFibration`,
`TypingContext.cons` = context-extension Γ.A, the fibred-Π right adjoint). fib-2: the
El universe reflection gluing term and type (shipped; `StandaloneTarskiUniverse.Code
≃ gen_universeCode`, the axis decode/El).

**Home** `Core/Fib/` — shipped `fib-1*`, `fib-2*` files (`ContextDisplayPi.lean`,
`DisplayFibre.lean`, `UniverseElDecode.lean`, `UniverseCodeBridge.lean`).

### 12.2 Everything ⊣ mode — the MTT fibration `[in-flight]` ★ {fib-3 #1581}

The keystone: the whole kernel fibred over the mode base; Gratzer's "decidable Conv =
decidable mode theory." Realized via the A1 lock (§5.3) pinned to a real mode-12
unpointable multiplier, `ObligationModality → ModalityPath`, the judgment indexed by
`ModalityPath`. The two mode-side decidability gates are the remaining prereq; the
walking-equivalence polygraph (§3.5) supplies the SN precedence.

**Home** `Core/Fib/FibrationArchitecture.lean` + the fib-3 files; consumes
`Polygraph/WalkingEquivalence/` + `Axis/Mode/ModeOmega`.

### 12.3 Cross-axis coherence, bi-initiality, joint canonicity `[in-flight/C]` {fib-4/5/6/7/8}

fib-4: transpension recovers the zoo across all four axes (cross-axis right-adjoint
coherence). fib-5: the fibred kernel is the bi-initial model of its presentation
(the syntactic model from (fxSignature, fxTypingBundle, Conv); weak up-to-iso
bi-initiality — the strict version is off-limits, needs Quot.sound/funext). fib-6:
the four-axis unified sconing (joint canonicity/normalization). fib-7: joint
decidable Conv (the **O-NORM** frontier — per-fragment [S], joint [O]). fib-8: the
cell substrate IS the four glued ω-categories (the Gray-tensor 4-way coherence).

**Home** `Core/Fib/` — the fib-4..8 files; fib-8 consumes `Polygraph/TwoCategory/GrayCategory`.
O-NORM is the honest open frontier, marked.

### 12.4 Obstruction cohomology & the no-go `[R decidable / O]` {fib-9/10, NOGO-1 #1444, O-OBSTRUCT #1434}

fib-9: the 21-dim periodic table of admissible type theories (obstruction cohomology).
fib-10 / NOGO-1: the first machine-checked type-theory NO-GO — a feature-row
combination provably rejected (a certified non-joinable critical-pair set = a
certified obstruction; or mechanize a known no-go, e.g. Fire Triangle). The FX
conjecture "non-sharp ι ⟺ no 𝒰_ω:𝒰_ω" is T2 (needs the uniform O-OBSTRUCT theorem).

**Home** `Core/Fib/ObstructionCohomology.lean` + `Core/Fib/NoGo.lean` (NOGO-1); the
decidable combination-predicate reads `Typed/Dimensions/AxisObligation/` (CFND). The
H² semantic obstruction is `[O]`.

### 12.5 The megaapex QIIT & extraction `[C/O]` {fib-11/12/13/15/16, FRONTIER-QIIT-PRESENTATION #1865}

fib-11: syntheticization as a 2-functor doctrine → kernel-as-value. fib-12/QIIT: the
kernel as a presented transpension-powered QIIT, metatheory = its initiality (present,
don't declare — Lean rejects intrinsic II; Allais–McBride extrinsic; full
self-application via internal-parametricity initiality, POPL24 blueprint). fib-13: **THE-ONE-OBJECT**
— FX as the single presented (∞,ω)-polygraph. fib-15: model existence/soundness
(the consistency-via-a-model leg). fib-16: extraction correctness (the fibred kernel
→ executable, the simulation).

**Home** `Core/Fib/` — fib-11..13; the QIIT presentation ties `Polygraph/Homotopy/`
(the clan/hyperdoctrine) + `Axis/Grade/` (the product-graded self-indexing). fib-13
is the telos; fib-16 extraction → the LowX pipeline (`IFACE-EXTRACTION #1850`, a
dimension-generic erasure functor).

---

## 12A. Domain XI — certificate mathematics (exact linear algebra & the Moscow problem)

**Home law.** Per-instance certificates of open conjectures are corpus artifacts
(Q5) → `Typed/Corpus/Certificates/`; the exact-arithmetic engine they share with
Steiner homology and matroid-Hodge is a zero-dep library → `ComputerAlgebra/` (new
top-level, `Init`-only: `IntMatrix`, `SmithNormalForm`, `RatSturm`,
`SosCertificate`, `PerronFrobenius`). One library, three-plus payoffs.

### 12A.1 The Goreinov–Tyrtyshnikov–Zamarashkin ("Moscow") conjecture `[R instances / O general]` ★

Statement (1997): every real n×k matrix with orthonormal columns has a k×k
submatrix Q̂ with ‖Q̂⁻¹‖₂ ≤ √n (⟺ σ_k(Q̂) ≥ 1/√n ⟺ every k-subspace of ℝⁿ lies
within principal angle arccos(1/√n) of a coordinate subspace; tight). Status:
n×2 real PROVEN (Sengupta–Pautov 2026, crux = Perron–Frobenius) + equality
criteria and complex asymptotics (Nesterenko: extremals = 3-cluster rows /
regular tetrahedra); **OPEN for all 2 < k < n−1**. Why it fits the kernel: every
fixed (n,k) instance is one first-order sentence over ℝ — SOS/Positivstellensatz
+ Sturm certificates check in exact rational arithmetic (Init-only, zero-axiom);
the compact ∀-side goes by ε-net + Lipschitz + per-point certificate (the
Flyspeck pattern; SEARCH-1 #1269 is the finite-∀ toolkit); extremals are finite
clean configurations. The ladder: **MOSCOW-CERT** [R] (certificate factory for
fixed instances — kernel-checked instances of a live open conjecture) →
**MOSCOW-N2** [R, serious] (mechanize Sengupta–Pautov — the FIRST machine-checked
case; zero-axiom Perron–Frobenius as the reusable brick) → **MOSCOW-NET** [R/C]
(Flyspeck-style full verification of small (n,k) beyond k=2 — e.g. a first
machine proof of (5,3)) → **INTERLACE** [R toolkit / O application] (mechanize
interlacing families / real-stability — the Kadison–Singer toolkit;
real-rootedness is Sturm-checkable; no mechanization known — verify before
claiming). Conjecture **X5**: extremal configurations for ALL (n,k) are
finite-subgroup orbit frames `[C — extrapolates the two proven equality criteria;
verify not folklore]`. Payoff grade: certified skeleton/low-rank error bounds =
a Precision (dim 14) contract — kernel-checked compression guarantees.

### 12A.2 Same-shape targets & the selection criterion `[R slices / O uniformity]`

Crouzeix's conjecture (fixed dim/degree = RCF/SOS-certifiable; constant 2 open),
per-dimension Grothendieck-constant bounds, algorithmic Kadison–Singer (making
MSS constructive is type-B-shaped: certified search over interlacing witnesses).
**Selection criterion, stated once:** pick problems whose fixed slices are
certificate-decidable AND whose uniformity frontier has a geometric/algebraic
handle — the kernel eats instances, humans+LLM attack uniformity. Erdős-style
pure combinatorics fails the first clause *informatively* (certificates carry no
structure toward uniformity). Workflow lesson from the n×2 proof itself: the
authors' loop WAS ENGINE-DISCOVERS with human verification as the bottleneck
(the LLM-suggested Perron–Frobenius nearly discarded as hallucination; a year of
dead-end checking) — the kernel's honest pitch is collapsing "is this lead
real?" to a build and making every failed attempt a durable lemma.

---

## 12B. Domain XII — the synthetic discrete engine & condensed/chromatic shadows

**Home law.** Combinatorics-without-walking assembles from tracker parts:
`Axis/Grade/` (CSHD groupoid cardinality) + ISO-CONV #1452 + type-16 polynomial
functors/species + SEARCH-1 #1269 + DPROP-1 #1268, plus a new `Typed/Corpus/Discrete/`.
The condensed/chromatic entries are *shadows*: reachable low rungs of frontier
fields, honestly tiered; the full theories stay `[O]`.

### 12B.1 The synthetic discrete engine `[R assembly / C conjectures]` ★

The zero-axiom discipline FORCES the synthetic route: `Quot.sound` is banned, so
set-level orbit-counting doesn't exist — but univalent counting doesn't need it
(the classifying type IS the quotient; §7.5 Tier C). The walking-killers:
univalent counting over BΣₙ (unlabeled structures = Σ over the classifier;
Burnside/Polya = groupoid cardinality of action groupoids); species as
polynomial functors (Joyal; derivative = one-hole contexts = McBride's
derivative of a type); exodromy (constructible sheaves on a finite poset =
functors P → Vect — no open-set walking); tt-geometry (classification = the
lattice of thick ideals); combinatorial Hodge (AHK log-concavity = per-matroid
finite exact linear algebra — certificates on the `ComputerAlgebra/` substrate).
Conjecture register **C1–C6**: C1 quotient-free Polya (cycle-index count as
homotopy cardinality, zero-axiom, no quotients — first-of-kind mechanization);
C2 cardinality = 1-semiadditivity (`card` exists ⟺ norm maps invert over ℚ;
ties X7); C3 light-condensed as a codata mode (§12B.2); C4 the kernel's own
Balmer spectrum (thick-ideal lattice of the finite-type ⊗=× fragment — "FX has
chromatic height 0"; either answer pays, refutation = a new chromatic invariant
of a type theory, and fib-9's periodic table becomes the Priestley dual of an
obstruction lattice); C5 matroid-Hodge certificates [R per-instance]; C6
bijective proofs as lifting problems (a bijective proof = a 2-cell above the
decategorified identity; natural bijection = functorial lift; obstructions
calibrated against Pak's bijection-complexity program).

### 12B.2 Condensed / pyknotic shadow `[C shadow / O field]`

Field targets (believed): analytic stacks + the six-functor formalism
everywhere, geometrized local Langlands (Fargues–Scholze), liquid/solid
functional analysis (the Liquid Tensor Experiment is ALREADY mechanized in Lean
— the precedent that this field formalizes), Efimov K-theory, LIGHT condensed
(countable data — Scholze's own tameness move), exodromy (Barwick–Glasman–Haine).
FX reading: solidification/liquidification = idempotent monads = Rijke–Shulman
reflective modalities (type-10); discrete ⊣ underlying = the shipped cohesion
edge (ZOO-COHESION-EDGE #1929; COHESION-O4 #1270 is the survey slot); a light
profinite set = an M-type over decidable FinSet (type-3, shipped) with
bisimulation-as-Conv; FORCE-MOD #1450 supplies the presheaf/sheafification
substrate. Honest falsifier for C3: sheafification may demand impredicativity —
that failure would itself be a NOGO-style publishable result.

### 12B.3 Chromatic shadow `[C height ≤ 1 / O height ≥ 2]`

Field state (post-2023): telescope conjecture DISPROVED (Burklund–Hahn–Levy–
Schlank; the gap now measured by algebraic K-theory), redshift PROVEN in bulk,
chromatic splitting open, higher semiadditivity/ambidexterity (Carmeli–Schlank–
Yanovski) the organizing principle, chromatic Nullstellensatz. FX owns the
elementary shadow: 1-semiadditivity over ℚ = groupoid cardinality well-defined
(CSHD; π-finite types are definable) — "semiadditive height" enters as a graded
modality with heights 0–1 computable, ≥ 2 flagged `[O]`. Conjecture **X7**: the
usage semiring `{0, 1, ω}` measures the *failure of ambidexterity* (linearity =
the height-(−1) obstruction) — "chromatic height of a resource discipline"
becomes definable. Conjecture **X6** (wild; K₀-shadow first): the rank invariant
of K₀ of the rung-n certificate category (exactness from cut-elimination) is the
proof-theoretic ordinal, and categorifying theory-of-proofs raises the
reflection rank by exactly one — "Gödel = redshift" `[O full / C at K₀]`.
Shared substrate for XII.2 + XII.3: Stone-type duality — ONE codata brick
(pro-objects over decidable finite posets, bisimulation as Conv) is the entry to
both condensed sites and Balmer/Priestley spectra.

---

## 13. The dependency DAG (frontier modules)

```
ComputerAlgebra/ (Init only)  ⟶  Polygraph/  (Init, + ComputerAlgebra for Steiner homology)
  OmegacE ─┐
  Category ─┼─ TwoCategory ─ Marked ─ Complicial
  OmegaCategory(Squier,FreeStrictOmega) ─ Invertibility
  Steiner ──────────────┐        (⊕ Computad ⊕ WalkingEquivalence ⊕ SemiModel ⊕ Homotopy)
        │               │
        ▼               ▼
Axis/  Term ── Type(Level,Universe,Interval,Strength) ── Context ── Mode(GradeAlgebra,Cohesion,Transp,A1,Lnl,Galois)
        └──────────────── Fibrancy ◄── (imported by all four axes) ──────────────┘
        └──────────────── Grade (Spectrum, Decategorification) ◄── Mode.GradeAlgebra
                                        │
                                        ▼
Core/   Substrate(Cell,Cost,Profile,Semantics,Univalence)
        Rewriting(RuleTables,Reduction,Confluence,Normalize/NbE,Word)
        Metatheory(Reducibility,Normalization,Ordinal,Reflection,Resolution,Sconing,Canonicity)
        Fib(fib-1..16, TheOneObject)   ◄── the ONLY four-axis meeting point
                                        │
                                        ▼
Typed/  Engine(Union,tables) ── Metatheory(SR,FT,Denote,Normalizer,Sconing,Graded)
        Dimensions(Cost/OptimizationPolygraph, Graded, Parametricity)
        Rott ── Complexity(Firewall,Barriers,LowerBounds,Certificate) ── SelfFormalize
                                        │
                                        ▼
FXProfile / ProfileFibration / Extension   (profiles, strength flags, admissible extensions)
```
Rule: an arrow means *may-import*. `Core/Fib/` is downstream of all four Axis axes
and of `Polygraph/`; `Typed/` is downstream of `Core/`; the profile layer is the
sink. `FX1PolyAudit/` mirrors every path with `#assert_no_axioms` twins.

---

## 14. The new-modules index (flat)

| Module (proposed) | Domain | Tier | Home |
|---|---|---|---|
| Steiner/* (ADC, adjunction, coords, loop-free order, Gray tensor) | I | R★ | `Polygraph/Steiner/` |
| FreeStrictOmegaMonad | I | R/O | `Polygraph/OmegaCategory/` |
| Complicial/{Horn,StreetNerve} | I | R | `Polygraph/Complicial/` |
| WalkingEquivalence/* + DecidableWalkingWord | I | R | `Polygraph/WalkingEquivalence/` |
| SemiModel/{FibrationCategory,EnrichedWFS,Saturation} | I | R/O | `Polygraph/SemiModel/` |
| Computad/* (re-home FreeTwoCell, signature-generic) | I | R | `Polygraph/Computad/` |
| Homotopy/{HomotopyLanguage,ClanHyperdoctrine} | I/VIII | C | `Polygraph/Homotopy/` |
| Interval/{IntervalTheory,Affine,Directed,Kan,ShapeProduct} | II | R | `Axis/Type/Interval/` |
| MultigradeUniverse, CategoricalUnivalence, GlueRealignment | II/IV | C/R | `Axis/Type/Universe/` |
| Rott/{Relativity,SrpRows,ObservationalDsl} | II | R | `Typed/Rott/` |
| DefunivMeasure | II | C | `Core/Metatheory/Normalization/StrongNorm/` |
| DimensionLockAdjoint, NegativeModality | III | R | `Axis/Context/`, `Axis/Type/` |
| LnlDoctrine, GaloisModality, ForcingModality, TranspensionAdmission | III | R/C | `Axis/Mode/` |
| MahloUniverse | IV | R | `Axis/Type/Universe/` |
| Strength/{StrengthDial,ReflectionRankCertificate} | IV | R/C | `Axis/Type/Strength/` |
| Grade/{Spectrum,Decategorification} | V | C/R | `Axis/Grade/` |
| GradedMetatheory, SamenessUnification | V | C | `Typed/Metatheory/` |
| SigAlgebraCandidate, PolynomialData | VI | C | `Core/Metatheory/Reducibility/` |
| NbE reify arms (Sigma,Modal,Universe,Directed), DecConvHybrid | VI | C | `Core/Rewriting/Normalize/NbE/` |
| Resolution/PolygraphicResolution | VI | C | `Core/Metatheory/Resolution/` |
| ArtinGluingFT, OrthogonalCR | VI | C | `Typed/Metatheory/Sconing/`, `Core/Rewriting/Confluence/` |
| Reflection/{GodelBoundary,GlpAlgebra} | VII | R/C | `Core/Metatheory/Reflection/` |
| Ordinal/* (notations, Steiner-order SN) | VII | R/C | `Core/Metatheory/Ordinal/` |
| SelfFormalize/{MetatheoryAsTypes,StratifiedProof,NormalizerReflected,DiscoveryEngine} | VII | C | `Typed/SelfFormalize/` |
| Complexity/{Firewall,Barriers/*,LowerBounds/*,Certificate,AlgorithmicInfo,NaturalParametricity} | IX | R/C/O | `Typed/Complexity/` |
| Cost/{OptimizationPolygraph,CostNormalForm,NoSearchHomology,OptimalityOrthogonality} | IX | R | `Typed/Dimensions/Cost/` |
| Fib/{TheOneObject,ObstructionCohomology,NoGo,DisplaySubstitution} | X | S/C/R | `Core/Fib/` |
| ComputerAlgebra/{Number,LinearAlgebra,Polynomial,Positivity} | XI | S seed/R★ | `ComputerAlgebra/` |
| Steiner homology via SNF (H₁/H₂ + torsion) | I/IX | R | `Polygraph/Steiner/` + `ComputerAlgebra/` |
| Certificates/{MoscowInstance,MoscowNbyTwo,Interlacing} | XI | R/C | `Typed/Corpus/Certificates/` |
| Discrete/{UnivalentCount,Species,BalmerSpectrum} | XII | R/C | `Typed/Corpus/Discrete/` + `Axis/Grade/` |
| Cost/{ParetoNormalForm,PebbleGames,InPlaceTheorem} | IX | R | `Typed/Dimensions/Cost/` |
| ObservationalId table (funext/univalence/quot as rows) | VI | C★ | `Core/Rewriting/RuleTables/ObservationalId/` |
| QuotientAdmission (the tier grade) | V | R/C | `Typed/Dimensions/QuotientAdmission.lean` |

---

## 15. Open-problems register (genuinely open in the field)

FX can *contribute* to these, never *assume* them. Each is a wall the tier
discipline forbids crossing silently.

1. **Simpson's conjecture** & coherence of weak (∞,ω) above dim 3 (§3.7). `[O]`
2. **A constructive theory of ∞-categories** (Gambino–Henry's own flag) (§3.9). `[O]`
3. **Kan/hcomp filling undecidable** (= f.p.-group word problem) — a *proven* wall
   that forces per-fragment decidability (§4.7, §3.8). `[O — proven wall]`
4. **Full Segal directed-univalence computational model** (§4.6). `[O]`
5. **Chromatic / motivic height** — no synthetic internalization exists (§4.8). `[O]`
6. **Consistency of Reinhardt / super-Reinhardt / Berkeley under ZF** — leaning
   possibly-inconsistent (§6.4). `[O]`
7. **Ordinal analysis of full Z₂ / ZFC**; predicative Mahlo (§6.3, §9.4). `[O]`
8. **P vs NP**, P vs NC¹ (KRW), NEXP vs TC⁰, **MCSP**, poly-time GI (§11.3, §11.6). `[O]`
9. **HoTT autophagy** (a type theory formalizing itself with symmetry) (§9). `[O]`
10. **Same-flag self-consistency / internal truth-predicate** (Gödel-II/Tarski) (§9.1). `[O]`
11. **The Goreinov–Tyrtyshnikov–Zamarashkin conjecture** for 2 < k < n−1 (§12A.1). `[O]`

**FX-specific conjectures** (T2 — real new results if proven):

- The **resolution-height = proof-theoretic-ordinal** bridge (§8.6, §9.4).
- **non-sharp-ι ⟺ no-𝒰_ω:𝒰_ω** (§12.4).
- **natural-proofs = internal-parametricity** — the definability⇒constructivity
  lemma (§11.4).
- **optimality = orthogonality** basis-completeness (§11.4).
- The **GLP-univ bridge** as a theorem (§6.5, §9.4).
- **Simpson-for-FX**: the decidable-convergent-presentation semistrictification
  fragment (§3.7).

**The X-register (2026-07-02, bold conjectures — honesty-tagged):**

- **X1** memoization ⊣ rematerialization; the time×space Pareto frontier = fixed
  points of the induced (co)monad; the asymmetry cliff = failure of enriched
  boundedness (§11.7). `[C]`
- **X2** torsion H₁ of a cost-oriented ℤ-Squier complex = cost-neutral,
  erasure-positive strategy monodromy — homology detecting thermodynamically
  irreversible search (§3.1, §11.7). `[C→O; verify literature]`
- **X3** THE-ONE-OBJECT = terminal coalgebra of `categorify`; self-formalization
  (#1874) = coinduction on it — fib-13 as a universal property. `[C]`
- **X4** the FPₙ decidability ladder: the decision-method hierarchy (vector-eq <
  convergent < completion < ad-hoc < undecidable) graded by homological
  finiteness, generalizing Squier's FP₃/FDT one dimension per method. `[C; check
  Guiraud–Malbos FDTₙ]`
- **X5** Moscow extremals are group frames (§12A.1). `[C; verify not folklore]`
- **X6** Gödel = redshift at K₀ (§12B.3). `[O full / C at K₀]`
- **X7** ambidexterity = the usage grade (§12B.3). `[C; novel framing]`

**The C-register (discrete engine, §12B.1):** C1 quotient-free Polya · C2
cardinality = 1-semiadditivity · C3 light-condensed as a codata mode · C4 the
kernel's Balmer spectrum · C5 matroid-Hodge certificates · C6 bijective proofs
as lifting problems.

---

## 16. Honesty rails — the tier discipline made mechanical

The rails below are not prose caveats; they are the *design law* that makes FX's
frontier contribution real. Each is enforced by a grade the kernel propagates.

1. **The two ceilings never merge.** Computational content (~external Mahlo, where
   FX lives, choice-irrelevant) is distinct from consistency flags (arbitrarily
   high, choice-relevant only at the top). A strength flag is kernel-*proven* to add
   no canonicity before it may be granted; the grant gates on a reflection-rank
   certificate, not ordinal height. (§6, §9.4)
2. **The type-A/type-B firewall is a typing rule.** A rewriting-optimality result
   (type-B, basis-relative, T1) may never be relabeled a complexity lower bound
   (type-A, all-algorithms, T3). Police it at four places: unconditional general
   circuit bounds, class separations, poly-time MCSP/GI, and — most insidiously —
   any type-B result wearing a type-A name. (§11)
3. **Self-formalization is free; soundness costs one Gödel-forced flag.** No rung
   proves its own Con; the ladder is unbounded, not closable. Incompleteness is
   *generative* (the supply of new problems never runs dry), not a wall. (§9)
4. **Per-fragment, not joint.** Decidable Conv, canonicity, and SN are per-fragment
   results; the joint O-NORM statement is open and Kan-undecidability *forces* it.
   Never advertise a complete hcomp/Kan decider. (§4.7, §12.3)
5. **The non-fibrant interval is a fix, not a hack.** The affine interval breaks
   HITs; FX's interval is non-fibrant *because* that is the honest resolution
   (parametricity + def-univalence, not full cubical). (§4.7, §5.3)
6. **Present, don't declare; consume, don't emit.** Intrinsic QIITs → extrinsic
   presentation. Lower-bound certificates are consumed, never promised as outputs.
   Drive the discovery engine on the computable `L`, never the uncomputable `K`.
   (§9.6, §11.6, §12.5)
7. **Every deliverable has a zero-axiom twin.** `FX1PolyAudit/` mirrors the tree;
   a frontier module is not done until its `#assert_no_axioms` twin is green. The
   audit tree is the honesty ledger executed. (§1)
8. **Claims carry provenance.** Load-bearing claims in this file are tagged
   `Source(paper)` / `OurCorollary(source)` / `Conjecture` — born from the
   Steiner mis-attribution (the "linear algebra" reading is ours, §3.1). Dim-8
   provenance applied to the development itself.
9. **The spine is a checked artifact.** The dependency DAG (§13) gets a
   build-time tripwire (e.g. `rg "^import FX1Poly.Axis" FX1Poly/Polygraph` must
   be empty, and its siblings per layer) — the 2026-07-02 refactor exposed a
   silent transitive-import reliance; architecture is enforced like axioms and
   deletions, not socially.

---

## Appendix A — keystone module skeletons (Lean shapes)

Faithful sketches, not compiling code: they fix the *shape* and the *home* of the
keystone modules so a builder knows what to write. All identifiers are ASCII and
telling-word per the project naming law; predicates lead with a question verb;
spec primitives (`shift`, `subst`, `whnf`, `refl`) are the sanctioned exceptions.
`(Q)` marks which rubric question routed the placement.

### A.1 `Polygraph/Steiner/` — the free strict ω-category as linear algebra (Q1)

```lean
namespace FX1Poly.Polygraph.Steiner

-- an augmented directed complex: graded free ℤ-modules + boundary matrix + positivity
structure AugmentedDirectedComplex where
  basisAtoms      : Nat -> Type                                   -- generators per dimension
  boundaryMatrix  : {dim : Nat} -> basisAtoms (dim + 1) -> FreeAbelianGroup (basisAtoms dim)
  augmentation    : basisAtoms 0 -> Int
  boundaryComposesToZero : forall {dim} (atom : basisAtoms (dim + 2)),
      appliedBoundary (appliedBoundary atom) = 0                  -- ∂∂ = 0

-- a cell is an integer vector over the dimension-n basis
abbrev SteinerCell (complex : AugmentedDirectedComplex) (dim : Nat) : Type :=
  FreeAbelianGroup (complex.basisAtoms dim)

-- source / target are the negative / positive split of the boundary matrix
def sourceOfCell (complex) {dim} (cell : SteinerCell complex (dim + 1)) : SteinerCell complex dim :=
  negativePart (applyBoundary complex cell)
def targetOfCell (complex) {dim} (cell : SteinerCell complex (dim + 1)) : SteinerCell complex dim :=
  positivePart (applyBoundary complex cell)

-- composition is vector arithmetic modulo the shared k-boundary : x *_k y = x + y - shared
def composeAtDimension (complex) {dim} (lowerDim : Nat)
    (leftCell rightCell : SteinerCell complex dim) : SteinerCell complex dim :=
  leftCell + rightCell - sharedBoundary complex lowerDim leftCell rightCell

-- EQUALITY of composites is decidable integer-vector equality — the whole word problem
instance decidableSteinerCellEq (complex) (dim) : DecidableEq (SteinerCell complex dim) :=
  inferInstanceAsFinsuppDecEq

-- the loop-free boundary-containment order (atom a occurs in ∂b) — canonical SN precedence
def boundaryContainment (complex) : {dim : Nat} -> complex.basisAtoms dim -> complex.basisAtoms (dim+1) -> Prop
def loopFreeOrderIsWellFounded (complex) (isLoopFree : IsLoopFreeBasis complex) :
    WellFounded (transitiveClosure (boundaryContainment complex))               -- the free SN measure

-- Steiner's equivalence, restricted to the loop-free subcategory
theorem strictOmegaEquivalentToLoopFreeAdc :
    StrictOmegaCatWithLoopFreeBasis =~= AdcWithLoopFreeBasis                     -- Thm 1.2.1.23

-- Gray tensor is the chain tensor with the Koszul sign (preserves loop-free bases)
def grayChainTensor (left right : AugmentedDirectedComplex) : AugmentedDirectedComplex
theorem grayTensorPreservesLoopFree (left right) (hl hr) :
    IsLoopFreeBasis (grayChainTensor left right)                                 -- flips fxMode_nn true
```
**Depends** `Init` only. **Feeds** `fib-3` (SN precedence), `term-GRAY-FULL`
(Gray tensor), the free-ω-cat monad. **Audit** twin `FX1PolyAudit/Polygraph/Steiner/`.

### A.2 Fibrancy is a mode property — the `Axis/Fibrancy/` classifier is dropped

Fibrancy is **not** a standalone cross-axis classifier. It is one property of the
mode axis, shipped in `Axis/Mode/FibrancyMode.lean` (`FibrancyKind` +
`joinFibrancy`, the 2LTT f/e presentation, mode-13). The earlier proposal for a
zero-dependency `Axis/Fibrancy/` imported by all four axes has been dropped —
per-axis consumers read the fibrancy kind off the mode property, and "fibred over
mode" is a Core/Fib gluing statement, not a separate folder.

### A.3 `Axis/Type/Strength/` — the reflection-rank strength dial (Q3/Q6)

```lean
namespace FX1Poly.Axis.Type.Strength

-- a strength level is a CERTIFIED reflection rank (Pakhomov-Walsh), NOT a raw ordinal height
structure StrengthLevel where
  reflectionRank    : ReflectionRankNotation                 -- worm-notation up to ε0/Γ0
  contentTier       : ContentTier                            -- certified | believed | frontier
  hasNormalizingOperator : Bool                              -- T1 rung ships an IR operator?

inductive ContentTier | certified | believed | frontier     -- T1 | T2 | T3

-- the NON-NEGOTIABLE admission gate: grant a strength bump only against a rank certificate
def admitsStrengthBump (fromLevel toLevel : StrengthLevel)
    (certificate : ReflectionRankCertificate fromLevel toLevel) : Prop

-- the load-bearing honesty theorem: a non-content flag adds NO reduction rules
theorem flagAddsNoCanonicity (level : StrengthLevel)
    (isFlag : level.hasNormalizingOperator = false) :
    forall term reduct, StepUnderFlag level term reduct -> StepBaseline term reduct
    -- ⇒ the flag is kernel-PROVEN content-null : honest-by-construction
```
**Depends** `Core/Metatheory/Ordinal/` (the notations), `Axis/Type/Universe/`.
**The novelty** first foundation carrying a per-rung machine-checked
content-vs-flag tag. **Feeds** `FXProfile/`, `ProfileFibration/`.

### A.4 `Core/Rewriting/Normalize/NbE/` — NbE-as-a-functor, the candidate dissolver (Q4)

```lean
namespace FX1Poly.Core.Rewriting.Normalize.NbE

-- the semantic domain built BY CONSTRUCTION — no impredicative candidate-existential
inductive SemanticValue : Nat -> Type                        -- values, per scope
inductive NeutralValue  : Nat -> Type                        -- stuck / blocked forms

def evaluate  {scope} (environment : ValueEnv scope) (term : RawTerm scope) : SemanticValue scope
def reifyValue {scope} (typeValue : SemanticValue scope) (value : SemanticValue scope) : RawTerm scope
-- reify arms (the type-directed eta) : each fibrancy's extensionality falls out of ONE reify
def reifyAtSigma    : ... -> RawTerm scope                   -- surjective-pairing η
def reifyAtModal    : ... -> RawTerm scope                   -- μ◇→A η (A1 negative readback)
def reifyAtUniverse : ... -> RawTerm scope                   -- carries the def-univ type data
def reifyAtDirected : ... -> RawTerm scope                   -- Segal/directed reify

-- decidable Conv WITHOUT rewriting-search or SMT : reify ⊕ structural normal-form equality
def decideConv {scope} (left right : RawTerm scope) : Decidable (Conv left right) :=
  decidableOfNormalFormEquality (reifyValue _ (evaluate emptyEnv left))
                                (reifyValue _ (evaluate emptyEnv right))
theorem nbeSoundAndComplete : forall left right, (reifyRoundTrip left = reifyRoundTrip right) <-> Conv left right
```
**Depends** `Core/Substrate/Cell/`, the shipped `Reducibility/`. **Dissolves** the
`RawTerm -> Prop` impredicative residual (predicativizes the metatheory). **Feeds**
`DISSOLVE-DECCONV-NBE`, `FRONTIER-NBE-FUNCTOR-FULL`, every fibrancy's extensionality.

### A.5 `Core/Metatheory/Reflection/` — the GLP worm & the autonomous progression (Q4)

```lean
namespace FX1Poly.Core.Metatheory.Reflection

-- a GLP worm : a finite word in the reflection-calculus modalities [0],[1],[2],…
abbrev Worm : Type := List Nat
def wormOrdinal (worm : Worm) : OrdinalNotation                -- o(·) : worms ≅ ε0 (elementary)
def wormReduces  (worm : Worm) : Worm -> Prop                  -- the decidable reduction relation
theorem wormOrderIsWellFounded : WellFounded wormReduces       -- decidable-combinatorial

-- the reachable self-reference budget (Gödel-safe): Con of a STRICTLY WEAKER subtheory
theorem provesConOfWeakerRung (rung : StrengthLevel) (lower : StrengthLevel)
    (isStrictlyWeaker : lower.reflectionRank < rung.reflectionRank) :
    ProvableAt rung (Consistency lower)                        -- n+1 ⊢ Con(n), never n ⊢ Con(n)

-- the autonomous progression : grant Con only against a certified well-ordering (Turing-Feferman)
def autonomousProgression : StrengthLevel -> Option StrengthLevel  -- deny-by-default; the certified climb
```
**Depends** `Core/Metatheory/Ordinal/`, the shipped `Axis/Mode/Provability.lean`
(mode-23 GLP). **The novelty (triple-confirmed unclaimed)** first mechanized
autonomous progression = first machine-checked ordinal analysis of a theory.
**Boundary** `GodelBoundary.lean` states the walls the ladder respects.

### A.6 `Typed/Dimensions/Cost/` — the optimization polygraph & no-search homology (Q5)

```lean
namespace FX1Poly.Typed.Dimensions.Cost

-- optimization schemas are DIM-3 rules over the term rewriting, oriented cost-decreasing
structure OptimizationSchema where
  redexTemplate     : ReductTemplate                          -- the shape it recognizes
  reductTemplate    : ReductTemplate                          -- what it rewrites to
  costStrictlyDecreases : forall term, costFunction (applyReduct reductTemplate term)
                                     < costFunction (applyRedex redexTemplate term)

-- cost-RPO termination + Newman ⇒ a UNIQUE cost normal form
def costNormalForm (term : RawTerm scope) : RawTerm scope
theorem costNormalFormIsUnique : forall term, exists! nf, ReachesCostNf term nf

-- optimality = orthogonality (type-B, basis-relative) — a GENUINE theorem, scoped
def isCostOptimalInBasis (term : RawTerm scope) : Prop :=
  IsOrthogonalNormalForm optimizationPolygraph term
theorem optimalityEqualsOrthogonality :
    forall term, isCostOptimalInBasis term <-> HasNoDistinctOptimalPath term   -- COPT-6

-- the no-search theorem : H1 = 0 (Squier homology) ⟺ search-free optimum (measured in the COST grade)
theorem noSearchIffHomologyVanishes :
    firstSquierHomology optimizationPolygraph = trivialGroup
    <-> forall term, HasSearchFreeOptimum term                                 -- CNOS-3
```
**Depends** `Core/Rewriting/RuleTables/`, `Core/Metatheory/Resolution/` (the H1).
**Firewall** every result here is type-B; NEVER relabel as a type-A complexity
bound. **Cost is the dim-13 grade** (Lévy-optimal steps ≠ wall-clock).

### A.7 `Typed/Complexity/` — the epistemic-complexity library & the firewall (Q5)

```lean
namespace FX1Poly.Typed.Complexity

-- the firewall : a lower bound is TAGGED type-A vs type-B, and the tag PROPAGATES as a grade
inductive BoundKind
  | typeB (basisRelative : Prop)                              -- rewriting/optimality, T1 decidable
  | typeAConditional (hypothesis : ComplexityHypothesis)      -- e.g. SETH — T1 conditional
  | typeARestricted  (model : RestrictedCircuitModel)         -- monotone/AC0/resolution — T1
  | typeAUnconditional                                        -- P-vs-NP-adjacent — T3, FORBIDDEN to emit

-- the triple optimality certificate : upper × lower × epistemic tag (the honest scale, operationalized)
structure OptimalityCertificate (problem : ComputationalProblem) where
  upperBound     : CostBound problem                          -- a cost-decreasing rewrite (always present)
  lowerBound     : Option (LowerBound problem)                -- consumed, never promised
  epistemicTag   : BoundKind                                  -- rides as Trust(dim9) + Cost(dim13) grade
  tagIsWellFormed : refutesLaunderingTypeBAsTypeA epistemicTag

-- the three barriers, each a theorem (no mechanized barrier library exists — the clean FIRST)
theorem relativizationBarrier   : exists oracleA oracleB, SeparatesP_NP oracleA /\ CollapsesP_NP oracleB
theorem naturalProofsBarrier    (existsExpHardPrf : ExpHardPseudorandomFunctions) :
    forall property, IsNaturalProperty property -> not (SeparatesPpoly property)
theorem algebrizationBarrier    : ...

-- the T2 conjecture (NEGATIVE barrier-transfer only; the forbidden positive direction is T3-as-T1)
def naturalProofsAsInternalParametricity : Prop :=          -- LB-NATURAL-PARAM #1447, stated over transpension
  forall separator, IsInternallyParametricDefinable separator ->
    IsNaturalProperty separator                              -- ⇒ blocked under exp-hard PRFs
```
**Depends** `Typed/Dimensions/` (the Trust/Cost grades). **The novelty** first
machine-checked epistemic-complexity library. **Rail** the firewall is a typing
rule; T3 items are documented walls, never coded to "emit."

### A.8 `Core/Fib/TheOneObject.lean` — the R7 self-indexing fixpoint (Q4)

```lean
namespace FX1Poly.Core.Fib

-- the kernel presented as ONE product-graded (∞,ω)-polygraph value : signature × tables × Conv
structure PresentedKernel where
  signature   : FxSignature                                    -- the 205 generating cells
  ruleTables  : GradedRuleTables signature                     -- β/ι/η + the 21 graded dimensions
  conversion  : ConvertibilityRelation signature ruleTables

-- structural R7 fixpoint : the kernel is the categorify ⊣ decategorify fixed point (SIG-5, T1)
theorem kernelIsSelfIndexedFixpoint :
    PresentedKernel =~= categorify (decategorify PresentedKernel)               -- THE-ONE-OBJECT structural

-- the wildest coherent moonshot (T2) : the climbing ladder, height = FX's own GLP-worm ordinal
def climbingLadder : Nat -> PresentedKernel                                     -- FX@n
theorem eachRungProvesNormalizationOfThePrior (rung : Nat) :
    ProvableAt (climbingLadder (rung + 1)) (StrongNormalizes (climbingLadder rung))
    -- Gentzen/Lean4Lean : provable at n+1, NEVER at n (Gödel-II) ; the ladder never closes
```
**Depends** all four `Axis/<Axis>`, `Polygraph/`, `Typed/SelfFormalize/`,
`Axis/Grade/`. **The telos** fib-13. **Rail** semantic self-reading is T3; the
climb is T2 (unbounded, not closable — incompleteness is generative).

### A.9 `Axis/Type/Interval/` — interval theories & the affine substrate (Q2)

```lean
namespace FX1Poly.Axis.Type.Interval

-- an interval theory = a single-sorted algebraic theory over the two endpoints
structure IntervalTheory where
  operations   : List IntervalOperation                        -- {} | {∨} | {∨,∧} | {∨,∧,~}
  hasReversal  : Bool
  hasDiagonal  : Bool                                           -- contraction : the affine dial

def isCartesian (theory : IntervalTheory) : Prop := theory.operations = []
def isAffine    (theory : IntervalTheory) : Prop := theory.hasDiagonal = false  -- no contraction
def isSelfDual  (theory : IntervalTheory) : Prop                                -- admits the twist

-- the twist : a self-dual interval lifts to (I × I) with a reversal, inside a reversal-free base
def twistConstruction (theory : IntervalTheory) (selfDual : isSelfDual theory) : IntervalTheory
theorem directedIntervalRejectsTwist (theory) (isDirected : not (isSelfDual theory)) :
    not (AdmitsTwist theory)                                   -- validates reversal-free directed column
```
**Depends** `Init`. **The affine interval is the A1 substrate** (no diagonal ⇒
non-fibrant ⇒ HIT-safe). **Feeds** the multigrade universe, the Kan ops, the A1 lock.

### A.10 `Polygraph/Invertibility/` — the shipped witness-closure (reference, Q1)

```lean
namespace FX1Poly.Polygraph.Invertibility        -- SHIPPED 9e2737ca, for reference

structure WitnessOperator (Element : Type) where
  apply    : (Element -> Prop) -> (Element -> Prop)
  monotone : forall p q, (forall x, p x -> q x) -> (forall x, apply p x -> apply q x)

inductive inductiveClosure (op : WitnessOperator Element) : Element -> Prop     -- LEAST fixpoint
def coinductiveClosure (op : WitnessOperator Element) (x : Element) : Prop :=    -- GREATEST fixpoint
  exists postFixed, IsPostFixed op postFixed /\ postFixed x

-- ★ the F1 theorem : SN IS the inductive fixpoint of the reduction witness-closure operator
theorem inductiveClosure_reductWitnessOperator_iff_isStronglyNormalizing {term : RawTerm scope} :
    inductiveClosure reductWitnessOperator (reductionCellOf term) <-> IsStronglyNormalizing term
```

### A.11 `Polygraph/SemiModel/Saturation.lean` — metatheory-once-over-generators (Q1)

```lean
namespace FX1Poly.Polygraph.SemiModel

-- a constructive backdrop : the ω / complemented-mono instance (no quotients, no choice)
structure ConstructiveBackdrop (Category : Type) where
  distinguishedMonos : MorphismClass Category                  -- complemented (decidable) inclusions
  omegaChainColimits : HasOmegaChainColimits Category          -- coproducts of complements
  closedUnderCobase  : ClosedUnderCobaseChange distinguishedMonos

-- ★ the saturation theorem : structure on the GENERATORS extends functorially to ALL cells (S5)
theorem structureOnGeneratorsSaturatesToAllCells (backdrop) (structureOnGenerators) :
    exists! extendedStructure, ExtendsAlongLeftFactor structureOnGenerators extendedStructure
    -- = "prove the metatheory ONCE over the polygraph"
```
**Depends** `Polygraph/Category/`. **The constructive substrate** for the SemiModel
core; the ∞-localization stays `[O]`, deliberately bypassed.

### A.12 `Axis/Mode/LnlDoctrine.lean` — the grade↔mode crossover (Q3)

```lean
namespace FX1Poly.Axis.Mode

-- an LNL doctrine : nonlinear (all structural rules) + linear (exchange only), joined by F ⊣ U
inductive ObjectSort | nonlinear | linear
structure LnlDoctrine where
  objectSorts     : ObjectSort -> Type
  admissible      : SignedObjectList -> Prop                   -- entries-only structural-rule discipline
  storeModality   : objectSorts .nonlinear -> objectSorts .linear      -- F
  fetchModality   : objectSorts .linear    -> objectSorts .nonlinear   -- U ; F ⊣ U ; ! = F∘U

-- a doctrine = "one grade-checker parameterized by a semiring/tier" ⇒ 21 dims = a PRODUCT of doctrines
def gradeCheckerOfDoctrine (doctrine : LnlDoctrine) : GradeChecker
```
**Depends** `Axis/Mode/GradeAlgebra/`. **Feeds** `mode-22/25/26`,
`FRONTIER-GRADED-EVERYTHING`, the grade-mode spectrum R1–R3.

---

## Appendix B — build order (the staged brick sequence)

Each domain builds bottom-up along the DAG; a `→` means "unblocks." Bricks are
atomic-green (`lake build FX1Poly FX1PolyAudit` clean) with a zero-axiom twin.

**Substrate (Domain I).** `Computad/` re-home SHIPPED 2026-07-02 (POLYGRAPH-4..9:
the carrier carve-out + the 40-file FreeTwoCell/WalkingAdjunction tower + TwoMonad;
Axis/Mode 79→38 files, zero Polygraph→Mode back-edges; residue: `ModeOmegaWeakGray`
deferred on generalizing `GrayCategory` over an arbitrary `RawTwoCategory`, plus a
namespace-normalization sweep). Remaining order: `ComputerAlgebra/` (ℤ/ℚ substrate; brick 1 shipped) →
`Polygraph/Steiner/` (ADC + coords + decidable-eq + loop-free order) →
`ComputerAlgebra/LinearAlgebra/SmithNormalForm` (computable H₁/H₂ + torsion) → `GrayChainTensor` (flips
`fxMode_nn`) → `FreeStrictOmegaMonad` → `Marked/Marking` genericization →
`Complicial/` (horn=equation) → `WalkingEquivalence/` (+ `DecidableWalkingWord` —
do EARLY, pure OmegacE reuse, discharges #638) → `SemiModel/Saturation` →
`Homotopy/`. Steiner first — it de-risks fib-3 by handing over the SN precedence.

**Identity/interval (Domain II).** Fibrancy is one mode property
(`Axis/Mode/FibrancyMode`, shipped — no standalone classifier step).
`Axis/Type/Interval/{IntervalTheory,AffineInterval}` → `Typed/Rott/{Relativity,SrpRows}`
→ `MultigradeUniverse` + `CategoricalUnivalence` (CUA/FE grade) → `DefunivMeasure`
(the SN gate) → `DirectedInterval` + directed reify.

**Mode (Domain III).** the A1 lock as the `Γ\r ⊣ −.𝕀` adjoint (`DimensionLockAdjoint`)
→ `A1-SUBST-OPEN` (substitution-under-open) → `NegativeModality` (the live former)
→ `LnlDoctrine` → cohesion `b` → `GaloisModality` → `ForcingModality`.

**Strength (Domain IV).** `Core/Metatheory/Ordinal/` (notations + Steiner-order SN)
→ `GlpAlgebra` (worms) → `Axis/Type/Strength/{StrengthDial,ReflectionRankCertificate}`
→ `MahloUniverse` (IR, the content ceiling) → `GlueRealignment` (U8 theorem)
→ the flag `hasNo…=false` content-null proofs.

**Grade (Domain V).** `Axis/Grade/{Decategorification,Spectrum}` →
`Typed/Dimensions/Graded/` (grade-vector premises) → `GradedMetatheory` (prove once)
→ `SamenessUnification`.

**Dissolution (Domain VI).** `SigAlgebraCandidate` → `PolynomialData` → NbE reify arms
→ `DecConvHybrid` → `ArtinGluingFT` → `OrthogonalCR` → `Resolution/PolygraphicResolution`
(the metatheory-as-resolution capstone).

**Self-reference (Domain VII).** `Reflection/GodelBoundary` → `Reflection/GlpAlgebra`
→ `Ordinal/*` → `Typed/SelfFormalize/{MetatheoryAsTypes,StratifiedProof}` →
`NormalizerReflected` → `DiscoveryEngine`.

**Complexity (Domain IX).** `Complexity/Firewall` → `Barriers/*` (the clean first) →
`LowerBounds/*` (conditional + restricted, tagged) → `Certificate` (LB-CERT) →
`Cost/OptimizationPolygraph` → `NoSearchHomology` → `NaturalParametricity` (T2).

**Fibration (Domain X, the assembly).** fib-1/2 [S] → fib-3 (consumes
`WalkingEquivalence` + the A1 lock) → fib-4/5 → fib-6/7 (sconing, O-NORM) → fib-8
(Gray 4-way) → fib-9/10 (obstruction, no-go) → fib-11/12 (QIIT) → fib-13
(`TheOneObject`). fib-16 extraction is the exit to LowX.

**Certificates (Domain XI).** `ComputerAlgebra/` (brick 1 shipped) → `PerronFrobenius` → MOSCOW-CERT
instances → MOSCOW-N2 (first machine-checked case of the hypothesis) →
MOSCOW-NET (e.g. (5,3)) → INTERLACE toolkit.

**Discrete + shadows (Domain XII).** CSHD-0..5 → C1 quotient-free Polya →
C2/X7 ambidexterity = cardinality → the pro-object codata brick (Stone) →
C3 light-condensed core ‖ C4 Balmer spectrum → C5 Hodge certificates (on `ComputerAlgebra/`).

**Quotients (Domain V §7.5).** QUOT design-lock (the 3-dial grade + admission
table) → EXT-2 rows → the ObservationalId table (EXT-3/4/6 unified, §8.7) →
EXT-7 convergence-certified definitional tier → the collapse theorems
(‖classifying‖₀ = set, effectivity-for-free).

**Vector cost (Domain IX §11.7).** `ParetoNormalForm` → `PebbleGames`
(black/red-blue/reversible) → the REVOLVE showcase (dual of OPT-7) →
`InPlaceTheorem` at fib-16 → the three-objective (time×space×erasure) ledger.

---

## Appendix C — the compressed dimensions (concepts folded for length)

Concepts real to the program but compressed above; each still gets a home.

- **type-16 polynomial-functor calculus** `[C]` — derivative, composition, the
  polynomial monad; the data fragment's semantic engine (§8.2). Home
  `Core/Metatheory/Reducibility/PolynomialData.lean` + `Axis/Type/PolynomialFunctor.lean`.
- **type-17 guarded recursive types** `[C]` — the later modality, Löb, guarded domain
  equations. Home `Axis/Mode/GuardedRecursion.lean` (shipped mode-15) +
  `Axis/Type/GuardedType.lean` (the domain-equation solver).
- **mode-25 session/protocol duality** `[S]` — duality as a self-inverse 2-cell;
  protocol metatheory as a modal instance (BRIDGE-SESSION-DUAL). Home
  `Axis/Mode/Session.lean` (shipped).
- **BRIDGE-EFFECTS-MODAL** `[C]` — algebraic effects / graded monads as instances of
  the modality calculus. Home `Axis/Mode/EffectModality.lean` (new).
- **LEARN-AD** `[R]` — reverse-mode automatic differentiation as a graded-optics kernel
  construction with a *definitional* chain rule. Home `Typed/Dimensions/Optics.lean` (new).
- **PHYS-LANDAUER** `[C]` — Landauer erasure as a grade; the second law as
  SN-monotonicity. Home `Typed/Dimensions/Graded/Landauer.lean` (new; ties the erasure
  dimension). A physics-as-grade curiosity, honestly bounded.
- **SEARCH-1 searchable types** `[R]` — via selection functions; decidable
  quantification over exponential spaces. Home `Typed/Dimensions/Searchable.lean` (new).
- **DPROP-1 dProp / Sierpinski split** `[R]` — decidable and semi-decidable proposition
  universes. Home `Axis/Type/Universe/DecidableProp.lean` (new).
- **COHESION-O4 condensed / cohesion focus** `[C]` — what the shipped modality substrate
  gives condensed mathematics. Home a survey note under `Axis/Mode/Cohesion*`.
- **ARITH-TOTALITY** `[R encode / O inhabit]` — a Π⁰₁ conjecture as a kernel totality
  type (inhabitation = truth). Home `Typed/Dimensions/ArithTotality.lean` (the *encoding*
  is the contribution; the proof term is not on offer). §9.
- **ISO-CONV** `[R decidability]` — finite-structure isomorphism as decidable Conv in a
  univalent finite universe (GI reframed; decidability only, never efficiency). Home
  `Typed/Complexity/IsoConv.lean`. §11.6.
- **term-SSC / Fiore-Plotkin-Turi** `[S]` — the single-substitution Σ-monoid; SOAS
  completeness. Home `Axis/Term/SSC/` (shipped). The substitution-algebra spine under
  the free-ω-cat monad.

---

## Appendix D — provenance matrix (concept → durable memory)

Where the deep detail for each domain persists (recall these before building).

| Domain | Primary memory reference |
|---|---|
| I — substrate, Steiner, semi-model, homotopy-language | `reference_henry_school_infty_omega_reads`, `reference_omega_cat_frontier_reads`, `project_polygraph_beyond_sota` |
| I — cubical models, saturation, LNL | `reference_cubical_models_saturation_lnl` |
| II — φ column, parametricity, affine, def-univalence | `reference_cubical_parametricity_phi_column` |
| II/VII — displayed-TT, directed, universe-coherence, self-formalization | `reference_displayed_directed_universe_cluster` |
| III — mode theory, transpension, A1 lock, cohesion | `reference_mtt_matt_papers`, `reference_transp_norm_paper_reads`, `project_transpension_zoo_honest_architecture`, the A1 `project_*` set |
| IV — universes, large cardinals, the strength dial | `reference_large_cardinal_ceiling`, `project_zf_strength_audit` |
| V — grade↔mode spectrum, decategorification | `Axis/Mode/grade-mode-spectrum.md` (design doc, in-tree) |
| VI — dissolution, NbE, metatheory-by-universal-property | `project_milestone_a_route_plan`, the DISSOLVE/FTGEN `project_*` set |
| VII — reflection, GLP, autonomous progression, the bootstrap | `project_self_reference_reflection_ceiling` |
| VIII — ZF-strength, constructivity | `project_zf_strength_audit` |
| IX — complexity, firewall, barriers, optimization | `project_complexity_ceiling_honesty_map`, `project_meta_algorithmic_optimization_vision` |
| X — the four-axis fibration, the telos | `project_fib_arc_design_lock`, `project_fib3_mode_floor`, `roadmap_*` |

---

*Status: this document is the frontier map + placement charter. It is prose, not a
proof obligation; the Lean realizations it points at are tracked tasks (the fib-*,
DISSOLVE-*, FRONTIER-*, ZOO-*, LB-*, COPT-*/CNOS-*, and the axis rung families).
Constituent detail lives in the memory reference-maps (the five paper-cluster reads
+ the three ceiling maps + `project_polygraph_beyond_sota`) and in
`Axis/Mode/grade-mode-spectrum.md`. When a placement here conflicts with a shipped
reality, the shipped reality wins and this file is corrected. The Lean skeletons in
Appendix A are shape sketches, not compiling code — they fix intent and home, and
must be re-derived against the live APIs when built.*
