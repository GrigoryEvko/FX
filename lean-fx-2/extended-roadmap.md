# extended-roadmap.md — lean-fx-2 from Day 10 with operadic polygraph substrate (mathematically grounded)

**Single source of truth for post-v1.0 lean-fx-2 development.** This
document supersedes:

* `roadmap-beyond-frontier.md` (Era I-VII version, retained for
  historical reference)
* `errratas.md` (mathematical foundations companion — fully merged
  into Part I + Part VI + Appendix C + Bibliography of this document)

**Architectural commitments** (locked through this document; see §
"Architectural shift" for details):

1. **Three orthogonal encoding columns**: Tree (`RawTerm`/`Term`),
   Operadic Polygraph (`RawPolyTerm`/`PolyTerm`, subsuming hypergraph
   via Squier reading), Value-form (`RawValueTerm`/`ValueTerm`, Path 2
   staged).
2. **PolyTerm is operadic**, not globular — multi-input/multi-output
   cells from the start, which subsumes Lafont interaction nets and
   eliminates the need for a separate `HyperTerm` IR.
3. **M04 strong normalization via Path 2 staged**: Stage 1 ships Tait
   reducibility (Prop-valued `RC : Ty → Term → Prop`, no eval
   function); Stage 2 ships `ValueTerm` with closure-based eval/quote
   for decidable Conv via NF equality.
4. **FX1.check_sound is the trust anchor**, per `kernel-metaplan.md` —
   THIS roadmap describes post-v1.0 evolution; FX1/FX0 trust spine
   work is orthogonal and ships independently.

Each "Day" represents 3-4 weeks of focused work; total duration to
Day 95 is approximately 7-8 years at single-team pace, with
substantial parallelism possible.

## Companion documents (orthogonal axes)

* `kernel-sprint.md` — Days 0–9 (current MVP path to v1.0)
* `kernel-metaplan.md` — FX1/FX0 trust spine (orthogonal to this
  roadmap; load-bearing for "Root-FX1" trust status)
* `computability-rules.md` — invariants every Era must preserve
  (orthogonal: applies to ALL kernel additions in this document)
* `ROADMAP.md` — current-day phasing within v1.0 sprint
* `AXIOMS.md` — strict zero-axiom commitment (no exceptions)
* `WORKING_RULES.md` — kernel-discipline rules

## Discipline (load-bearing across all Eras)

Every Day's deliverable must satisfy `computability-rules.md`:
* No axioms (`#print axioms` reports zero)
* No `noncomputable`/`@[extern]`/`@[implemented_by]`/`opaque` markers
* Constructor-driven dispatch + well-founded recursion
* Decidable judgments for the active graded dimensions; the roadmap
  target is the 24-dimensional vector in Part I §5, while any
  earlier slice must state which prefix/subset is implemented

The deep load-bearing principle is the **Brouwer-Heyting-Kolmogorov
interpretation lifted to (∞,n)-categorical level**: every connective,
every modality, every coherence, every reduction has an explicit
computational construction. **Computability is maintained by
REFUSING TO INTRODUCE ANYTHING WITHOUT EXPLICIT COMPUTATIONAL
CONTENT.**

**Rigor boundary** (load-bearing, not rhetorical):
* A **kernel theorem** is a Lean theorem over finite, explicitly
  represented syntax/data, with zero axioms and no hidden oracle.
* A **model theorem** is a kernel theorem conditional on an explicit
  mathematical model supplied as data (for example a finite site, a
  finite thermodynamic model, a bounded hardware timing model). The
  theorem proves consequences inside that model, not that the physical
  world satisfies the model.
* A **certificate theorem** checks a finite certificate emitted by an
  external solver, optimizer, simulator, ML search, or hardware
  measurement pipeline. The external tool proposes; the kernel checks.
* A **realization assumption / TCB extension** records trust in a
  physical implementation or vendor library. It cannot be promoted to
  `Root-FX1` by prose; it needs a bridge theorem plus a checked
  certificate format.
* `opaque` in user-facing prose means sealed API / private concrete
  constructor only. Kernel code may not use Lean `opaque` for shipped
  zero-axiom artifacts.
* Physics-facing work (Maxwell/RLC/STA, energy/Landauer, M-theory
  search) is valid roadmap material only when phrased as
  computational model construction, finite search, and certificate
  checking. It must not claim real-world truth before an explicit
  model and validation boundary are stated.

**Status legend** (matches `ROADMAP.md`):
* `[x]` — shipped, zero-axiom verified
* `[~]` — partial
* `[ ]` — not started
* `(blocked)` — gated on prerequisite
* `(exploratory)` — research-grade
* `(parallel)` — runs concurrently with critical path

---

## Vision

By Day ~96.9 (Era W close-out, post Era IV.5/T/R/W insertions),
lean-fx-2 should have:

1. **PolyTerm** (operadic Squier polygraph) as the kernel substrate
   at Layer P alongside `RawTerm`, with verified bidirectional
   encoding to `Term`. Multi-input/multi-output cells subsume
   Lafont/Lamping interaction nets — no separate HyperTerm IR
   required.
2. **Polygraph cells at six dimensions** encoding terms, rewrites,
   confluence, strategies, hardware fibres, and refinement functors.
   Sharing-cell families (Lamping `!`-fan, `?`-fan, brackets,
   croissants) folded into PolyTerm at dim-0/1.
3. **ValueTerm** (Path 2 Stage 2) as the closure-based value-form
   encoding, unlocking decidable Conv via NF equality.
4. **M04 strong normalization proven** (Path 2 Stage 1) via Tait
   reducibility — Prop-valued `RC : Ty → Term → Prop` with
   fundamental theorem.
5. **Stratified execution via PolyTerm sharing-cells** for
   hardware-aware execution (GEMM stratum + Path stratum).
6. **B200-cluster realization** with verified hardware retrofit across
   CPU / GPU / FPGA / dataflow targets.
7. **Tropical-semiring GEMM** as the universal computational substrate
   for kernel operations.
8. **Optimal transport integration** for ML-guided differentiable
   superoptimization.
9. **Refinement feedback API** providing structured suggestions to
   LLM agents and programmers.
10. **Cohesive ∞-topos modal layer** at polygraph level.
11. **Synthetic physical mechanization** library (`fx-mtheory`).
12. **Algorithm discovery via dim-6 search** for AlphaTensor-style
    wins.
13. **Multi-level hardware polygraph (Era IV.5)**: Maxwell at
    Level 0 + RLC + STA + Digital + μArch with 4 verified
    abstraction functors; spacetime-typed primitives Charge / Wire
    / Register / Instruction; light-cone constraint, setup/hold +
    hazards as type errors, Kirchhoff KCL via Noether on
    time-translation, side-channel typing (7 channels), discrete
    Stokes theorem for represented calculi + Landauer-style checked
    model certificates.
14. **Site-parametric kernel (Era T)**: `Term : (S : CausalSite) →
    Ctx → Ty → RawTerm → Type`; 10+ verified site instances
    (sequential ℕ/ℝ, parallel monoidal, branching tree, dagger
    compact = quantum, Sorkin causal poset, hybrid clock, smooth
    manifold = physics, asymptotic BigO = algorithm-discovery, FEU
    hardware); 6 verified site morphisms; temporal cohesion
    ◯⊣▷⊣⟐⊣ℑ; 8-modality spacetime cohesion combining with
    spatial ♭⊣◇⊣□⊣♯.
15. **Reflection layer (Era R)**: ReflTerm + Term.reify +
    ReflTerm.elaborate roundtrip zero-axiom at all 75 ctors; Tactic
    monad with verified-correctness theorem (Era VI tactics
    re-implementable as reflective programs); macros + DSL embedding;
    FX-in-FX self-hosting (B13 bootstrap unblocked).
16. **World-as-type (Era W)**: World as a sealed interface with
    concrete finite/Kripke implementations + peek/poke + Iris-
    style step-indexed Kripke worlds (constructive fragment);
    effect-as-world-transition iso preserving existing FX programs;
    counterfactual operators with verified non-interference;
    selective per-application full Iris parity deferred to Era XIII.
17. **Four encoding columns**: Tree + PolyTerm + ValueTerm + EGraph
    (Willsey et al. 2021) with verified subsumption lattice +
    cost-minimal extraction.
18. **24-dim grade vector**: 21 original + dim-22 (Belnap-Dunn FOUR
    consistency from Era IV) + dim-23 (Energy / Landauer as an
    explicit finite thermodynamic-model/certificate layer, not a
    blanket physical claim) + dim-24 (Incrementality / ILC change
    calculus, Cai et al. ICFP 2014).
19. **Promise/Guard/Fallback runtime properties (Era VIII D63.A)**:
    compile-time loose bound + runtime measurement + adaptive
    fallback for analog ENOB / actual delay / actual power /
    calibration accuracy; per-chip characterization as type
    parameter; load-bearing for Era IV.5 abstraction-functor
    soundness conditions and FEU-FX vertical analog precision.
20. **FEU-FX co-design super-accelerator (Vertical I)**: FEU v5.1
    with 12 cheap firmware adjustments + 3 medium-cost hardware
    additions (v6); ~10⁹ polygraph cells/μs target; 7-level fractal
    (3⁷ = 2187 atoms per tile) maps to polygraph dim 0..6; 27-die
    ternary cube as polygraph dim-6 parallel-strategy distribution.

Every kernel theorem is zero-axiom and computable per
`computability-rules.md`. Model theorems, external certificates, and
hardware realizations carry their trust boundary explicitly. Hardware
retrofit work is pursued through the SHK-B200 design + multi-level
Maxwell-grounded framework (Era IV.5), but physical adequacy is never
promoted without a checked model/certificate and a TCB record where
needed.

**FX1 trust anchor**: every Day's output is classified per
`kernel-metaplan.md` root-status labels (`Root-FX1`,
`LeanKernel-FX1`, `FX-rich`, `Bridge`, `FX0-root`, `Scaffold`,
`Deferred`). Default for new rich-layer work in this roadmap is
`FX-rich`; promotion to `Bridge` requires an explicit
`encode_*_sound` theorem; promotion to `Root-FX1` requires
`FX1.check_sound` coverage. No claim of minimal-root trust without
the bridge.

## Architectural shift — what changes at Layer 0

### Before (v1.0 architecture)

```
Layer 0  Foundation: Mode, RawTerm, RawSubst, Ty, Subst, Context
Layer 1  Term: intrinsic typed Term + Rename + Subst + ToRaw
Layer 2  Reduction: Step, ParRed, Compat
Layer 3  Confluence: Cd, CdLemma, Diamond, ChurchRosser
Layer 4  HoTT/Cubical/Modal/Graded layers ...
```

Single encoding (Tree). Rewriting via Step. Confluence via cd_lemma +
Church-Rosser.

### After (operadic-polygraph + value-form architecture)

```
Layer P  Polygraph substrate (operadic, Squier reading)
         ├── PolyCell (universal cell type, dimension-indexed,
         │            multi-port arities)
         ├── PolyTerm/RawPolyTerm (polygraph IR for FX terms;
         │            sharing-cell family enabled for Lamping)
         ├── ValueTerm/RawValueTerm (closure-based value-form;
         │            Path 2 Stage 2)
         └── Dim-by-dim machinery (source/target/composition/
                                   parallelism for dims 0–6)

Layer 0  Foundation: Mode, RawTerm, RawSubst, Ty, Subst, Context
         └── verified embedding RawTerm ⇌ PolyTerm at dim 0
Layer 1  Term: intrinsic typed Term
         ├── verified embedding Term ⇌ PolyTerm at dim 0+
         └── verified embedding Term → ValueTerm via eval (Stage 2)
Layer 2  Reduction (now polygraph-cells at dim 1)
Layer 3  Confluence (now polygraph-cells at dim 2)
Layer 4  Strategy + hardware + refinement + algorithm dimensions
         (dim 3-6, polygraph cells)
Layer 5+ HoTT/Cubical/Modal/Graded — operate over polygraph
```

### The four-encoding grid

```
                Tree           Operadic Polygraph    Value-form        E-Graph
                ────           ──────────────────    ──────────        ───────
untyped raw  →  RawTerm        RawPolyTerm           RawValueTerm      RawEGraph
typed kernel →  Term           PolyTerm              ValueTerm         EGraph
```

Each column captures a different structural axis:
* **Tree**: induction-friendly syntax; primary representation for
  metatheory induction proofs
* **Operadic Polygraph**: dim/sharing/coherence; primary
  representation for hardware retrofit, ∞-frontier, refinement
  feedback. Multi-port cells absorb hypergraph (interaction net)
  structure.
* **Value-form**: model-theoretic content WITHOUT external meaning
  (purely internal Lean inductive optimized for normal-form
  representation); primary representation for decidable Conv via NF
  equality. **Not "external semantic" — just a different syntactic
  encoding aligned to value-form.**
* **E-Graph** (Willsey-Nandi-Wang-Stepp-Tatlock-Panchekha 2021,
  per Era XII Day 93.A e-graph integration): equivalence-class
  encoding via union-find over canonical-class representatives.
  Each EGraph node is an e-class (set of equivalent terms);
  congruence closure maintained automatically. Primary
  representation for: Era V optimization (cost-minimal
  representative extraction), Era VI tactic search (saturate then
  extract), Era IX OT integration (e-class as fuzzy semantic
  class), Era XII algorithm discovery (search over e-class
  modifications). Equality saturation algorithm runs in
  O(|e-classes|^d) for depth-d search; tractable for d ≤ 10
  (Willsey et al. POPL 2021, egg framework).

### Subsumption lattice (syntactic encodings)

```
              Tree  ─────  PolyTerm(operadic)  ─────  HashCons (⊆ Hyper ⊆ PolyO)
               ↓                ⊃ globular polygraph (special case)
            ValueTerm           ⊃ hypergraph (sharing-cell family)
           (eval direction;
            quote is partial/lossy
            for non-NF terms)
```

* `Tree → PolyTerm`: bijection at dim 0 (lossless)
* `PolyTerm[core only] → Tree`: bijection inverse
* `PolyTerm[core + sharing cells] → Tree`: lossy unfolding (sharing
  collapses)
* `Tree → ValueTerm`: forward eval (lossy at quote — only NF
  recoverable)
* `Hypergraph ⊆ PolyTerm`: hypergraph IS PolyTerm with sharing-cell
  family enabled
* `Globular polygraph ⊊ PolyTerm`: PolyTerm is operadic, strictly
  more expressive
* `Tree → EGraph`: lossy quotient (each Term maps to its e-class
  equivalence representative; Term ↦ e-class id under congruence
  closure)
* `EGraph[representative-extracted] → Tree`: argmin extraction
  per cost function (lossy: many Trees in same e-class)
* `EGraph ↔ PolyTerm[+ saturation cells]`: e-graphs ARE polygraphs
  with explicit equivalence-witnessing 2-cells; equality saturation
  generates dim-2 cells via congruence closure

Existing kernel preserved via embedding theorems. Future extensions
expressed natively as polygraph cells. The kernel becomes
**dimension-extensible** — adding new computational machinery means
adding cells at the appropriate dimension, not redesigning Layer 0.

### M04 SN strategy: Path 2 staged

* **Stage 1 (Era S Day 38–40)**: Tait reducibility predicate
  `RC : Ty → Term → Prop`, fundamental theorem proving every
  well-typed term is reducible, SN as corollary. ~3000 LoC.
  Prop-valued logical relation — no eval function, no `ValueTerm`
  inductive yet.
* **Stage 2 (Era S Day 41–45)**: `ValueTerm` mutual inductive
  (closure-based, no host functions), `eval` structurally recursive
  on Term (termination via Stage 1's fundamental theorem),
  `quote : ValueTerm → NormalTerm`, decidable Conv via
  `decEq (quote (eval t1)) (quote (eval t2))`. ~2500 LoC delta.

**Total Era S: ~5500 LoC.** Both stages ship; Stage 2 builds on
Stage 1's SN witness rather than redoing termination.

### FX1 trust spine interlock

Per `kernel-metaplan.md`, every per-Day deliverable receives a
root-status label. Default for this roadmap's output is `FX-rich`.
Promotion ladder:

```
declared → typed → computational → encoded-sound → checker-sound → FX0-certified
```

Only `checker-sound` (covered by `FX1.check_sound`) and
`FX0-certified` are root-trust statuses. v1.0 close-out path
(`kernel-sprint.md`) ships `FX1.check_sound`. **THIS roadmap
describes post-v1.0 evolution; FX1 readiness is presupposed for any
"Bridge"-status promotion.**

---

## Part I — Mathematical Foundations

This Part supplies the precise mathematical objects, theorems, and
literature pointers underlying every Era's operational plan.
Math-dense content preserved verbatim from the merged `errratas.md`.
Each Day in Part II references the relevant §X here.

### §1. Polygraph definition (Burroni 1993, Métayer)

A polygraph (a.k.a. computad, Street 1976) is built inductively.

**Definition 1.1** (n-polygraph). For each n ≥ 0, an n-polygraph is
defined by induction:

```
0-polygraph:    a set X₀ (the 0-cells)

(n+1)-polygraph (X, X_{n+1}):
  • An n-polygraph X
  • A set X_{n+1}
  • Source/target maps  s_{n+1}, t_{n+1} : X_{n+1} → X_n^*
    where X_n^* is the FREE n-CATEGORY generated by X
  • Such that for all c ∈ X_{n+1}, s(c) and t(c) are PARALLEL:
        s_n(s_{n+1}(c)) = s_n(t_{n+1}(c))
        t_n(s_{n+1}(c)) = t_n(t_{n+1}(c))
```

**Definition 1.2** (∞-polygraph). The colimit ∞-polygraph X_∞ has
cells at every dimension, with X_n^* = colim_{m ≤ n} X_m^*.

**Theorem 1.3** (Burroni). The category Pol_∞ of ∞-polygraphs admits
all small limits and colimits, has a forgetful functor U : Pol_∞ →
Cat_∞ to ω-categories, and U has a left adjoint F : Cat_∞ → Pol_∞.

**Corollary 1.4** (Free ω-category from polygraph). Every n-polygraph
X presents a free n-category F(X), which is the universal n-category
generated by X subject to no relations.

**Operadic / Squier reading (FX commitment)**. For rewriting
applications (Squier 1987, Métayer 2008), the "free n-category"
generated by an n-polygraph admits *strings* (composites) of n-cells
as source/target of (n+1)-cells, not single n-cells. Equivalently:
the free n-category is a multicategory or PROP. Under this reading,
1-cells can have arity (n, m) for any natural numbers — multi-input
multi-output. **This subsumes Lafont-style interaction nets and
hypergraphs natively.** FX's PolyTerm uses this operadic reading
throughout; HyperTerm is not a separate IR but a sharing-cell family
within PolyTerm.

**FX commitment**: PolyCell (Day 10) is the data underlying X_n;
TypedPolyTerm (Day 12) is the indexed data structure for the typed
variant; Layer P implements F and U as kernel operations over
operadic polygraphs.

### §2. Free ω-category construction in detail

**Definition 2.1** (Free n-category over polygraph X).

```
X_0^* = X_0  with identities only at dim 0

X_{n+1}^* (the free (n+1)-category over X_{n+1}) consists of:
  • All cells of X_n^*  (lifted via inclusion)
  • Free vertical compositions: for parallel n+1-cells α, β, the
    formal composite α ∗_n β
  • Free horizontal compositions (whiskering): for c ∈ X_{n+1}
    with t(c) = s(c'), the formal composite c · c'
  • Identity (n+1)-cells id_α for α ∈ X_n^*
  Quotiented by:
  • Associativity:  α ∗ (β ∗ γ) = (α ∗ β) ∗ γ
  • Unit laws:       id ∗ α = α = α ∗ id
  • Interchange:     (α ∗ β) · (γ ∗ δ) = (α · γ) ∗ (β · δ)
```

**Theorem 2.2** (Strict ω-category laws). The above presentation
satisfies all strict ω-category axioms. Métayer 2008 gives the
homotopy-coherent (weak) variant.

**FX commitment**: Day 10 ships strict ω-categorical composition;
Day 14 ships weak coherence via dim-3 cells; Day 63+ extends to
∞-groupoidal coherence.

### §3. Coherence theorems

For weak n-categories, coherence is non-trivial.

**Theorem 3.1** (Mac Lane 1963 — pentagon coherence for monoidal
categories). The pentagon law

```
((A ⊗ B) ⊗ C) ⊗ D --α--> (A ⊗ (B ⊗ C)) ⊗ D --α--> A ⊗ ((B ⊗ C) ⊗ D)
   |                                                  |
   α                                                  ↓ id ⊗ α
   ↓                                                  
(A ⊗ B) ⊗ (C ⊗ D) --α--> A ⊗ (B ⊗ (C ⊗ D))
```

implies all higher associativity coherences.

**Theorem 3.2** (Joyal-Street 1993 — braided coherence). Pentagon
+ hexagon imply all coherences for braided monoidal categories.

**Theorem 3.3** (Gurski 2013 — tricategorical coherence). Every
tricategory is triequivalent to a Gray-category. Coherence reduces
to a polygraphic resolution of dim ≤ 4.

**Theorem 3.4** (Squier 1987 — polygraphic coherence). A finite
convergent rewriting system has a finite presentation iff its
polygraphic resolution at every dim is finitely generated.

**FX commitment**: Day 14 ships strategy-equivalence as dim-3 cells
satisfying pentagon + hexagon. Day 63 extends to higher coherences
via cubical machinery.

### §4. Confluence machinery

**Definition 4.1** (Reduction relations).

```
Local confluence (WCR):  t →¹ a, t →¹ b ⟹ ∃c. a →* c ∧ b →* c
Strong confluence (SCR): t →¹ a, t →¹ b ⟹ ∃c. a →= c ∧ b →= c    (≤ 1 step)
Confluence (CR):         t →* a, t →* b ⟹ ∃c. a →* c ∧ b →* c
Diamond:                 t →¹ a, t →¹ b ⟹ ∃c. a →¹ c ∧ b →¹ c    (= 1 step)
```

**Theorem 4.2** (Newman's lemma 1942). SN ∧ WCR ⟹ CR.

**Theorem 4.3** (Hindley-Rosen 1969). If R, S are CR and they
commute (R; S = S; R as relations), then R ∪ S is CR.

**Theorem 4.4** (Tait-Martin-Löf parallel reduction). For β-reduction
in λ-calculus, defining parallel reduction →_∥ as the reflexive
contextual closure, →_∥ has the diamond property, hence (→_∥)* = →*
is CR.

**Theorem 4.5** (Knuth-Bendix completion). For terminating term
rewriting systems, given critical pairs, completion either succeeds
(producing a confluent system), fails (irreducible critical pair), or
diverges.

**Theorem 4.6** (Squier polygraphic resolution). A polygraph is
**finitely derivation type** (FDT) iff its 3-polygraph of
critical-pair joins is finitely generated. FDT implies CR.

**FX commitment**: Day 13 ships diamond property at dim 2 via
Tait-MLF (Theorem 4.4); Era V Day 32 extends to β+η via Geuvers 1992
adaptation; Day 87 ships user-extensible β rules with Knuth-Bendix-
style verification (STRICT-35).

### §5. The 24-dimensional decidability matrix

FX's grade dimensions (original 21 + dim-22 consistency from
Era IV + dim-23 energy from Era IV.5 / Era V D38.B + dim-24
incrementality from Era V D38.A change calculus extension):

| # | Dimension | Algebraic structure | Decidability |
|---|-----------|---------------------|--------------|
| 1 | Type | Indexed family of types | Bidirectional algorithm |
| 2 | Refinement | Σ-type w/ Decidable predicate | Constructive checker; SMT may emit certificates only |
| 3 | Usage | Semiring {0,1,ω} | Finite, constant time |
| 4 | Effect | Free commutative monoid | Decidable join |
| 5 | Security | Boolean lattice | Trivially decidable |
| 6 | Protocol | Finite state transducer | Decidable step |
| 7 | Lifetime | Region preorder | Decidable preorder |
| 8 | Provenance | Finite label lattice | Decidable join/meet |
| 9 | Trust | Discrete total order | Decidable order |
| 10 | Representation | Finite layout enum | Decidable equality |
| 11 | Observability | 2-element lattice | Trivial |
| 12 | Clock domain | Finite discrete set | Decidable equality |
| 13 | Complexity | Cost-tropical (BigO mod) | Decidable on closed forms |
| 14 | Precision | (ℕ, +, 0) | Constant time |
| 15 | Space | (ℕ, +, 0) | Constant time |
| 16 | Overflow | 4-element enum | Trivial |
| 17 | FP order | 2-element enum | Trivial |
| 18 | Mutation | 4-element lattice | Decidable preorder |
| 19 | Reentrancy | Boolean | Trivial |
| 20 | Size | (ℕ, ≤) | Decidable order |
| 21 | Version | Finite ordered labels | Decidable order |
| 22 | Consistency | Belnap-Dunn FOUR (bilattice) | Decidable bilattice ops |
| 23 | Energy | Finite energy model / certificate layer over (ℝ⁺, +, 0) | Decidable only for bounded closed models with explicit entropy/cost certificates |
| 24 | Incrementality | Δ-types (Cai et al. ICFP 2014) | Δ-decidable per ILC framework |

**Dimension 23 (Energy)** — added per Era IV.5 / Era V D38.B:
speculative but worth approaching because it is the physics-grounded
dimension. The kernel obligation is deliberately narrower than the
physical ambition: for a finite reduction graph and an explicitly
provided thermodynamic model/certificate, each Step may carry a
checked energy lower-bound witness. Landauer-style statements are
model theorems inside that supplied model; they are not blanket claims
that real hardware obeys the model. Total energy along a reduction
path is represented as a finite path cost / 1-cochain on the reduction
graph. This supports energy-minimal search inside checked models and
keeps the physical-realization boundary explicit.

**Dimension 24 (Incrementality)** — added per Era V D38.A:
ILC-style change calculus (Cai-Giarrusso-Rendel-Ostermann ICFP 2014).
Every type A has a change type ΔA; every function f : A → B has
a derivative Df : A × ΔA → ΔB. Required for the agentic-LLM use
case where every iteration is a change, not a fresh start; for
incremental editor support; for incremental verification
(re-typecheck only changed regions).

**Theorem 5.1** (FX dimensional decidability, bounded form). For a
finite term, finite context, bounded unfolding budget, finite
user-rule database, and active dimension set I ⊆ {1..24}, the product
∏_{i∈I} D_i is decidable when every active D_i supplies a total
decider returning either a proof or a finite counterexample. Combined
checking time is bounded by the sum of active decider costs plus the
cost of cross-dimension compatibility checks.

**Corollary 5.2**. FX kernel checking is decidable for the bounded,
certificate-checked fragment above. Polynomial-time claims require
per-dimension polynomial deciders and bounded search depth; they are
not global claims about arbitrary SMT, arbitrary user rules, or
unbounded optimization search.

**Corollary 5.3** (Energy-bounded compilation, bounded form). Given a
finite equivalence class/search graph, a finite energy model, checked
per-Step energy certificates, and budget ε > 0, the kernel can decide
whether one of the enumerated equivalent programs has total checked
energy ≤ ε. Discovering the equivalence class or validating the
physical model is outside this theorem and remains a proposal/
measurement/TCB boundary.

### §6. Constructor-driven dispatch (the engine)

**Definition 6.1** (Constructor-driven dispatch). A reduction rule
ρ : t → t' is constructor-driven iff t = E[c(args)] where:
- E is an evaluation context
- c is a CONSTRUCTOR of some type
- ρ's redex shape is determined by c
- t' is computed by case analysis on c with explicit construction

**Theorem 6.2** (Constructor-driven systems are confluent + SN-able).
For a TRS where every rule is constructor-driven and the constructor
hierarchy is well-founded, Newman's lemma applies: SN proof reduces
to per-rule termination measures.

**Examples** (rules at FX's lowest level):

| Rule | Scrutinee | Dispatch |
|------|-----------|----------|
| β-app | `app (lam body) arg` | substitute: `body[arg/0]` |
| η-app | `lam (app f.weaken (var 0))` | unweaken: `f` |
| ι-natElim-zero | `natElim natZero z s` | pick zero branch: `z` |
| ι-natElim-succ | `natElim (natSucc n) z s` | recurse: `s n (natElim n z s)` |
| β-fst-pair | `fst (pair a b)` | project: `a` |
| η-pair | `pair (fst p) (snd p)` | identity: `p` |
| transp-Refl | `transp (pathLam A.weaken) src` | identity: `src` |
| transp-Pi | `transp (pathLam (pi A B)) f` | lam-app contractum |
| ua-β | `transp (uaToEquiv e) src` | apply equiv: `e.fwd src` |
| modal-β | `modElim (modIntro inner)` | unwrap: `inner` |
| modal-η | `modIntro (modElim m)` | identity: `m` |
| effect-erase | `g (f : T with E)` when g doesn't observe E | erase E |
| refine-narrow | `(x : {n : ℕ | P n}).inner` when P decidable | project x |
| mode-coerce | mode-uniform A | coerce identity |
| bits-concat-proj | `bits {a, b}[k:0]` | slice |
| linear-consume | `consume x` | reduces uses of x to absurd |

**Property 6.3** (FX's discipline). Every rule shipped at any Day in
Part II must be expressible in this form. The strict harness
STRICT-1 + STRICT-22 verifies.

### §7. Reductions committed at the lowest level

For Layer P (polygraph substrate), the following reductions are
fundamental kernel β-rules. Each is shipped as a dim-1 polygraph
cell with confluence proof at dim-2. **Full enumeration preserved
in Appendix C — Reduction Zoo Catalog.** This subsection gives the
canonical 18 reduction families with their type-preservation +
confluence properties.

#### 7.1 β (function application)

```
β-app:    app (lam body) arg  →  body[arg / var 0]
β-appPi:  appPi (lamPi body) arg  →  body[arg / var 0]
```

**Substitution rule**: `body[arg/0]` is captured by `Term.subst0`,
defined via `Action` typeclass framework (`Foundation/Action.lean`).

**SR**: Source has type `codomainType`; target has type
`codomainType.subst0(arg)`. For non-dep arrow, `codomainType` doesn't
depend on the binder, so `subst0` is identity. For dep Π,
`codomainType.subst0(arg)` is the actual codomain at `arg`.

**Confluence**: β satisfies diamond at parallel-reduction level
(Theorem 4.4).

#### 7.2 η (function extensionality)

```
η-lam:    lam (app f.weaken (var 0))  →  f             (when f doesn't use binder)
η-lamPi:  lamPi (app f.weaken (var 0))  →  f          (when f's type matches)
```

**Permissive form** (used in Step.par for cd_lemma compatibility):

```
η-lam-par:  lam (app f.weaken arg)  →  f
            when arg ⟶_par var 0 and f doesn't use binder
```

**SR**: Source has type `Π x, codomain`; target has type `Π x,
codomain` (same). Type preserved trivially.

**Confluence**: β-η critical pair exists (consider `lam (app (lam
body) (var 0))` reducible by β to `lam (body[0/0])` and by η
to `lam body`). These join via congruence — β substitutes `var 0`
for the binder which is the identity substitution, so β-target = η-
target structurally. Geuvers 1992 proves βη-CR for CC.

**Strategic placement**: η ships at Step.par level on Day 32 (Era V);
optionally extended to single-step Step on Day 39 (with optimal
reduction).

#### 7.3 ι (recursor / pattern matching)

For each inductive type T with constructors c_1, ..., c_k, the
recursor `T.recOn` has rules:

```
ι_T_c_i:  T.recOn (c_i args) cases  →  cases.case_i args (T.recOn args' cases)
```

where `args'` are the recursive arguments of c_i.

**Examples** (full enumeration in Appendix C §R2):

```
ι-natElim-zero:    natElim natZero z s          →  z
ι-natElim-succ:    natElim (natSucc n) z s      →  s n (natElim n z s)
ι-listElim-nil:    listElim listNil z s         →  z
ι-listElim-cons:   listElim (listCons h t) z s  →  s h t (listElim t z s)
ι-boolElim-true:   boolElim boolTrue t e        →  t
ι-boolElim-false:  boolElim boolFalse t e       →  e
ι-fst-pair:        fst (pair a b)               →  a
ι-snd-pair:        snd (pair a b)               →  b
ι-recordProj:      recordProj (recordIntro fields) k  →  fields[k]
ι-modElim:         modElim (modIntro v)         →  v
ι-pathApp-refl:    pathApp (pathLam (var 0)) i  →  i
ι-glueElim:        glueElim (glueIntro b _)     →  b
```

**SR**: each rule is type-preserving by case-analysis on the
constructor's typing rule.

**Confluence**: ι rules are non-overlapping with each other (different
head constructors); ι rules and β rules don't overlap (different
eliminator/intro pairings); the system is locally confluent and
terminating, hence CR by Newman's lemma.

#### 7.4 δ (definition unfolding)

```
δ-def:  c   →  body_of(c)
        when c is a `def` or `let` binding
```

Definitionally equal terms are reducible to a common normal form via
δ. **FX**: definitions can be marked `@[reducible]` (auto-unfold) or
`@[sealed]` (no unfolding; not Lean `opaque`). δ is non-confluent if combined with η in
some pathological cases; standard practice (Coq, Lean) is to delay
δ until other reductions stabilize.

**Strategic placement**: shipped throughout, governed by
`@[reducible]` annotations (Day 10+).

#### 7.5 ζ (let binding)

```
ζ-let:  let x = a in b   →  b[a/x]
```

Equivalent to β on a lambda (`(λx. b) a`) but separated for
performance reasons (sharing).

**FX**: ζ-reduction is part of the kernel from Day 10 onward.

#### 7.6 proj (record/structure projection)

```
proj-η:  recordIntro {field_1 := r.field_1, ..., field_n := r.field_n}  →  r
proj-β:  (recordIntro fields).field_k                                    →  fields.field_k
```

**FX commitment**: proj-β is standard (Day 10+); proj-η ships on Day
32 alongside function η.

#### 7.7 σ (substitution propagation)

Not a primary reduction, but a commutation rule used in confluence
proofs:

```
σ_subst:  (lam body)[s / x]  →  lam (body[s'·↑ / x])
```

where s' is `s` lifted past the binder. Internal to Layer P.

#### 7.8 π (pair η)

```
π-pair-η:  pair (fst p) (snd p)  →  p
π-Σ-η:    sigma (proj_1 p) (proj_2 p)  →  p
```

**FX**: ships on Day 32 with function η.

#### 7.9 transp-β family (cubical)

```
transp-Refl:    transp (pathLam A.weaken) src  →  src
transp-Pi:      transp (pathLam (pi A B)) f    →  lam-app contractum
transp-Sigma:   transp (pathLam (sigma A B)) p →  pair contractum
transp-List:    transp (pathLam (list A)) xs   →  map (transp A) xs
transp-Either:  transp (pathLam (either A B)) →  either-case contractum
transp-Glue:    transp (pathLam (glue ...)) src → glue-aware contractum
```

**FX commitment**: shipped on Day 33 (Era V).

#### 7.10 hcomp-β family (cubical)

```
hcomp-cap:    hcomp sides (just-cap) at i=0  →  cap
hcomp-side:   hcomp sides cap at i=1         →  sides applied at top
hcomp-Refl:   hcomp (refl sides) cap         →  cap
```

**FX commitment**: shipped on Day 33.

#### 7.11 ua-β (univalence)

```
ua-β:    transp (uaToEquiv e) src   →  e.fwd src
```

**FX commitment**: shipped on Day 40 with the full Era V close-out.

#### 7.12 modal-β + modal-η

```
modal-β:  modElim (modIntro v)   →  v
modal-η:  modIntro (modElim m)   →  m   (when modal type allows η)
```

**FX commitment**: shipped on Day 36 (Era V) for cohesive modalities;
extended to other modalities through Era VII.

#### 7.13 effect-erase β (FX-unique)

```
effect-erase:  g (f : T with E)  →  g (f : T)
               when g : (T with E') → R and E ⊥ E' (orthogonal)
```

**Decidability**: effect-row orthogonality is decidable since effect
rows are finite. **FX commitment**: shipped on Day 34.

#### 7.14 refinement-narrow β (FX-unique)

```
refine-narrow:  (x : {n : ℕ | P n}).inner   →  x
                when P n is decidable
```

**Decidability**: requires `Decidable (P n)` instance. **FX
commitment**: shipped on Day 35.

#### 7.15 mode-coerce β (FX-unique)

```
mode-coerce:   coerce_strict_to_obs A x   →  x_in_obs
               when A is mode-uniform
```

**Decidability**: mode-uniformity is decidable on type structure.
**FX commitment**: shipped on Day 36.

#### 7.16 bits-level β (FX-unique, hardware)

```
bits-concat-proj:  bits {a, b}[k:0]  →  slice(a, b, k, 0)
bits-slice-merge:  merge (slice ...) (slice ...) at adjacent ranges → slice
```

**Decidability**: bit-vector arithmetic decidable in QF_BV.
**FX commitment**: shipped on Day 37.

#### 7.17 linear-consume β (FX-unique, grade)

```
linear-consume:  consume(x) ; e[x]   →   consume(x) ; e[absurd]
                 (uses of x after consume reduce to absurd)
```

**Decidability**: grade arithmetic decidable on (ℕ, +, 0) or
fractional perm semiring. **FX commitment**: shipped on Day 38.

#### 7.18 WMM-β family (Era VII)

Each memory model gives reordering β rules:

```
TSO-relax-relax-reorder:  load(x)_relaxed; load(y)_relaxed   →  load(y)_relaxed; load(x)_relaxed
ARM-acquire-no-reorder:   ¬ (acquire_load(x); op_y → op_y; acquire_load(x))
SC-DRF-fence-elide:       fence; expr   →  expr  when DRF and SC-equivalent
```

**Decidability**: data-race-freedom decidable per WMM axiomatic
specification. **FX commitment**: shipped on Day 53 (post Era V; Era
VII renumbered).

---

## Part II — Per-Day Plan (Day 10 – Day 95+)

Each Era's per-Day section combines:
* **Goal**: what ships at the end of this Day
* **Tasks**: granular sub-tickets for execution
* **Mathematical content**: precise objects, theorems, categorical
  structure (preserved from `errratas.md` Part II)
* **Acceptance**: zero-axiom build green + relevant strict gates

Days 32 and 38 (Era V close + Era S start) are reorganized vs
previous extended-roadmap to reflect the operadic-polygraph + Path 2
staged architecture.

## Era I — Polygraph substrate at Layer P (Day 10–15)

The foundational shift. Critical path. ~5 months.

### Day 10 — PolyCell + dimension framework (CRITICAL)

**Goal**: define the n-polygraph data structure following Burroni
1993 (Part I §1).

**Tasks**:
* [ ] D10.1 `Foundation/Polygraph/PolyCell.lean` — universal cell type
  with dimension index, source/target as parallel (n-1)-cells
* [ ] D10.2 `Foundation/Polygraph/Dimension.lean` — dimension-indexed
  inductive structure, well-foundedness on dim
* [ ] D10.3 `Foundation/Polygraph/Parallel.lean` — parallel cells
  (identical lower-dim source AND target)
* [ ] D10.4 `Foundation/Polygraph/Composition.lean` — vertical
  (sequential) and horizontal (parallel) composition; in operadic
  reading, composition is multi-input/multi-output via tensor
* [ ] D10.5 Strict harness gate `STRICT-22` — polygraph well-formedness
* [ ] D10.6 `Smoke/AuditPolyCell.lean` zero-axiom audit

**Construction**:
```
PolyCell : (n : ℕ) → Type
  | 0 ⟹ Vertex (a finite/inductive set)
  | n+1 ⟹ Σ (parallel_pair : ParallelPair n), Cell  with
    s, t : (n+1)-cell → n-cell satisfying parallel condition
```

**Theorems to ship**:
1. **Well-foundedness**: `∀ c : PolyCell n, finite-descent c` —
   structural recursion on n; no infinite descent.
2. **Source/target consistency**: `∀ c, parallel(s(c), t(c))` at
   dim n-1.
3. **Decidable equality**: `instance : DecidableEq (PolyCell n)` for
   each n, provided underlying vertex set has DecidableEq.

**Categorical structure**: `Pol_n` forms a category with morphisms =
polygraph homomorphisms preserving s, t.

**Pitfall**: the free n-category `X*` is NOT identical to `PolyCell`
— it includes freely-generated composites. Day 10 ships PolyCell
only; Day 14 ships the free closure. "Parallel" requires definitional
equality at the next-lower dim, not propositional.

**Acceptance**: PolyCell + WF + DecidableEq ship zero-axiom; STRICT-22
green.

### Day 11 — RawPolyTerm/PolyTerm — terms-as-dim-0 cells (CRITICAL)

**Goal**: encode FX's RawTerm constructors as 0-cells of an operadic
polygraph. Each constructor's port arity matches its number of
arguments. Sharing-cell families (Lamping `!`-fan, `?`-fan, brackets,
croissants) are deferred to Era III but already accommodated by the
operadic structure.

**Tasks**:
* [ ] D11.1 `Foundation/RawPolyTerm.lean` — RawTerm constructors as
  dim-0 cells with port arities; ports correspond to free variables
  + binder-introduced names
* [ ] D11.2 `Foundation/PolyTerm.lean` — typed mirror parallel to
  Term
* [ ] D11.3 Verified bijection `RawTerm.toPoly : RawTerm → RawPolyTerm`
* [ ] D11.4 Verified bijection `RawPolyTerm.toRaw : RawPolyTerm → RawTerm`
* [ ] D11.5 `RawTerm.toPoly_toRaw : ∀ t, t.toPoly.toRaw = t`
* [ ] D11.6 `RawPolyTerm.toRaw_toPoly : ∀ p, p.toRaw.toPoly = p`
* [ ] D11.7 `Smoke/AuditRawPolyBijection.lean` zero-axiom audit

**Functorial encoding**: define `φ : RawTerm → RawPolyTerm` as a
functor between the appropriate categories.
* RawTerm has its own structural inductive form (free term algebra).
* RawPolyTerm encodes the same data with port/wire structure.
* `φ` is a structure-preserving bijection.

**Theorems to ship**:
1. **Bijection**: `RawTerm.toPoly` is a bijection with inverse
   `RawPolyTerm.toRaw`.
2. **Functoriality**: `φ` commutes with substitution:
   `(t.subst σ).toPoly = t.toPoly.subst σ`.
3. **Action preservation**: rename, weaken, lift commute with `φ`.

**Categorical statement**: `φ` is a natural isomorphism between the
free term algebra functor (`RawTerm`) and the polygraph 0-cell
functor (`RawPolyTerm`).

**Pitfalls**: cells of variable arity (binders introduce arity
changes via port flow); mode discipline (intrinsic typing) handled at
the typed-mirror layer Day 12.

**Acceptance**: bijection + functoriality + action commute, all
zero-axiom; STRICT-22 extends to RawPolyTerm.

### Day 12 — Step-as-dim-1 cells + intrinsic typing for PolyTerm (CRITICAL)

**Goal**: encode the Step relation as 1-cells of the polygraph, with
sources and targets being 0-cells (terms). Lift PolyTerm to
intrinsically typed `PolyTerm : Ctx → Ty → RawPolyTerm → Type`.

**Tasks**:
* [ ] D12.1 `Foundation/PolyTerm.lean` — typed `PolyTerm` mirroring
  intrinsic Term: `PolyTerm : Ctx mode level scope → Ty level scope
  → RawPolyTerm scope → Type`
* [ ] D12.2 Verified bijection `Term ⇌ PolyTerm` preserving raw
  projection (`Term.toRaw = (Term.toPoly).toRawTerm` definitionally)
* [ ] D12.3 `Foundation/Polygraph/Step.lean` — Step constructors as
  dim-1 cells with verified source/target
* [ ] D12.4 Embedding `Step ⇌ Dim1Cell PolyTerm` with verified
  equivalence on reduction shape
* [ ] D12.5 STRICT-23: dimensional consistency (Step ctors → dim-1
  cells preserve typing across the bijection)
* [ ] D12.6 `Smoke/AuditTypedPolyEmbedding.lean`

**Construction**:
```
PolyTerm : Ctx → Ty → RawPolyTerm → Type
  -- mirrors Term, with RawPolyTerm rather than RawTerm

Dim1Cell : PolyTerm s → PolyTerm t → Type
  -- mirrors Step
```

**Bijection theorem**: `Step ⇌ Dim1Cell` preserving:
* Source/target maps (`s ↦ source term`, `t ↦ target term`)
* Reduction shape (β ↦ β-cell, ι ↦ ι-cell, etc.)
* Type preservation (SR holds for both)

**β and η coverage at dim-1 — kernel commitment** (per Part I §7.1, §7.2; full
enumeration in Appendix C). Every type former in FX's kernel (Π, Σ, arrow,
Bool, Nat, List, Option, Either, Pair, Record, Refine, Modal, Path, Glue,
Codata, Session, Effect, Equiv, IdStrict, Id) ships its β-rule AND its
η-rule as a dim-1 cell — no exceptions. PolyTerm dim-1 cell ctors:

```
-- β rules (eliminator-on-introduction):
β-app :              Dim1Cell  (app (lam b) a)                     (b[a/0])
β-appPi :            Dim1Cell  (appPi (lamPi b) a)                 (b[a/0])
β-fst-pair :         Dim1Cell  (fst (pair a b))                    a
β-snd-pair :         Dim1Cell  (snd (pair a b))                    b
β-recordProj :       Dim1Cell  (recordProj (recordIntro fields) k) (fields[k])
β-refineElim :       Dim1Cell  (refineElim (refineIntro v p))      v
β-modElim :          Dim1Cell  (modElim (modIntro v))              v
β-pathApp-pathLam :  Dim1Cell  (pathApp (pathLam body) i)          (body[i/0])
β-glueElim :         Dim1Cell  (glueElim (glueIntro b _))          b
β-codataDest :       Dim1Cell  (codataDest (codataUnfold ... obs)) (lookup obs)
β-sessionRecv :      Dim1Cell  (sessionRecv (sessionSend channel v) ...)
β-effectHandle :     Dim1Cell  (handle (perform op args) k)        (handler.case_op args k)
β-equivApp :         Dim1Cell  (equivApp (equivIntroHet f g h) x)  (f x)
... (one β rule per (eliminator, introduction) pair in §R1-§R8)

-- η rules (introduction-on-eliminator collapses to identity):
η-lam :              Dim1Cell  (lam (app f.weaken (var 0)))        f       (when var 0 ∉ f)
η-lamPi :            Dim1Cell  (lamPi (appPi f.weaken (var 0)))    f       (similarly)
η-pair :             Dim1Cell  (pair (fst p) (snd p))              p
η-record :           Dim1Cell  (recordIntro {fᵢ := r.fᵢ})          r
η-modal :            Dim1Cell  (modIntro (modElim m))              m       (modal type allows η)
η-path :             Dim1Cell  (pathLam (pathApp p (var 0)))       p       (when var 0 ∉ p)
η-codata :           Dim1Cell  (codataUnfold {oᵢ := c.oᵢ})         c
η-equiv :            Dim1Cell  (equivIntroHet (extract... e))      e
η-refine :           Dim1Cell  (refineIntro (refineElim r) p)      r       (η for refinement)
η-unit :             Dim1Cell  any : Ty.unit                       ()      (η for unit, definitional)

-- ι rules (recursors on constructors):
ι-natElim-zero, ι-natElim-succ, ι-natRec-zero, ι-natRec-succ,
ι-listElim-nil, ι-listElim-cons, ι-boolElim-true, ι-boolElim-false,
ι-optionMatch-none, ι-optionMatch-some, ι-eitherMatch-inl, ι-eitherMatch-inr,
ι-idJ-refl, ι-oeqJ-oeqRefl, ι-idStrictRec-idStrictRefl
```

**Coverage discipline (STRICT-23 + STRICT-9 jointly enforce)**:
Every Step.par ctor in the kernel has both β and η dim-1 cell mirrors when
the type former admits η. Type formers without η-laws (raw inductives like
Bool/Nat/List where η is non-canonical) instead have a *uniqueness theorem*:
ι rules are exhaustive and any normal-form-of-that-type is a constructor
expression.

**Cubical β/η** (full enumeration in Day 33 / Part I §7.9–§7.11): transp-Refl,
transp-Pi, transp-Sigma, transp-{closed types}, transp-Glue, hcomp-cap,
hcomp-side, hcomp-Refl, ua-β, ua-η (transp at uaToEquiv reduces; quote
reads back as identity equiv when path is reflexive).

**FX-unique β/η** (Days 34–38 / Part I §7.13–§7.17): effect-erase,
refine-narrow, mode-coerce, bits-level, linear-consume — each with its
type former's η counterpart where the type theory admits it.

**Categorical statement**: Step is equivalent to a Burroni 1-polygraph
generator over the 0-polygraph PolyTerm.

**Pitfall**: subject reduction must hold — `source.type = target.type`
for each Step ctor. Confluence at this level isn't yet diamond — that's
Day 13.

**Acceptance**: bijection theorems Step ⇌ Dim1Cell zero-axiom; STRICT-23
green; SR preserved across encoding.

### Day 13 — Confluence-as-dim-2 cells (CRITICAL)

**Goal**: represent confluence proofs as 2-cells. A dim-2 cell has
source/target as parallel 1-cells (i.e., two parallel reductions).
The 2-cell witnesses their confluence.

**Tasks**:
* [ ] D13.1 `Foundation/Polygraph/Confluence.lean` — confluence
  proofs (`cd_lemma`, diamond) as dim-2 cells with explicit
  source/target as parallel pairs of dim-1 cells
* [ ] D13.2 Embedding `cd_lemma ⇌ Dim2Cell PolyTerm` with verified
  Squier-coherence shape
* [ ] D13.3 Diamond property at dim 2
* [ ] D13.4 STRICT-24: dim-2 cells respect dim-1 sources/targets
* [ ] D13.5 `Smoke/AuditPolygraphConfluence.lean`

**Construction**:
```
Dim2Cell : (α β : ParallelPair Dim1Cell) → Type
where α and β have same source and same target (in 0-cells)

example: cd_lemma's diamond
  dim2_diamond : ∀ {t a b}, (t →¹ a) → (t →¹ b)
                 → ∃ c. (a →¹ c) ∧ (b →¹ c)
```

**Theorems to ship**:
1. **Squier coherence** (Part I §3 Theorem 3.4): every critical pair
   has a dim-2 cell.
2. **Diamond property** (Part I §4 Theorem 4.4): parallel reduction
   has the diamond.
3. **Tait-Martin-Löf**: the parallel closure has CR.

**Categorical statement**: Squier's theorem says that a confluent
+ terminating 1-polygraph is finitely-derivation-type iff its
dim-2 (critical pair completion) polygraph is finitely generated.

**Pitfall**: β-η critical pairs require careful enumeration
(Knuth-Bendix). Cubical β rules introduce dimension-specific
critical pairs that need cubical-aware diamond proofs (CCHM 2017,
ABCFHL 2019). Both deferred to Era V Day 32–33.

**Acceptance**: existing `cd_lemma` reformulated as dim-2 cell
generation; STRICT-24 green.

### Day 14 — Strategy-equivalences-as-dim-3 cells (CRITICAL)

**Goal**: represent equivalences between rewrite strategies as 3-cells.
A dim-3 cell witnesses that two parallel dim-2 cells (which are pairs
of parallel dim-1 cells) reach the same result modulo permutation.

**Tasks**:
* [ ] D14.1 `Foundation/Polygraph/Strategy.lean` — rewrite strategies
  as paths in the dim-1 graph; equivalences between strategies as
  dim-3 cells
* [ ] D14.2 Strategy combinator framework: leftmost / outermost /
  optimal / parallel / random
* [ ] D14.3 Strategy-equivalence at dim 3
* [ ] D14.4 Cost-graded dim-3 cells: each cell carries a cost-tropical
  weight encoding strategy efficiency
* [ ] D14.5 STRICT-25: dim-3 cells respect dim-2 sources/targets
* [ ] D14.6 `Smoke/AuditPolygraphStrategy.lean`

**Construction**:
```
Strategy : Type := List Dim1Cell  -- a sequence of rewrites
StrategyEquiv : Strategy → Strategy → Prop
  := paths produce same NF, with dim-3 cell as witness
```

**Cost-graded extension**: each dim-3 cell carries a cost-tropical
weight `cost : (ℝ̂, min, +)` representing strategy efficiency.

**Theorems to ship**:
1. **Strategy equivalence is transitive** at dim 3.
2. **Cost-tropical structure** forms a semiring on dim-3 cells.
3. **Pentagon coherence at dim 3** (Part I §3 Theorem 3.1) holds for
   strategy-composition.

**Categorical statement**: dim-3 cells witness 2-categorical
coherence of strategy associativity. Equivalent to the polygraph's
3-skeleton being a (2,3)-Gray-category.

**Pitfall**: strategy equivalence must respect cost monotonically.
Pentagon law applies to strategy composition; more complex coherences
(hexagon, MacLane) arrive in Era X via cubical machinery.

**Acceptance**: pentagon coherence + cost-tropical semiring laws
zero-axiom; STRICT-25 green.

### Day 15 — Era I close-out (CRITICAL)

**Goal**: ensure the (∞,3)-truncation of the FX polygraph is fully
verified.

**Tasks**:
* [ ] D15.1 `PolyTerm` ships at Layer P with dim 0-3 fully verified
* [ ] D15.2 `Foundation/Polygraph/Spec.lean` — universal spec for any
  cell at any dimension
* [ ] D15.3 Audit dashboard reports +500 polygraph-related decls
  zero-axiom
* [ ] D15.4 `kernel-metaplan.md` updated with polygraph substrate
* [ ] D15.5 `ARCHITECTURE.md` updated with new Layer P
* [ ] D15.6 Era I commit + status report

**Theorems shipped**:
1. **Universal property of PolyCell**: free n-category construction
   has correct universal property (Part I §1.4).
2. **Squier coherence** at dim 2 (Part I §3.4).
3. **Strategy equivalence** at dim 3 with pentagon coherence
   (Part I §3.1).
4. **Free ω-category restriction**: FX (∞,3)-truncation gives a
   strict 3-category (Part I §2.2).

**β/η coverage status**: every type former in the FX kernel has its
β-rule + η-rule represented as a dim-1 cell (per Day 12). PolyTerm
encoding is **complete with respect to β/η for all terms and types**.
Future eras add reductions (cubical β in Day 33, FX-unique β in
Days 34–38) as further dim-1 cells.

**Acceptance**: every existing FX kernel theorem can be re-stated in
(∞,3)-polygraph form; bidirectional encodings preserve all
properties; no existing audit gate regresses.

---

## Era II — Kernel retrofit onto polygraph (Day 16–20)

Re-expresses existing kernel operations as polygraph cells. ~4 months.

### Day 16 — Reduction kernel retrofit (CRITICAL)

**Goal**: re-express `Step` operations as projections through
PolyTerm. No behavioral change; only equivalence theorems added.

**Tasks**:
* [ ] D16.1 `Reduction/Step.lean` operations re-projected through
  PolyTerm
* [ ] D16.2 `Reduction/StepStar.lean` as dim-1 path-composition
* [ ] D16.3 `Reduction/ParRed.lean` as parallel dim-1 cells
* [ ] D16.4 Equivalence theorem (below)
* [ ] D16.5 Strict harness extension catches divergence
* [ ] D16.6 Smoke audit reduction retrofit

**Theorems to ship**:
1. **Reduction equivalence**: `∀ s t, Step s t ⇔ Dim1Cell (s.toPoly) (t.toPoly)`.
2. **Parallel reduction commutes with projection**:
   `Step.par s t ⇔ ∃ parallel-set of Dim1Cells encoding the same
   reduction shape`.
3. **Subject reduction preserved** under encoding (each Step ctor's
   SR theorem lifts to a Dim1Cell SR theorem).

**No mathematical content change** — this is a retrofit that ensures
existing semantics aren't perturbed. Era II is purely additive.

**Acceptance**: equivalence theorem proven for all 105+ Step ctors;
strict harness STRICT-3/STRICT-9 parity gates extend to Dim1Cell.

### Day 17 — Confluence kernel retrofit (CRITICAL)

**Goal**: lift `cd_lemma` to dim-2-cell generation. The function
`cd : Dim1Cell s t → Dim2Cell (s.toPoly →* nf)` produces the
canonical diamond completion.

**Tasks**:
* [ ] D17.1 `Confluence/RawCd.lean` re-expressed as dim-2-cell
  generator
* [ ] D17.2 `Confluence/RawCdLemma.lean` lifted to polygraph proof
* [ ] D17.3 `Confluence/Diamond.lean` as dim-2 diamond cells
* [ ] D17.4 `Confluence/ChurchRosser.lean` as parStar polygraph
  closure
* [ ] D17.5 Equivalence theorems for entire confluence cascade
* [ ] D17.6 Smoke audit confluence retrofit

**Theorems to ship**:
1. **cd_lemma at dim 2**: `cd` produces a diamond completion as a
   dim-2 cell witness.
2. **Diamond property at parallel reduction** (Part I §4 Theorem
   4.4): pairs of par-reductions admit diamond completion.
3. **Church-Rosser at dim 2**: the closure of dim-1 cells via
   dim-2 diamond is CR.

**Categorical statement**: Squier's coherence (Part I §3 Theorem
3.4) applies — the polygraph's dim-2 completion is the canonical
witness of confluence.

**Acceptance**: existing `cd_lemma` reformulated as dim-2-cell
generation; STRICT-24 green; all consumers continue to typecheck
zero-axiom.

### Day 18 — HoTT/Cubical layer retrofit (parallel)

**Goal**: encode cubical paths as dim-1 cells with interval-cube
coordinates.

**Tasks**:
* [ ] D18.1 `HoTT/Path` as dim-1 path-cells (Path A x y has cells
  at dim 1 from x to y)
* [ ] D18.2 `HoTT/Equivalence` as dim-2 cells
* [ ] D18.3 `HoTT/HIT` constructors as dim-0 + dim-1 cells
* [ ] D18.4 `Cubical/PathLemmas` as polygraph identities
* [ ] D18.5 Equivalence + smoke audits

**Cubical specifics**:
* **Path types**: `Path A x y` has cells at dim 1 from x to y
* **Cube faces**: the n-cube I^n has n+1 distinct face inclusions
* **Kan composition**: `hcomp + transp` give cubical composition
* **Glue types**: identify type-equivalence with path-equivalence

**Categorical statement**: the cubical model lives in the
**(∞,1)-topos of cubical sets PSh(□)**, where □ is the cube
category. CCHM 2017 establishes the model; ABCFHL 2019 fixes
regularity.

**Pitfall**: cubical TT's "regularity" condition needs care. CCHM
violates it weakly; ABCFHL fixes it. FX uses ABCFHL-style
regularity per Part VI §C1.

**Acceptance**: cubical encoding zero-axiom; STRICT-24 extends to
dim-1/2 cubical cells.

### Day 19 — Graded/Modal/Refine retrofit (parallel)

**Goal**: lift Wood-Atkey graded calculus, Schreiber modal
adjunctions, refinement type-checking into polygraph form.

**Tasks**:
* [ ] D19.1 `Graded/` operations as dim-1 with grade-tropical weight
* [ ] D19.2 `Modal/` modalities as dim-2 functors between polygraph
  fibres
* [ ] D19.3 `Refine/` predicates as dim-3 refinement-functor cells
* [ ] D19.4 Equivalence + smoke audits

**Mathematical content**:
* **Graded calculus**: Wood-Atkey 2022 corrected Lam rule with
  context division `Γ / p` lifted to dim-1 with grade-tropical
  weights on each rewrite cell (Part VI §C5 cost-tropical
  equivalence).
* **Modal**: per Schreiber's framework, the modal layer has
  adjoint functors (♭ ⊣ ◇ ⊣ □ ⊣ ♯) acting on polygraph fibres.
  Each modality is a dim-2 functor.
* **Refine**: refinement types as Σ-types with Decidable
  predicates, lifted to dim-3 refinement-functor cells (Era VIII
  groundwork).

**Theorems to ship**:
1. **Graded SR**: Wood-Atkey discipline preserves typing through
   the dim-1 polygraph encoding.
2. **Modal functorial laws**: each modality is a functor satisfying
   the Schreiber-Shulman adjunction laws (Part VI §C3).
3. **Refinement decidability**: Decidable predicates compute
   through the dim-3 refinement functor.

**Acceptance**: graded + modal + refine retrofit zero-axiom; Atkey
2018 attack still rejected (regression test from D5.5).

### Day 20 — Era II close-out (CRITICAL)

**Goal**: every existing kernel operation expressible in polygraph
form. Performance regression check: polygraph form within 5% of
tree form.

**Tasks**:
* [ ] D20.1 Every existing kernel operation has polygraph form
* [ ] D20.2 Audit dashboard reports +1000 retrofit decls zero-axiom
* [ ] D20.3 Performance regression check (≤5% slowdown for tree-walk)
* [ ] D20.4 `MIGRATION.md` updated documenting polygraph migration
* [ ] D20.5 Era II commit

**Headline theorems**:
1. **Embedding faithfulness**: φ is a faithful functor from current
   FX kernel (Tree column) to polygraph kernel (PolyTerm column).
2. **No theorem regression**: every shipped audit gate continues to
   pass under polygraph encoding.

**Acceptance**: any FX program can be processed via polygraph
substrate without behavioral change; existing tooling continues to
work via projection; new tooling can target polygraph directly.

---

## Era III — Sharing cells in PolyTerm + stratification + BSP (Day 21–25 + 25.A)

**Architectural note**: previous extended-roadmap envisioned HyperTerm
as a separate IR. With operadic PolyTerm (Part I §1, Squier reading),
hypergraph structure (Lafont 1990) is a *cell family within
PolyTerm*, not a separate type. Era III enables sharing-cell ctors in
PolyTerm + ships stratification + BSP framework atop the unified IR.
~4 months.

### Day 21 — Lamping sharing-cells in PolyTerm (CRITICAL)

**Goal**: encode Lamping-style optimal sharing as additional cell
families in PolyTerm at dim-0/1, NOT as a separate IR.

**Lamping interaction nets** (1990): a sharing-aware extension of
λ-calculus where each cell has a principal port + N auxiliary ports;
sharing fans (`!`) and de-share fans (`?`) explicitly track
duplicated subterms.

**Tasks**:
* [ ] D21.1 `Foundation/PolyTerm/SharingCells.lean` — sharing-cell
  family added to PolyTerm at dim-0:
  - `shareFan` (1→2 ports): replicates a wire (`!`-cell)
  - `desharefan` (2→1 ports): joins two wires (`?`-cell)
  - `bracket` (level-tracking nesting depth)
  - `croissant` (level-tracking nesting depth)
* [ ] D21.2 Lamping-style optimal sharing encoding
  `Term → PolyTerm[core + sharing cells]` with explicit fans
* [ ] D21.3 Verified roundtrip on the no-sharing fragment
  (`Term ⇌ PolyTerm[core only]`); sharing-encoded form is lossy
  to Tree (unfold can be exponential)
* [ ] D21.4 STRICT-26: sharing-cell well-formedness (every fan port
  paired correctly; brackets/croissants at consistent levels)
* [ ] D21.5 Smoke audit sharing cells

**Theorems**:
1. **Lamping correctness**: optimal reduction with sharing cells
   preserves semantic equivalence (Asperti-Mascari-Guerrini 1998).
2. **Lévy optimality** (1978): each redex family contracted at most
   once when reduction strategy is optimal.
3. **Roundtrip on no-sharing fragment**:
   `PolyTerm[core only].toTerm ∘ Term.toPolyTerm = id`.

**Pitfall**: sharing fans must track levels via brackets/croissants;
get this wrong and reduction loses confluence. Lamping's ~13 rules
(or BOHM's ~9) are the reference.

**Acceptance**: PolyTerm with sharing cells encodes Term losslessly
when no sharing is introduced; sharing extension preserves Lamping
discipline; STRICT-26 green.

### Day 22 — Stratification (GEMM vs Path) (CRITICAL)

**Goal**: decidable classifier `stratify : Subgraph → {GEMM, Path,
Mixed}` factoring a polygraph subgraph into hardware-friendly strata.

**Tasks**:
* [ ] D22.1 `Foundation/Polygraph/Stratify.lean` — decidable
  classifier
* [ ] D22.2 Verified properties: unique stratification, decomposable
  Mixed → GEMM ∪ Path, polynomial decision time
* [ ] D22.3 Per-stratum locality lemmas
* [ ] D22.4 Cross-stratum independence proof
* [ ] D22.5 Smoke audit stratification

**Stratification criterion**:
* **GEMM**: subgraphs where reductions factor as semiring matrix
  products. Detected by:
  - All operations are local + pure
  - Reductions can be expressed as `M ⊗_S N` for some semiring S
  - Examples: closure operations, decidable predicate evaluation
* **Path**: subgraphs involving cubical paths, transp, glue, hcomp.
  Detected by presence of path-cell constructors.
* **Mixed**: contains both, decomposable into GEMM ∪ Path.

**Theorem**: `stratify` is decidable in O(|G|) for subgraph G;
decomposition for Mixed is unique.

**Categorical statement**: stratification factors the polygraph
hypergraph into its **GEMM-stratum** (algebraic, GEMM-friendly via
idempotent semirings per Appendix B) and **Path-stratum** (cubical,
sequential).

**Acceptance**: stratify decidable + linear-time + uniqueness
proven; STRICT-26 green.

### Day 23 — Strong confluence at hypergraph level (CRITICAL)

**Goal**: Lafont's strong confluence theorem for FX cells. Strong-CR
> CR — each rule commutes with each other rule directly without
extra steps.

**Tasks**:
* [ ] D23.1 Lafont's strong-confluence theorem for FX cells
* [ ] D23.2 Per-rule local rewriting non-conflict proof
* [ ] D23.3 cd_lemma lifted to hypergraph rewriting
* [ ] D23.4 Smoke audit hypergraph confluence

**Theorem (Lafont 1990)**: For any pure interaction net system
(determinism + locality), strong confluence holds:
```
t →¹ a ∧ t →¹ b on disjoint subgraphs ⟹ a →¹ c ∧ b →¹ c
                                          for the same c (no extra steps)
```

**Corollary**: parallel rewriting on disjoint subgraphs is correct
without scheduling overhead.

**Strong-CR vs CR distinction** (Part I §4):
* CR: `t →* a ∧ t →* b ⟹ ∃ c. a →* c ∧ b →* c`
* Strong-CR: each rule commutes with each other rule directly

**FX commitment**: GEMM stratum has strong-CR (Lafont applies);
Path stratum has CCHM-style cubical confluence (weaker but still
CR). Cross-stratum independence (D22.4) ensures the two stratum
proofs compose.

**Acceptance**: strong confluence proved at GEMM stratum;
CCHM confluence proved at Path stratum; STRICT-23 extends to
hypergraph.

### Day 24 — BSP super-step framework (CRITICAL)

**Goal**: Valiant 1990 Bulk-Synchronous Parallel model for
polygraph execution.

**Tasks**:
* [ ] D24.1 `Foundation/BSP.lean` — super-step decomposition
* [ ] D24.2 Terminal-node detection + sync barrier
* [ ] D24.3 BSP scheduling theorem: any super-step ordering correct
* [ ] D24.4 Pipelined super-step framework
* [ ] D24.5 Smoke audit BSP semantics

**BSP cost model** (per super-step):
```
Cost = max_{processor i}(work_i + h_i · g) + L
where:
  work_i = local computation on processor i
  h_i = communication volume (# words sent/received)
  g = bandwidth-per-word (architecture parameter)
  L = latency / barrier cost (architecture parameter)
```

**For FX on B200 cluster** (concrete instantiation):
* g ≈ 1/(28.8 TB/s) per super-step (NVSwitch bandwidth)
* L ≈ 5 μs (NVLink latency)
* work per super-step ≈ ms-scale (TensorCore throughput)

**Theorems to ship**:
1. **BSP equivalence**: any topological super-step ordering is
   correct (independence-preserves-result for parallel cells).
2. **Sync barrier soundness**: all writes observable post-barrier.

**Acceptance**: BSP model + cost-bound proven; multi-processor
schedule correctness verified.

### Day 25 — Era III close-out (CRITICAL)

**Goal**: stratified BSP polygraph execution fully verified.

**Tasks**:
* [ ] D25.1 PolyTerm sharing-cells + stratification + BSP fully
  verified (Day 21 sharing folded into PolyTerm; no separate
  HyperTerm)
* [ ] D25.2 Performance benchmark: polygraph form vs tree form
* [ ] D25.3 Audit dashboard reports +400 polygraph-Era-III decls
  zero-axiom
* [ ] D25.4 Era III commit

**Headline theorem**: the (∞,3)-polygraph projects faithfully to
the (stratified, BSP)-polygraph rewriting system, preserving all
reduction relations.

**Acceptance**: kernel can process any FX program via polygraph IR
with verified equivalence to tree IR; stratification correctly
decomposes; BSP execution model proven.

### Day 25.A — Pipe-chain pipeline parallelism (CRITICAL)

**Goal**: compiler pass mapping FX surface `|>` chains (spec §4.2 +
§11.12) to BSP super-step decomposition with verified observable
equivalence. Pipeline stages = super-steps when adjacent operations
commute under effect-row analysis; data-dependent stages serialize.

**Construction (pipe-chain to stage DAG)**:
```
PipeChain := e_0 |> f_1 |> f_2 |> ... |> f_n
           = (...((e_0 |> f_1) |> f_2)...) |> f_n       -- left-assoc

StageDAG := finite DAG with
  nodes : Stage = { input_type, output_type, effect_row,
                    function_body, latency_estimate }
  edges : Dependency = predecessor.output ~= successor.input

def schedule : PipeChain -> StageDAG
  -- per |>-edge, classify:
  --   sequential edge  iff effect_row(f_i) cap effect_row(f_i+1) != 0
  --                    on conflicting access (read-after-write,
  --                    write-after-write per §9.4 effect taxonomy)
  --   parallel edge    iff effect_row(f_i) _|_ effect_row(f_i+1)
  --                    (orthogonal effects)
  --   pipeline-stage   iff data dependency holds but effects
  --                    commute under reordering (canonical case)
```

**Effect-row commutativity (decidable)**: for `E1, E2 in Pow(BuiltInEffects)`
the predicate `E1 _|_ E2` decides in O(|E1| · |E2|) time per §9.4:
- `Tot _|_ X` for all X (pure-anything always commutes)
- `Read _|_ Read` (multiple readers safe per §9.4)
- `Write _|_ Write` iff distinct memory regions (alias-analysis-gated)
- `IO _|_ IO` iff distinct channels (channel-type-gated)
- `Alloc _|_ X` for all X except `Alloc(Region(r))` self-conflict
  (thread-local allocators per §9.4)
- `Async _|_ Async` iff distinct task groups

**Stage-DAG to BSP super-step compilation**:
```
def compile_to_BSP : StageDAG -> BSP-super-step-sequence
  topologicalLayers : StageDAG -> List (Set Stage)
    -- stage s in layer k  <=>  max predecessor depth(s) = k
  emit each layer L_k as a BSP super-step;
  insert NVSwitch / InfiniBand sync barrier between layers
    (per Era III Day 24 BSP cost model with FEU-style g = 1/28.8 TB/s,
     L = 5 us per Era IV D28)
```

**Theorem (pipeline-equivalence)**:
```
forall (pc : PipeChain) (input : InputType pc),
  [[ pc ]](input) =_obs [[ compile_to_BSP(schedule(pc)) ]](input)
  -- Observable equivalence: same returned value + same observable
  -- side-effect sequence MODULO independent-effect commutation
  -- (Plotkin-Power 2002 algebraic effect commutativity).
```

**Theorem (latency speedup bound)**:
```
For pc with n stages and effect-row classification yielding k
parallelizable stages,
  latency_BSP(compile_to_BSP(schedule(pc)))
    <= ceil(n/p) * stage_avg_latency
       + ceil(log_2 p) * BSP_sync_barrier_cost
  where p = parallelism budget bounded by min(k, num_processors).
  Sequential baseline: n * stage_avg_latency.
  Speedup ~ n / (n/p + log p * barrier_ratio); converges to p for
            large n.
```

**Tasks**:
* [ ] D25.A.1 `Foundation/Polygraph/PipeChain.lean` — PipeChain
  inductive mirroring FX `|>` surface (spec §4.2)
* [ ] D25.A.2 `Foundation/Polygraph/StageDAG.lean` — Stage +
  Dependency + StageDAG well-formedness predicate
* [ ] D25.A.3 `Effect.commutes : EffectRow -> EffectRow -> Decidable`
  per §9.4 effect taxonomy + alias-analysis bridge
* [ ] D25.A.4 `schedule : PipeChain -> StageDAG` decidable scheduler
  (poly-time over |chain|)
* [ ] D25.A.5 `compile_to_BSP : StageDAG -> BSP-super-step-sequence`
  topological-layer compilation
* [ ] D25.A.6 Pipeline-equivalence theorem zero-axiom (Plotkin-Power
  2002 algebraic-effect commutativity bridge)
* [ ] D25.A.7 Latency-bound theorem with explicit p-bounded speedup
* [ ] D25.A.8 STRICT-65-III-PipeChain gate: pipe-chain compilation
  soundness + commutativity-decidability
* [ ] D25.A.9 Bridge to surface: FX §4.2 / §11.12 `|>` syntax
  compiles via this pass (round-trip with Surface/Print verified)
* [ ] D25.A.10 Smoke audit + commit

**References**: Valiant 1990 (BSP cost model, CACM); Backus 1978 (Can
programming be liberated from the von Neumann style?, CACM —
FP-style composition); Hughes 1989 (Why functional programming
matters, Comp. J. — pipeline composition); Marlow-Newton-Peyton-Jones
2011 (Haxl monad for parallel I/O, Haskell Symp.);
Kiselyov-Lämmel-Schupke 2004 (extensible effect rows, Haskell Symp.);
Plotkin-Power 2002 (notions of computation, FoSSaCS — effect
commutativity).

**Acceptance**: pipe-chain compilation pass zero-axiom; observable
equivalence proven under effect-row commutativity (Plotkin-Power);
latency speedup bound demonstrated on representative FX pipelines
(`map`, `filter`, `groupBy` chains from §11.12 pipeline execution
modes); FX surface `|>` no longer just sugar but a load-bearing
compilation target.

---

## Era IV — Hardware retrofit + B200 cluster (Day 26–31)

The hardware-lottery-immune realization layer. ~5 months.

### Day 26 — HardwareTarget typeclass (CRITICAL)

**Goal**: hardware abstraction as a typeclass with verified
primitives. Per-target instances declare capabilities.

**Tasks**:
* [ ] D26.1 `Foundation/HardwareTarget.lean` — typeclass
* [ ] D26.2 Per-target instances (CPU, B200, A100, FPGA, RISC-V
  RVV, ARM SVE, dataflow)
* [ ] D26.3 Capability declaration framework
* [ ] D26.4 Smoke audit per-target capability matrix

**Construction**:
```
class HardwareTarget where
  parallel_reduce : (T → T → T) → [T] → T
  atomic_op : Atomic T → T
  vector_lanes : ℕ
  memory_hierarchy : List CacheLevel
  -- ...

instance B200 : HardwareTarget where ...
instance CPU_RISC_V_RVV : HardwareTarget where ...
instance FPGA_Xilinx_Versal : HardwareTarget where ...
```

**Categorical statement**: `HardwareTarget` is a category with
morphisms = capability-preserving maps. Realizations parameterize
over `HardwareTarget` instances.

**Acceptance**: typeclass + ≥7 instances + capability-preservation
proof zero-axiom.

### Day 27 — Verified realization framework (CRITICAL)

**Goal**: realization is a functor from `Spec` to `Hardware ×
Realization` with verified equivalence.

**Tasks**:
* [ ] D27.1 `Realization` structure: spec + per-target impl + proof
* [ ] D27.2 STRICT-27: realization equivalence gate
* [ ] D27.3 Standard realization combinators (sequential, parallel,
  pipelined)
* [ ] D27.4 Smoke audit realization framework

**Definition**: a realization R for spec S on target H is a triple
`(impl, equiv, perf)` where:
* `impl : Spec → Concrete H` is the concrete implementation
* `equiv : ∀ s, ⟦impl s⟧ = ⟦s⟧` is verified equivalence
* `perf : ∀ s, time(impl s) ≤ optimal(s, H)` is performance bound

**Equivalence relation** for "verified equivalent":
* **Strong bisimulation**: every spec step matched by impl step
* **Trace equivalence**: same observable traces
* For type-theoretic operations: **observational equivalence on
  closed terms** (the HoTT-friendly notion; Part VI §C5 Era IV row).

**Acceptance**: Realization framework + STRICT-27 zero-axiom.

### Day 28 — B200 GPU realization for GEMM stratum (CRITICAL)

**Goal**: bind tropical/Boolean GEMM to hardware kernels with
verified input/output certificate formats; cuBLAS/cuDNN paths are
TCB extensions unless independently checked by reference/certificate
comparison. Ship FP8/INT8 tensor-core paths with explicit realization
status.

**Tasks**:
* [ ] D28.1 cuBLAS/cuDNN binding via verified encoding plus
  realization-assumption record / output certificate checker
* [ ] D28.2 Tropical-GEMM custom CUDA kernel (FP8/INT8 paths)
* [ ] D28.3 Boolean-GEMM kernel for reachability problems
* [ ] D28.4 NVSwitch-aware multi-GPU coordination
* [ ] D28.5 Realization equivalence proof
* [ ] D28.6 Performance audit on B200 reference workloads

**Key trust boundary**: cuBLAS is not a proof source. Either its
output is checked against a small verified certificate/reference
checker for the relevant semiring fragment, or the call is recorded
as a TCB extension (per Part VI §C7 hardware retrofit row).

**Theorems to ship**:
1. **Encoding correctness**: `GemmSubgraph.toMatrix` produces a
   matrix that, when multiplied via cuBLAS, gives the correct
   semiring reduction.
2. **Tensor-core soundness**: TensorCore FP8 multiplication is
   correct for our semiring choices (Boolean, tropical).

**Acceptance**: B200 realization equivalence proven; perf hits
target on B200 reference workloads.

### Day 29 — CPU realization for Path stratum (CRITICAL)

**Goal**: standard CCHM/ABCFHL evaluator on CPU; cache-aware paths.

**Tasks**:
* [ ] D29.1 Standard interpreter for cubical Path operations
* [ ] D29.2 Branch-prediction-friendly encoding
* [ ] D29.3 Cache-aware access patterns
* [ ] D29.4 Realization equivalence proof
* [ ] D29.5 Performance audit on representative path workloads

**Theorem**: `cpu_path_normalize : PathSubgraph → NormalForm` is
verified equivalent to the abstract CCHM evaluation (Part I §4
+ ABCFHL 2019 reference model).

**Acceptance**: CPU Path-stratum realization zero-axiom.

### Day 30 — Sync protocol + paraconsistent layer (CRITICAL)

**Goal**: hash-based reconciliation + hierarchical sync via
NVSwitch topology + 22nd grading dimension via Belnap-Dunn FOUR
bilattice.

**Tasks**:
* [ ] D30.1 Hash-based terminal-node reconciliation
* [ ] D30.2 Hierarchical sync (within-node NVSwitch, cross-node
  InfiniBand)
* [ ] D30.3 Speculative computation framework
* [ ] D30.4 Persistent memoization caching
* [ ] D30.5 Pipelined super-step execution
* [ ] D30.6 22nd grading dimension: consistency (Belnap-Dunn FOUR)
* [ ] D30.7 Adaptive logic for dialethic specs
* [ ] D30.8 Smoke audit sync + paraconsistent

**Belnap-Dunn FOUR bilattice**:
```
Truth values: T (true), F (false), B (both), N (neither)
Truth ordering: F < N, F < B, N < T, B < T
Knowledge ordering: N < F, N < T, F < B, T < B
```

**Bilattice operations**:
```
∧ (truth meet):    F ∧ x = F, T ∧ x = x, B ∧ N = F (etc.)
∨ (truth join):    T ∨ x = T, F ∨ x = x, ...
⊗ (knowledge meet): meet in knowledge order
⊕ (knowledge join): join in knowledge order
```

**Theorem (Belnap-Dunn)**: FOUR is a complete bilattice with
distributive operations.

**FX integration**: dimension-22 grade carries FOUR-valued
consistency witnessing. Operations on inconsistent-but-bounded
specs proceed via **adaptive logic** (Batens 1989).

**Acceptance**: dimension-22 + FOUR + adaptive logic zero-axiom;
sync protocol verified across NVSwitch + InfiniBand topology.

### Day 31 — Era IV close-out (CRITICAL)

**Goal**: hardware retrofit fully verified across B200, CPU, FPGA
reference targets.

**Tasks**:
* [ ] D31.1 Adaptive scheduler — runtime profiles + selects
  realization
* [ ] D31.2 End-to-end Mathlib-equivalent benchmark on 8-GPU B200
* [ ] D31.3 Cross-architecture equivalence smoke (CPU vs B200 vs
  FPGA produce same NF)
* [ ] D31.4 Performance: target 100× speedup over current Lean
  Mathlib build time
* [ ] D31.5 Era IV commit

**Headline theorem**: any FX program, when typechecked via the
polygraph substrate dispatched through realizations, produces the
same NF regardless of target.

**Acceptance**: FX kernel runs on B200 cluster with verified
correctness; multi-target dispatch works; paraconsistent layer
handles contradictory specs; performance demonstrably superior.

---

## Era IV.5 — Multi-level hardware polygraph (Day 31.5–31.9)

Maxwell at Level 0 as semantic anchor; (Node × Cycle) at Level 3
as daily-use abstraction; verified abstraction functors between
levels. ~6 months. Inserted between Era IV (HardwareTarget) and
Era V (reduction completion) so spacetime-typed Step ctors in Era V
have multi-level substrate to live on.

**Architectural commitment**: hardware reasoning is a 5-level
abstraction stack
```
Polygraph_EM (Level 0) ──F_M→RLC──→ Polygraph_RLC (Level 1)
   ──F_RLC→STA──→ Polygraph_STA (Level 2)
   ──F_STA→Dig──→ Polygraph_Digital (Level 3)
   ──F_Dig→μA──→ Polygraph_μArch (Level 4)
```
Each F_·→· is an abstraction functor with explicit soundness
condition (quasi-static, settling-time, timing-closure, pipeline-
correctness respectively). Soundness verified once, inherited
everywhere. Most computation lives at Level 3-4; Level 0 is the
SEMANTIC REFERENCE.

**Theorem (multi-level naturality)**: for compatible observable
`f` at Level n and its push-forward `F.f` at Level n+1,
```
∫_{Level n} f  =  ∫_{Level n+1} (F.f)
```
Integration is consistent across levels via the abstraction
functor — programs choose the level cheapest for the question.

**Honest caveat (load-bearing)**: analog properties — ENOB
σ_total, actual delay τ, actual power P, calibration accuracy —
are fundamentally RUNTIME, per-chip-variable, time-varying. Static
type-checking gives loose bounds at best (±3-5 dB on ENOB
depending on mode + per-chip offset). Honest type story:
compile-time loose bound + runtime measurement + adaptive
fallback. Era IV.5 ships static-checkable parts; runtime
infrastructure (promise/guard/fallback) ships in Era VIII
extension D63.A.

### Day 31.5 — Maxwell polygraph + lumped RLC + F_M→RLC (CRITICAL)

**Goal**: Level 0 Maxwell-grounded polygraph as semantic anchor +
Level 1 lumped RLC as computable abstraction + verified
F_Maxwell→RLC functor with explicit quasi-static condition.

**Construction (Maxwell polygraph)**:
```
Polygraph_EM := {
  dim-0 generators :
    spacetime point (x : ℝ³, t : ℝ)
    + field state (E : Ω¹(M)⊗ℝ³, B : Ω²(M), ρ : C^∞(M),
                   J : Vec(M))
    + materials (ε(x), μ(x), σ(x)) on chip volume M ⊂ ℝ³

  dim-1 generators : Maxwell evolution as PDE
    Faraday 2-form:    F = E∧dt + B
    Homogeneous:       dF = 0      (∇·B=0, ∇×E + ∂B/∂t = 0)
    Inhomogeneous:     d⋆F = J     (∇·E = ρ/ε₀,
                                    ∇×B − μ₀ε₀ ∂E/∂t = μ₀ J)

  dim-2 generators : conservation as Noether
    Continuity:        dJ = 0      (∂ρ/∂t + ∇·J = 0;
                                    derived from d²F=0 + d⋆F=J)
    Energy-momentum:   ∂_μ T^μν = 0 (Poynting; T_μν = stress-
                                    energy tensor of EM field)

  dim-5 generators : gauge + Lorentz invariance
    A → A + dχ  leaves F = dA invariant; SO(3,1) covariance.

  Smoothness: required (SDG dependency to Era X Day 72,
                        Kock-Lawvere axiom KL).
}
```

**Construction (lumped RLC polygraph)**:
```
Polygraph_RLC := {
  dim-0 : finite node set V ⊂ chip;
          node potentials V_i(t) : ℝ → ℝ;
          branch currents I_b(t) : ℝ → ℝ
  dim-1 : component constitutive laws
    R: V = IR              (Ohm)
    L: V = L · dI/dt       (Faraday induction lumped)
    C: I = C · dV/dt       (capacitive)
    Sources: V₀(t), I₀(t)
  dim-2 : Kirchhoff laws
    KCL: ∀ node n,  Σ_{b ∋ n} sign(b,n) · I_b = 0
    KVL: ∀ loop ℓ,  Σ_{b ∈ ℓ} sign(b,ℓ) · V_b = 0
  dim-3 : multi-rate coupling (transformers, controlled sources)
}
```

**F_Maxwell→RLC functor (formal)**:
```
F_M→RLC : Polygraph_EM → Polygraph_RLC defined by:
  per metal/dielectric region R ⊂ M, define node n_R with
    V(n_R, t) := −∫_{path from gnd to R} E·dl       (line integral)
    I(b, t)   := ∫_{cross-section A_b} J·dA          (surface int.)

QuasistaticCondition(M, f_max) :=
  diam(M) ≪ λ_min   where λ_min = c_material / f_max

For SiO₂ dielectric at 5 GHz: c_material ≈ 1.5×10⁸ m/s, λ ≈ 30 mm.
For 13×17.3 mm die: diam/λ ≈ 0.7 — NOT strict QS regime; F_M→RLC
sound only for local metal regions with diam ≤ 3 mm.
```

**Soundness theorem (Jackson §6.7 quasi-static expansion)**:
```
For chip M satisfying QuasistaticCondition(M, f_max), Maxwell
solution F with boundary conditions, and lifted RLC solution
F_M→RLC(F):
  ‖F − lift(F_M→RLC(F))‖_∞  ≤  ε_qs(diam(M)/λ_min, f_max)
  with ε_qs(r, f) = O(r²)  as r → 0
```

**Tasks**:
* [ ] D31.5.1 `Foundation/Hardware/MaxwellPolygraph.lean` — smooth
  (∞,5)-polygraph (depends on Era X Day 72 SDG)
* [ ] D31.5.2 Faraday tensor F ∈ Ω²(M × ℝ); 4-current J ∈ Ω¹(M × ℝ);
  exterior d, Hodge ⋆ on Lorentzian metric
* [ ] D31.5.3 Maxwell equations dF=0, d⋆F=J as polygraph relations;
  verify d²=0 implies dJ=0
* [ ] D31.5.4 Conservation laws (continuity, Poynting, energy-
  momentum tensor T^μν) as Noether-derivation theorems from gauge
  invariance + d² = 0
* [ ] D31.5.5 Gauge invariance A → A + dχ + Lorentz SO(3,1) at
  dim 5
* [ ] D31.5.6 `Foundation/Hardware/RLCPolygraph.lean` — V/I on
  finite node graph
* [ ] D31.5.7 KCL/KVL as dim-2 cells; component laws as dim-1
* [ ] D31.5.8 F_Maxwell→RLC functor + QuasistaticCondition predicate
  with formal diam(M)/λ_min ratio computation
* [ ] D31.5.9 Soundness theorem with ε_qs(r,f) = O(r²) error bound
* [ ] D31.5.10 STRICT-41-IV5-Maxwell well-formedness gate
* [ ] D31.5.11 Smoke audit Phase IV.5 D31.5

**References**: Jackson 1999 (Classical Electrodynamics, 3rd ed.,
§6.7 quasi-static expansion); Schreiber 2013 (Differential
cohomology in a cohesive ∞-topos); Frankel 2011 (Geometry of
Physics); Eldering 2013 (normally hyperbolic invariant manifolds).

**Acceptance**: Polygraph_EM + Polygraph_RLC + F_M→RLC ship as
explicit model artifacts after the SDG dependency is available. The
kernel proves the formal consequences of the supplied model and
quasi-static witness; real-chip adequacy remains a measured
realization boundary, not a kernel theorem.

### Day 31.6 — STA event polygraph + light cone constraint (CRITICAL)

**Goal**: Level 2 polygraph (per-event timestamps with delay ranges)
+ light-cone-constrained morphisms + setup/hold refinement typing
+ tropical critical-path matmul (GEMM-encodable per Era IX D65).

**Construction (STA polygraph)**:
```
Polygraph_STA := {
  dim-0 : timed events (n, t) ∈ NodeId × ℝ⁺
          (signal-transition timestamps per node)

  dim-1 : delay-graded morphisms
          edge (n, t) → (n', t') with t' − t ∈ [d_min, d_max]
          (per-edge real-valued delay range from RLC parameters)

  graded by : tropical max-plus (ℝ⁺, max, +) for critical-path
              tropical min-plus (ℝ⁺, min, +) for hold-margin
              series:    sum of delays
              parallel:  max of max_delays / min of min_delays

  dim-2 : timing constraints
          setup(reg, edge) := stable(input,
                                     [edge.t − t_setup, edge.t])
          hold(reg, edge)  := stable(input,
                                     [edge.t, edge.t + t_hold])
          skew(clk, r₁, r₂):= |arrival(clk, r₁) − arrival(clk, r₂)|
                              < τ_skew
          jitter(clk)      := σ_phase(clk) < τ_jitter

  dim-3 : path equivalences (Squier coherence on critical-path
                              classification)
}
```

**Tropical critical-path theorem**:
```
For DAG G with per-edge delays (d_min, d_max), the source-to-sink
critical path delay matrix
  D[i,j]_max  =  max over paths p : i → j  of  Σ_{e ∈ p} d_max(e)
is computed by tropical max-plus matrix exponentiation:
  D = M*  where M[i,j] := d_max(i,j) if edge exists else −∞,
        and (M*)[i,j] := max_k M^k[i,j] (Kleene closure)
GEMM-encodable on B200 per Era IX Day 65.
Complexity: O(|V|³) dense / O(|V|² + |E| log |V|) sparse Dijkstra.
```

**Light cone constraint (kernel-enforced)**:
```
∀ (e : Wire src dst : Polygraph_STA),
  e.min_delay ≥ |dst.position − src.position| / c_material

c_material = c · √(1/(ε_r · μ_r))
SiO₂ (ε_r = 3.9, μ_r ≈ 1):  c_material ≈ 1.5 × 10⁸ m/s

For 5 GHz cycle = 200 ps: light traverses 30 mm vacuum / 15 mm SiO₂.
For 1 cm wire: τ_min ≥ 70 ps regardless of drive strength.
```

**Setup/hold soundness theorem**:
```
For register reg with (t_setup, t_hold) and clock period T_clk,
F_STA→Digital is sound iff
  ∀ data path p ending at reg.input,
    (i)  p.max_delay + t_setup + skew_max ≤ T_clk    (setup)
    (ii) p.min_delay − t_hold − skew_min ≥ 0         (hold)
```

**Tasks**:
* [ ] D31.6.1 `Foundation/Hardware/STAPolygraph.lean` — discrete
  events with ℝ⁺ timestamps
* [ ] D31.6.2 Per-edge (d_min, d_max) graded morphisms over
  (ℝ⁺, max, +) tropical + (ℝ⁺, min, +) min-plus dual; reuses
  Era I Day 14 + Era IX Day 64 catalog
* [ ] D31.6.3 Tropical critical-path Kleene-closure matmul;
  Bellman-Ford / Dijkstra implementations; GEMM-encoding for
  B200 per Era IX D65
* [ ] D31.6.4 Light cone min_delay ≥ length / c_material as
  type-level predicate when geometry supplied
* [ ] D31.6.5 (Position × Time) numerical sampling layer (Yee 1966
  FDTD; Courant condition Δt ≤ Δx/(c√3) for 3D stability;
  O((Δx)² + (Δt)²) convergence)
* [ ] D31.6.6 Setup/hold StableOver predicate over time intervals
  as dim-2 cells
* [ ] D31.6.7 Crosstalk via mutual capacitance C_m
  (ΔV ≈ C_m/(C_self + C_m) · dV_aggressor); jitter σ_phase;
  IR drop V_drop = R_pdn · I_switching all added to delay range
* [ ] D31.6.8 F_RLC→STA functor + SettlingTimeCondition
  (signal slew τ_s ≪ stage delay τ_g, e.g. τ_s/τ_g < 0.1)
* [ ] D31.6.9 STRICT-42-IV5-STA gate
* [ ] D31.6.10 Smoke audit + commit

**References**: Yee 1966 (FDTD); Taflove-Hagness 2005 (FDTD
electrodynamics); Sapatnekar 2004 (timing analysis); Brummayer-
Biere 2009 (QF_BV decision procedure for bit-vector timing);
Brayton-Hachtel-Sangiovanni-Vincentelli 1981 (logic synthesis).

**Acceptance**: Polygraph_STA + tropical critical-path GEMM +
light cone + setup/hold typing ship zero-axiom for the represented
timing model; Era IX Day 65 B200 acceleration extends to STA
workloads only through realization certificates / TCB records.

### Day 31.7 — Digital (Node × Cycle) polygraph + spacetime-typed primitives (CRITICAL)

**Goal**: Level 3 polygraph (cycle-discrete) + Charge / Wire /
Register / Instruction types parameterized over SpacetimePoint with
Kirchhoff conservation as kernel theorem; hazards as type errors.

**Construction (spacetime-typed primitives)**:
```lean
structure SpacetimePoint where
  node    : NodeId        -- finite, decidable
  cycle   : Cycle         -- ℕ; or ℕ × ClockDomain for multi-clock
  phase   : Option Phase  -- sub-cycle granularity for combinational

structure ChargeMagnitude where
  coulombs : Rat          -- decEq

def Charge (point : SpacetimePoint) (mag : ChargeMagnitude) : Type
  splitting:  Charge p (m₁+m₂) → Charge p m₁ × Charge p m₂
  combining:  Charge p m₁ × Charge p m₂ → Charge p (m₁+m₂)
  flow:       Charge p₁ m → Wire p₁ p₂ d h → Charge p₂ m
              -- magnitude preserved, position moves, cycle advances

def Wire (src dst : SpacetimePoint) (delay : Picoseconds)
         (h : dst.cycle = src.cycle + delay.toCycle) : Type
  composition:  Wire A B d₁ h₁ → Wire B C d₂ h₂
                → Wire A C (d₁+d₂) h₃

def Register (clk : ClockDomain) (loc : NodeId) (ty : ValueType)
             (cyc : Cycle clk) : ty
def clock_edge :
  Register clk loc ty cyc → Signal ty
  → StableOver input [edge − t_setup, edge + t_hold]
  → Register clk loc ty (cyc + 1)

structure InstrShape where
  reads    : List (RegId × Cycle.Offset)
  writes   : List (RegId × Cycle.Offset)
  pipeUses : List (PipelineResource × Cycle.Offset)
  duration : Nat

def Instruction (encoding : InstrEncoding) (shape : InstrShape)
                (issue : Cycle) : Type
```

**Kirchhoff conservation theorem (model-level Noether witness)**:
```
∀ (node : NodeId) (cyc : Cycle),
  Σ (incoming charges at ⟨node, cyc⟩)
  = Σ (outgoing charges at ⟨node, cyc⟩)

Proof obligation: the supplied digital hardware model carries a
time-translation symmetry witness; combined with Wood-Atkey
linear-graded discipline this proves charge magnitude is conserved
through Wire flow inside the model. Real silicon still requires
measurement/realization certificates.
```

**Pipeline linearity (hazards-as-type-errors)**:
```
∀ (resource : PipelineResource) (cyc : Cycle),
  ∃! (instr : LiveInstruction), instr.uses (resource, cyc)
  -- exactly one instruction owns each pipeline-resource × cycle slot
  -- Type error if two instructions claim same slot:
  --   RAW hazard:   reader's read_cycle < writer's write_cycle
  --   WAR hazard:   late writer overwrites old read source
  --   WAW hazard:   two writers same dst
  --   structural:   two instructions same physical resource
```

**Forwarding-as-typed-witness**:
```
forward_EX_to_ID :
    (producer : Instruction enc₁ shape₁ t₁)
    (h_writes : (reg, t₁ + 2) ∈ producer.shape.writes)
    (consumer : Instruction enc₂ shape₂ t₂)
    (h_reads  : (reg, t₂ + 2) ∈ consumer.shape.reads)
    (h_adj    : t₂ = t₁ + 1)
    → DataAvailable reg (t₂ + 2)
-- Producer in EX (cycle t₁+2) forwards directly to consumer in ID
-- (cycle t₂+2 = t₁+3), bypassing the 2-cycle MEM/WB latency.
-- Successful type-check ⟺ no RAW hazard.
```

**F_STA→Digital functor with timing-closure soundness**:
```
F_STA→Digital(closure : TimingClosure(design)) :
  Polygraph_STA → Polygraph_Digital
  cycle_quantize(events) := { events' | events'.cycle =
                                ⌊events.t / T_clk⌋ }

Theorem: TimingClosure(design)
  ⟺  ∀ p ∈ critical paths,
       p.max_delay + t_setup + skew_max ≤ T_clk
       ∧ p.min_delay − t_hold − skew_min ≥ 0
  ⟹ semantics_at_STA(design)
     ≅ semantics_at_Digital(F_STA→Digital(design))
```

**Tasks**:
* [ ] D31.7.1 `Foundation/Hardware/DigitalPolygraph.lean` —
  (Node × Cycle) coordinate system
* [ ] D31.7.2 SpacetimePoint = (Node, Cycle, Option Phase) struct
  with decEq
* [ ] D31.7.3 Charge type with split/combine/flow + graded linear
  discipline lifted from Wood-Atkey 2022 to (ℝ⁺, +, ·) magnitude
  semiring
* [ ] D31.7.4 Kirchhoff KCL theorem (dim-2 cell) zero-axiom for
  supplied digital model with explicit time-translation symmetry
* [ ] D31.7.5 Wire as dim-1 morphism with Picoseconds delay;
  composition with delay sum; cycle-advance witness
* [ ] D31.7.6 Register as time-indexed function with StableOver
  setup/hold witness; clock_edge as time-shift operator
* [ ] D31.7.7 Instruction = cycle-span; pipe-resource linear
  ownership; InstrShape with reads/writes/pipeUses
* [ ] D31.7.8 forward_EX_to_ID + forward_MEM_to_EX +
  forward_WB_to_ID typed witnesses
* [ ] D31.7.9 Hazard-as-type-error (4 hazard classes RAW/WAR/WAW/
  structural typed-fail)
* [ ] D31.7.10 F_STA→Digital functor + TimingClosure predicate
* [ ] D31.7.11 STRICT-43-IV5-Digital gate
* [ ] D31.7.12 Smoke audit + commit

**Auto-vectorization extension (SIMD-width inference per target)**:
For Wire payload type `Vec n ScalarTy` with `n` compile-time constant,
compiler infers SIMD lane assignment per HardwareTarget capability:
```
target = x86-AVX-512:  16 x FP32 / 8 x FP64 / 64 x INT8 / 32 x INT16
target = ARM-NEON:     4 x FP32 / 2 x FP64 / 16 x INT8 / 8 x INT16
target = RISC-V-RVV:   VLEN-bounded (VL = 128 / 256 / 512 / 1024 bits)
target = FEU (Era IV.5): per-tile width via Era T FEU_hardware site
                         instance (3^7 = 2187 atoms per tile; parallel
                         SIMD lane = trit-width on Trip cores)
target = scalar:        n = 1 (fallback)

def vectorize : Wire src dst delay (Vec n ScalarTy) h
              -> forall (target : HardwareTarget),
                 Wire src dst delay (target.lane_pack ScalarTy n) h
  -- decidable from n + ScalarTy + target.vector_lanes capability
  -- preserves delay (vectorization is parallel, not sequential)
```

**Theorem (SIMD-equiv-scalar)**:
```
forall (w : Wire src dst delay (Vec n ScalarTy) h)
       (target : HardwareTarget),
  semantics(w) =_bit semantics(vectorize w target)
  -- bit-identical for integer ops always;
  -- bit-identical for FP under strict IEEE 754 (FX §3.11 default);
  -- reorder permitted under `with Reassociate` opt-in only.
```

* [ ] D31.7.13 `vectorize` pass per HardwareTarget instance
* [ ] D31.7.14 SIMD-equiv-scalar theorem zero-axiom (per ScalarTy:
  bool / u8 / u16 / u32 / u64 / i8 / i16 / i32 / i64 / f32 / f64)
* [ ] D31.7.15 Verified SIMD intrinsic mapping (AVX-512 / NEON / RVV
  intrinsics auto-emit from Wire vector types)
* [ ] D31.7.16 Bridge to Vertical I: FEU lane width inferred from
  Era T FEU_hardware site per-tile dim-4 hardware fibres

**References**: Hennessy-Patterson 6th ed. §C.2 (pipelining
hazards); Sapatnekar 2004 (timing); Wood-Atkey 2022 (graded linear
calculus); Tofte-Talpin 1997 (region-based memory analog for
linear-resource discipline); Intel AVX-512 / ARM NEON / RISC-V RVV
ISA manuals (vendor-published).

**Acceptance**: Polygraph_Digital + spacetime-typed primitives
zero-axiom as model data; KCL/Kirchhoff theorem from an explicit
Noether-style symmetry witness; setup/hold + 4 hazard-classes as
type errors; F_STA→Digital sound under TimingClosure certificate.

### Day 31.8 — μArch polygraph + side-channel typing (CRITICAL)

**Goal**: Level 4 polygraph (instruction-level / pipeline aggregate)
+ side-channel effects as kernel modalities + Spectre/Rowhammer/
Meltdown reframed as unintended 2-cells in silicon polygraph.

**Construction (μArch polygraph)**:
```
Polygraph_μArch := {
  dim-0 : pipeline-stage × cycle × machine state
          (PC, regfile, memory, BPState, cache_state, ...)
  dim-1 : pipeline transitions; ISA ops
          fetch:    (PC, c) → (insn-in-IF, c+1)
          decode:   (insn-in-IF, c) → (insn-in-ID, c+1)
          execute:  (insn-in-ID, c) → (insn-in-EX, c+1)
          memory:   (insn-in-EX, c) → (insn-in-MEM, c+1)
          writeback:(insn-in-MEM, c) → (state', c+1)
  dim-2 : hazards + forwarding rules; ISA refinement (impl ≅ spec
          on architecturally-visible state)
  dim-3 : strategy equivalences (e.g., out-of-order ≡ in-order on
          observable state, modulo speculation)
}
```

**Side-channel effects (kernel modalities)**:
```
effect Timing       { observe duration : Cycles }
effect Power        { observe instantaneous : Watts;
                      total : Joules }
effect EM           { observe spectrum : ElectromagneticSpectrum }
effect Cache        { observe access_pattern : List CacheLine }
effect Speculation  { observe predictor_state : BPState }
effect Thermal      { observe temperature : Celsius }
effect Acoustic     { observe vibration : Spectrum }

ConstantTime(f : A → B) :=
  ∀ (a₁ a₂ : A), secret(a₁) = secret(a₂) ⟹
                  Timing(f a₁) = Timing(f a₂)

SideChannelFree(f) :=
  ∀ ξ ∈ {Timing, Power, EM, Cache, Speculation, Thermal, Acoustic},
  ∀ (a₁ a₂ : A), secret(a₁) = secret(a₂) ⟹
                  ξ(f a₁) = ξ(f a₂)
-- f is multi-channel constant-trace on its secret inputs
```

**Side-channel attacks-as-2-cells (Bernstein 2005, Kocher et al.
2019, Kim et al. 2014, Lipp et al. 2018)**:
```
A side-channel attack is a 2-cell α : intended_morphism ⇒
unintended_morphism in the silicon polygraph (Polygraph_μArch
fibered over Polygraph_RLC) that does NOT exist in the spec
polygraph. The 2-cell witnesses information flow from secret
inputs to observable side-channel outputs.

Spectre v1 (CVE-2017-5753):
  intended: branch_predict(secret) → BPState_normal
  unintended: BPState_perturbed_by_secret → cache_state_observable
  2-cell α: speculation_window leaks secret to cache_state

Rowhammer:
  intended: refresh_DRAM_row(addr)
  unintended: row_hammer_pattern → bit_flip_adjacent_row
  2-cell α: DRAM refresh-coupling violates row independence

Detection := enumerate suspect 2-cells in silicon vs spec.
Defense  := 2-cell elimination (constant-time, cache-flush,
            BP-isolation, refresh-rate boost).
```

**F_Digital→μArch functor with pipeline-correctness soundness**:
```
F_Dig→μArch : Polygraph_Digital → Polygraph_μArch
  pipeline_aggregate(cycles) := group by instruction lifetime

Soundness: ∀ (instr : Instruction)
            (forwarding : ForwardingRules)
            (h : proper_forwarding(instr, forwarding)),
  pipelined_behavior(instr) ≅ ISA_spec_behavior(instr)
  -- on architecturally-visible state, modulo speculation 2-cells
```

**Tasks**:
* [ ] D31.8.1 `Foundation/Hardware/uArchPolygraph.lean`
* [ ] D31.8.2 Instructions as cycle-spans with explicit data
  dependencies; ISA-spec-vs-impl
* [ ] D31.8.3 ISA-to-pipeline refinement (lifted from Era IV §28.4
  hardware retrofit)
* [ ] D31.8.4 F_Dig→μArch functor + PipelineCorrectness predicate
* [ ] D31.8.5 7 side-channel effects (Timing, Power, EM, Cache,
  Speculation, Thermal, Acoustic) as kernel modalities
* [ ] D31.8.6 ConstantTime / SideChannelFree composite types per
  Bernstein 2005, Almeida-Barbosa-Barthe-Dupressoir 2016
* [ ] D31.8.7 Spectre v1/v2 (CVE-2017-5753, -5715), Rowhammer
  (Kim 2014), RAMBleed (Kwong-Genkin-Gruss-Yarom 2020), Meltdown
  (CVE-2017-5754) reframed as unintended 2-cells
* [ ] D31.8.8 Cache side-channel formalization (Bernstein 2005
  cache-timing; Yarom-Falkner 2014 Flush+Reload)
* [ ] D31.8.9 STRICT-44-IV5-μArch + side-channel gate
* [ ] D31.8.10 Smoke audit + commit

**References**: Hennessy-Patterson 6th ed.; Bernstein 2005
(cache-timing attacks on AES); Kocher et al. 2019 (Spectre);
Lipp et al. 2018 (Meltdown); Kim et al. 2014 (Rowhammer);
Kwong-Genkin-Gruss-Yarom 2020 (RAMBleed); Yarom-Falkner 2014
(Flush+Reload); Almeida-Barbosa-Barthe-Dupressoir 2016 (verified
constant-time crypto).

**Acceptance**: full multi-level abstraction stack from Maxwell to
μArch represented as explicit model data with zero-axiom morphism
theorems where certificates are supplied; cross-level integration
consistent inside the model; side-channel typing operational for
crypto primitives in fx-net Era IX vertical.

### Day 31.9 — Era IV.5 close-out + multi-level calculus (CRITICAL)

**Goal**: per-level differentiation and integration appropriate to
each level; cross-level naturality (∫_n = ∫_{n+1} ∘ F push-forward);
discrete Stokes for represented calculi; Landauer-style model
certificates (links to F1 dimension 23); close Era IV.5.

**Per-level calculus catalog**:
```
| Lvl | Time      | Space    | Differentiation       | Integration              | Algebra            |
|---|-----------|----------|-----------------------|--------------------------|--------------------|
| 0 | ℝ          | ℝ³       | ∂/∂t, ∂/∂xⁱ, d (de Rham) | ∫_M f dV, ∫_∂ ω (Stokes)  | smooth manifold    |
| 1 | ℝ          | finite   | dV/dt ODEs            | ∫₀ᵀ I(t)dt, Laplace      | f.d. state ODEs    |
| 2 | ℝ⁺ tstmp   | finite   | δ between events      | tropical Σ over path     | (ℝ⁺, max, +)       |
| 3 | ℕ cycles   | finite   | Δf(c) = f(c+1) − f(c) | Σ_{c∈[a,b]} f(c)         | (ℕ, +, ·)          |
| 4 | per-instr  | stages   | Δ between instr's     | Σ over instructions      | (ℕ, +)             |
```

**Discrete Stokes theorem (formal model theorem, zero-axiom for
represented calculi)**:
```
For finitely-presented site S with boundary ∂ and exterior d
(de Rham at Level 0; discrete d at Level 2-4),
  ∀ (ω : k-cochain on S) (M : (k+1)-region in S),
    ∫_∂M ω  =  ∫_M dω

Specialized cases:
  Level 3 (telescoping):
    Σ_{c=a}^{b−1} (f(c+1) − f(c))  =  f(b) − f(a)
  Level 2 (tropical Stokes):
    max over path-end events = max over path-edge deltas
    (longest-path = sum-of-edge-delays critical-path identity)
  Level 0 (Stokes/de Rham):
    ∫_∂M ω = ∫_M dω  on smooth oriented manifold M with boundary
```

**Cross-level integration consistency theorem**:
```
For F : Polygraph_n → Polygraph_{n+1} verified abstraction functor,
local observable f at Level n, F.f its push-forward,
  ∫_{Level n} f  =  ∫_{Level n+1} (F.f)

Specialized total-energy along all five levels:
  ∫∫_{Level 0} (E·J) dV dt
  ≡ ∫_{Level 1} Σ_components (V·I) dt
  ≡ Σ_{events at Level 2} energy(event)
  ≡ Σ_{cycles at Level 3} (P_cycle · T_clk)
  ≡ Σ_{instructions at Level 4} (E_avg · n_cycles)
```

**Power as path-dependent 1-cochain (finite-graph first; de Rham
analogy only when a smooth model is supplied)**:
```
Instantaneous power P : SpacetimePoint → Watts is a 0-cochain.
Energy E := ∫ P dt over a reduction path is path-dependent —
different reduction paths from program-state s to state s' yield
different total energy despite identical functional behavior.

Hence E is represented as a finite 1-cochain (assigns a checked
non-negative cost to each path) in the supplied reduction graph.
Its cohomology class measures path-dependence inside that graph.
[E] = 0 iff energy is path-independent in the supplied model; any
physical interpretation requires a realization certificate.

Compiler optimization for energy: find path in equivalence class
[s]/(path-equivalent) minimizing ∫ P dt → tropical shortest-path
over (ℝ⁺, +, min) on the reduction graph.
```

**Landauer-style model theorem (links to F1 dim-23 Energy)**:
```
For explicit finite thermodynamic model M and Step s:
  M proves s irreversible
  M supplies entropy_decrease certificate
  M supplies LandauerLowerBound law
  ⟹ checked_energy_cost M s ≥ k_B · T · entropy_decrease M s · ln 2

At T = 298.15 K the numeric floor is checked from interval
certificates for constants and units. Reversible/quantum claims
require explicit finite model certificates.
```

**Tasks**:
* [ ] D31.9.1 `Foundation/Hardware/MultiLevelCalculus.lean` per-
  level calculus catalog
* [ ] D31.9.2 Level 0 calculus: ∂/∂t, ∂/∂xⁱ, exterior d (smooth,
  via SDG Era X Day 72); de Rham complex
* [ ] D31.9.3 Level 1 calculus: ODE integration via 4th-order
  Runge-Kutta + Lipschitz convergence rate; Laplace transform via
  contour integration on imaginary axis
* [ ] D31.9.4 Level 2 calculus: tropical max-plus + min-plus dual;
  semiring laws verified
* [ ] D31.9.5 Level 3 calculus: finite Σ over cycle intervals;
  Δ-operator
* [ ] D31.9.6 Level 4 calculus: incremental Δ (links to dim-24
  ILC change calculus, Cai-Giarrusso-Rendel-Ostermann ICFP 2014)
* [ ] D31.9.7 Cross-level naturality theorems (∫_n = ∫_{n+1} ∘ F)
* [ ] D31.9.8 Discrete Stokes ∫_∂M ω = ∫_M dω zero-axiom for
  represented finite calculi; smooth-via-SDG variant only after the
  SDG model is explicitly supplied
* [ ] D31.9.9 Power/energy finite 1-cochain + H¹ class over the
  represented reduction graph
* [ ] D31.9.10 Landauer-style checker for explicit finite
  thermodynamic models and interval-certified constants
* [ ] D31.9.11 Smoke audit comprehensive Era IV.5
* [ ] D31.9.12 Era IV.5 commit + status

**References**: Spivak 1965 (Calculus on Manifolds — Stokes
theorem); Hirani 2003 (Discrete Exterior Calculus PhD);
Bobenko-Suris 2008 (Discrete Differential Geometry); Litvinov-
Maslov 1996 (idempotent semirings); Landauer 1961 (Irreversibility
and heat generation); Bennett 1973 (Logical reversibility);
Fredkin-Toffoli 1982 (Conservative logic); Cai-Giarrusso-Rendel-
Ostermann 2014 (incremental λ-calculus, ICFP).

**Acceptance**: Era IV.5 complete; full multi-level hardware
polygraph + per-level calculus operational; abstraction functors
verified as model morphisms; discrete Stokes ships as a formal
theorem for the represented calculus. Landauer/energy statements
ship only as checked finite thermodynamic-model theorems and
runtime/physical adequacy remains under Promise/Guard/Fallback plus
realization certificates.

---

## Era V — Reduction completion (Day 32–40)

β + η + cubical β + FX-unique reductions, all expressed at polygraph
level. ~7 months.

### Day 32 — Full β + η as polygraph cells, ALL type formers (CRITICAL)

**Goal**: ship η as single-step `Step` ctor (currently only Step.par
permissive form exists per #1632/#1635 backlog) AND η as dim-1 cell
in PolyTerm, for **every type former in the kernel that admits an
η-law**. This closes the kernel commitment "β AND η at the kernel
level for all terms and types" introduced in Day 12.

**Type formers with η-laws (full enumeration)**:
- Function types: `η-lam` (arrow), `η-lamPi` (dependent Π)
- Σ types: `η-pair`
- Records: `η-record`
- Modal types: `η-modal` (one per modality: ◇, □, ♭, ♯, ghost, cap,
  later, clock — eight ctors)
- Path types: `η-path` (`pathLam (pathApp p (var 0)) ≡ p`)
- Codata: `η-codata` (observation-extensionality)
- Equiv: `η-equiv` (`equivIntroHet (extract... e) ≡ e`)
- Refinement: `η-refine` (definitional, since refinement adds no
  structure beyond the witness)
- Unit: `η-unit` (definitional uniqueness)

**Type formers WITHOUT η-laws** (η does not apply; uniqueness via
ι rules):
- Bool, Nat, List, Option, Either — η is not canonical for raw
  inductives; instead, ι-coverage theorems prove every NF is a
  constructor expression.
- Identity types (Id, OEq, IdStrict) — η-rule is the J-elimination's
  ι-rule on `refl`.

**Tasks**:
* [ ] D32.1 `Step.etaLam`/`Step.etaLamPi` typed Step ctors
* [ ] D32.2 `Step.etaPair`, `Step.etaRecord` typed Step ctors
* [ ] D32.3 `Step.etaModal_X` for each modality X (8 ctors)
* [ ] D32.4 `Step.etaPath`, `Step.etaCodata`, `Step.etaEquiv`,
  `Step.etaRefine`, `Step.etaUnit` typed Step ctors
* [ ] D32.5 Step.par mirrors for each (permissive form per Geuvers
  1992 for βη-CR)
* [ ] D32.6 RawStep.par mirrors per STRICT-3
* [ ] D32.7 Compat cascade (rename + subst preserve every η ctor)
* [ ] D32.8 cd / cd_lemma arms for all η ctors (dim-2 cells)
* [ ] D32.9 Inversion lemmas for each η ctor
* [ ] D32.10 SR proofs (each η preserves typing trivially since
  source.type = target.type)
* [ ] D32.11 β-η critical pair joinability via dim-2 cells (Geuvers
  1992 adaptation per Part I §4 Theorem 4.4 + Theorem 4.6)
* [ ] D32.12 Smoke audit comprehensive β+η coverage

**Theorem (kernel-level β/η coverage commitment)**:
```
∀ (T : TypeFormer), T ∈ {Π, Σ, arrow, Record, Modal_X (X ∈ 8 mods),
                          Path, Codata, Equiv, Refine, Unit} ⇒
  ∃ (β-rule η-rule : Step ctor), 
    β-rule reduces (eliminator (intro args)) → contractum
    η-rule reduces (intro (eliminator x)) → x

∀ (T : TypeFormer), T ∈ {Bool, Nat, List, Option, Either, Id, OEq,
                          IdStrict} ⇒
  ∃ (ι-coverage : Theorem),
    ∀ t : Term ctx T raw, IsCanonical t ↔ t = ctor(args) for some ctor
```

**Confluence**: Geuvers 1992 proves βη-CR for the Calculus of
Constructions; the same technique extends to FX's modal/cubical/
graded extensions because each new type former's β/η pair is
non-overlapping with other type formers (different head ctors). The
β-η critical pair within a single type former is joinable
structurally (β substitutes (var 0) for binder = identity
substitution, so β-target = η-target).

**Acceptance**: every type former in the kernel has Step.X β-rule +
Step.X η-rule (where applicable), all zero-axiom; STRICT-3 + STRICT-9
parity green; Compat + Confluence cascade clean; β-η joint CR proved
via dim-2 cells.

### Day 33 — Cubical β rules complete (CRITICAL)

**Goal**: ship cubical transp + hcomp + glue β rules at polygraph
level (per Part I §7.9, §7.10, §7.11).

**Tasks**:
* [ ] D33.1 D2.5.5 transpPi cascade as polygraph cells
* [ ] D33.2 D2.5.6 transpSigma cascade
* [ ] D33.3 D2.5.7 transp{ListType,OptionType,EitherType,Record}
* [ ] D33.4 D2.5.8 betaPathReflApp
* [ ] D33.5 D2.5.9 glueAtFace
* [ ] D33.6 hcompBeta + transpBeta typed mirrors
* [ ] D33.7 All cells dim-1 with corresponding dim-2 cd-lemma cells
* [ ] D33.8 Era D2.5.x tickets closed

**Theorems to ship**:
1. **Cubical β-CR**: each cubical β rule satisfies the cubical
   diamond property (Part I §4 Theorem 4.4 adapted).
2. **Cubical SR**: each cubical β rule preserves cubical typing.

**Reference**: CCHM 2017, "Cubical Type Theory: A Constructive
Interpretation of the Univalence Axiom"; ABCFHL 2019, "Syntax and
Models of Cartesian Cubical Type Theory."

**Acceptance**: every cubical β rule from Appendix C §R6 ships at
polygraph dim-1 level with dim-2 cd-lemma cells; #1556–1675 closed.

### Day 34 — FX-unique: capability erasure β (CRITICAL)

**Goal**: ship `Step.effectErase` per Part I §7.13 / Appendix C §R8.

**Tasks**:
* [ ] D34.1 `Step.effectErase` as dim-1 cell with effect-row
  decidability
* [ ] D34.2 Type-level effect-row check
* [ ] D34.3 SR + Compat + Confluence as polygraph cells
* [ ] D34.4 Smoke + cross-effect erasure tests

**Reduction rule**:
```
effect-erase:  g (f : T with E)  →  g (f : T)
               when g : (T with E') → R and E ⊥ E' (orthogonal)
```

**Decidability theorem**: effect-row orthogonality is decidable on
finite effect rows (Part VI §C7).

**SR**: erasing an unobserved effect preserves typing (effect-row
projection is monotone wrt effect annotations).

**Acceptance**: effect-erase ships zero-axiom with full β/cong/SR
cascade.

### Day 35 — FX-unique: refinement narrowing β (CRITICAL)

**Goal**: ship `Step.refineNarrow` per Part I §7.14 / Appendix C
§R9.

**Tasks**:
* [ ] D35.1 `Step.refineNarrow` polygraph cell
* [ ] D35.2 Decidability instance integration
* [ ] D35.3 SR + Compat + Confluence
* [ ] D35.4 Smoke + decidable predicate audit

**Reduction rule**:
```
refine-narrow:  (x : {n : ℕ | P n}).inner   →  x
                when P n is decidable
```

**Decidability theorem**: for `Decidable P` instance, narrowing
computes (constant time per the Part VI §C7 refinement obligation
row, when SMT is not needed).

**SR**: refinement preserved under narrowing (the refinement
predicate is the same at source + target).

**Acceptance**: refine-narrow ships zero-axiom; auto-discharge for
Decidable predicates at kernel level.

### Day 36 — FX-unique: cross-mode coercion β (CRITICAL)

**Goal**: ship `Step.modeCoerce` per Part I §7.15 / Appendix C §R10.

**Tasks**:
* [ ] D36.1 `Step.modeCoerce` polygraph cell
* [ ] D36.2 Mode-bridge decidability
* [ ] D36.3 D4.6 mode bridges → definitional reductions
* [ ] D36.4 SR + Compat + Confluence
* [ ] D36.5 Smoke audit cross-mode coercions

**Reduction rule**:
```
mode-coerce:   coerce_strict_to_obs A x   →  x_in_obs
               when A is mode-uniform
```

**Decidability theorem**: mode-uniformity of types is decidable on
type structure (recursive descent over Ty constructors).

**SR**: cross-mode coercion preserves typing modulo mode shift; the
mode-bridge equivalence (Day D4.6 from kernel-sprint) collapses to
a definitional reduction.

**Acceptance**: mode-coerce ships zero-axiom; D4.6 mode bridges
become definitional rather than propositional.

### Day 37 — FX-unique: hardware bit-level β (CRITICAL)

**Goal**: ship hardware bit-level β rules per Part I §7.16 /
Appendix C §R11.

**Tasks**:
* [ ] D37.1 `Step.bitsConcatProj` polygraph cell
* [ ] D37.2 Bits zero/sign-ext + slice + merge β
* [ ] D37.3 Format projection β
* [ ] D37.4 SR + Compat + Confluence
* [ ] D37.5 fx-chip integration smoke (RTL ≡ ISA at bit level)

**Reduction rules**:
```
bits-concat-proj:  bits {a, b}[k:0]   →   slice(a, b, k, 0)
bits-zero-ext:     zext n (bits b)    →   bits (b ++ 0^n)
bits-sign-ext:     sext n (bits b)    →   bits (b ++ msb(b)^n)
bits-slice-merge:  merge (slice a) (slice b) [k:0] [m:k+1]
                                      →   slice (a ++ b)
```

**Decidability theorem**: bit-vector arithmetic decidable in
QF_BV (Brummayer-Biere 2009 SMT theory of bit-vectors).

**Acceptance**: bits-level β ships zero-axiom; fx-chip RTL ≡ ISA
verified at bit level.

### Day 38 — FX-unique: grade-aware linear erasure (CRITICAL)

**Goal**: ship `Step.linearConsume` per Part I §7.17 / Appendix C
§R12.

**Tasks**:
* [ ] D38.1 `Step.linearConsume` polygraph cell
* [ ] D38.2 Grade tracking through Step
* [ ] D38.3 Wood/Atkey 2022 calculus integration
* [ ] D38.4 SR + Compat + Confluence
* [ ] D38.5 Smoke audit linear discipline

**Reduction rule**:
```
linear-consume:  consume(x) ; e[x]   →  consume(x) ; e[absurd]
                 (uses of x after consume reduce to absurd)
```

**Decidability theorem**: grade arithmetic decidable on (ℕ, +, 0)
or Wood-Atkey 2022 fractional-permission semiring (Part VI §C5
Era V row).

**Wood-Atkey integration**: this rule is the kernel's enforcement
of the corrected Lam rule. The fundamental theorem (Era S Day 42)
relies on linear-consume + Lam-rule discipline; together they make
the linear typing zero-axiom-coherent.

**Acceptance**: linear-consume + grade arithmetic zero-axiom;
Atkey 2018 attack still rejected (regression test).

### Day 38.A — Dimension-24 Incrementality / ILC change calculus (CRITICAL)

**Goal**: ship dimension-24 (Incrementality) per §5 dimensional
matrix; ILC-style change calculus (Cai-Giarrusso-Rendel-Ostermann
ICFP 2014) at kernel level.

**Construction (ILC change types)**:
```
For every type A : Ty level scope, define a CHANGE TYPE
ΔA : Ty level scope satisfying:
  (i)   nil_change : A → ΔA      (no-change witness)
  (ii)  apply : A × ΔA → A         (apply change to base)
  (iii) compose : ΔA × ΔA → ΔA    (sequential change composition)
  (iv)  ⊕ laws (apply respects compose, nil is identity, etc.)

For every function f : A → B, define DERIVATIVE
  Df : A × ΔA → ΔB
satisfying the FUNDAMENTAL ILC LAW:
  apply (f a, Df (a, da))  =  f (apply (a, da))

i.e., Df propagates changes through f correctly.
```

**Type-formers (per Term ctor)**:
```
Δ(Ty.nat)         = ℤ                  -- signed deltas on ℕ
Δ(Ty.bool)        = Maybe Bool          -- flip or not
Δ(Ty.arrow A B)   = (A × ΔA) → ΔB       -- ILC's higher-order Δ
Δ(Ty.piTy A B)    = Σ (a : A) (da : ΔA), ΔB[a, da]
Δ(Ty.list A)      = List (Op A)         -- insert/delete/modify
                    where Op A = Insert A | Delete | Modify ΔA
Δ(Ty.record fs)   = Record (map Δ fs)
Δ(Ty.id A x y)    = ΔA × ΔA → ΔA-path
Δ(Ty.path A x y)  = ... (cubical incrementality)
Δ(Ty.modal m A)   = Δ(modal m A) — modality-aware change
```

**Theorems**:
```
ILC fundamental theorem (Cai et al. 2014):
  ∀ (f : A → B) (a : A) (da : ΔA),
    apply (f a, Df (a, da))  =  f (apply (a, da))

Composition law:
  D(g ∘ f) (a, da)  =  Dg (f a, Df (a, da))
                     -- chain rule analog

Naturality with site morphism (Era T):
  for F : Site_a → Site_b, Δ commutes with F.transport:
  F.transport (ΔA)  ≅  Δ(F.transport A)
```

**Use cases (load-bearing for agentic LLM)**:
- Incremental type-checking: re-check only changed regions
- LLM iterative editing: each edit is a Δ, propagated through
  derivatives rather than full re-compilation
- Editor responsiveness: lean-language-server / rust-analyzer
  patterns become FX kernel primitives
- Live programming: hot-reload with verified change propagation

**Tasks**:
* [ ] D38.A.1 `Foundation/Graded/Incrementality.lean` — dimension-24
  graded structure
* [ ] D38.A.2 ΔA type-former per Ty ctor (~25 cases per Era V Ty
  inventory)
* [ ] D38.A.3 nil_change / apply / compose primitives + laws
* [ ] D38.A.4 Df derivative generator for every Term ctor (~75
  cases) per ILC framework
* [ ] D38.A.5 ILC fundamental theorem zero-axiom for all ctors
* [ ] D38.A.6 Composition law (chain rule analog)
* [ ] D38.A.7 Higher-order ΔA→ΔB function-typed changes (Cai et
  al. 2014 §3.2)
* [ ] D38.A.8 Naturality with Era T site morphisms (Δ commutes
  with F.transport)
* [ ] D38.A.9 STRICT-59-V-Incremental gate
* [ ] D38.A.10 Smoke + commit

**Reference**: Cai-Giarrusso-Rendel-Ostermann 2014 (A theory of
changes for higher-order languages: Incrementalizing
λ-calculi by static differentiation, ICFP); Hammer-Acar 2007
(self-adjusting computation); Cockett-Cruttwell-Lemay 2014
(differential categories — categorical foundation).

**Acceptance**: dimension-24 incrementality zero-axiom; ILC
fundamental theorem at all 75 Term ctors; agentic-LLM use case
unlocked (incremental kernel verification).

### Day 38.B — Dimension-23 Energy / Landauer model certificates (SPECULATIVE, MODEL-LAYER)

**Goal**: introduce dimension-23 as a computational interface for
finite energy models and checked certificates. This is physics-
grounded and speculative: the kernel may verify consequences of an
explicit model, but it does not assert that real hardware, real
thermodynamics, or quantum dynamics satisfy that model without a
separate realization certificate.

**Construction (energy as checked model data)**:
```
EnergyCost := ℚ_nonneg                 -- computable representation;
                                          real-valued physics constants
                                          enter via rational interval
                                          certificates

structure EnergyModel where
  cost_lower_bound : Step source target → EnergyCost
  entropy_decrease : Step source target → EnergyCost
  is_reversible    : Step source target → Decidable Bool
  constants        : PhysicalConstantsAsIntervals
  laws             : List CheckedModelLaw

-- A Step has an energy meaning only relative to an EnergyModel.
def Step.energy_cost (M : EnergyModel) (s : Step source target)
    : EnergyCost := M.cost_lower_bound s
```

**Model theorem (Landauer-style lower bound, conditional)**:
```
For an explicit finite thermodynamic model M containing:
  - temperature T and units/constants as data,
  - entropy_decrease certificate for Step s,
  - proof that s is irreversible in M,
  - model law LandauerLowerBound M,
the kernel checks:
  s.energy_cost  ≥  k_B · T · s.entropy_decrease · ln 2

At T = 298.15 K, the numeric floor is a checked computation once
the constants/units certificate is supplied.

Reversible Steps (by Bennett 1973 theorem on logical
reversibility inside M): entropy_decrease = 0, hence model
cost-floor 0.

Quantum unitary claims require an explicit finite-dimensional
unitary model and entropy-preservation certificate. They are not
kernel-global facts.
```

**Path-dependent total energy as 1-cochain**:
```
For energy model M and reduction path π : t →* t' =
Step₁ ; Step₂ ; ... ; Stepₙ,
total_energy(M, π)  :=  Σᵢ Step.energy_cost M Stepᵢ

Two paths π₁, π₂ : t →* t' may have different total_energy
even if t and t' are identical.

The cohomology class [E] ∈ H¹(reduction-graph; ℚ_nonneg) classifies
path-dependence inside the finite graph model:
  [E] = 0  ⟺  energy is path-independent
            ⟺  all compared reduction paths have equal checked cost.
  Reversibility / thermodynamic optimality require additional model
  laws and are not inferred from [E] = 0 alone.

Compiler optimization for energy:
  argmin over equivalence-class representatives of total_energy(·)
  (tropical shortest-path on reduction graph in (ℝ⁺, +, min)
   semiring; GEMM-encodable per Era IX Day 65)
```

**Cumulative energy across reduction paths (Era IV.5 multi-level,
conditional on abstraction certificates)**:
```
Cross-level energy consistency (Era IV.5 D31.9 multi-level
calculus integration):
  ∫∫_{Level 0} (E_field · J_current) dV dt
  ≡ Σ_{Level 1} ∫₀ᵀ Σ_components (V·I) dt
  ≡ Σ_{events at Level 2} energy(event)
  ≡ Σ_{cycles at Level 3} (P_cycle · T_clk)
  ≡ Σ_{Steps at Level 4} Step.energy_cost M step

Total checked energy is invariant across levels only when the
abstraction functors provide explicit energy-preservation
certificates (multi-level naturality theorem from Era IV.5 Day
31.9). Without those certificates, the lower levels are measurement
inputs, not kernel facts.
```

**Tasks**:
* [ ] D38.B.1 `Foundation/Graded/Energy.lean` — dimension-23 graded
  structure with finite energy-cost algebra and certificate formats
* [ ] D38.B.2 EnergyModel-relative `Step.energy_cost M s` and finite
  certificate schema per Step family
* [ ] D38.B.3 Model-relative entropy_decrease + is_reversible
  certificate checkers; Bennett-style characterization only when
  the supplied model proves the required hypotheses
* [ ] D38.B.4 Landauer-style lower-bound checker: irreversible Step
  in explicit model M + entropy certificate ⟹ checked inequality
* [ ] D38.B.5 Reversible-Step library: syntactic reversibility
  witnesses for η, selected linear β, and βι-on-canonical forms;
  cost = 0 only for EnergyModels that interpret those witnesses as
  physically reversible
* [ ] D38.B.6 Path-dependent total energy as finite 1-cochain;
  [E] ∈ H¹(reduction-graph; ℚ_nonneg) classification inside the
  supplied graph model
* [ ] D38.B.7 Compiler argmin-energy search via tropical
  shortest-path (GEMM-encoded per Era IX Day 65)
* [ ] D38.B.8 Cross-level energy consistency theorem for supplied
  abstraction certificates (links to Era IV.5 D31.9 multi-level
  calculus)
* [ ] D38.B.9 STRICT-57-V-Energy gate
* [ ] D38.B.10 Smoke + commit

**References**: Landauer 1961 (Irreversibility and heat
generation in the computing process, IBM J. Res. Dev.);
Bennett 1973 (Logical reversibility of computation, IBM J.);
Fredkin-Toffoli 1982 (Conservative logic, Int. J. Theor. Phys.);
Frank 2017 (Foundations of generalized reversible computing).

**Acceptance**: dimension-23 energy ships as a zero-axiom finite
checker and model-theorem layer; Landauer-style claims are checked
only when their finite thermodynamic model and certificates are
present; reversible-Step cost 0 is a theorem only inside models that
prove the Bennett reversibility hypotheses; path-dependent energy
cost over finite reduction paths ships; physical adequacy remains a
realization boundary.

### Day 38.C — Side-channel typing extension (parallel)

**Goal**: 7 side-channel effects (Timing/Power/EM/Cache/Speculation/
Thermal/Acoustic) as kernel-level effect modalities; SideChannelFree
composite type.

**Construction**:
```
effect Timing       : Cycles                  -- duration observable
effect Power        : Watts × Joules           -- instant + total
effect EM           : ElectromagneticSpectrum  -- RF emissions
effect Cache        : List CacheLine           -- access pattern
effect Speculation  : BPState                  -- branch predictor
effect Thermal      : Celsius                  -- temperature
effect Acoustic     : Spectrum                 -- vibration/coil whine

ConstantTime(f : A → B) :=
  ∀ (a₁ a₂ : A), secret(a₁) = secret(a₂) ⟹
                  Timing(f a₁) = Timing(f a₂)

SideChannelFree(f) :=
  ∀ ξ ∈ {Timing, Power, EM, Cache, Speculation,
         Thermal, Acoustic},
  ∀ (a₁ a₂ : A), secret(a₁) = secret(a₂) ⟹
                  ξ(f a₁) = ξ(f a₂)

-- Multi-channel constant-trace; required for security-critical code
-- (extends FX §12.5 `with CT` from timing-only to all 7 channels).
```

**Tasks**:
* [ ] D38.C.1 7 side-channel effects per Era IV.5 D31.8.5
* [ ] D38.C.2 ConstantTime / SideChannelFree composite types
* [ ] D38.C.3 Bridge from existing FX §12.5 `with CT` (timing-only)
  to multi-channel framework
* [ ] D38.C.4 STRICT-58-V-SideChannel gate
* [ ] D38.C.5 Crypto fragment audit (fx-net Era IX vertical AES,
  ChaCha20-Poly1305, Ed25519 verified SideChannelFree)
* [ ] D38.C.6 Smoke + commit

**References**: Bernstein 2005 (cache-timing attacks on AES);
Almeida-Barbosa-Barthe-Dupressoir 2016 (verified constant-time
cryptographic implementations, CCS); Yarom-Falkner 2014 (Flush+
Reload, USENIX); Kocher et al. 2019 (Spectre attacks); Lipp et al.
2018 (Meltdown).

**Acceptance**: 7 side-channel effects + SideChannelFree composite
zero-axiom; crypto verified across all 7 channels.

### Day 39 — Optimal reduction (Lévy-Lamping) at polygraph level (CRITICAL)

**Goal**: ship `OptStep` as dim-1 cells with sharing-graph
semantics; verify simulation with standard Step.

**Tasks**:
* [ ] D39.1 `OptStep` as dim-1 cells with sharing-graph semantics
* [ ] D39.2 OptStep ↔ Step simulation via dim-2 cells
* [ ] D39.3 STRICT-28: sharing-graph well-foundedness gate
* [ ] D39.4 Optimal reduction equivalence with standard
* [ ] D39.5 Smoke audit + complexity bound proofs

**Lévy optimality** (1978): a reduction strategy is optimal iff
each **redex family** is contracted at most once. Redex families
are defined via labels propagated through reduction.

**Lamping's algorithm** (1990): represents λ-terms as interaction
nets with sharing fans, brackets, and croissants. Optimal-reduction
is implementable via local rewrites using the sharing-cells from
Era III Day 21.

**Theorems to ship**:
1. **Lévy soundness**: optimal-reduction normalizes to the same NF
   as standard reduction.
2. **Optimal-CR**: optimal reduction is confluent.
3. **Sharing-graph well-foundedness** (STRICT-28): sharing
   reductions terminate (reuses Stage 1 RC predicate from Era S
   Day 41 for termination certificate).

**Reference**: Asperti-Mascari-Guerrini 1998 "BOHM" + Lamping 1990
+ Lévy 1978.

**Acceptance**: OptStep ↔ Step simulation proven; STRICT-28 green;
Lévy optimality witnessed at polygraph level.

### Day 39.5 — User-facing `@[strategy(S)]` attribute (CRITICAL)

**Goal**: surface-level annotation exposing Era V Day 39
optimal-reduction machinery + Era I Day 14 strategy 3-cells to user
code; per-strategy SN proofs + strategy-equivalence theorem;
deterministic compilation under explicit strategy selection.

**Construction (strategy enum + StratStep)**:
```lean
inductive ReductionStrategy where
  | Leftmost      -- leftmost-outermost (call-by-name standard)
  | Outermost     -- normal-order
  | Applicative   -- call-by-value (innermost-leftmost)
  | Lazy          -- WHNF + memoization (Haskell-style)
  | Optimal       -- Levy-Lamping per Era V Day 39

inductive StratStep : ReductionStrategy -> Term -> Term -> Type where
  | leftmost     (h : isLeftmost_redex source)
                 (step : Step source target)
                 : StratStep .Leftmost source target
  | outermost    (h : isOutermost_redex source)
                 (step : Step source target)
                 : StratStep .Outermost source target
  | applicative  (h : isInnermostLeftmost_redex source)
                 (step : Step source target)
                 : StratStep .Applicative source target
  | lazy         (h : isWHNF_target source target)
                 (step : Step source target)
                 : StratStep .Lazy source target
  | optimal      (h : OptStep source target)  -- per Day 39
                 : StratStep .Optimal source target

-- User-facing attribute (FX §17.4 custom-attribute infrastructure)
syntax "@[strategy(" reductionStrategyIdent ")]" : attr
-- Examples:
--   @[strategy(Lazy)]    def fib : Nat -> Nat := ...
--   @[strategy(Optimal)] def complex_pipeline := ...
--   (no annotation): compiler picks via cost-tropical default
```

**Per-strategy SN theorems**:
```
forall (S : ReductionStrategy) (t : Term ctx ty raw),
  exists (nf : Term ctx ty raw_nf),
    StratStep.star S t nf  /\  isNF nf

S = Leftmost     : Plotkin 1975 standardization theorem
S = Outermost    : normal-order normalization (Curry-Feys 1958)
S = Applicative  : call-by-value; SN holds for typed terms via
                   Era S Day 43 Tait reducibility (RC predicate)
S = Lazy         : WHNF reachable via Launchbury 1993 natural
                   semantics for lazy evaluation
S = Optimal      : Levy 1978 + Lamping 1990 per Era V Day 39
                   (sharing-cell well-foundedness, STRICT-28)
```

**Strategy-equivalence theorem (Church-Rosser corollary)**:
```
forall (t : Term ctx ty raw) (S1 S2 : ReductionStrategy),
  let nf_S1 := normalize S1 t
  let nf_S2 := normalize S2 t
  nf_S1  =_{beta, eta, iota}  nf_S2

  -- By per-strategy SN (above) + Church-Rosser (Era II Day 17),
  -- any two strategies produce the SAME normal form up to
  -- alpha-equivalence.
  -- Strategy choice affects PERFORMANCE (compile-time cost +
  -- runtime behavior under lazy / eager), not OBSERVATIONAL RESULTS.
```

**Cost-tropical strategy ranking (default selector)**:
```
For each Term t and each S, cost(S, t) in (R-hat, min, +) per
Era I D14 cost-tropical semiring on strategy 3-cells.
Compiler default: pick argmin_S cost(S, t).
User override @[strategy(S)]: force compilation through StratStep S
  regardless of cost.
Tie-break: prefer S with strictest SN witness (Optimal > Leftmost > ...).
```

**Tasks**:
* [ ] D39.5.1 `Foundation/Reduction/StratStep.lean` — strategy-indexed
  Step relation (5 ctors)
* [ ] D39.5.2 `ReductionStrategy` enum + per-strategy redex predicates
  (isLeftmost / isOutermost / isInnermostLeftmost / isWHNF_target)
* [ ] D39.5.3 Per-strategy SN theorems via Era S Day 43 Tait
  reducibility + Plotkin 1975 standardization
* [ ] D39.5.4 Strategy-equivalence theorem (Church-Rosser corollary)
  zero-axiom
* [ ] D39.5.5 `@[strategy(S)]` attribute parser + elaborator
  integration (FX §17.4 custom-attribute infrastructure)
* [ ] D39.5.6 Cost-tropical strategy ranking via Era I D14
  cost-tropical semiring lift
* [ ] D39.5.7 Compiler-side strategy selection: default = cost-min;
  `@[strategy(S)]` = forced; diagnostic on cost-discrepant override
* [ ] D39.5.8 STRICT-66-V-Strategy gate: per-strategy SN + equivalence
  + attribute-elaboration soundness
* [ ] D39.5.9 Bridge to FX §22 sketch mode: sketch-mode default =
  `@[strategy(Lazy)]`; release default = `@[strategy(Optimal)]`
* [ ] D39.5.10 Smoke audit + commit; update FX §17.4 docs

**References**: Plotkin 1975 (Call-by-name, call-by-value and the
lambda-calculus, TCS); Curry-Feys 1958 (Combinatory Logic Vol. 1 —
normal-order); Launchbury 1993 (A natural semantics for lazy
evaluation, POPL); Levy 1978 (Reductions correctes et optimales dans
le lambda-calcul, PhD); Lamping 1990 (interaction nets, POPL);
Asperti-Mascari-Guerrini 1998 (BOHM, JFP).

**Acceptance**: `@[strategy(S)]` operational on user functions;
per-strategy SN proven zero-axiom for all 5 strategies; strategy
equivalence theorem proven via Church-Rosser; cost-tropical ranking
integrated as default selector; FX sketch-mode (§22) maps to Lazy by
default while release maps to Optimal — full surface-to-strategy
pipeline operational.

### Day 40 — Era V close-out (CRITICAL)

**Goal**: kernel reduction surface is complete — every type former has
its β + η + ι + δ + ζ + proj rules + cubical β + FX-unique β shipped
as both Step ctor (Tree encoding) and dim-1 cell (PolyTerm encoding).

**Tasks**:
* [ ] D40.1 M-series complete: M03 (eval reaches WHNF) at polygraph
  level
* [ ] D40.2 M05 progress theorem (already in_progress)
* [ ] D40.3 M08 headStep? extends to all ι-rules
* [ ] D40.4 M09 headStep? completeness
* [ ] D40.5 D2.6 Univalence ua_β kernel-internal (#1571)
* [ ] D40.6 D3.6 ua_β sub-lemmas (#1572)
* [ ] D40.7 Era V commit + status

**Headline theorem** (kernel reduction completeness):
```
∀ (T : TypeFormer), ∀ (eliminator-on-introduction redex r at T),
  ∃ (β-rule : Step ctor) Δ (β-cell : Dim1Cell PolyTerm),
    β-rule reduces r → contractum  ∧  β-cell encodes the same.

Plus η dual for type formers admitting η (per Day 32 enumeration).

Plus ι rules for every (recursor, constructor) pair.

Plus cubical β: transp-Refl, transp-Pi, transp-Sigma, transp-{closed},
                transp-Glue, hcomp-{cap, side, Refl}, ua-β.

Plus FX-unique: effect-erase, refine-narrow, mode-coerce, bits-level,
                linear-consume.
```

**Acceptance**: every cubical β rule shipped at polygraph level;
M-series complete; ua_β computational; full β+η+ι+δ+ζ+proj+cubical
+FX-unique β coverage.

---

## Era S — Semantic substrate (Path 2 staged) (Day 41–46)

The metatheory anchor. Prop-valued Tait reducibility at Stage 1
unblocks M04 SN (the load-bearing v1.0+ open goal #1273); Stage 2
ships ValueTerm + eval/quote for decidable Conv via NF equality.
Both stages use Stage 1's fundamental theorem as termination
witness — no double work. ~5 months elapsed.

**Encoding column added at this Era**: `RawValueTerm` / `ValueTerm`,
the value-form encoding (closure-based, no host functions, fully
internal to Lean — NOT external semantic content per
discussion-of-record about "semantic" being misleading rhetoric;
it's a different syntactic encoding optimized for normal-form
representation). See Architectural shift §"three-encoding grid".

**β/η at the kernel level for ValueTerm — structural absorption**:
ValueTerm closures CANNOT have β/η redexes by construction:
* β: `applyValue : ValueTerm (Π A B) → ValueTerm A → ValueTerm B`
  is the structural eliminator. Applying a `lamClosure env body`
  evaluates `body` in the extended environment — β is implicit in
  the structure, not a separate Step.
* η: every `lamClosure` IS in η-normal form by virtue of being a
  closure. There's no `lam (app f (var 0))` syntactic redex pattern
  because closures don't carry a redex shape.

So Era S delivers β/η coverage for ValueTerm by **structural
construction** rather than by adding Step ctors. The eval/quote
roundtrip ensures Tree's β/η rules and ValueTerm's structural β/η
agree.

### Day 41 — Stage 1: RC predicate + Ty-arm enumeration (CRITICAL)

**Goal**: ship the Tait reducibility predicate
`RC : Ty → Term → Prop` with one arm per Ty constructor (~25 arms in
FX's expanded Ty).

**Tasks**:
* [ ] D41.1 `Foundation/Reducibility/RC.lean` — inductive
  `RC : ∀ {level scope} (ty : Ty level scope) {ctx} {raw},
        Term ctx ty raw → Prop`
* [ ] D41.2 Per-Ty arms (one per type former):
  - `RC.nat`, `RC.bool`, `RC.unit`, `RC.empty` (closed types: SN
    base case)
  - `RC.arrow`, `RC.piTy` (functions: closure under application)
  - `RC.sigmaTy`, `RC.pair` (Σ: closure under fst/snd)
  - `RC.listType`, `RC.optionType`, `RC.eitherType` (parametric
    inductives)
  - `RC.id`, `RC.oeq`, `RC.idStrict`, `RC.equiv` (identity types)
  - `RC.path`, `RC.glue` (cubical)
  - `RC.modal` (one definition parameterized by Modality, covering
    all 8 modalities)
  - `RC.refine`, `RC.record`, `RC.codata`, `RC.session`, `RC.effect`
* [ ] D41.3 `RC` decidability infrastructure (witness extraction)
* [ ] D41.4 `Smoke/AuditRCDef.lean` zero-axiom for the predicate
  itself

**Construction (function-arrow case)**:
```lean
inductive RC : ∀ {level scope} (ty : Ty level scope)
               {ctx : Ctx mode level scope} {raw : RawTerm scope},
               Term ctx ty raw → Prop where
  | nat (term : Term ctx Ty.nat raw) (sn : SN term) : RC Ty.nat term
  | arrow {A B : Ty level scope}
          (term : Term ctx (Ty.arrow A B) raw)
          (closes : ∀ {raw'} (arg : Term ctx A raw'),
                    RC A arg → RC B (Term.app term arg))
          : RC (Ty.arrow A B) term
  | -- per Ty constructor
```

**Pitfall**: indexed-inductive partial-match propext trap (per
memory `feedback_lean_indexed_partial_match`). Mitigation: full
enumeration over 25 Ty arms; no wildcards.

**Acceptance**: RC inductive ships zero-axiom with all 25 Ty arms;
no host functions in the data (only Prop-valued universally
quantified arrows in `closes`-style fields).

### Day 42 — Stage 1: fundamental theorem per-Term-arm (CRITICAL)

**Goal**: prove `∀ t : Term ctx ty raw, RC ty t` for every Term
constructor (~75 arms after FX's full ctor expansion).

**Tasks**:
* [ ] D42.1 `Foundation/Reducibility/Fundamental.lean` — fundamental
  theorem stub + induction skeleton
* [ ] D42.2 Per-Term-ctor case:
  - Var/lit/unit cases (~10): direct via SN of canonical forms
  - β-redex cases (lam, app, lamPi, appPi, pair, fst, snd, ...): use
    closure properties of RC.arrow / RC.sigmaTy
  - ι-cases (boolElim, natElim, listElim, ...): induction on
    constructor argument
  - Cubical cases (pathLam, pathApp, transp, hcomp, glue): use
    cubical model interpretations
  - Modal cases (modIntro, modElim): per modality
  - Refine/Record/Codata/Session/Effect cases
  - cumulUp case
* [ ] D42.3 STRICT-26-prime: every Term ctor has its fundamental
  theorem case proven zero-axiom
* [ ] D42.4 `Smoke/AuditFundamentalThm.lean`

**Headline theorem**:
```lean
theorem RC.fundamental {ctx : Ctx mode level scope}
                       {ty : Ty level scope} {raw : RawTerm scope}
                       (t : Term ctx ty raw) :
    RC ty t
  -- proof: induction on t's structure
  -- ~75 cases, one per Term ctor
```

**Pitfall**: Wood-Atkey 2022 graded Lam rule (per memory) requires
context division `Γ/p` — the Lam case must respect grading. FX's
Atkey-attack rejection theorem (#1341) confirms the discipline; the
fundamental theorem inherits it.

**Acceptance**: fundamental theorem ships zero-axiom for all 75 Term
ctors; no `sorry`/`admit` durable.

### Day 43 — Stage 1: M04 SN headline + Era S Stage 1 close (CRITICAL)

**Goal**: extract SN as corollary of fundamental theorem; close M04
ticket #1273 / #1564.

**Tasks**:
* [ ] D43.1 `Foundation/Reducibility/SN.lean` — corollary
  `M04.strong_normalization`
* [ ] D43.2 Headline theorem with full kernel surface coverage
* [ ] D43.3 Closure theorems: SN + Compat → confluence-via-Newman
  (Part I §4 Theorem 4.2)
* [ ] D43.4 `Smoke/AuditM04SN.lean` headline audit
* [ ] D43.5 Close M04 ticket; update ROADMAP

**Headline theorem**:
```lean
theorem M04.strong_normalization {ctx : Ctx mode level scope}
                                 {ty : Ty level scope}
                                 {raw : RawTerm scope}
                                 (t : Term ctx ty raw) :
    SN t := (RC.fundamental t).extract_sn
```

**Acceptance**: M04 closes; #1273 + #1564 marked completed; SN holds
across all kernel reductions including Era V cubical β + FX-unique β.

### Day 44 — Stage 2: ValueTerm/NeutralValue/ValueEnv inductives (CRITICAL)

**Goal**: ship the value-form encoding as the third orthogonal
encoding column, with closure-based representation (NO host
functions — closures carry unevaluated body + env).

**Tasks**:
* [ ] D44.1 `Foundation/RawValueTerm.lean` — untyped value-form
  inductive
* [ ] D44.2 `Foundation/ValueTerm.lean` — typed mirror
  (`ValueTerm : Ctx → Ty → Type` — note no `raw` index; semantic
  collapse means multiple raw terms map to the same ValueTerm by
  design)
* [ ] D44.3 `Foundation/NeutralValue.lean` — neutrals (stuck on free
  variables): var, app of neutral, fst of neutral, etc.
* [ ] D44.4 `Foundation/ValueEnv.lean` — environments mapping ctx
  bindings to ValueTerm
* [ ] D44.5 STRICT-27: ValueTerm well-formedness (closures' env types
  match ctx)

**Construction**:
```lean
mutual
  inductive ValueTerm : Ty → Type where
    | natLit (n : Nat) : ValueTerm Ty.nat
    | natNeu (n : NeutralValue Ty.nat) : ValueTerm Ty.nat
    | boolLit (b : Bool) : ValueTerm Ty.bool
    | unitVal : ValueTerm Ty.unit
    | pair (a : ValueTerm A) (b : ValueTerm B)
        : ValueTerm (Ty.sigmaTy A B)
    | lamClosure (env : ValueEnv ctx)
                 (body : Term (ctx.cons argTy) resTy bodyRaw)
        : ValueTerm (Ty.arrow argTy resTy)
    | -- per Ty ctor; closures carry unevaluated bodies + envs
    | universal_neu (n : NeutralValue ty) : ValueTerm ty

  inductive NeutralValue : Ty → Type where
    | var (i : Fin scope) : NeutralValue (lookupTy ctx i)
    | app (n : NeutralValue (Ty.arrow A B)) (a : ValueTerm A)
        : NeutralValue B
    | -- per eliminator

  inductive ValueEnv : Ctx mode level scope → Type where
    | nil : ValueEnv Ctx.empty
    | cons (env : ValueEnv ctx) (v : ValueTerm ty)
        : ValueEnv (ctx.cons ty)
end mutual
```

**Theorems**:
1. **No host functions**: every ctor uses constructor-driven
   dispatch only (per Part I §6).
2. **Closures are η-normal by construction**: there's no syntactic
   redex pattern in `lamClosure`.

**Acceptance**: ValueTerm + NeutralValue + ValueEnv ship zero-axiom;
STRICT-27 green; no host functions anywhere.

### Day 45 — Stage 2: eval + quote (CRITICAL)

**Goal**: ship `eval : Term → ValueEnv → ValueTerm` (structurally
recursive on Term, terminates by Stage 1 fundamental theorem) and
`quote : ValueTerm → NormalTerm` (structural on Ty).

**Tasks**:
* [ ] D45.1 `Algo/Eval.lean` (rebuild) — `Term.eval` per-ctor
  - β-app: `eval (app f a) env := apply (eval f env) (eval a env)`
  - β-fst-pair: `eval (fst p) env := match eval p env | pair a _ => a`
  - All eliminator-on-introduction reductions become structural
    pattern matches in eval
  - All ι-rules absorbed similarly
  - Termination certificate: Stage 1's fundamental theorem witnesses
    termination on any well-typed input
* [ ] D45.2 `Algo/Quote.lean` — `ValueTerm.quote` per-Ty
  - quote a closure: apply to fresh neutral var, recursively quote
    result, wrap as Term.lam
  - quote neutrals: rebuild as Term ctor application
  - Note: quote produces η-long normal forms (every closure
    quotes back as a syntactic lambda, even if the source had no
    explicit lambda) — this is the η aspect
* [ ] D45.3 `Algo/NbE.lean` — composition `nbe := quote ∘ eval`
* [ ] D45.4 `Smoke/AuditEvalQuote.lean`

**Theorems shipped**:
1. **eval termination**: every well-typed term evaluates to a
   ValueTerm in finite steps (corollary of Day 43's M04 SN).
2. **quote totality**: every ValueTerm quotes to a NormalTerm.
3. **eval/quote roundtrip soundness**:
   `t ≅β,η,ι quote (eval t emptyEnv)` for every closed t.
4. **β-on-ValueTerm = structural**:
   `apply (lamClosure env body) v = eval body (env.cons v)` —
   β is structural pattern-match, not a separate Step.
5. **η-on-ValueTerm = identity**: closures are η-normal; quote
   produces η-long forms automatically.

**Acceptance**: eval + quote ship zero-axiom; roundtrip soundness
proven; β/η on ValueTerm verified structural per theorem 4 + 5.

### Day 46 — Stage 2: decidable Conv + Era S close-out (CRITICAL)

**Goal**: ship `Conv.decide` via NF equality and close Era S with
full Path 2 staged delivery.

**Tasks**:
* [ ] D46.1 `Reduction/ConvDecide.lean` — `instance Conv.decide`
  via `decEq (quote (eval t1 nil)) (quote (eval t2 nil))`
* [ ] D46.2 Soundness theorem: `Conv t1 t2 → nbe t1 = nbe t2`
* [ ] D46.3 Completeness theorem: `nbe t1 = nbe t2 → Conv t1 t2`
* [ ] D46.4 STRICT-28: NbE/Conv decision parity gate
* [ ] D46.5 `Smoke/AuditConvDecide.lean`
* [ ] D46.6 Era S commit + status

**Theorem (Conv decidability via NbE)**:
```lean
instance Conv.decide (t1 t2 : Term ctx ty raw) : Decidable (Conv t1 t2) := by
  let v1 := Term.eval t1 ValueEnv.nil
  let v2 := Term.eval t2 ValueEnv.nil
  let nf1 := v1.quote
  let nf2 := v2.quote
  exact decEq nf1 nf2
```

**Acceptance**: Era S complete; M04 SN closed; decidable Conv via
NF; ValueTerm encoding column live; β/η coverage on ValueTerm
proven structural; v1.0+ trust spine compatible (Bridge status
promotion now possible for theorems using ValueTerm if FX1.check_sound
extends to cover the bridge).

---

## Era VI — Auto-proof at polygraph level (Day 47–53)

Tactics-as-cells. Critical for "user never writes proofs" vision.
~6 months.

### Day 47 — Decidable as polygraph cell (CRITICAL)

**Goal**: ship `Step.tactic_decide` per Part I §7 + Appendix C §R14;
tactics absorbed into the kernel β-reduction surface.

**Tasks**:
* [ ] D47.1 `Step.tactic_decide` as dim-1 cell, gated by
  `Decidable P`
* [ ] D47.2 Constructive Decidable instance database (audited)
* [ ] D47.3 SR + Compat + Confluence
* [ ] D47.4 STRICT-29: tactic-as-β termination gate
* [ ] D47.5 Smoke audit decide-β

**Construction**: for each Decidable proposition P, the
`tactic_decide` β-rule fires:
```
tactic_decide:  (decide P).inner   →  (Decidable P).val
                when Decidable P is constructive
```

**Termination**: Decidable instances are polynomial-time decidable
by definition (Part VI §C7).

**Acceptance**: decide-β polygraph cell zero-axiom; STRICT-29 green.

### Day 48 — Linear arithmetic as polygraph cell (CRITICAL)

**Goal**: ship `omega` and `linarith` as β rules.

**Tasks**:
* [ ] D48.1 `Step.tactic_omega` for Presburger
* [ ] D48.2 `Step.tactic_linarith` for linear arithmetic over ordered
  fields
* [ ] D48.3 Verified Omega decision procedure as dim-1 cell
* [ ] D48.4 Smoke + benchmark

**Omega decision procedure** (Pugh 1991): Presburger arithmetic
over ℤ is decidable (super-exponential worst case, ~polynomial
average).

**Linarith** (linear arithmetic over ordered fields): decidable via
**Fourier-Motzkin elimination**.

**Theorem**: both are kernel-verifiable as β rules with bounded
search depth.

**Acceptance**: omega + linarith ship as zero-axiom dim-1 cells.

### Day 49 — Polynomial / ring / field as polygraph cell (CRITICAL)

**Goal**: ship `ring`, `field`, `polyrith` tactics as β rules.

**Tasks**:
* [ ] D49.1 `Step.tactic_ring` for commutative rings
* [ ] D49.2 `Step.tactic_field` for field equations
* [ ] D49.3 `Step.tactic_polyrith` for polynomial arithmetic
* [ ] D49.4 SR + Compat + Confluence + Smoke

**Theorem (Buchberger 1965)**: Gröbner basis computation gives a
decision procedure for polynomial ideal membership.

**FX commitment**: ring/field decision via verified Gröbner basis;
polyrith via verified Buchberger.

**Acceptance**: polynomial/ring/field tactics zero-axiom.

### Day 50 — Termination synthesis as polygraph cell (CRITICAL)

**Goal**: standard termination measure machinery as kernel β.

**Tasks**:
* [ ] D50.1 Lexicographic-order auto-discovery
* [ ] D50.2 Size-measure auto-discovery on inductives
* [ ] D50.3 Multiset-ordering auto-discovery
* [ ] D50.4 Coq-Equations-style at kernel level
* [ ] D50.5 Smoke audit termination synthesis

**Standard machinery** (per Part VI §C6):
* **Multiset Path Order (MPO)** — Dershowitz 1979:
  ```
  For ordering ≥ on terms, MPO ≥_M is defined by:
    s ≥_M t  iff  s = f(s_1, ..., s_n) and:
      (1) some s_i ≥_M t, OR
      (2) f > head(t) and ∀ tj. s ≥_M tj, OR
      (3) f = head(t) and {s_i} ≥_M-multiset {t_j}
  ```
* **Lexicographic Path Order (LPO)** — Kamin-Lévy 1980:
  similar but uses lex order on argument tuples.
* **Recursive Path Order (RPO)** — Plaisted 1978: generalization.
* **Polynomial interpretations** — Lankford 1979: assign polynomial
  norms to function symbols; reduction must strictly decrease norm.
* **Dependency Pair method** — Arts-Giesl 2000: modern automation;
  reduces termination to chain-non-existence in dependency graph.

**FX commitment**: ship MPO + DP method as termination synthesizers
(Part VI §C6).

**Acceptance**: termination synthesis automatic for 80%+ recursive
defs; STRICT-29 + STRICT-30 green.

### Day 51 — Refinement type inference (CRITICAL)

**Goal**: Liquid Haskell-style HM + refinement inference at kernel.

**Tasks**:
* [ ] D51.1 Liquid-Haskell-style HM-refinement inference
* [ ] D51.2 Constraint generation from AST
* [ ] D51.3 SMT proposal import with independently checkable proof
  witnesses/counterexamples
* [ ] D51.4 Refinement narrowing at call sites
* [ ] D51.5 Smoke + inference quality benchmark

**Constraint generation**: for each program point, generate
`v : T | φ(v)` constraints from typing rules.

**Constraint solving**: Z3/CVC5 may propose a model, proof trace, or
unsat certificate; the FX kernel accepts only certificates checked by
a small verified checker. If no checkable certificate is produced,
the result is advisory only and cannot close a proof obligation.

**Theorem (Liquid Haskell)**: refinement inference is decidable
for the decidable fragment of the constraint language.

**Acceptance**: refinement inference + certificate-checked solver
integration zero-axiom on the decidable fragment; raw SMT success is
never a proof source.

### Day 52 — Loop invariant + Hoare inference (parallel)

**Goal**: Houdini's algorithm + Pre/Post abduction at kernel.

**Tasks**:
* [ ] D52.1 Houdini's algorithm at kernel level
* [ ] D52.2 Pre/post abduction for `let` bindings
* [ ] D52.3 Solver-proposed invariant strengthening with
  kernel-checkable certificates
* [ ] D52.4 Auto-test generation from inferred refinements
* [ ] D52.5 Smoke audit + Dafny-comparison

**Houdini** (Flanagan-Leino 2001): start with all candidate
invariants, drop ones not preserved by loop body, iterate to
fixpoint.

**Convergence**: Houdini converges in O(|candidates|) iterations.

**Pre/Post abduction** (Calcagno et al. 2009): for each statement,
infer pre/post conditions via constraint backwards-propagation.

**Acceptance**: Houdini + abduction zero-axiom; competitive with
Dafny on loop-invariant inference benchmark.

### Day 53 — Era VI close-out (CRITICAL)

**Goal**: 80%+ refinement obligation auto-discharge benchmark on
representative FX programs.

**Tasks**:
* [ ] D53.1 All decidable + arithmetic + polynomial tactics shipped
  as polygraph cells
* [ ] D53.2 Refinement inference operational
* [ ] D53.3 Termination synthesis automatic for 80%+ recursive
  defs
* [ ] D53.4 Era VI commit

**Acceptance**: typical FX program with refinement annotations
elaborates without user-supplied proof obligations for decidable
fragments.

---

## Era VII — WMM at polygraph level (Day 54–58)

**Note**: per-Day D-prefix identifiers in Eras VI–XIII below were
authored against the pre-Era-S Day numbers. The +6 shift from Era S
insertion (Day 41–46) means the numerical content reads correctly
when each "Day NN" inside Eras VI–XIII is interpreted as
"Day NN + 6". Era heading ranges above have been updated; a future
mechanical pass will renumber inner D-prefixes for consistency.


Highest commercial-value Era. ~4 months.

### Day 54 — WMM type-level orderings (CRITICAL)

**Goal**: memory orderings as types per Appendix C §R13.

**Tasks**:
* [ ] D54.1 `MemOrder` enum + `Loc<a, ord>` types
* [ ] D54.2 `Atomic.load` / `Atomic.store` with ordering
* [ ] D54.3 SR + Compat + decidability
* [ ] D54.4 Smoke

**Definition**: `MemOrder ::= Relaxed | Acquire | Release | AcqRel
| SeqCst`

**Inclusion order**:
```
Relaxed < Acquire ≤ AcqRel
Relaxed < Release ≤ AcqRel
AcqRel ≤ SeqCst
```

**Decidability**: ordering arithmetic is constant-time decidable on
finite enum (Part VI §C7).

**Acceptance**: MemOrder enum + Atomic ops zero-axiom.

### Day 55 — DRF as polygraph predicate (CRITICAL)

**Goal**: data-race-freedom predicate at polygraph level.

**Tasks**:
* [ ] D55.1 Data-race-freedom as dim-2 cell witness
* [ ] D55.2 DRF → SC equivalence theorem
* [ ] D55.3 Promising semantics integration
* [ ] D55.4 Smoke + race-freedom proofs

**Definition**: `DRF(prog)` iff every pair of conflicting accesses
(read-write or write-write to same location) is ordered by
synchronization.

**Theorem (Adve-Hill 1990)**: DRF programs have SC-equivalent
semantics under any standard WMM.

**Promising semantics** (Kang-Hur-Lahav-Vafeiadis 2017): formal
operational model for relaxed memory, used for verification.

**RC11** (Lahav-Vafeiadis 2017): repaired C11 memory model.

**Acceptance**: DRF predicate + Adve-Hill theorem + Promising
semantics integration zero-axiom.

### Day 56 — Per-architecture compilation as polygraph cells (CRITICAL)

**Goal**: each architecture is a fiber of dim-4.

**Tasks**:
* [ ] D56.1 x86 TSO compilation cells
* [ ] D56.2 ARM-WMM compilation cells (dmb instructions)
* [ ] D56.3 RISC-V WMM compilation cells (fence ops)
* [ ] D56.4 GPU memory model cells (NVIDIA / AMD)
* [ ] D56.5 Cross-arch observational equivalence

**TSO (x86)**: total store ordering. Stores buffered until commit.
Reads can bypass writes to different locations.

**ARM**: weaker model. Both reads and writes can be reordered with
memory ordering hints (dmb instructions for fences).

**RISC-V WMM**: relaxed model with explicit fence ops.

**Theorem (CompCert-TSO, Sevcik thesis)**: x86 TSO compilation
from SC source preserves semantics.

**Acceptance**: per-architecture compilation zero-axiom for the
formal TSO/ARM/RISC-V/GPU memory models represented in the kernel;
real hardware conformance remains a vendor/spec TCB boundary unless
checked by separate litmus-test/certificate pipelines.

### Day 57 — WMM optimizations as polygraph cells (CRITICAL)

**Goal**: relaxed reordering, RMW fusion, fence elision verified
per WMM.

**Tasks**:
* [ ] D57.1 Verified relaxed-load reordering
* [ ] D57.2 Read-modify-write fusion
* [ ] D57.3 Acquire/release fence elision when SC-DRF
* [ ] D57.4 Lock-free data structure templates
* [ ] D57.5 STRICT-30: DRF-preservation gate

**Theorems**:
1. **Relaxed reordering correctness**: for relaxed memory operations
   on independent locations, reordering preserves observable
   behavior under any standard WMM.
2. **Acquire/release fence elision**: in SC-DRF programs, certain
   fences are redundant.

**Acceptance**: WMM optimizations zero-axiom; STRICT-30 green.

### Day 58 — Era VII close-out (CRITICAL)

**Goal**: lock-free structures verified end-to-end.

**Tasks**:
* [ ] D58.1 Lock-free counter / hazard-pointer / RCU verified
  end-to-end across 3+ architectures
* [ ] D58.2 Era VII commit

**Examples**: hazard-pointer-based concurrent stack; RCU lock-free
list; Treiber stack; Michael-Scott queue.

**Acceptance**: FX programs with WMM-typed memory ops compile to
per-architecture optimal code with proven race-freedom.

---

## Era VIII — Refinement feedback (dim 5) (Day 59–63)

Structured suggestions for LLM/programmer. ~4 months.

### Day 59 — Refinement-functor framework (CRITICAL)

**Goal**: refinement functors as natural transformations between
dim-3 search functors at refinement contexts.

**Tasks**:
* [ ] D59.1 `Polygraph/Dim5/RefinementFunctor.lean`
* [ ] D59.2 Constraint→speedup mapping decidability
* [ ] D59.3 STRICT-31: dim-5 cell well-formedness
* [ ] D59.4 Smoke audit refinement functors

**Definition** (formal):
```
Cat_Refinement : category of refinement contexts
  Objects: refinement contexts (sets of constraints)
  Morphisms: refinement strengthenings (constraint-additions)

Cat_Search : category of search problems  
  Objects: search-space + cost function
  Morphisms: problem-reductions

Search : Cat_Refinement → Cat_Search   (functor)

Dim5Cell : NaturalTransformation Search Search'
  i.e., for every refinement context R, a morphism Search(R) → Search'(R)
  satisfying naturality square.
```

**Naturality square**: for refinement-strengthening f : R → R':
```
        Dim5Cell(R)
Search(R) ─────────→ Search'(R)
   │                       │
   ↓ Search(f)              ↓ Search'(f)
   │                       │
Search(R') ────────→ Search'(R')
        Dim5Cell(R')
```

**Acceptance**: dim-5 cells + naturality square zero-axiom;
STRICT-31 green.

### Day 60 — Speedup estimation (CRITICAL)

**Goal**: cost-tropical computation across refinement
strengthenings.

**Tasks**:
* [ ] D60.1 Cost-tropical computation
* [ ] D60.2 Per-refinement-class speedup catalog (verified)
* [ ] D60.3 Marginal speedup gradient computation
* [ ] D60.4 Smoke audit speedup estimation

**Speedup gradient**: for refinement-strengthening f : R → R',
```
Δcost(f) = cost(Search(R')) - cost(Search(R))
```

In tropical semiring (Appendix B), gradient is non-standard. Use:
* **Subdifferential** in convex analysis
* **Soft-min via LogSumExp**: log-domain gradient
* **Marginal speedup**: discrete derivative

**Acceptance**: speedup gradient computation zero-axiom; per-
refinement-class catalog ships verified.

### Day 61 — Proof obligation generation (CRITICAL)

**Goal**: automated proof obligation construction.

**Tasks**:
* [ ] D61.1 For each refinement strengthening, generate proof goal
* [ ] D61.2 Decidability classification (auto-provable / provable
  / user-required)
* [ ] D61.3 Confidence scoring
* [ ] D61.4 Smoke audit obligation generation

For each refinement-strengthening f : R → R':
1. Generate the "must prove" goal for f (the additional constraints
   in R' \ R).
2. Classify decidability:
   - **Auto-provable**: Decidable instance exists
   - **Provable**: a solver can emit a kernel-checkable certificate
   - **User-required**: needs human input
3. Compute confidence score per goal.

**Acceptance**: obligation generation, decidability classification,
and confidence scoring ship zero-axiom; confidence scores and solver
outputs are advisory until the certificate checker accepts them.

### Day 62 — Feedback API for LLM/programmer (CRITICAL)

**Goal**: structured output type for daemon API.

**Tasks**:
* [ ] D62.1 `RefinementFeedback` structured output type
* [ ] D62.2 REST endpoint via existing fxc daemon (§24)
* [ ] D62.3 Suggestion ranking by speedup magnitude
* [ ] D62.4 Auto-application thresholds (>0.9 confidence → auto)
* [ ] D62.5 LLM-friendly JSON + human-friendly markdown formats

**Construction**:
```
RefinementFeedback : Type := {
  current_refinement : RefinementContext
  current_asm : ASMSequence
  current_cost : Cost
  suggestions : Vector Suggestion
}

Suggestion : Type := {
  proposed_refinement : RefinementStrengthening
  expected_speedup : Cost.Ratio
  proof_obligation : Proposition
  automatic_provable : Probability
  semantic_implication : NaturalLanguage
}
```

**Acceptance**: API operational + ranking + auto-application zero-
axiom.

### Day 63 — Era VIII close-out (CRITICAL)

**Goal**: end-to-end demo verifying speedup predictions match
empirical measurements within 5%.

**Tasks**:
* [ ] D63.1 End-to-end demo: agent submits FX program → daemon
  returns ranked refinement suggestions with verified speedups
* [ ] D63.2 Round-trip benchmark: agent applies suggestions →
  measured speedup matches dim-5 prediction within 5%
* [ ] D63.3 Era VIII commit

**Acceptance**: refinement strengthening becomes a collaborative
process with kernel-derived suggestions; LLM agents receive
structured feedback that mechanically guides program improvement.

### Day 63.A — Promise/Guard/Fallback effect (CRITICAL — load-bearing for Era IV.5 + FEU-FX)

**Goal**: ship gradual-typing infrastructure for runtime properties
that cannot be statically typechecked (analog ENOB, actual
delay, actual power, calibration accuracy). Compile-time loose
bound + runtime guard + adaptive fallback policy. Required by
Era IV.5 multi-level hardware soundness conditions
(F_RLC→STA settling-time, F_STA→Digital timing-closure) and
FEU-FX vertical (per-chip ENOB measurement + adaptive precision
escalation).

**Construction (Promise type)**:
```lean
-- A "promise" is a refinement that's checked at runtime
structure Promise (P : Prop) where
  compile_bound  : ((lo : ℝ) × (hi : ℝ))         -- loose static
  runtime_check  : Unit → Result CheckOk CheckFailReason
  on_failure     : FallbackPolicy P
  -- The refinement P holds iff runtime_check passes; if fails,
  -- on_failure provides recovery.

-- Concrete instantiation: ENOB requirement
def ENOB_at_least (n : Rational) : Type :=
  Promise (analog_ENOB ≥ n)

-- Concrete instantiation: timing-margin requirement
def TimingMargin_at_least (margin : Picoseconds) : Type :=
  Promise (slack_setup ≥ margin ∧ slack_hold ≥ margin)

-- Concrete instantiation: power-budget requirement
def PowerBudget_below (W : Watts) : Type :=
  Promise (instant_power ≤ W ∧ avg_power_window ≤ W * 0.8)
```

**Construction (Guard effect)**:
```lean
-- Effect that runs the runtime check and provides fallback action
effect Guard (P : Prop) (compile_bound : ℝ × ℝ) where
  measure_actual : Unit → ℝ                -- runtime measurement
  re_calibrate   : Unit → Unit              -- spare-row sweep,
                                               FG-AUTOCAL refresh
  escalate_mode  : Unit → NewMode           -- mode escalation
                                               (FAST→DEFAULT→
                                                ENHANCED→PRECISION)
  fall_back      : FallbackTarget → Unit    -- to digital, to
                                               lower freq, etc.

-- Operations producing promised values
def mac_with_enob {n : Rational} :
    (inputs : Vec)
    → Vec with ENOB_at_least n
            with Guard (analog_ENOB ≥ n) compile_bound
where
  compile_bound = (mode_loose_lower n, mode_loose_upper n)
```

**Construction (FallbackPolicy adaptive)**:
```lean
inductive FallbackPolicy (P : Prop) where
  -- Re-measure: assume measurement was stale
  | re_measure
  -- Re-calibrate then re-measure
  | re_calibrate_then_measure
  -- Escalate to higher-precision mode (FAST→DEFAULT→ENHANCED→
  -- PRECISION); each step takes more cycles but achieves higher
  -- guaranteed ENOB
  | escalate_precision (current : PrecisionMode)
  -- Reduce operating frequency (more averaging time, better SNR)
  | reduce_frequency (current : Frequency)
  -- Fall back to digital (Tern computes exactly, slower but
  -- guaranteed correct)
  | fall_back_to_digital
  -- Trap to OS for graceful degradation
  | trap_to_os (reason : String)
  -- Combinator: try first, then second on failure
  | sequenced (first : FallbackPolicy P) (then : FallbackPolicy P)
```

**Theorem (Promise/Guard soundness)**:
```
∀ (p : Promise P) (action : ⟦P⟧ → α),
  let result := run_with_guard p action
  match result with
  | .promised_holds α' => α' is sound w.r.t. P
  | .promised_fails fb => fallback fb is invoked;
                           result is sound w.r.t. weaker P'
                           ⊆ P (per fallback policy's
                                guaranteed lower bound)
```

**Use cases (concrete instantiations)**:
```
-- FEU analog ENOB (per-chip variable; runtime measured via
-- §19.6 7-level spare-row ramp)
mac_inference (input : Vec d)
  : Vec d with ENOB_at_least 12
           compile_bound = (13.0, 14.5)  -- DEFAULT mode loose
           runtime_check = read_spare_row_calibration ()
           on_failure = sequenced re_calibrate_then_measure
                                  (escalate_precision DEFAULT)

-- Real-time deadline (per-PVT-corner variable)
process_request (req : Request)
  : Response with TimingMargin_at_least 50_ps
              compile_bound = (40, 100)
              runtime_check = read_BIST_timing_probe ()
              on_failure = reduce_frequency current

-- Power envelope (per-temp variable)
gpu_kernel (params : Tensor)
  : Tensor with PowerBudget_below 50_W
            compile_bound = (45, 55)
            runtime_check = read_per_tile_power_monitors ()
            on_failure = throttle_then_resume
```

**Tasks**:
* [ ] D63.A.1 `Foundation/Promise/Foundation.lean` — Promise
  refined-runtime type
* [ ] D63.A.2 Guard effect with measure / re-calibrate / escalate
  / fall-back operations
* [ ] D63.A.3 FallbackPolicy inductive with 7 variants +
  composability via sequenced combinator
* [ ] D63.A.4 Promise/Guard soundness theorem zero-axiom
* [ ] D63.A.5 Concrete ENOB_at_least n + TimingMargin_at_least m +
  PowerBudget_below w predicates per Era IV.5 D31.8 + FEU-FX
* [ ] D63.A.6 Adaptive precision-mode escalation (FAST→DEFAULT→
  ENHANCED→PRECISION per FEU §19.4 precision-mode catalog)
* [ ] D63.A.7 Bridge to FEU-FX vertical: spare-row 7-level
  ramp calibration as runtime_check implementation
* [ ] D63.A.8 STRICT-60-VIII-PromiseGuard gate
* [ ] D63.A.9 Smoke + commit

**Per-chip characterization parameter (links to Era IV.5 + Vertical I)**:
```lean
-- Per-die manufacturing characterization data
structure Characterization (die : DieID) where
  manufacturing_corner    : ProcessCorner    -- TT, FF, SS
  per_column_OTA_offset   : Vec 2187 ℝ        -- FG-AUTOCAL data
  per_tile_defect_map     : Vec 285 DefectMask
  per_IGZO_plane_Vth      : Vec 10 Volts
  per_PLL_lock_freq       : Frequency
  per_DRAM_PHY_delay_trim : Vec 4 Picoseconds
  per_SerDes_lane_eq      : Vec 32 EQCoefficient

-- Operations parameterized by characterization
def mac_per_chip<die_id, char : Characterization die_id>
    (tile : TileCalibrated die_id char)
    (weights : Lattice tile)
    (inputs : Vec d)
    : Vec d
```

**Tasks (continued)**:
* [ ] D63.A.10 `Foundation/PerChip/Characterization.lean`
* [ ] D63.A.11 Characterization struct (mirrors FEU §3 / §5
  per-chip parameter tables)
* [ ] D63.A.12 Per-chip type-parametric operations (compatible only
  with their characterization data)
* [ ] D63.A.13 STRICT-61-VIII-PerChip gate
* [ ] D63.A.14 Smoke + commit

**Acceptance**: Promise/Guard/Fallback ships zero-axiom; per-chip
characterization parametricity operational; Era IV.5 abstraction-
functor soundness conditions handle runtime measurements
gracefully; FEU-FX vertical's analog-ENOB / timing-margin /
power-budget all use this infrastructure.

---

## Era IX — Optimal transport integration (Day 64–68)

ML-augmented superoptimization with kernel verification. ~4 months.

### Day 64 — Tropical / idempotent semiring substrate (CRITICAL)

**Goal**: semiring catalog (Appendix B).

**Tasks**:
* [ ] D64.1 `Foundation/Semiring/Tropical.lean` — (ℝ̂, min, +)
* [ ] D64.2 `Foundation/Semiring/Boolean.lean` — (Bool, ∨, ∧)
* [ ] D64.3 `Foundation/Semiring/MaxPlus.lean` — for cost analysis
* [ ] D64.4 `Foundation/Semiring/LogSumExp.lean` — soft-min for OT
* [ ] D64.5 Custom semiring framework for refinement evaluation

**Tropical semiring** (ℝ̂, min, +) where ℝ̂ = ℝ ∪ {+∞}:
* Identity for min: +∞
* Identity for +: 0
* Min distributes over +.

**Boolean semiring** (Bool, ∨, ∧):
* Identity for ∨: false
* Identity for ∧: true

**Max-plus semiring** (ℝ̂, max, +): for cost analysis.

**LogSumExp semiring** at temperature ε:
* ⊕ = LogSumExp_ε(x, y) = ε log(e^{x/ε} + e^{y/ε})
* ⊗ = +
* As ε → 0, LogSumExp → max (recovers max-plus).

**Theorem (Litvinov-Maslov 1996)**: many shortest-path-like
problems unify as matrix algebra over idempotent semirings.

**Acceptance**: semiring instances + verified laws zero-axiom.

### Day 65 — Tropical-GEMM kernel for B200 (CRITICAL)

**Goal**: custom CUDA kernel for tropical-semiring GEMM.

**Tasks**:
* [ ] D65.1 Custom CUDA kernel for tropical GEMM (FP8 / FP16 paths)
* [ ] D65.2 Boolean-GEMM kernel
* [ ] D65.3 LogSumExp-GEMM for soft search
* [ ] D65.4 Realization equivalence vs reference impl
* [ ] D65.5 Performance: 2.5 PFLOPs equivalent throughput on B200

**Implementation**: replace the `+` and `×` operations in the
inner loop of CUDA's GEMM kernel with `min` and `+`. Use
TensorCore-compatible types (FP8, INT8) for throughput.

**Theorem**: tropical-GEMM produces the correct shortest-path /
min-cost reduction.

**Acceptance**: tropical/Boolean/LogSumExp GEMM kernels verified
equivalent to reference impl; B200 throughput target met.

### Day 66 — Sinkhorn-style soft polygraph search (parallel)

**Goal**: Sinkhorn-Knopp algorithm for soft search.

**Tasks**:
* [ ] D66.1 Soft-min via LogSumExp at temperature ε
* [ ] D66.2 Sinkhorn iteration for kernel β-rule scoring
* [ ] D66.3 Differentiable cost-gradient
* [ ] D66.4 Recovery: as ε → 0, hard search recovered
* [ ] D66.5 Smoke audit soft search

**Sinkhorn algorithm** (1967, popularized by Cuturi 2013): given a
matrix C of costs, compute the regularized optimal transport plan
via iterative scaling.

**Convergence rate** (Cuturi-Peyré): linear in regularization ε:
```
‖π_k - π*‖ ≤ C · (1 - ε)^k
```

**Soft-min reduction**: as ε → 0, recovers hard tropical search.

**Acceptance**: Sinkhorn iteration zero-axiom; soft↔hard recovery
verified.

### Day 67 — Gromov-Wasserstein subgraph similarity (parallel, exploratory)

**Goal**: GW distance for polygraph regions.

**Tasks**:
* [ ] D67.1 GW distance computation between polygraph regions
* [ ] D67.2 Cross-region proof transfer via GW plan
* [ ] D67.3 Optimization-pattern matching
* [ ] D67.4 Incremental compilation: re-optimize only high-GW-distance
  regions
* [ ] D67.5 Smoke audit + benchmark

**Definition (Mémoli 2011)**: for metric measure spaces (X, dx, μ)
and (Y, dy, ν), GW distance is:
```
GW₂(X, Y) = inf_{π coupling} ∫∫ |dx(x, x') - dy(y, y')|² dπ(x,y) dπ(x',y')
```

**Computational complexity**: NP-hard in general; polynomial
approximations exist (Solomon et al. 2016).

**Acceptance**: GW computation + cross-region transfer zero-axiom
on the tractable approximation fragment.

### Day 68 — Era IX close-out (CRITICAL)

**Goal**: ML-guided polygraph search with kernel verification
operational.

**Tasks**:
* [ ] D68.1 ML-guided polygraph search operational
* [ ] D68.2 OT machinery integrated as kernel β-rule scorer
* [ ] D68.3 Verified extraction (kernel verifies ML's MAP path)
* [ ] D68.4 Era IX commit

**Acceptance**: ML model proposes rewrites; kernel verifies; MAP
path extracted with proven optimality at chosen strategy level.

---

## Era X — ∞-frontier (Day 69–78)

Higher-dimensional structure. ~10 months.

### Day 69 — ∞-groupoid finite dimensions (CRITICAL)

**Goal**: cubical-extended interval at dim n with computation rules.

**Tasks**:
* [ ] D69.1 Cubical-extended interval at dimension n
* [ ] D69.2 n-cell ctors for n ≤ 4 with computation rules
* [ ] D69.3 Coherence laws (associator / pentagon / hexagon)
* [ ] D69.4 STRICT-32: n-cell decidability gate
* [ ] D69.5 Smoke audit higher dimensions

**Cubical interval object I**: a single object I in cubical type
theory satisfying:
* Two endpoint constants 0, 1 : I
* Connections, reversals (CCHM)
* Lattice operations (∧, ∨)

**n-cube I^n**: the n-fold product of intervals.

**n-truncated types**:
```
isContr : Type → Prop  (contractibility)
n-truncated A : iff homotopy groups π_k(A) trivial for k > n
```

**Theorem (cubical Agda)**: types are n-truncated iff their
n+1-paths contract.

**Acceptance**: n-cell ctors for n ≤ 4 + coherence laws zero-axiom;
STRICT-32 green.

### Day 70 — (∞,1)-categories / directed types (CRITICAL)

**Goal**: simplicial type theory (Riehl-Shulman 2017).

**Tasks**:
* [ ] D70.1 Directed path types (non-invertible 1-cells)
* [ ] D70.2 Riehl-Shulman simplicial type theory primitives
* [ ] D70.3 State machine (§13) lifted to directed types
* [ ] D70.4 Smoke audit non-invertible morphisms

**Directed interval**: 𝟚 := bool with directed structure
(no symmetry).

**Hom type**: `Hom_A(x, y) := type of directed paths from x to y`.

**Theorem (Riehl-Shulman)**: simplicial type theory soundly models
∞-categories.

**Comparison**: HoTT's `Path A x y` is INVERTIBLE (Hom is
symmetric); simplicial Hom is DIRECTED (asymmetric).

**Acceptance**: directed types + Hom + machine-lift zero-axiom.

### Day 71 — Cohesive ∞-toposes (CRITICAL)

**Goal**: Schreiber's cohesive structure at ∞-dimension.

**Tasks**:
* [ ] D71.1 Modal ♭ ⊣ ◇ ⊣ □ ⊣ ♯ chain at ∞-dimension
* [ ] D71.2 Cohesive structure as polygraph dimension fibre
* [ ] D71.3 Schreiber-Shulman primitives
* [ ] D71.4 D4.5 adjoint chain extension to ∞
* [ ] D71.5 Smoke + adjunction coherence

**Cohesion** (Lawvere 1991, Schreiber 2013):

The shape ∫, flat ♭, sharp ♯ form an adjoint triple ∫ ⊣ ♭ ⊣ ♯
between the cohesive ∞-topos H and its discrete subspace H_disc.

**Differential cohesion** (Schreiber): adds reduced ⊝, infinitesimal
shape ℑ for super-geometric structure.

**FX commitment**: 4-modality chain ♭ ⊣ ◇ ⊣ □ ⊣ ♯ extends the
3-modality cohesion (Part VI §C3). The 4th modality ◇ (diamond)
interpolates flat and shape.

**Acceptance**: cohesive ∞-topos infrastructure + adjunction
coherence zero-axiom.

### Day 72 — Differential cohesion + SDG (parallel, exploratory)

**Goal**: synthetic differential geometry.

**Tasks**:
* [ ] D72.1 ⊝ (reduced), ℑ (infinitesimal shape), & (sharp-
  infinitesimal)
* [ ] D72.2 Kock-Lawvere infinitesimals
* [ ] D72.3 Smooth function types
* [ ] D72.4 Manifold types via cohesive
* [ ] D72.5 ODE solution types
* [ ] D72.6 Analog hardware verification framework

**Kock-Lawvere axiom** (1981): there exists D ⊆ ℝ such that
* D = {x : ℝ | x² = 0}
* D ≠ {0}
* Every f : D → ℝ has unique linear extension f(d) = f(0) +
  f'(0) · d

**Smooth function types**: in cohesive ∞-topos, types come equipped
with smooth structure via the shape modality.

**Theorem**: synthetic differential geometry recovers classical
calculus operations in constructive setting.

**Acceptance**: SDG primitives + manifold types + ODE solutions
zero-axiom on the constructive fragment.

### Day 73 — Linear ∞-types (parallel, exploratory)

**Goal**: linear logic + cubical (Riley 2022).

**Tasks**:
* [ ] D73.1 Linear lambda + cubical
* [ ] D73.2 Riley/Atkey-Ghani primitives
* [ ] D73.3 No-cloning enforcement at type level
* [ ] D73.4 Quantum gate types as linear morphisms
* [ ] D73.5 Smoke audit linear-cubical confluence

**Riley's linear HoTT** (2022): combines Atkey-Ghani linear types
with cubical paths.

**Key constraints**:
* No-cloning enforced at type level
* Linear → unrestricted converter (! comonad)
* Cubical paths as linear-algebraic morphisms

**Theorem (Riley)**: linear HoTT is consistent + computational.

**Acceptance**: linear ∞-types operational; quantum gate types
encoded as linear morphisms.

### Day 74 — Equivariant ∞-types (parallel, exploratory)

**Goal**: G-types with action.

**Tasks**:
* [ ] D74.1 Group action on types: G ⟶ Aut(A)
* [ ] D74.2 Equivariant morphisms with computation
* [ ] D74.3 Symmetry-aware parallel algorithms
* [ ] D74.4 Smoke audit symmetric algorithms

**Definition**: G-type = type A with action α : G × A → A
satisfying:
* α(e, x) = x (identity action)
* α(g, α(h, x)) = α(g·h, x) (composition)

**Equivariant cohomology**: cohomology of G-types respecting the
action structure.

**Genuine vs naive equivariance**: genuine treats fixed points
explicitly; naive ignores them.

**Acceptance**: G-action + equivariant cohomology zero-axiom on
finite G.

### Day 75 — Synthetic Tait computability (CRITICAL)

**Goal**: Sterling 2021 PhD thesis approach.

**Tasks**:
* [ ] D75.1 Sterling-style internal Tait reducibility
* [ ] D75.2 SN proof internalized as type-theoretic construction
* [ ] D75.3 M04 SN proven INSIDE FX (not externally)
* [ ] D75.4 STRICT-33: self-reference soundness gate
* [ ] D75.5 Smoke audit self-foundationalization

**Internal Tait reducibility**:
```
Reducible_T : Term → Type → Prop
  Reducible_T t A iff:
    - t is SN
    - t reduces only to canonical forms in A
    - All "uses" of t in elimination contexts reduce
```

**Theorem (Sterling)**: synthetic Tait gives M04 SN proof
internalized as type-theoretic construction.

**Note**: this is the *internal* version of Era S Day 43's M04
proof. Era S ships externally (using Lean's metatheory); Day 75
ships internally (using FX itself as the metatheory).

**Acceptance**: SN proven inside FX; STRICT-33 green; FX bootstraps
its own metatheory.

### Day 76 — Internal parametricity at ∞ (parallel, exploratory)

**Goal**: Bernardy-Coquand-Moulin parametricity at ∞-level.

**Tasks**:
* [ ] D76.1 Bernardy-Coquand-Moulin at ∞-level
* [ ] D76.2 Free theorems for polymorphic functions automatically
* [ ] D76.3 Reflexive parametricity computation
* [ ] D76.4 Smoke audit free-theorem extraction

**Reynolds' abstraction theorem** (1983): for every polymorphic
function f : ∀ A. T(A), every relation R ⊆ A × B preserves f.

**Internal version** (Bernardy-Moulin 2010): parametricity
internalized as type-theoretic operator.

**∞-categorical version**: parametricity at every dimension.

**Acceptance**: free theorems extractable for polymorphic
functions; parametricity zero-axiom.

### Day 77 — (∞,n)-categories for general n (exploratory)

**Goal**: weak ω-categories.

**Tasks**:
* [ ] D77.1 (∞,n)-category primitives for n up to 4
* [ ] D77.2 Lurie's HTT internal language hooks
* [ ] D77.3 Coherence theorems at level n
* [ ] D77.4 Stop-criteria: ship up to n=4

**Definitions** (multiple equivalent):
* **Quasi-categories** (Joyal): simplicial sets satisfying weak Kan
* **Complete Segal spaces** (Rezk): bisimplicial sets
* **Globular operads** (Batanin): operads in globular sets

**Cobordism hypothesis** (Lurie): the cobordism (∞,n)-category is
free symmetric monoidal (∞,n)-category on one fully-dualizable
object.

**Acceptance**: (∞,n)-categories operational up to n=4; Lurie HTT
hooks zero-axiom.

### Day 78 — Era X close-out

**Goal**: ∞-frontier infrastructure operational.

**Tasks**:
* [ ] D78.1 ∞-groupoid + cohesive + linear + equivariant integrated
* [ ] D78.2 Synthetic Tait operational
* [ ] D78.3 Era X commit

**Acceptance**: FX has full ∞-type-theoretic structure; metatheory
self-foundational; cohesive + linear layers operational for physics
and quantum mechanization.

---

## Era T — Causal site explicit / temporal substrate (Day 78.5–78.9)

Site-parametric kernel + temporal cohesion + verified site catalog.
Recognizes Era I's polygraph as an implicit single-site choice;
Era T makes parametricity explicit. Term becomes
`Term : (S : CausalSite) → Ctx → Ty → RawTerm → Type`.
~5 months.

**Architectural commitment**: existing FX work re-frames as
`Term @ FX.standardSite`. New applications choose alternative
sites: dagger compact (quantum, Selinger 2007), Sorkin-Bombelli
1987 causal poset (distributed, discrete spacetime), smooth
manifold (Era XI synthetic physics), hybrid (Node × Cycle)
(FEU per Era IV.5), branching tree (LLM dialogues, game-theoretic
interactions).

**Theorem (site-parametric transfer, hypothesis-bearing)**:
```
For finitely-presented (∞,n)-category C with bounded dim n ≤ 6,
finite generators per dim, decidable cell equality, typed
source/target maps, explicit substitution/renaming actions, a
well-founded reduction measure, and local-confluence/diamond
witnesses for every critical pair, ∃ a CausalSite S such that:
  (i)   Term @ S well-formed (Burroni 1993 polygraph data)
  (ii)  typing decidable for the bounded/certificate-checked
        fragment in poly(|term|, |generators|) only when each
        supplied site decider is polynomial
  (iii) Tait-Martin-Löf parallel-reduction confluence holds
        for Term @ S when S has chosen monoidal+symmetric
        structure and the site supplies the needed parallel
        reduction constructors and joinability witnesses
  (iv)  M04 strong normalization lifts only when the site supplies a
        reducibility interpretation for every added type former and
        a proof that every added reduction decreases the chosen
        measure
  (v)   soundness theorems from Era I-XII transfer only along
        verified site morphisms whose hypotheses match the theorem.
```

**Why this Era exists**: Era I shipped a single polygraph as if it
were canonical. The Era I polygraph is a specific instance C_FX
with generators {Term ctors @ dim 0; Step ctors @ dim 1; cd_lemma
cells @ dim 2; strategy 3-cells @ dim 3 (Era I D14, MacLane
pentagon); hardware fibres @ dim 4 (Era IV); refinement functors
@ dim 5 (Era VIII); algorithm equivalences @ dim 6 (Era XII)}.
Era T makes parametricity explicit, unlocking quantum / distributed
/ hardware / physics applications via site choice rather than
site rebuild.

### Day 78.5 — CausalSite as data + site-parametric Term (CRITICAL)

**Goal**: `CausalSite` as kernel data structure + lift Term to be
parametric, with verified backwards-compatibility theorem
`Term ≅ Term @ FX.standardSite` zero-axiom at all 75 ctors.

**Construction**:
```lean
structure CausalSite where
  -- Bounded-dim truncation (FX commits to n ≤ 6 per Era I App.A)
  generators : Fin 7 → Type
  -- Decidable equality at each dim (computability requirement)
  decEqAt    : ∀ d, DecidableEq (generators d)
  -- Source/target maps to lower-dim cells
  source     : ∀ {d : Fin 6}, generators d.succ
                              → List (generators d.castSucc)
  target     : ∀ {d : Fin 6}, generators d.succ
                              → List (generators d.castSucc)
  -- Parallelism witness (Burroni 1993 Defn 1.1)
  parallel   : ∀ {d : Fin 5} (cell : generators d.succ.succ),
                ParallelAt d (source cell) (target cell)
  -- Optional structure (regime selectors)
  monoidal   : Option (MonoidalStructure generators)
                 -- ⊗ (Mac Lane 1971 §VII)
  symmetry   : Option (SymmetricStructure generators)
                 -- σ (Joyal-Street 1993 hexagon)
  dagger     : Option (DaggerStructure generators)
                 -- f† (Selinger 2007 dagger compact closed)
  choice     : Option (CoproductStructure generators)
                 -- ⊕ (categorical coproduct)
  iteration  : Option (IterationStructure generators)
                 -- f* (Kleene star, traced monoidal)
```

**FX standard site (canonical instance)**:
```lean
def FX.standardSite : CausalSite where
  generators 0 = Term ctors      -- 75 per Era V close
  generators 1 = Step ctors      -- ~120 per Era V close
  generators 2 = cd_lemma cells  -- ~120 per Era II Day 17
  generators 3 = strategy 3-cells  -- per Era I Day 14
  generators 4 = hardware fibres   -- per Era IV
  generators 5 = refinement functors  -- per Era VIII
  generators 6 = algorithm equivalences  -- per Era XII
  monoidal   = some _  -- Step.par parallelism (Tait-MLF)
  symmetry   = some _  -- σ permutation invariance
  dagger     = none    -- generally not invertible
  choice     = some _  -- if-then-else, match (Era V ι rules)
  iteration  = some _  -- recursion bounded by termination
```

**Theorem (standardSite_equiv_existing)**:
```
Term ≅ Term @ FX.standardSite
  -- bijective on all 75 ctors with rfl-equivalent typing,
  -- rename, subst, Step, cd_lemma, parStar.confluence
  -- Era II retrofit theorems all lift through this iso
```

**Tasks**:
* [ ] D78.5.1 `Foundation/Polygraph/Site.lean` — CausalSite struct
  with finitely-presented (∞,n)-polygraph data
* [ ] D78.5.2 generators (Fin 7 → Type) + decEqAt + source/target
  + parallel witness per Burroni 1993 Defn 1.1
* [ ] D78.5.3 5 optional structures with formal definitions: Mac
  Lane 1971 §VII (monoidal), Joyal-Street 1993 (symmetric), Selinger
  2007 (dagger compact closed), categorical coproduct (choice),
  Kleene-star traced monoidal (iteration)
* [ ] D78.5.4 `FX.standardSite : CausalSite` canonical instance
* [ ] D78.5.5 `Term @ S` site-parametric definition with rename/subst
  inheriting from S's structure (when monoidal: ⊗-aware subst; when
  dagger: †-coherent subst)
* [ ] D78.5.6 Equivalence `Term ≅ Term @ FX.standardSite` zero-axiom
  at all 75 ctors (Era II retrofit theorems lift through iso)
* [ ] D78.5.7 STRICT-45-T-Site: CausalSite well-formedness gate
  (parallelism witnesses + structure-flag coherence)
* [ ] D78.5.8 Smoke audit + commit

**References**: Burroni 1993 (polygraphs); Métayer 2008
(cofibrant objects); Mac Lane 1971 (Categories for the Working
Mathematician, §VII monoidal); Joyal-Street 1993 (braided); Selinger
2007 (dagger compact); Bénabou 1967 (bicategories); Schultz-Spivak-
Vasilakopoulou 2017 (temporal type theory in topos of sheaves).

**Acceptance**: CausalSite + site-parametric Term + standardSite
equivalence ship zero-axiom; existing FX continues unchanged;
applications can choose alternative sites.

### Day 78.6 — Site morphisms verified (CRITICAL)

**Goal**: site morphisms as functors with explicit soundness
conditions; verified compilation = site morphism (CompCert-style
generalizing per Leroy 2009).

**Construction**:
```lean
structure SiteMorphism (S T : CausalSite) where
  on_gen   : ∀ d, S.generators d → T.generators d
  -- Functoriality: source/target preservation
  on_src   : ∀ {d} c, on_gen d (S.source c)
                       = T.source (on_gen _ c)
  on_tgt   : ∀ {d} c, on_gen d (S.target c)
                       = T.target (on_gen _ c)
  -- Structure preservation (when both sides have it)
  on_monoidal : S.monoidal = some _ → T.monoidal = some _ →
                preserves_⊗
  on_symmetry : S.symmetry = some _ → T.symmetry = some _ →
                preserves_σ
  on_dagger   : S.dagger = some _ → T.dagger = some _ →
                preserves_†
  ...
```

**Standard morphisms with soundness conditions**:
```
discretize : ContinuousTimeSite → DiscreteTimeSite
  (Yee 1966 leapfrog FDTD)
  Soundness: Courant Δt ≤ Δx/(c√3) for 3D stability
  Convergence: O((Δx)² + (Δt)²) per Yee 1966; Taflove-Hagness 2005

parallelize : SequentialSite → MonoidalSite
  (introduces ⊗ for independent ops)
  Soundness: dependency analysis (no read-after-write conflict);
             observational equivalence preserved on closed terms

dualize : Site → Site†
  (dagger reversal for quantum)
  Soundness: involutive, dualize ∘ dualize = id;
             requires Site.dagger = some _;
             preserves † by construction (Selinger 2007)

cyclify : LinearTimeSite → CyclicSite
  (introduces Kleene-star *)
  Soundness: termination measure on iterated rewrites;
             total termination preserved on bounded inputs

branch : SequentialSite → TreeSite
  (introduces ⊕ at branching nodes)
  Soundness: choice independence; left/right branches commute
             with subsequent operations (categorical coproduct
             coherence)

abstract_n_to_n+1 : Site_Level_n → Site_Level_{n+1}
  -- Era IV.5 abstraction functors are specific instances:
  --   F_Maxwell→RLC : Polygraph_EM → Polygraph_RLC
  --     (Day 31.5 quasi-static condition)
  --   F_RLC→STA : Polygraph_RLC → Polygraph_STA
  --     (Day 31.6 settling-time condition)
  --   F_STA→Digital : Polygraph_STA → Polygraph_Digital
  --     (Day 31.7 timing-closure condition)
  --   F_Dig→μArch : Polygraph_Digital → Polygraph_μArch
  --     (Day 31.8 pipeline-correctness condition)
```

**Theorem (site morphism soundness, general)**:
```
For verified F : SiteMorphism S T satisfying its soundness
condition cond_F, and t : Term @ S,
  observation_equivalence_S→T (eval_in S t)
                              (eval_in T (F.transport t))

with observation_equivalence_S→T = the appropriate equivalence
relation: strict iso for strict monoidal F, bisimulation for
symmetric F, observational eq on closed terms for general F.
```

**Design theorem (CompCert-style compilation as site morphism, Leroy
2009 generalized, for represented compiler passes)**:
```
Verified compiler from program in Term @ SourceSite to binary in
Term @ TargetSite is represented as a verified site morphism plus a
soundness witness, when the pass preserves the site structure:
  Compiler(SourceSite, TargetSite)
    := SiteMorphism SourceSite TargetSite
       with soundness_cond = "semantic preservation"

Cross-architecture equivalence (Era IV D31.3 "CPU vs B200 vs FPGA
produce same NF") is the naturality square:
  source_program ──Compiler_CPU──→ binary_CPU
       │                              │
   Source-id                       interpret_CPU
       ↓                              ↓
  source_program ──Compiler_B200──→ binary_B200 ──interpret_B200──→ result
       ↓                              ↓
   Source-id                       interpret_FPGA
       ...
  All Compiler_X ∘ source-program ≡ result on observables.
```

**Tasks**:
* [ ] D78.6.1 `Foundation/Polygraph/SiteMorphism.lean`
* [ ] D78.6.2 SiteMorphism struct with functoriality (on_src/on_tgt)
  + structure preservation per optional flag combinations
* [ ] D78.6.3 discretize with Courant condition Δt ≤ Δx/(c√3) and
  Yee 1966 O((Δx)² + (Δt)²) convergence; FDTD specialization
* [ ] D78.6.4 parallelize with dependency-graph analysis;
  observational eq preservation
* [ ] D78.6.5 dualize as dagger involution; verified
  dualize ∘ dualize = id_Site
* [ ] D78.6.6 cyclify with termination measure (well-founded
  on iteration count)
* [ ] D78.6.7 branch with choice-independence per coproduct
  coherence
* [ ] D78.6.8 abstract_n_to_n+1 instances (Era IV.5 functors
  F_M→RLC, F_RLC→STA, F_STA→Dig, F_Dig→μA all become
  abstract_n_to_n+1 with specific cond_F)
* [ ] D78.6.9 CompCert-style corollary specializing Leroy 2009
  to the SiteMorphism framework
* [ ] D78.6.10 STRICT-46-T-Morphism gate (verifies functoriality
  + structure preservation + soundness witness)
* [ ] D78.6.11 Smoke audit + commit

**References**: Yee 1966 (FDTD); Taflove-Hagness 2005 (FDTD
electrodynamics); Selinger 2007 (dagger compact); Leroy 2009
(CompCert formal verification CACM); Lurie HTT 2009 (∞-functor
framework); Mac Lane 1971; Bénabou 1967.

**Acceptance**: 6 standard site morphisms + CompCert corollary
ship zero-axiom; cross-site translation operational; Era IV.5
abstraction functors retroactively recognized as instances.

### Day 78.7 — Temporal cohesion ◯ ⊣ ▷ ⊣ ⟐ ⊣ ℑ (CRITICAL)

**Goal**: temporal modal layer parallel to spatial cohesion
(Schreiber 2013 ♭ ⊣ ◇ ⊣ □ ⊣ ♯), giving 8-modality spacetime
cohesion when combined.

**Construction (temporal cohesion adjoint chain)**:
```
For chosen temporal site T (e.g., (ℕ, ≤) discrete linear time):

ℑ : Type → Type     -- timeless extraction (forget time;
                       presheaf colimit over T)
⟐ : Type → Type     -- have-been (past view; presheaf left-Kan
                       extension along ℑ)
▷ : Type → Type     -- next (Nakano 2000 later;
                       presheaf right-Kan extension)
◯ : Type → Type     -- always (constant in time;
                       presheaf right-Kan extension along ℑ)

Adjunctions (Mac Lane 1971 §IV.1):
  ◯ ⊣ ▷    ◯ left-adjoint to ▷ ("always implies next")
  ▷ ⊣ ⟐    ▷ left-adjoint to ⟐ ("next implies have-been")
  ⟐ ⊣ ℑ    ⟐ left-adjoint to ℑ ("past implies timeless")

Triangle identities for each (η, ε) pair:
  (ε_◯ ▷ A) ∘ (◯ η_▷ A) = id_◯A
  (▷ ε_◯ A) ∘ (η_▷ ◯ A) = id_▷A
  ... (similar for ▷ ⊣ ⟐ and ⟐ ⊣ ℑ)

Naturality squares for unit/counit per Mac Lane 1971 §IV.1.
```

**Spacetime cohesion (combined 8-modality)**:
```
Spatial cohesion (Schreiber 2013, applied at Era IV Day 4.5):
  ♭  ⊣  ◇  ⊣  □  ⊣  ♯

Temporal cohesion (this Day):
  ◯  ⊣  ▷  ⊣  ⟐  ⊣  ℑ

Spacetime cohesion (composition):
  ♭◯  ⊣  ◇▷  ⊣  □⟐  ⊣  ♯ℑ
  -- e.g., ♭◯ A := "discrete time-invariant projection of A";
  --       ♯ℑ A := "codiscrete eternal extension of A"

Compatibility theorem: spatial and temporal cohesion modalities
COMMUTE on the doubly-cohesive ∞-topos (Schreiber 2013 differential
cohesion adapted; Bahr-Graulund-Møgelberg 2019 ICFP for discrete
case).
```

**Theorem (◯ characterizes pure / time-invariant)**:
```
∀ (f : A → B),
  f ∈ ◯ (A → B)  ⟺  f is Tot (no Effect, no IO, no Async)
                    ⟺  f is a global section of constant sheaf
                       Δ_◯(A → B) on temporal site T
                    ⟺  f's behavior is time-invariant
```

**Theorem (◇ characterizes effectful / time-dependent)**:
```
∀ (f : A → B with E),
  E ≠ Tot  ⟺  f ∈ ◇ (A → B)
            ⟺  f's meaning depends on temporal site state
            ⟺  f acts as a time-dependent natural transformation
               between presheaves on T

Effects ARE the witnesses of time-dependence: each effect type
(IO, Read, Write, Async) corresponds to a class of witnesses for
how time evolves through the operation.
```

**Tasks**:
* [ ] D78.7.1 `Foundation/Modal/TemporalCohesion.lean`
* [ ] D78.7.2 ℑ (timeless), ⟐ (have-been), ▷ (Nakano later, lifted
  from Era IV Day 4.7.2), ◯ (always) as kernel modalities;
  presheaf-theoretic semantics on chosen temporal site T
* [ ] D78.7.3 Adjunctions ◯ ⊣ ▷ ⊣ ⟐ ⊣ ℑ with verified triangle
  identities (Mac Lane 1971 §IV.1)
* [ ] D78.7.4 Naturality squares for (η_◯⊣▷, ε_◯⊣▷),
  (η_▷⊣⟐, ε_▷⊣⟐), (η_⟐⊣ℑ, ε_⟐⊣ℑ)
* [ ] D78.7.5 Composition with spatial cohesion (♭⊣◇⊣□⊣♯) →
  8-modality spacetime cohesion (♭◯ ⊣ ◇▷ ⊣ □⟐ ⊣ ♯ℑ)
* [ ] D78.7.6 Spatial-temporal commutativity theorem (Schreiber-
  Shulman 2014 differential cohesive adapted)
* [ ] D78.7.7 ◯-characterizes-Tot theorem (pure functions ≅ ◯-fixed)
* [ ] D78.7.8 ◇-characterizes-effectful theorem (effects ≅ ◇-mobile
  natural transformations)
* [ ] D78.7.9 STRICT-46-T-Cohesion gate
* [ ] D78.7.10 Smoke audit + commit

**References**: Nakano 2000 (later modality, LICS); Schreiber 2013
(Differential cohomology in a cohesive ∞-topos); Schreiber-Shulman
2014 (Quantum gauge field theory in cohesive HoTT); Bahr-Graulund-
Møgelberg 2019 (Adjoint logic for FRP, ICFP); Birkedal-Mogelberg-
Schwinghammer-Stovring 2013 (Synthetic guarded domain theory,
LICS); Schultz-Spivak-Vasilakopoulou 2017 (Dynamical systems and
sheaves).

**Acceptance**: temporal cohesion zero-axiom; 8-modality spacetime
cohesion operational; pure/effectful characterization theorems
ship; FX has full spatial + temporal modal infrastructure.

### Day 78.8 — Time-invariance modality + site catalog (CRITICAL)

**Goal**: Eternal/Temporal kind distinction + 10-instance pre-built
site catalog with verified well-formedness per instance.

**Construction (Eternal/Temporal kind)**:
```lean
inductive Kind where
  | Eternal   -- time-invariant; ◯-fixed point
  | Temporal  -- time-dependent; ◇-mobile

def Type@Kind : Kind → Type → Type
  | .Eternal,  A => ◯ A          -- constant sheaf over T
  | .Temporal, A => Σ (w : World), A   -- world-indexed (per Era W
                                          if landed)

def liftEternalToTemporal {A} : Type@Eternal A → Type@Temporal A
  -- pure values lift trivially as constant time-invariant sections

def restrictTemporalToEternal {A} :
  Type@Temporal A → Option (Type@Eternal A)
  -- only when ∀ w, value(w) = value(w') for all w, w'
  -- (witnessed by ◯-fixed-point check)
```

**Site catalog (10 verified instances)**:
```
sequential_N : CausalSite
  -- Objects: ℕ
  -- Hom n m: if n ≤ m then unit else empty
  -- 1-cell: tick : Hom n (n+1)
  -- monoidal: none; symmetric: none; iteration: some (ℕ-recursion)
  -- Verified: decidable order, finite presentation per
  --           prefix-length truncation

sequential_R : CausalSite
  -- Objects: ℝ
  -- Hom t s: if t ≤ s then unit else empty
  -- Truncation to (ℕ Δt) for finitely-presented prefix per chosen
  --   sampling rate Δt; infinitely-deep but well-defined
  -- Bridge to sequential_N via discretize site morphism

parallel_monoidal : CausalSite
  -- Objects: lists of resource types
  -- Hom: transitions between resource configurations
  -- monoidal: some (⊗ = independent resources)
  -- symmetric: some (σ = resource-order-independent)
  -- π-calculus / CSP semantics adapted

branching_tree : CausalSite
  -- Objects: tree nodes T
  -- Hom n m: unique path from n to m if exists else empty
  -- choice: some (⊕ at each branching node)
  -- Used for game-theoretic / dialogue / LLM-conversation
  --   modeling

dagger_compact : CausalSite
  -- Objects: finite-dim Hilbert spaces (formal duals)
  -- Hom: linear maps; tensor product; dual; identity
  -- monoidal: some (⊗); symmetric: some (σ); dagger: some (†)
  -- compact-closed structure per Selinger 2007
  -- ZX-calculus (Coecke-Duncan POPL 2008) is a sub-instance

causal_poset : CausalSite
  -- Objects: discrete poset P (Sorkin causal set)
  -- Hom: ≤ relation in P; binary
  -- Source-target structure: a ≤ b ⟺ ∃ unique 1-cell a → b
  -- Sorkin-Bombelli 1987 discrete spacetime; Henson 2009
  -- Models: Lamport-style distributed logical time; quantum
  --         gravity foundations

hybrid_clock : CausalSite
  -- Objects: (cycle_count : ℕ, wallclock : ℝ⁺) lex-ordered
  -- Hom: (n₁, t₁) ≤ (n₂, t₂) iff n₁ ≤ n₂ ∧ t₁ ≤ t₂
  -- monoidal: none
  -- Models: real-time hardware (FEU per Era IV.5)

smooth_manifold : CausalSite
  -- Objects: smooth manifold M (per Era XI synthetic physics)
  -- Hom: smooth maps; tangent vectors as 1-cells
  -- monoidal: some (⊗ when bundle structure)
  -- Requires SDG (Era X Day 72)
  -- Models: classical mechanics, gauge theory, GR

asymptotic_BigO : CausalSite
  -- Objects: cost classes (BigO equivalence classes)
  -- Hom: O(f) ≤ O(g) preorder
  -- Poset-enriched commutative monoid (per Era XII Day 89)
  -- Models: algorithm-equivalence space; cross-complexity-class
  --         search

FEU_hardware : CausalSite
  -- Objects: SpacetimePoint = (Node, Cycle) per FEU v5 285 tiles
  -- Hom: wire delays, register clock edges, pipeline transitions
  -- monoidal: some (⊗ = independent columns / tiles)
  -- choice: some (⊕ = mux selectors at gates)
  -- 7-level fractal structure: 3⁷ = 2187 atoms per tile
  -- Direct integration with FEU-FX vertical (see verticals
  -- section below)
```

**Tasks**:
* [ ] D78.8.1 `Foundation/Modal/TimeInvariance.lean` — Kind enum
  + Type@Kind type former
* [ ] D78.8.2 liftEternalToTemporal + restrictTemporalToEternal
  with ◯-fixed-point verification
* [ ] D78.8.3 Bridge: pure FX functions (Tot effect) ≅ Eternal-kind
* [ ] D78.8.4 `Foundation/Polygraph/SiteCatalog.lean`
* [ ] D78.8.5 sequential_N : (ℕ, ≤) with tick generator
* [ ] D78.8.6 sequential_R : (ℝ, ≤) with FDTD-style truncation
* [ ] D78.8.7 parallel_monoidal with π-calculus / CSP semantics
* [ ] D78.8.8 branching_tree for game / dialogue / LLM
* [ ] D78.8.9 dagger_compact (Selinger 2007 + ZX subgenerator)
* [ ] D78.8.10 causal_poset (Sorkin-Bombelli 1987)
* [ ] D78.8.11 hybrid_clock for real-time hardware
* [ ] D78.8.12 smooth_manifold (depends on Era X Day 72 SDG)
* [ ] D78.8.13 asymptotic_BigO (poset-enriched commutative monoid)
* [ ] D78.8.14 FEU_hardware (3⁷ fractal, links to Era IV.5 + FEU-FX
  vertical)
* [ ] D78.8.15 Per-instance well-formedness verification (decEq,
  finite presentation, structural axioms) zero-axiom
* [ ] D78.8.16 STRICT-47-T-Catalog gate (per-instance audit)
* [ ] D78.8.17 Smoke + commit

**References**: Sorkin-Bombelli 1987 (causal sets, Phys. Rev.
Lett.); Henson 2009 (causal sets, Quantum Gravity Handbook);
Selinger 2007 (dagger compact); Coecke-Duncan 2008 (ZX-calculus,
POPL); Schreiber 2013 (cohesive ∞-topos); Era XII §28-29.

**Acceptance**: time-invariance modality + 10 site instances ship
zero-axiom; users choose site without rebuilding kernel; cross-
catalog morphisms verified where applicable.

### Day 78.9 — Era T close-out + cross-Era integration (CRITICAL)

**Goal**: full causal-site-explicit + temporal substrate
operational; existing Eras retroactively unified under the
parametric framework.

**Cross-Era reframings** (existing theorems lift through Term ≅
Term @ standardSite, then parameterize over alternative sites):

```
Era VII (WMM) reframes as 4-instance × 4-morphism diamond:
  TSO_site (x86-64): release-acquire monotonicity
  ARM_site:           weaker ordering with explicit dmb fences
                      (per ARM ARM v8 spec)
  RISCV_site:         relaxed with explicit fence ops
                      (per RVWMO formal model)
  GPU_site:           NVIDIA / AMD relaxed memory model
  Cross-arch obs eq (D31.3) becomes 4-way naturality square:
    program ──CompTSO──→ x86-bin
       │                    │
   prog-id              interpret_TSO
       ↓                    ↓
    program ──CompARM──→ ARM-bin ──interpret_ARM──→ result
       ↓                    ↓
   prog-id              interpret_RVWMO
       ...
  CompCert-TSO (Sevcik 2009) lifts as instance.

Era IV.5 multi-level reframes as site-stratification:
  Polygraph_EM      = smooth_manifold ⊗ (sequential_R)
  Polygraph_RLC     = lumped_finite_node ⊗ sequential_R
  Polygraph_STA     = lumped_finite_node ⊗ sequential_R⁺_event
  Polygraph_Digital = FEU_hardware (or x86_arch_hardware)
  Polygraph_μArch   = pipeline_aggregate(Digital)
  Each F_·→· = abstract_n_to_n+1 site morphism instance.

Era XI (synthetic physics) reframes as Term @ smooth_manifold:
  Pontrjagin-Thom theorem (Day 80)
  Hopf-tom Dieck (Day 80)
  Sati-Schreiber main theorem (Day 86, Hypothesis H)
  All live in Term @ smooth_manifold (with Era X Day 72 SDG
    providing the smooth structure).

Era XII (algorithm discovery) reframes as Term @ asymptotic_BigO:
  + multi-die ternary cube (FEU 27-die per FEU-FX vertical) as
    27-instance site distribution for parallel proof-strategy
    search; each die runs in a distinct Term @ S_i where S_i
    differs in 3-cell strategy choice.

Era IV.5 + Era T integration: spacetime-typed primitives
  (Charge, Wire, Register, Instruction at Day 31.7) are sections
  of fibrations over FEU_hardware site. Conservation laws
  (Kirchhoff, pipeline-linearity) are Noether instances on
  FEU_hardware's symmetries.
```

**Headline theorem (parametric polygraph foundation, bounded
transfer form)**:
```
For finitely-presented site S with bounded dim n ≤ 6, decidable
cell equality, finite generators per dim, typed source/target maps,
substitution/renaming actions, well-founded reduction measure,
critical-pair joinability witnesses, and chosen optional structure
(monoidal/symmetric/dagger/choice/iteration) flags:
  (a) Term @ S is well-formed (Burroni 1993)
  (b) typing decidable for the bounded/certificate-checked fragment
      when every site judgment has a total checker
  (c) reduction confluent when the supplied parallel-reduction and
      critical-pair witnesses cover every reduction family
  (d) M04 strong normalization holds only when the site supplies the
      Era S reducibility interpretation and decrease proof for all
      added reductions
  (e) each soundness theorem from Era I-XII transfers only through
      a verified site morphism that proves that theorem's required
      hypotheses.
```

**Tasks**:
* [ ] D78.9.1 Comprehensive smoke audit Era T
* [ ] D78.9.2 Era VII WMM reframed as 4-site instance × 4-morphism
  diamond; CompCert-TSO Sevcik 2009 lifts as specific instance
* [ ] D78.9.3 Era IV.5 multi-level reframed as site-stratification
  with abstract_n_to_n+1 morphism instances
* [ ] D78.9.4 Era XI synthetic physics reframed as
  `Term @ smooth_manifold` (depends on Era X Day 72 SDG)
* [ ] D78.9.5 Era XII algorithm discovery reframed as
  `Term @ asymptotic_BigO` + 27-die parallel-strategy distribution
  (links to FEU-FX vertical)
* [ ] D78.9.6 Era IV.5 spacetime-typed primitives recognized as
  sections of fibrations over FEU_hardware site; Kirchhoff +
  pipeline-linearity = Noether instances
* [ ] D78.9.7 STRICT-48-T-Coverage gate: all Era reframings cover
  the existing theorem inventory
* [ ] D78.9.8 Era T commit + status

**References**: Burroni 1993; Geuvers 1992 (CC βη-CR); Sevcik 2009
(CompCert-TSO PhD thesis); Schultz-Spivak-Vasilakopoulou 2017
(temporal type theory); Mac Lane 1971; Schreiber 2013.

**Acceptance**: Era T complete; site-parametric kernel operational;
cross-Era unification under parametric framework verified;
multiple downstream applications enabled (quantum, distributed,
hardware, physics, LLM dialogue, algorithm discovery) all
expressible as Term @ specific_site instances.

---

## Era XI — Synthetic physical mechanization (Day 79–88)

`fx-mtheory` library: formal physics-model mechanization and search.
The rigorous target is computational: encode explicit mathematical
models, prove theorems inside those models, and run bounded search for
model refinements that reproduce known equations/observables. This
does not claim that M-theory or any candidate model is the physical
world; it creates a zero-axiom framework where such claims become
finite hypotheses, derivations, and checked comparison certificates.
~10 months for the initial formal-model slice.

### Day 79 — Cohomology theory types (CRITICAL)

**Goal**: mapping space types as kernel primitives.

**Tasks**:
* [ ] D79.1 Cohomotopy π^n(X) as type
* [ ] D79.2 Equivariant cohomotopy π_G^n(X)
* [ ] D79.3 K-theory classifying spaces
* [ ] D79.4 Cobordism types (MO, MU, MString)
* [ ] D79.5 Eilenberg-MacLane K(A, n) HITs

**Cohomotopy**: π^n(X) := [X, S^n]_*

In HoTT/cubical: `Cohomotopy(X, n) := X →* S^n / homotopy`

**Equivariant cohomotopy**: π_G^n(X) := G-equivariant pointed maps.

**Acceptance**: cohomotopy + K-theory + cobordism + EM HITs zero-
axiom on the constructive fragment.

### Day 80 — Foundational topology theorems (CRITICAL)

**Goal**: Pontrjagin-Thom + Hopf-tom Dieck + Boardman.

**Tasks**:
* [ ] D80.1 Pontrjagin-Thom theorem
* [ ] D80.2 Hopf degree theorem
* [ ] D80.3 Equivariant Hopf-tom Dieck theorem
* [ ] D80.4 Boardman homomorphism

**Pontrjagin-Thom theorem**: stable cohomotopy ≃ framed bordism.

**Hopf degree theorem** (1926): π_n(S^n) = ℤ.

**Equivariant Hopf-tom Dieck** (1979): π_G^n(S^n) ≃ A(G) where
A(G) is the Burnside ring.

**Acceptance**: foundational topology theorems zero-axiom on the
fragment ABCFHL cubical TT can prove.

### Day 81 — Burnside ring + representation rings (CRITICAL)

**Goal**: A(G) and RO(G) as semiring types with verified laws +
GEMM-encoding for B200.

**Tasks**:
* [ ] D81.1 A(G) Burnside ring as semiring type
* [ ] D81.2 RO(G) representation ring as semiring type
* [ ] D81.3 Decidability + verified semiring laws
* [ ] D81.4 GEMM-encoding for B200 batched evaluation

**Burnside ring A(G)** (Burnside 1911):
* Elements: ℤ-linear combinations of finite G-sets
* Addition: disjoint union
* Multiplication: Cartesian product
* Rank: number of conjugacy classes of subgroups

**Representation ring RO(G)**:
* Elements: virtual G-representations
* Addition: direct sum
* Multiplication: tensor product

**Mark homomorphism**: A(G) → ℤ × ... × ℤ (one ℤ per conjugacy
class of subgroup) is injective; image determined by congruence
conditions.

**Acceptance**: A(G), RO(G) semirings + mark homomorphism + B200
GEMM-encoding zero-axiom.

### Day 82 — Differential cohomotopy (parallel)

**Goal**: differential refinement of cohomotopy.

**Tasks**:
* [ ] D82.1 Twisted cohomotopy with local coefficient systems
* [ ] D82.2 Differential cohomotopy with connections
* [ ] D82.3 Curvature + connection types
* [ ] D82.4 Smoke audit differential structures

**Twisted cohomotopy**: cohomotopy with local coefficient systems.

**Differential cohomotopy**: π̂^n(X) combines π^n with connections.

**Acceptance**: differential structure types + connection types
zero-axiom.

### Day 83 — Orbifold types (CRITICAL)

**Goal**: quotient HITs.

**Tasks**:
* [ ] D83.1 Quotient HITs T^n / G for finite G
* [ ] D83.2 ADE-type singularity catalog
* [ ] D83.3 Crystallographic point group types
* [ ] D83.4 Smoke audit orbifold structures

**Orbifold T^n / G**: quotient of n-torus by finite group action.

**ADE classification** (Coxeter): finite subgroups of SU(2) (binary
polyhedral groups):
* A_n: cyclic Z_{n+1}
* D_n: dihedral
* E_6, E_7, E_8: exceptional

**Acceptance**: orbifold quotient HITs + ADE catalog zero-axiom.

### Day 84 — Brane charge types (CRITICAL)

**Goal**: D-brane charges in equivariant cohomotopy (Hypothesis H).

**Tasks**:
* [ ] D84.1 D-brane charge as equivariant cohomotopy
* [ ] D84.2 O-plane charge as Burnside ring element
* [ ] D84.3 M-brane / MO-plane charges
* [ ] D84.4 Charge quantization decidability

**Hypothesis H** (Sati-Schreiber 2019): the M-theory C-field is
charge-quantized in unstable equivariant Cohomotopy.

**Acceptance**: brane charge types + quantization decidability
zero-axiom.

### Day 85 — Tadpole + anomaly cancellation predicates (CRITICAL)

**Goal**: decidable Props for cancellation conditions.

**Tasks**:
* [ ] D85.1 Local/twisted tadpole cancellation as decidable Prop
* [ ] D85.2 Global/untwisted tadpole cancellation
* [ ] D85.3 M5/MO5 anomaly cancellation
* [ ] D85.4 Smoke audit cancellation conditions

**Local/twisted tadpole cancellation**: D-brane charge as
combination of regular + trivial G-representations.

**Global/untwisted tadpole cancellation**: dim(D-brane charge) =
card(O-plane G-set).

**Acceptance**: tadpole + anomaly cancellation predicates
decidable + zero-axiom.

### Day 86 — Sati-Schreiber theorem inside explicit model (CRITICAL)

**Goal**: mechanization of the headline theorem.

**Tasks**:
* [ ] D86.1 `equivariant_cohomotopy_implies_tadpole_cancellation`
  theorem in FX
* [ ] D86.2 Proof via Hopf-tom Dieck + Boardman
* [ ] D86.3 Verification on Tables 1 + 2 from the paper
* [ ] D86.4 Smoke audit theorem zero-axiom

**Model theorem**: in the explicitly encoded Sati-Schreiber
hypothesis/model fragment, brane charge quantization in unstable
equivariant Cohomotopy implies the encoded tadpole cancellation
conditions.

**Proof structure**:
1. Apply unstable equivariant Hopf-tom Dieck.
2. Lift via super-differential cohomology.
3. Use unstable Pontrjagin-Thom to identify brane configurations.
4. Apply Boardman homomorphism for D-brane Chan-Paton charges.

**Acceptance**: the encoded theorem is proven zero-axiom relative to
the explicit model data. Any claim that the encoded model matches
physical M-theory is outside the kernel theorem and belongs to the
model-comparison/search layer.

### Day 87 — Case-by-case Table 1 mechanization (CRITICAL)

**Goal**: mechanize each row of Sati-Schreiber Table 1.

**Tasks**:
* [ ] D87.1 D5/D9-branes on T^4 // Z2 (BST99)
* [ ] D87.2 D4-branes on T^4 // Zk (AFIRU00a)
* [ ] D87.3 D3/D7/D8-branes — full table coverage
* [ ] D87.4 Each row mechanically derives stated tadpole condition

**Examples**:
* D5/D9-branes on T^4 / Z_2: tadpole condition c = 16 · 2_reg
* D4-branes on T^4 / Z_3: c = 4 · 3_reg + 4 · 1_triv
* ... (see paper).

**Acceptance**: each Table 1 row mechanically derives the stated
tadpole condition zero-axiom.

### Day 88 — Era XI close-out (CRITICAL)

**Goal**: fx-mtheory v0.1 release.

**Tasks**:
* [ ] D88.1 fx-mtheory v0.1 release
* [ ] D88.2 Performance: full Sati-Schreiber paper verifiable in
  <1 hour on B200 cluster
* [ ] D88.3 Academic paper draft on the mechanization
* [ ] D88.4 Era XI commit

**Acceptance**: first kernel-verified mechanization of an explicit
M-theory-inspired formal model fragment, plus comparison artifacts
against known equations/tables. Physical adequacy remains a search
and validation program, not an assumed premise.

---

## Era R — Reflection layer (Day 88.5–88.9)

Layer Ω part 1: make FX's internal `Term` / `Type` / `Step` /
`HasType` derivation structures into FX-typed values. Quote/Splice/
Reify primitives. Tactics-as-reflective-programs replacing Era VI's
ad-hoc kernel β-rules. Self-hosting infrastructure. ~6 months.

**Architectural commitment**: the kernel exposes its internal data
structures as kernel-typed values via reflective universes
`ReflTerm`, `ReflTy`, `ReflDerivation`. Programs gain the ability
to manipulate FX programs as data — what Lean 4 (`Lean.Expr` +
`MetaM`), Idris 2 (`Elab Reflection`), Coq (`Ltac2`, MetaCoq) all
provide. Reflection unlocks: DSLs, tactic frameworks, macros,
verified compilers in FX, FX-in-FX bootstrap.

**Theorem (reflection roundtrip, headline)**:
```
∀ (t : Term ctx ty raw),
  ReflTerm.elaborate (Term.reify t) = .ok ⟨ctx, ty, raw, t⟩

  -- Reify is total; elaborate is partial (may produce ElabError);
  -- but on input that came from reify, elaborate succeeds and
  -- recovers the exact same term up to definitional equality.
```

**Theorem (Lean-style metaprogramming sound)**:
```
For tactic programs τ : ReflTerm → ReflTerm in the Tactic monad
(Day 88.8), and goal G : Term ctx ty raw with reify_goal(G) = R,
  τ R = .ok R'  ⟹  ∃ G' : Term ctx ty raw,
                    elaborate R' = .ok ⟨_, _, _, G'⟩
                    ∧ G' is a valid proof of the original goal.
  -- Successful tactic produces a verified Term; no axiom-leak.
```

**Why this Era exists** (vs Era VI auto-proof): Era VI shipped
tactics as kernel β-rules baked in (decide, omega, ring, polyrith
as `Step.tactic_*` ctors). Era R generalizes: tactics become
*reflective programs* manipulating `ReflTerm` data. Era VI's
specific tactics become specializations of the Era R framework;
new tactics ship as user code without kernel modification.

### Day 88.5 — ReflTerm + Term.reify primitive (CRITICAL)

**Goal**: ship `ReflTerm` as inductive mirroring `Term` ctors +
`Term.reify` primitive + `ReflTerm.elaborate` partial inverse +
verified roundtrip theorem at all 75 Term ctors.

**Construction**:
```lean
-- Mirrors all 75 Term ctors with explicit ctx / ty / raw indices
-- collapsed to data fields (the indexed types are recovered at
-- elaborate time via re-typechecking).
inductive ReflTerm where
  | var       (idx : Nat)
  | app       (f arg : ReflTerm)
  | lam       (body : ReflTerm)
  | lamPi     (body : ReflTerm)
  | appPi     (f arg : ReflTerm)
  | pair      (a b : ReflTerm)
  | fst       (p : ReflTerm)
  | snd       (p : ReflTerm)
  | natZero
  | natSucc   (n : ReflTerm)
  | natElim   (motive z s : ReflTerm) (n : ReflTerm)
  | natRec    (motive z s : ReflTerm) (n : ReflTerm)
  | listNil
  | listCons  (h t : ReflTerm)
  | listElim  (motive z s : ReflTerm) (xs : ReflTerm)
  | optionNone
  | optionSome (v : ReflTerm)
  | optionMatch (motive n s : ReflTerm) (o : ReflTerm)
  | eitherInl (v : ReflTerm) | eitherInr (v : ReflTerm)
  | eitherMatch (motive l r : ReflTerm) (e : ReflTerm)
  | boolElim  (motive t f : ReflTerm) (b : ReflTerm)
  | boolTrue | boolFalse
  | refl      (a : ReflTerm)
  | idJ       (motive base : ReflTerm) (a b p : ReflTerm)
  | oeqRefl   (a : ReflTerm)
  | oeqJ      (motive base : ReflTerm) (a b p : ReflTerm)
  | idStrictRefl (a : ReflTerm)
  | idStrictRec (motive base : ReflTerm) (a b p : ReflTerm)
  | pathLam   (body : ReflTerm)
  | pathApp   (p i : ReflTerm)
  | transp    (path src : ReflTerm)
  | hcomp     (sides cap : ReflTerm)
  | glueIntro (b sides : ReflTerm)
  | glueElim  (g : ReflTerm)
  | uaToEquiv (e : ReflTerm) | equivApply (e a : ReflTerm)
  | equivIntroHet (f g h : ReflTerm) | uaIntroHet (...) | funextIntroHet (...)
  | recordIntro (fields : List ReflTerm)
  | recordProj (r : ReflTerm) (k : Nat)
  | refineIntro (v p : ReflTerm) | refineElim (r : ReflTerm)
  | codataUnfold (head tail : ReflTerm)
  | codataDest (c : ReflTerm)
  | sessionSend (ch v : ReflTerm) | sessionRecv (ch : ReflTerm)
  | modIntro (modality : ReflModality) (inner : ReflTerm)
  | modElim  (m : ReflTerm)
  | subsume  (m : ReflTerm) (modality_target : ReflModality)
  | cumulUp  (level_low level_high : ReflLevel) (inner : ReflTerm)
  | universeCode (lvl : ReflLevel)
  | arrowCode (a b : ReflTerm) | piTyCode (a b : ReflTerm)
  | sigmaTyCode (a b : ReflTerm) | productCode (a b : ReflTerm)
  | sumCode (a b : ReflTerm) | listCode (a : ReflTerm)
  | optionCode (a : ReflTerm) | eitherCode (a b : ReflTerm)
  | idCode (a x y : ReflTerm) | equivCode (a b : ReflTerm)
  | interval0 | interval1 | intervalOpp (i : ReflTerm)
  | intervalMeet (i j : ReflTerm) | intervalJoin (i j : ReflTerm)
  | equivReflId | funextRefl | equivReflIdAtId | funextReflAtId
  | uaToEquivOfEqType | transpReflBeta
```

**Theorems**:
```lean
def Term.reify {ctx ty raw} : Term ctx ty raw → ReflTerm
  -- structural recursion over Term ctors (75 cases)
  -- proves: Term.reify t.toRaw = (Term.reify t).toRawForm
  -- (commutes with raw projection)

def ReflTerm.elaborate (e : ReflTerm)
  : Either ElabError (Σ ctx ty raw, Term ctx ty raw)
  -- partial: may fail with type-mismatch, scope-error, etc.
  -- produces: typed Term + its ctx/ty/raw indices reconstructed

theorem Term.reify_elaborate_roundtrip
    {ctx ty raw} (t : Term ctx ty raw) :
  ReflTerm.elaborate (Term.reify t) = .ok ⟨ctx, ty, raw, t⟩
  -- proof: case analysis on Term, with re-typechecking at each
  --        ctor establishing the reconstruction is unique
```

**Quote/Antiquote syntax**:
```lean
-- Compile-time quote: lifts a syntactic expression to ReflTerm
syntax "`(" term ")" : ReflTerm
-- e.g., `(λ x. x + 1) elaborates to:
--   ReflTerm.lam (ReflTerm.app2 ReflTerm.intAdd
--                                (ReflTerm.var 0)
--                                (ReflTerm.intLit 1))

-- Antiquote: splice ReflTerm into a Term context
syntax "${" term "}" : Term
-- e.g., let r : ReflTerm := compute_some_term ()
--       lam x. ${r} + x   -- splices r into the lambda body
```

**Tasks**:
* [ ] D88.5.1 `Foundation/Reflection/ReflTerm.lean` — ReflTerm
  inductive (mirrors all 75 Term ctors)
* [ ] D88.5.2 ReflTy + ReflLevel + ReflModality + ReflEffect
  supporting types
* [ ] D88.5.3 `Term.reify : Term ctx ty raw → ReflTerm` structural
  recursion at all 75 ctors
* [ ] D88.5.4 `ReflTerm.elaborate` with explicit ElabError cases
  (scope-error, type-mismatch, ctor-arity-error, etc.)
* [ ] D88.5.5 Roundtrip theorem `reify ; elaborate = .ok ∘ pack`
  zero-axiom at all 75 ctors
* [ ] D88.5.6 Quote syntax `(...) : ReflTerm parser
* [ ] D88.5.7 Antiquote syntax ${...} : Term splicer with hygiene
  (capture-avoiding under binders)
* [ ] D88.5.8 STRICT-48-R-Refl: reflection roundtrip gate
* [ ] D88.5.9 Smoke audit reflection foundation

**References**: Boutin 1997 (Using reflection to build efficient
and certified decision procedures, TYPES); Christiansen-Brady 2016
(Elaborator reflection, ICFP); Sozeau et al. 2020 (MetaCoq, POPL);
Ziliani et al. 2015 (Mtac2, ICFP); Lean 4 manual (Lean.Expr +
MetaM).

**Acceptance**: ReflTerm + reify + elaborate + roundtrip ship
zero-axiom; quote/antiquote operational with hygiene; bootstrap
(B13) milestone unblocked.

### Day 88.6 — ReflTy + ReflLevel + universe reflection (CRITICAL)

**Goal**: reflect `Ty` and `Universe` structure as data; full
universe-polymorphism reflection per Era V cumulUp infrastructure.

**Construction**:
```lean
inductive ReflTy where
  | universe (lvl : ReflLevel)
  | arrow (a b : ReflTy)
  | piTy (a : ReflTy) (b : ReflTy)         -- dependent
  | sigmaTy (a : ReflTy) (b : ReflTy)
  | bool | nat | unit | empty
  | listType (a : ReflTy)
  | optionType (a : ReflTy)
  | eitherType (a b : ReflTy)
  | id (a x y : ReflTy)
  | oeq (a x y : ReflTy)
  | idStrict (a x y : ReflTy)
  | equiv (a b : ReflTy)
  | interval | path (a x y : ReflTy)
  | glue (...) | refine (a p : ReflTy)
  | record (fields : List (Name × ReflTy))
  | codata (head : ReflTy) (tail : ReflTy)
  | session (proto : ReflSessionProto)
  | effect (row : ReflEffectRow)
  | modal (modality : ReflModality) (inner : ReflTy)

inductive ReflLevel where
  | zero
  | succ (l : ReflLevel)
  | max (l₁ l₂ : ReflLevel)
  | imax (l₁ l₂ : ReflLevel)  -- Lean-style impredicative max
```

**Theorems**:
```lean
def Ty.reify : Ty level scope → ReflTy
def ReflTy.elaborate : ReflTy → Either ElabError (Σ level scope, Ty level scope)
theorem Ty.reify_roundtrip : ReflTy.elaborate (Ty.reify T) = .ok _

def UniverseLevel.reify : UniverseLevel → ReflLevel
theorem cumul_via_reflection :
  Ty.reify (Ty.cumulUp lvl_low lvl_high T)
  = ReflTy.lift_lvl_to_lvl' lvl_low lvl_high (Ty.reify T)
  -- Era V cumulUp infrastructure lifts to reflective level
```

**Tasks**:
* [ ] D88.6.1 `Foundation/Reflection/ReflTy.lean` — ReflTy mirroring
  all Ty ctors (~25 ctors per Era V close)
* [ ] D88.6.2 ReflLevel for cumulative Nat-indexed universes
  (per D1.2)
* [ ] D88.6.3 `Ty.reify` + `ReflTy.elaborate` + roundtrip theorem
* [ ] D88.6.4 Universe-polymorphism reflection: cumulUp lifts to
  ReflTy.lift_lvl operation; commutes with reify
* [ ] D88.6.5 Smoke + commit

**References**: Lean 4 universe-polymorphism implementation
(metaprogramming book, ch. on ULevel); MetaCoq Universe handling
(Sozeau et al. 2020).

**Acceptance**: ReflTy + ReflLevel + universe-polymorphism
reflection ship zero-axiom.

### Day 88.7 — Derivation reflection (typing proofs as data) (CRITICAL)

**Goal**: reflect typing derivations `Γ ⊢ t : T` as `ReflDerivation`
data; enable proof-relevant tactics + debugger explanations.

**Construction**:
```lean
-- Mirrors HasType inductive (Era VIII Day 8.7 typing rules ~25)
inductive ReflDerivation where
  | varRule    (Γ : ReflCtx) (idx : Nat) (T : ReflTy)
  | appRule    (deriv_f deriv_a : ReflDerivation)
  | lamRule    (Γ : ReflCtx) (paramTy : ReflTy)
                (deriv_body : ReflDerivation)
  | piRule     (deriv_a deriv_b : ReflDerivation)
  | universeRule (lvl : ReflLevel)
  | cumulUpRule (lvl_low lvl_high : ReflLevel)
                 (deriv_inner : ReflDerivation)
  | conversionRule (deriv : ReflDerivation) (conv : ReflConv)
  ... (one per HasType inductive constructor)

def Derivation.reify : (Γ ⊢ t : T) → ReflDerivation
def ReflDerivation.elaborate : ReflDerivation → Either ElabError Derivation

theorem Derivation.reify_roundtrip :
  ReflDerivation.elaborate (Derivation.reify d) = .ok d
```

**Tasks**:
* [ ] D88.7.1 `Foundation/Reflection/ReflDerivation.lean` —
  mirrors HasType inductive ~25 cases
* [ ] D88.7.2 reify + elaborate + roundtrip per derivation rule
* [ ] D88.7.3 Used for: proof-relevant tactics, debugger goal
  display, refinement-typed programming with proof witnesses
* [ ] D88.7.4 Smoke + commit

**References**: Sozeau et al. 2020 (MetaCoq derivation
reflection); Lean 4 `MetaM` goal-state representation.

**Acceptance**: ReflDerivation zero-axiom; proof-relevant tactics
unblocked.

### Day 88.8 — Tactic framework via reflection (CRITICAL)

**Goal**: ship `Tactic` monad on top of reflection; re-implement
Era VI's tactics (decide, omega, ring, polyrith, aesop) as
reflective programs; verified tactic-correctness theorem.

**Construction**:
```lean
-- Tactic state: current goal + hypotheses + meta-vars + metric
structure TacticState where
  goal       : ReflTerm × ReflTy
  context    : List (Name × ReflTy × Option ReflTerm)
  metavars   : List (MVarId × ReflTy)
  metric     : Cost  -- cost-tropical for strategy ranking

-- Tactic monad: state + error + effect
abbrev Tactic α := EStateM TacticError TacticState α

-- Primitive tactics
def Tactic.intro    : Tactic Unit
def Tactic.apply    : ReflTerm → Tactic Unit
def Tactic.assumption : Tactic Unit
def Tactic.rewrite  : ReflTerm → Tactic Unit
def Tactic.simp     : List ReflTerm → Tactic Unit
def Tactic.exact    : ReflTerm → Tactic Unit

-- Decision-procedure tactics (Era VI re-stated reflectively)
def Tactic.decide    : Tactic Unit  -- Decidable instance lookup
def Tactic.omega     : Tactic Unit  -- Pugh 1991 Presburger
def Tactic.linarith  : Tactic Unit  -- Fourier-Motzkin
def Tactic.ring      : Tactic Unit  -- Buchberger 1965 Gröbner
def Tactic.polyrith  : Tactic Unit  -- polynomial arithmetic
def Tactic.aesop     : Tactic Unit  -- proof search heuristic
```

**Tactic correctness theorem (load-bearing)**:
```lean
theorem Tactic.correctness {τ : Tactic Unit} {S : TacticState} :
  τ S = .ok ((), S')
  → S'.goal.fst.elaborate = .ok ⟨_, _, _, proof⟩
  → ∃ proof_for_original : Term S.goal.ctx S.goal.ty _,
      proof_for_original = ... -- constructed from S' proof + S
  -- Successful tactic ⟹ verified Term proof; zero-axiom.
```

**Tasks**:
* [ ] D88.8.1 `Foundation/Reflection/Tactic.lean` — Tactic monad
  + TacticState + TacticError
* [ ] D88.8.2 Primitive tactics (intro, apply, assumption,
  rewrite, simp, exact)
* [ ] D88.8.3 Decision-procedure tactics: decide (Decidable
  lookup), omega (Pugh 1991), linarith (Fourier-Motzkin), ring
  (Buchberger 1965 Gröbner), polyrith, aesop
* [ ] D88.8.4 Tactic-correctness theorem: successful tactic ⟹
  verified Term proof
* [ ] D88.8.5 Era VI tactics (Days 47-50) re-stated as Tactic
  primitives — bridge theorem proves they produce identical proofs
* [ ] D88.8.6 STRICT-49-R-Tactic: tactic-correctness gate
* [ ] D88.8.7 Smoke + commit + benchmark vs Era VI native (target:
  reflection within 2× native speed)

**References**: Pugh 1991 (Omega test for Presburger arithmetic);
Buchberger 1965 (Gröbner bases); Mahboubi-Strub 2016 (Mathematical
Components reflection); Coq Mtac2 (Ziliani et al. 2015); Lean 4
Aesop (Limperg 2023).

**Acceptance**: tactic framework zero-axiom; Era VI's 6 tactics
re-implementable as reflective programs; performance within 2× of
native Era VI implementations.

### Day 88.9 — Era R close-out + macros + bootstrap-readiness (CRITICAL)

**Goal**: macros + DSL embedding + FX-in-FX self-hosting
infrastructure (unblocks B13 bootstrap milestone).

**Construction (macro infrastructure)**:
```lean
-- macro_rules : reflective programs that produce Term values
-- Syntactic transformation pre-elaboration; verified hygiene
syntax "macro_rules" "|" macroPattern "=>" macroBody : command

-- Example DSLs (proof-of-concept)
-- SQL builder:
syntax "SELECT" sqlFields "FROM" sqlTable : term
macro_rules
  | `(SELECT $f FROM $t) => ...

-- Regex compiler (compile-time):
syntax "regex" str : term
macro_rules
  | `(regex $s) => -- compiles to verified DFA
```

**FX-in-FX self-hosting (B13 milestone)**:
```lean
-- Implement FX's elaborator + typechecker in FX (using reflection)
def FX.elaborator : ReflParseTree → Either ElabError ReflTerm
def FX.typechecker : ReflTerm → Either TypeError ReflDerivation
def FX.kernel.checkSound : ReflTerm → Bool  -- per metaplan FX1

theorem FX_in_FX_consistency :
  ∀ (input : ParseTree) (t : Term ctx ty raw),
    FX.elaborator (ParseTree.reify input) = .ok (Term.reify t)
    ↔ NativeKernel.elaborate input = .ok t
  -- FX-in-FX checker produces SAME results as native Lean 4 kernel.
  -- Ships zero-axiom; closes B13 bootstrap.
```

**Tasks**:
* [ ] D88.9.1 `Foundation/Reflection/Macro.lean` — macro_rules
  infrastructure
* [ ] D88.9.2 Hygiene (capture-avoiding substitution at macro
  level; α-renaming bound names)
* [ ] D88.9.3 Example DSLs: SQL builder, regex compiler, parser
  combinator
* [ ] D88.9.4 FX-in-FX elaborator (using ReflTerm + Tactic)
* [ ] D88.9.5 FX-in-FX typechecker (using ReflDerivation)
* [ ] D88.9.6 FX-in-FX self-consistency theorem (FX-in-FX checker
  ≡ native Lean 4 kernel on inputs)
* [ ] D88.9.7 Synthetic Tait (Era X Day 75) re-stated using
  reflection primitives — synthetic Tait now PROVES checker's own
  termination internally
* [ ] D88.9.8 STRICT-50-R-Bootstrap: B13 bootstrap-readiness gate
* [ ] D88.9.9 Era R commit + status

**Headline theorem (reflection completeness, B13 milestone)**:
```
For every Term-level operation (rename, subst, reduce, type-check)
there exists an equivalent reflective program manipulating
ReflTerm values. The reflective program is verified to produce
the SAME result as the native kernel implementation, zero-axiom.

This unlocks bootstrap: FX-in-FX, where the FX compiler is itself
an FX program and its correctness is a kernel theorem.
```

**Acceptance**: Era R complete; reflection operational across
Term/Ty/Derivation levels; tactic framework + macros + DSLs
operational; B13 bootstrap milestone unblocked.

---

## Era XII — Algorithm discovery (dim 6) (Day 89–96)

Cross-complexity-class search. Mostly research-grade. ~8 months.

### Day 89 — Algorithm-equivalence cells (dim 6) (CRITICAL)

**Goal**: cross-complexity-class equivalence with cost semiring.

**Tasks**:
* [ ] D89.1 `Polygraph/Dim6/AlgorithmEquivalence.lean`
* [ ] D89.2 Cross-complexity-class equivalence with cost semiring
  (BigO, ⊕, ⊗)
* [ ] D89.3 STRICT-34: dim-6 cell well-formedness
* [ ] D89.4 Smoke audit dim-6 cells

**BigO partial order**: not a semiring (no distributivity), but a
**poset-enriched commutative monoid**:
* Min (join in BigO order): O(f) + O(g) = O(max(f, g))
* Multiplication: O(f) · O(g) = O(f · g)
* Order: O(f) ≤ O(g) iff f ∈ O(g)

**Algorithm equivalence**: two algorithms are dim-6-equivalent iff
they compute the same function with potentially different complexity
classes.

**Acceptance**: dim-6 cells + BigO poset zero-axiom; STRICT-34
green.

### Day 90 — AlphaTensor-style search (parallel)

**Goal**: ML-guided dim-6 cell discovery.

**Tasks**:
* [ ] D90.1 ML-guided dim-6 cell discovery
* [ ] D90.2 Distributional polygraph search via Wasserstein gradient
  flow (JKO scheme)
* [ ] D90.3 Verified extraction
* [ ] D90.4 Reference: matrix multiplication faster algorithms
  for small dimensions

**AlphaTensor approach** (DeepMind 2022): RL agent searches
discrete algorithm space (matrix multiplication algorithms) via
tensor decomposition.

**Tensor rank**: ω = inf{α : matmul ∈ O(n^α)} where ω is the
matrix-multiplication exponent.

**Current bounds**: 2 ≤ ω ≤ 2.371552 (Williams-Xu-Xu-Zhou 2024).

**Acceptance**: ML-guided search operational + verified extraction
on matrix-multiplication benchmark.

### Day 91 — Counterexample-driven synthesis (parallel)

**Goal**: CEGIS (Counterexample-Guided Inductive Synthesis) at
kernel level.

**Tasks**:
* [ ] D91.1 Solver counterexample certificate → fix proposal as
  dim-6 cell
* [ ] D91.2 Sketch-style synthesis at kernel level
* [ ] D91.3 ML-guided proposal ranking
* [ ] D91.4 User-acceptance workflow via daemon

**CEGIS algorithm** (Solar-Lezama 2008):
1. Synthesize candidate program P.
2. Verify against spec; if pass, done.
3. Else extract counterexample CE.
4. Add CE to constraint set; loop to 1.

**Convergence**: guaranteed to terminate when synthesis space is
finite or has bounded structure.

**Acceptance**: CEGIS synthesis operational; daemon-mediated
user-acceptance flow zero-axiom.

### Day 92 — Cost-budget elaboration (CRITICAL)

**Goal**: typed cost budgets.

**Tasks**:
* [ ] D92.1 `with budget(O(n log n), 100ns/elem)` syntax
* [ ] D92.2 Cost-budget-driven implementation selection
* [ ] D92.3 Performance-bound types
* [ ] D92.4 Smoke audit + benchmark verification

**Type signature**: `f : ... with budget(C, T)` where C is BigO
class, T is per-element time.

**Compiler synthesis**: among candidate implementations, select
one satisfying both BigO ≤ C and per-element ≤ T.

**Acceptance**: cost-budget elaboration zero-axiom; benchmark
verification confirms perf bounds met.

### Day 93 — User-extensible β-rule database (CRITICAL)

**Goal**: user-supplied rewrite rules with full kernel
verification.

**Tasks**:
* [ ] D93.1 `@[beta_rule, prove_equivalent]` user attribute
* [ ] D93.2 Compiler-side verification pipeline
* [ ] D93.3 Confluence verifier (STRICT-35)
* [ ] D93.4 Termination verifier (STRICT-36)
* [ ] D93.5 SR verifier (STRICT-37)
* [ ] D93.6 Sandbox before global database commit

**Verification gates** (STRICT-35 to STRICT-37):
* **Confluence**: new rule's critical pairs join with existing.
* **Termination**: new rule preserves SN.
* **SR**: new rule preserves typing.

**Knuth-Bendix completion** (Part I §4 Theorem 4.5): when adding a
new rule, attempt completion; if completion converges, accept;
else reject.

**Acceptance**: user-extensible β rules with all 3 verification
gates green; Knuth-Bendix completion at kernel level zero-axiom.

### Day 93.A — E-graph integration as 4th encoding column (CRITICAL)

**Goal**: ship `EGraph` as the 4th encoding column (per architectural-
shift four-encoding grid: Tree / PolyTerm / ValueTerm / EGraph);
equality-saturation framework via egg-style congruence closure +
union-find on canonical class representatives (Willsey-Nandi-Wang-
Stepp-Tatlock-Panchekha 2021); integrates with Era V D38.A
incrementality, Era VI tactic search, Era IX OT, Era XII algorithm
discovery.

**Construction (e-graph data structure)**:
```lean
-- E-class id: sealed handle to an equivalence class.
-- Kernel implementation is concrete (Nat/Fin index into an array);
-- callers use the abstract API, but shipped code does not use
-- Lean `opaque`.
structure ECId where
  value : Nat
deriving DecidableEq

-- E-node: a Term ctor applied to e-class arguments (vs. nested
--          Term recursion in Tree encoding)
inductive ENode where
  | var       (idx : Nat)
  | app       (f arg : ECId)
  | lam       (body : ECId)
  | natZero | natSucc (n : ECId)
  | boolTrue | boolFalse
  | boolElim (motive t f : ECId) (b : ECId)
  | ... (mirrors all 75 Term ctors via ECId children)

-- E-class: set of equivalent e-nodes
structure EClass where
  id    : ECId
  nodes : Array ENode    -- finite, non-empty; congruence-closed
  data  : EClassMetadata -- analysis state per egg (Willsey 2021)

-- E-graph: union-find of e-classes + congruence-closure index
structure EGraph where
  classes      : Map ECId EClass
  uf           : UnionFind ECId    -- class merging
  hashcons     : Map ENode ECId    -- congruence index
  pending      : List (ECId × ECId) -- merge worklist
  invariants:
    -- canonical: ∀ c, find c = c
    -- congruence: ∀ n₁ n₂ : ENode, congruent n₁ n₂ ⟹
    --             find (lookup n₁) = find (lookup n₂)
```

**Equality saturation algorithm (Willsey et al. 2021, POPL)**:
```
def saturate (g : EGraph) (rules : List RewriteRule) (depth : Nat)
             : EGraph
  -- Phase 1: match rule-LHS patterns against e-graph (parallel)
  -- Phase 2: insert rule-RHS as new e-nodes, merge with matched class
  -- Phase 3: rebuild congruence closure (union-find + hashcons fix)
  -- Repeat for `depth` iterations or until saturation (no new merges)

theorem saturate_terminates :
  ∀ g rules d, ∃ g', saturate g rules d = g' ∧ g'.bounded_size

-- Complexity: O(|e-classes|^d) for depth-d search;
--             tractable for d ≤ 10 in practice (Willsey 2021)
```

**Extraction (cost-minimal representative per cost function)**:
```
def extract (g : EGraph) (root : ECId)
            (cost : ENode → ℝ⁺)
            : Term
  -- Bottom-up dynamic programming over the e-graph DAG
  -- Returns the minimum-cost Term in the e-class of root
  -- Cost functions: AST size, runtime, energy (Era V D38.B),
  --                 incrementality cost (Era V D38.A change deltas)

theorem extract_sound :
  ∀ g root cost, extract g root cost ∈ root.eClass.terms
                 ∧ ∀ t' ∈ root.eClass.terms, cost(extract) ≤ cost(t')
```

**Bridge to existing 3 encoding columns**:
```
def Term.toEGraph : Term ctx ty raw → EGraph
  -- Lossy: each Term maps to its e-class equivalence class
  -- Witness: ∀ t, ∃! ECId c, Term.toEGraph t.contains_class = c

def EGraph.extractToTerm (g : EGraph) (root : ECId) (cost : ENode → ℝ⁺)
                          : Term
  -- Lossy inverse: many Terms in same e-class; extract picks argmin

def PolyTerm.toEGraph : PolyTerm ctx ty raw → EGraph
  -- Lossy: e-graph forgets dim/sharing structure;
  -- preserved in dim-2 cells of EGraph (saturation rules)

theorem encoding_4th_lattice :
  Tree → PolyTerm → ValueTerm → EGraph
  with all 4 columns related via verified bidirectional coercions
  on appropriate fragments.
```

**Use cases (extends existing Era infrastructure)**:
```
- Era V D38.A incrementality: Δ-typed change classes via e-graph
  union (each Δ adds equivalence)
- Era VI tactic search: saturate goal e-graph, extract proof
- Era IX OT integration: e-class as fuzzy semantic class;
  Wasserstein on e-class probability distributions
- Era XII algorithm discovery: e-graph saturation generates
  candidate algorithms; STRICT-35/36/37 verifies each
- Era IV.5 + FEU-FX: hardware Merkle trie ≡ e-graph union-find
  (FEU §24.1 ternary Merkle trie repurposed as content-addressed
  cell hash trie)
```

**Tasks**:
* [ ] D93.A.1 `Foundation/EGraph/Foundation.lean` — ECId sealed
  finite handle, ENode inductive (mirrors 75 Term ctors via ECId
  children)
* [ ] D93.A.2 EClass + EGraph structure with union-find +
  congruence-closure invariants
* [ ] D93.A.3 saturate algorithm per Willsey 2021 Phase 1-3 (match
  / insert / rebuild)
* [ ] D93.A.4 Termination theorem (saturate terminates with
  bounded size for depth d ≤ 10)
* [ ] D93.A.5 extract algorithm with bottom-up DP over e-graph DAG
* [ ] D93.A.6 Extraction soundness theorem (min-cost rep per cost
  function)
* [ ] D93.A.7 Bridges: Term.toEGraph, PolyTerm.toEGraph,
  ValueTerm.toEGraph + extractToTerm inverse
* [ ] D93.A.8 4th-encoding-column subsumption-lattice theorem
  (verified bidirectional coercions)
* [ ] D93.A.9 Cross-Era integration: Era V D38.A change classes,
  Era VI tactics, Era IX Wasserstein, Era XII discovery, FEU-FX
  Merkle trie correspondence
* [ ] D93.A.10 STRICT-55-IX-EGraph + STRICT-56-IX-Extract gates
* [ ] D93.A.11 Smoke audit comprehensive
* [ ] D93.A.12 Era XII / Era IX commit (cross-Era artifact)

**References**: Willsey-Nandi-Wang-Stepp-Tatlock-Panchekha 2021
(egg: Fast and extensible equality saturation, POPL); Tate-
Stepp-Tatlock-Lerner 2009 (Equality saturation: a new approach
to optimization); Nelson-Oppen 1979 (congruence closure); Detlefs-
Nelson-Saxe 2005 (Simplify); Eyenmenger-Wisniewski 2025 (e-graphs
in proof assistants survey).

**Acceptance**: e-graph encoding column ships zero-axiom;
saturation + extraction operational; 4th column completes the
encoding lattice; cross-Era integration verified.

### Day 94 — NP-fragment specialization (parallel, exploratory)

**Goal**: refinement-strengthened algorithms for restricted
problem fragments.

**Tasks**:
* [ ] D94.1 Refinement-strengthened SAT solver for restricted
  formulas
* [ ] D94.2 Tree-decomposition-aware variants
* [ ] D94.3 Verified narrower-than-SOTA bounds for specific
  sub-problems
* [ ] D94.4 Smoke audit + benchmarks

**Tree-decomposition-aware SAT** (Bodlaender 1996): SAT with
tree-decomposition width ≤ k is solvable in O(2^k · n).

**FX provides**: for refinement-strengthened input types, kernel
selects optimal specialized algorithm.

**Acceptance**: NP-fragment specialization operational on
restricted SAT benchmarks; perf hits Bodlaender-bound.

### Day 95 — Self-extending β-rule database (exploratory)

**Goal**: kernel learns from user code.

**Tasks**:
* [ ] D95.1 User code teaches kernel new optimizations
* [ ] D95.2 Verified kernel extension
* [ ] D95.3 Cumulative speedup over time
* [ ] D95.4 Deterministic seed for reproducibility

**Cumulative speedup**: over multiple runs, kernel database grows
with verified user-supplied rules. Programs benefit from database
without explicit cooperation.

**Acceptance**: self-extending β-rule database operational;
deterministic seed for reproducibility.

### Day 96 — Era XII close-out (CRITICAL)

**Goal**: algorithm discovery operational on representative
benchmarks.

**Tasks**:
* [ ] D96.1 Algorithm-discovery operational on representative
  benchmarks
* [ ] D96.2 Cost-budget elaboration shipping
* [ ] D96.3 User-extensible β-rules with full verification gates
* [ ] D96.4 Era XII commit + status

**Acceptance**: FX kernel finds SOTA-equivalent or better algorithms
for narrow specializations with verified correctness.

---

## Era W — World-as-type layer (Day 96.5–96.9)

Layer Ω part 2: `World : Type` as a sealed first-class interface
with concrete finite/Kripke implementations; effects re-cast as
world transitions per Iris-style
step-indexed Kripke worlds (Jung-Krebbers-Jourdan-Bizjak-Birkedal-
Dreyer JFP 2018); counterfactual operators. Selective — full Iris
parity ships only when applications justify cost. ~5 months.

**Architectural commitment**: existing FX effects (IO, Async, Read,
Write, Crypto, Alloc, Div per Era V D5.9) re-cast as functions
`World → World × Result` with explicit world-state semantics. World
indexed by what's known about it via Kripke step-indexed
invariants.

**Theorem (effect-monad ≅ world-transition equivalence)**:
```
For each existing FX effect E,
  ∃ (world_repr_E : World → Type) (transition_E : ...),
    E-effect-monad ≅ Σ (w : World) (s : world_repr_E w),
                     World × world_repr_E (next-world)

Specifically:
  IO        : World → World × Result
              (peek/poke external state)
  Async     : World → Future (World × Result)
              (deferred world state)
  Read      : World → World × Reading
              (observation, world unchanged)
  Write     : World → World × Unit
              (world modified)
  Crypto    : World → World × Result
              (world: random oracle access)
  Alloc     : World → World × Address × Unit
              (world: memory allocator state)
  Div       : World → World × Diverges
              (no termination guarantee)
```

**Theorem (Iris step-indexing soundness, Jung et al. 2018)**:
```
For step-indexed world predicate P : ℕ → World → Prop satisfying
monotonicity (P (n+1) w → P n w) and Kripke-style restriction:
  step-indexed assertion validity preserves through resource
  framing + composition;
  Iris invariants hold under the chosen Kripke structure;
  resource transfers verified by combination of step-indexing +
  fractional permissions per Iris JFP 2018.
```

**Why selective**: most FX programs DON'T NEED full world types —
existing graded effects + linear types + session types cover ~80%
of practical cases. Era W ships world types for the 20% requiring
distributed-systems / concurrent-shared-state / verified-file-system
use cases. Unused machinery doesn't bloat user-facing kernel.

### Day 96.5 — World as sealed kernel interface + peek/poke (CRITICAL)

**Goal**: ship `World` as a sealed API with concrete computable
implementations and peek/poke primitives; bridge to existing FX
effects. The word "sealed" is deliberate: no Lean `opaque` in
zero-axiom kernel code.

**Construction**:
```lean
-- World is abstract at user level; internally a concrete finite or
-- Kripke-indexed structure hidden behind the module API.
structure World where
  state : WorldState
-- Decidable equality is required only for finite WorldState
-- instances used by executable checkers; Kripke/Iris instances use
-- observation equivalence instead.

def World.empty : World
def World.peek  : World → Sensor → World × Reading
                     -- observation: world unchanged
                     (ret_world : World) = w
def World.poke  : World → Effector → World
                     -- modification: world transitions

-- Open : Type → Type — types that may evolve under world state
def Open (T : Type) : Type :=
  Σ (w : World), (w → T)
  -- value depends on world; world-indexed

-- World-effect monad (Reader+State combinator)
def WorldM (α : Type) : Type :=
  World → α × World

-- Bridge to existing FX effects
def IOEff.toWorld : ∀ {α}, IOEff α → WorldM α
def IOEff.fromWorld : ∀ {α}, WorldM α → IOEff α
theorem IOEff.world_iso : ∀ {α} (e : IOEff α),
  IOEff.fromWorld (IOEff.toWorld e) = e
```

**Tasks**:
* [ ] D96.5.1 `Foundation/World/Foundation.lean` — World sealed API
  + concrete WorldState + empty/peek/poke primitives
* [ ] D96.5.2 `Open : Type → Type` for world-evolution-typed values
* [ ] D96.5.3 WorldM monad + bind/pure laws
* [ ] D96.5.4 Bridge to existing FX effects (Era V D5.9): IOEff,
  Async, Read, Write, Crypto, Alloc, Div all lift to WorldM
* [ ] D96.5.5 World-iso theorem: existing effect monad ≅ world
  monad (zero-axiom, preserves all existing programs)
* [ ] D96.5.6 STRICT-51-W-World: world-type well-formedness gate
* [ ] D96.5.7 Smoke audit world foundations

**References**: O'Hearn-Reynolds 2001 (separation logic origins);
Jung et al. 2018 (Iris from the ground up, JFP); Plotkin-Power
2002 (algebraic effects); Bauer-Pretnar 2015 (Eff language).

**Acceptance**: World sealed API + peek/poke + WorldM monad +
effect-bridge zero-axiom; existing FX programs continue under
world-typed framework via auto-lifted effects.

### Day 96.6 — Effects as verified world transitions (CRITICAL)

**Goal**: re-cast existing FX effects as world-modifying functions
with explicit pre/post semantics; migration tooling auto-lifts
existing programs.

**Construction (effect re-statement)**:
```lean
-- IO with explicit world transitions
def read_file (path : String) (w : World)
              (h : FileExists w path)  -- precondition on world
              : World × String         -- world possibly unchanged
                                       -- (depends on filesystem
                                       -- semantics)

-- Async with explicit world ordering
def async_op (op : World → α) (w : World)
             : World × Future α
  -- Future α evaluated when world advances; ordering tracked

-- Read/Write with observable state
def read_register (r : RegId) (w : World) : World × ValueOf r
def write_register (r : RegId) (v : ValueOf r) (w : World) : World

-- Crypto effect: world contains random oracle state
def crypto_random (n : Nat) (w : World)
                  : World × Bits n
  -- world's random oracle advances; subsequent reads see fresh
  -- randomness

-- Alloc: world state contains heap
def alloc (size : Nat) (w : World)
          : World × Address × Unit
  -- world's allocator advances; address fresh

-- Div: world state may not terminate
def div_op (op : World → α) (w : World)
           : Option (World × α)
  -- maybe world transitions, maybe diverges
```

**Migration theorem**:
```
∀ (program : ExistingFXProgram with effect E),
  program' := lift_to_world (program)
  ∀ (initial_world : World), evaluate (program', initial_world)
  ≡ existing_evaluation (program, initial_state)
  on observable outcomes (ignoring intermediate world details)
```

**Tasks**:
* [ ] D96.6.1 IO effect re-stated as `World → World × Result` with
  pre/post semantics per Era V §9
* [ ] D96.6.2 Async effect re-stated with explicit world ordering
* [ ] D96.6.3 Read/Write effects with observable state changes;
  separate read-only vs read-write
* [ ] D96.6.4 Crypto re-stated with random-oracle state
* [ ] D96.6.5 Alloc re-stated with heap-allocator state
* [ ] D96.6.6 Div re-stated with maybe-termination
* [ ] D96.6.7 Migration theorem: existing programs ≡ world-typed
  versions on observable outcomes
* [ ] D96.6.8 Migration tooling: auto-lift existing FX effects to
  WorldM (compile-time pass)
* [ ] D96.6.9 STRICT-52-W-Effect: effect-as-world-transition gate
* [ ] D96.6.10 Smoke audit effect migration

**References**: Plotkin-Power 2002 (algebraic effects); Bauer-
Pretnar 2015 (Eff); Lindley-McBride-McLaughlin 2017 (do unto);
Smolka et al. 2020 (algebraic effect handlers in Coq).

**Acceptance**: existing effect system operational under world-
typed framework; migration path verified zero-axiom; existing FX
programs continue without source changes.

### Day 96.7 — Iris-style step-indexed Kripke worlds (parallel, exploratory)

**Goal**: ship Iris step-indexed Kripke worlds for higher-order
shared state; concurrent invariant framework for distributed-
systems / kernel verification.

**Construction**:
```lean
-- Step-indexed Kripke world (Jung et al. 2018)
structure KripkeWorld where
  level     : ℕ                    -- step index
  resources : List (Resource × Permission)
                                   -- fractional permissions
                                   -- (Iris fractional)
  invariants : Set Invariant       -- concurrent invariants
  ghost_state : List GhostUpdate    -- higher-order ghost state

-- Step-indexed assertion (P : ℕ → KripkeWorld → Prop)
abbrev Assertion := ℕ → KripkeWorld → Prop

-- Monotonicity: P (n+1) w → P n w
def Assertion.monotone (P : Assertion) : Prop :=
  ∀ {n} {w : KripkeWorld}, P (n+1) w → P n w

-- Resource framing (separation logic)
def Assertion.frame (P Q : Assertion) (frame : Assertion) : Prop :=
  ∀ {n} {w : KripkeWorld},
    P n w → frame n w → Q n (combine w frame_resources)

-- Persistent invariant; represented as a record of closure proofs,
-- not Lean `opaque`.
structure Persistent (P : Assertion) : Prop where
  down_closed : ∀ {n w}, P n w → ∀ k, P (n - k) w
  -- always holds at lower step
```

**Theorem (Iris soundness, Jung et al. 2018)**:
```
Step-indexed assertion validity preserves through resource framing
+ composition. Iris invariants hold under chosen Kripke structure.
Resource transfers verified by step-indexing + fractional
permissions.

Soundness: if Iris proves ⊢ {P} prog {Q} then for any world w
satisfying P, prog terminates (or diverges via Δ-step) producing
result satisfying Q.
```

**Tasks**:
* [ ] D96.7.1 `Foundation/World/StepIndexed.lean` — Iris
  KripkeWorld structure with step-index + resources + invariants
* [ ] D96.7.2 Higher-order ghost state via Iris cmra (camera, per
  Jung 2018); update modality ⤳
* [ ] D96.7.3 Concurrent invariant framework with bidirectional
  framing
* [ ] D96.7.4 Soundness theorem (step-indexed validity preserves
  through resource framing); zero-axiom on the constructive
  fragment
* [ ] D96.7.5 Smoke + commit

**References**: Jung-Krebbers-Jourdan-Bizjak-Birkedal-Dreyer 2018
(Iris from the ground up, JFP); Krebbers et al. 2017 (Iris
interactive, POPL); Jung-Sieczkowski-Birkedal 2017 (HOCAP, ESOP).

**Acceptance**: Iris-style step-indexed worlds zero-axiom on the
constructive fragment; usable for verified concurrent reasoning.

### Day 96.8 — Counterfactual reasoning (parallel, exploratory)

**Goal**: counterfactual operators for "what-if" world-state
analysis; verified non-interference (counterfactual analysis
doesn't affect actual world).

**Construction**:
```lean
-- Counterfactual: hypothetical world transition
def Counterfactual (w : World) (transformation : World → World)
                   : Type :=
  Σ (w' : World), w' = transformation w
  -- type witnesses what would happen if we applied transformation
  -- without actually applying it

def hypothetical (w : World) (op : World → World × α)
                 : Counterfactual w (op ∘ Prod.fst) :=
  ⟨op w |>.fst, rfl⟩

-- Verified non-interference
theorem Counterfactual.non_interference :
  ∀ (w : World) (transformation : World → World),
    actual_world := w  -- real world unchanged
    (Counterfactual w transformation).fst ≠ actual_world
    ⟹ transformation creates a new branch in counterfactual space
    ⟹ actual_world remains identical
  -- The counterfactual is "imagined" only; no observable side
  -- effects in actual_world
```

**Tasks**:
* [ ] D96.8.1 `Foundation/World/Counterfactual.lean` —
  counterfactual world operators
* [ ] D96.8.2 hypothetical : World → (World → World × α)
  → CounterfactualResult
* [ ] D96.8.3 Verified non-interference theorem
* [ ] D96.8.4 Use cases: bug analysis ("what if input was X?");
  optimization ("what if we took the other branch?"); model
  checking
* [ ] D96.8.5 Smoke + commit

**Acceptance**: counterfactual operators zero-axiom; non-
interference verified.

### Day 96.9 — Era W close-out + verified examples (CRITICAL)

**Goal**: world-as-type layer operational on the constructive
fragment; verified examples (file system, concurrent counter)
demonstrate practical use; selective extensions documented.

**Verified examples (small but real)**:
```lean
-- Example 1: Verified file system
def safe_read (path : String) (w : World)
              (h : FileExists w path)
              : Σ (w' : World) (content : String),
                w' = w  -- world unchanged on read
                ∧ content = w.fileContent path

-- Example 2: Verified concurrent counter (Iris-style)
structure CounterRef where
  id : Nat
deriving DecidableEq
def newCounter (w : KripkeWorld) : KripkeWorld × CounterRef
def increment (ref : CounterRef) (w : KripkeWorld)
              (h : owns ref w)  -- ownership token
              : KripkeWorld × Unit
theorem counter_safety :
  ∀ (refs : List CounterRef) (w : KripkeWorld),
    all_owned refs w →
    parallel_increment refs w produces consistent count
```

**Tasks**:
* [ ] D96.9.1 Comprehensive smoke audit Era W
* [ ] D96.9.2 Verified file system mini-example (safe_read,
  safe_write, file_exists with Kripke invariants)
* [ ] D96.9.3 Verified concurrent counter (Iris-style with ghost
  ownership token)
* [ ] D96.9.4 Verified distributed consensus stub (Paxos round-1
  step, demonstrating multi-node Iris invariants)
* [ ] D96.9.5 STRICT-53-W-Examples gate: examples zero-axiom,
  ghost-state correct
* [ ] D96.9.6 Era W commit + status

**Headline theorem (world-as-type completeness, constructive
fragment)**:
```
For programs in the constructive fragment using only:
  - WorldM monad
  - peek/poke primitives
  - step-indexed Kripke invariants per Iris
  - fractional permissions
program correctness in FX is equivalent to Iris-style separation-
logic correctness on the same program. Verification via FX
inherits Iris's compositionality + framing properties.
```

**Acceptance**: Era W complete on the constructive + step-indexed
fragment; full Iris parity (higher-order classical concurrent
invariants) deferred to Era XIII selective extensions; verified
examples (file system, concurrent counter, consensus stub)
demonstrate practical applicability.

---

## Era XIII — Beyond beyond (Day 97+)

Speculative / research-frontier. Open-ended.

### Day 91+ — Stable ∞-categories / spectra (exploratory)

Bousfield localization computational (Bousfield 1979, "Localization
of spectra with respect to homology"); algebraic K-theory primitives;
spectra as types with Σ-Ω invertibility (Lurie 2017 *Higher Algebra*
§1 ambient framework).

### Day 92+ — Synthetic algebraic geometry (exploratory)
### Day 93+ — Motivic homotopy theory (exploratory)
### Day 94+ — Quantum HoTT (parallel, exploratory)
### Day 95+ — Self-reflective kernel (exploratory)
### Day 96+ — Probabilistic ∞-types (exploratory)
### Day 97+ — Game-theoretic ∞-types (exploratory)

Game semantics at ∞-dim (Hyland-Ong 2000 fully-abstract model for
PCF adapted); causal nets, Petri nets, interaction nets (Lafont 1990
already a special case of Era I Day 21 sharing-cell family; this Day
extends to game-theoretic semantics); concurrent algorithm
verification via game-model.

### Day 98+ — Anti-foundation / paraconsistent extensions (exploratory)

Aczel's AFA axiom (Aczel 1988, "Non-Well-Founded Sets") —
non-well-founded types; streams without termination via productivity
(dual to Era IV.5 D31.9 Bennett-1973 reversible-computing target);
controlled inconsistency for spec resolution (Belnap-Dunn FOUR per
Era IV D30 already in kernel — Day 98+ extension generalizes to full
paraconsistent logic per da Costa 1974, "On the theory of
inconsistent formal systems").

### Day 99+ — Type theory as physical reality (speculative)

---

## Verticals (parallel to all Eras after Era IV)

Each is a standalone library/product. Drives adoption.

### Vertical A — Verified API Gateway (parallel, ~6 months)
Univalence-based migration framework for Stripe-scale services.

### Vertical B — Verified CRDT Database (parallel, ~9 months)
HIT-based CRDTs with proven eventual consistency.

### Vertical C — Verified RTL Compiler (fx-chip extension) (parallel, ~12 months)
Bit-level β + multi-level bisimulation.

### Vertical D — Verified ML Compiler (parallel, ~12 months)
Quantization / distillation as univalence transports.

### Vertical E — Verified Smart Contract Platform (parallel, ~12 months)
Univalent upgradability.

### Vertical F — Verified Cryptographic Library (parallel, ~9 months)
TLS 1.3 / Signal in FX with constant-time verification.

### Vertical G — Verified Quantum Programming (parallel, ~12 months)
Linear ∞-types + QASM target.

### Vertical H — fx-physics ecosystem (parallel, ~24 months)
Beyond fx-mtheory: GR, QFT, condensed matter, gauge theory.

### Vertical I — FEU-FX co-design super-accelerator (parallel, ~18-24 months)

**Goal**: turn FEU v5 (the 225 mm² ternary fractal analog-digital
chip; 1.36 exaops; 28 nm + custom BEOL) into a native FX
super-accelerator. Twelve cheap firmware/configuration adjustments
+ three medium-cost hardware additions; preserves FEU's existing
neural-network-accelerator capabilities while adding native FX
polygraph support.

**Architectural recognition**: FEU's 7-level ternary fractal
(atom → triad → nonad → cell → SM → tile → die → cube; 3⁷ = 2187
atoms per tile) maps DIRECTLY to polygraph dim 0..6 per Era I
Appendix A:
- dim 0 (terms)              ← atoms (Trip cores hold cell state)
- dim 1 (Step ctors)         ← triads (3 alternatives per choice)
- dim 2 (cd_lemma cells)     ← nonads (3-arm confluence diamonds)
- dim 3 (strategy 3-cells)   ← cells (27 strategies per cell)
- dim 4 (hardware fibres)    ← SMs (81 atoms per realization)
- dim 5 (refinement functors) ← tiles (2187 atoms per refinement)
- dim 6 (algorithm equivs)   ← dies (multiple algorithms compete in
                                27-die ternary cube; per Era T site
                                catalog FEU_hardware instance)

**Twelve cheap adjustments (firmware/configuration, ~12 months)**:
1. New POLYGRAPH compute mode (alongside existing 8 modes
   MAC/MAC_TRANS/CASCADE/COLLISION/DIFFUSE/ANNEAL/MULTIGRID/
   SCRATCHPAD): junctions store cell hashes; column accumulation =
   composition; coupled settling = confluence verification.
2. Repurpose §24.1 ternary Merkle weight trie for content-
   addressed cell hashing (zero hardware cost).
3. Time-triggered FX kernel scheduler: compiler runs as
   time-triggered program on Tern via 162-entry CAM-IMEM modular
   tick matching (parse / typecheck / elaborate / codegen as 8-tick
   phases per 81-tick cycle).
4. Multi-die ternary cube (27 dies = 3³) as polygraph dim-6
   parallel-strategy distribution; PAM-3 SerDes (32 GBaud, 101 GB/s
   per direction, 406 GB/s aggregate) transports PolyTerm cells as
   raw trits (no encoding/decoding overhead).
5. PAM-3 SerDes native PolyTerm transport (recognition: §12.5
   PAM-3 already does this).
6. Embedded calibration as continuous polygraph soundness check
   (§19.6 spare-row 7-level ramp repurposed: ratio measurement
   verifies polygraph soundness invariants every 81 ticks).
7. Cubical intervals via 10 IGZO planes (5-dim cubical natively;
   each plane encodes one interval direction including connections
   ∧, ∨, reflection, degeneracy per CCHM 2017).
8. Coupled-settling fix-point as FX primitive `fix(f)` —
   §27.7 implicit (I − G)⁻¹ matrix inversion via charge
   redistribution at ~450 ps; usable for type-class resolution,
   DEQ models, Newton iteration.
9. Per-tile FX kernel state: SRAM repartition (40 KB → 20 KB
   ValueTerm cache + 10 KB Term hash table + 10 KB Tern stack/
   heap/DMA buffer); zero hardware change.
10. Effect-bit extension (§21.10 RO/LCL/DET → 8-bit graded modes:
    add LIN/AFF/ERA/IRR/PUB for Wood-Atkey grade vector at chip
    level); 60 T per Tern core, 17,520 T die-wide.
11. Co-located Term + ValueTerm dual storage in adjacent IGZO
    bank pairs; bank-switch converts representations in 0.22 ns.
12. NCL session-type primitives in Tern ISA (SESSION_NEW /
    SESSION_SEND / SESSION_RECV / SESSION_END / SESSION_BRANCH /
    SESSION_DUAL); ~5 new opcodes in unused 27-op ISA encoding.

**Three medium-cost hardware additions (~12 months on top)**:
13. ISA extension to Trip-A+/S only (cheaper than Trip-B+ extend):
    8 new ops (TERM_DISPATCH / STEP_FIRE / CD_DIAMOND /
    STRAT_COMPOSE / HASH_LOOKUP / COERCE_LEVEL / VAL_EVAL /
    QUOTE_STEP); ~80 T per atom × 327 atoms × 285 tiles = 7.5 M T
    ≈ 9 mm² ≈ 4% of die.
14. 8 dedicated Polygraph Tiles (replace 8 of 285 active tiles):
    Trip-A+/S with extended FX-ISA; 200 KB SRAM (vs 40 KB) for
    ValueTerm cache; reduced Lattice (5 layers vs 20); hardware
    Merkle trie content-lookup engine.
15. FX1.check_sound hardware fast path: 1-cycle structural
    type-check; multi-cycle Conv-decision via NbE pipeline on
    Trip CHAIN engine; decidable predicates discharged in parallel
    across 81 SMs of a tile.

**Honest analog ENOB caveat (carried forward from §IV.5)**: ENOB
is RUNTIME, per-chip-variable. Promise/Guard/Fallback (Era VIII
D63.A) handles compile-time loose bound + runtime measurement +
adaptive fallback. FEU's §19 7-level embedded calibration is the
runtime measurement infrastructure.

**Per-cycle polygraph cell composition rate** (target):
| Architecture                          | cells/μs    | Notes |
|---------------------------------------|-------------|-------|
| CPU (1 core, software)                | ~10²        | sequential |
| GPU (H100 fully utilized)             | ~10⁵        | branch-predication-limited |
| TPU v5                                | ~10⁵        | matmul-specialized |
| FPGA (Xilinx Versal)                  | ~10⁶        | 6-month bitstream design |
| FEU v5 (general analog accelerator)   | ~10⁷        | NN-style; polygraph emulated |
| **FEU-FX (post-vertical I)**          | **~10⁹**    | **native polygraph ops** |
| FEU-FX 27-die cube + multi-arch       | ~10¹¹       | parallel strategy search |

Speed advantage over current best (FPGA): 1000-10,000× target for
polygraph workloads. Correctness claims split into FX1.check_sound
kernel certificates, hardware realization certificates, and measured
performance reports; no speed/physics claim is a kernel theorem by
itself.

**Tasks** (parallel to Era IV-XII; integrated with Era IV.5
multi-level hardware framework + Era T FEU_hardware site instance):
* [ ] V_I.1 Document FEU-FX co-design (50-100 page spec covering
  items 1-15)
* [ ] V_I.2 Land items 1-12 (cheap firmware-only adjustments)
* [ ] V_I.3 Validate with tiny FX program (e.g., small kernel
  theorem proof) compiled to FEU-FX; measure speedup vs CPU; target
  100×+ ratio
* [ ] V_I.4 Plan v5.1 with items 1-12 locked in; tape-out target
  after FX kernel ships v1.0 + Era IV.5
* [ ] V_I.5 Plan v6 with items 13-15 (ISA + Polygraph Tiles +
  FX1 fast path)
* [ ] V_I.6 Plan v7 with items 16-18 (physics-direct polygraph;
  full multi-die 27-cube; edge-of-FX-applications: Sati-Schreiber
  theorem mechanization, biological electromagnetism simulation,
  etc.)

**Cross-references**: Era IV.5 (multi-level hardware Maxwell→μArch
provides the framework FEU runs in); Era T Day 78.8 catalog
(FEU_hardware site instance); Era V D38.B (energy dimension 23 as
finite model/certificate interface for evaluating FEU adiabatic
recovery claims, not as automatic physical truth); Era VIII D63.A
(Promise/Guard/Fallback for
runtime ENOB / timing / power).

**References**: FEU v5 design document (this repository's
`design_0.3.txt`); SPICE testbenches (`layout/spice/`, 399 files);
24 OSDI compact models (`include/models/`); BSIM-BULK 107.2.2
(28 nm PDK); IGZO_VA Verilog-A model.

---

## Critical path

The non-linear plan has a critical path that gates other work
(updated post Era IV.5 / Era T / Era R / Era W insertions):

```
Era I (polygraph substrate)
  Day 10 → 11 → 12 → 13 → 14 → 15

Era II (kernel retrofit)
  Day 16 → 17 (retrofit cascades)
  Day 18, 19 (parallel)
  Day 20 (close-out)

Era III (sharing cells + stratification + BSP)
  Day 21 → 22 → 23 → 24 → 25 → 25.A (pipe-chain pipeline parallelism)

Era IV (hardware retrofit)
  Day 26 → 27 → 28 → 29 → 30 → 31

Era IV.5 (multi-level hardware polygraph) — INSERTED
  Day 31.5 (Maxwell + RLC) → 31.6 (STA + light cone)
  → 31.7 (Digital + spacetime types) → 31.8 (μArch + side-channels)
  → 31.9 (multi-level calculus + Stokes + Landauer close-out)

Era V (reduction completion)
  Day 32 → 33 (β+η + cubical)
  Day 34 → 35 → 36 → 37 → 38 (FX-unique β rules)
  Day 38.A (Incrementality dim-24 / ILC) — parallel after D38
  Day 38.B (Energy dim-23 / Landauer-style model certificates) —
  parallel after D38
  Day 38.C (Side-channel typing extension) — parallel after D38
  Day 39 (optimal reduction) — parallel
  Day 39.5 (@[strategy(S)] user-facing attribute) — parallel after D39
  Day 40 (close-out)

Era S (semantic substrate / Path 2 staged)
  Day 41 → 42 → 43 → 44 → 45 → 46

Era VI/VII/VIII parallel branches
  Era VI Day 47-53 (auto-proof) — parallel
  Era VII Day 54-58 (WMM)        — parallel
  Era VIII Day 59-63 (refinement feedback) — needs Era V
  Era VIII Day 63.A (Promise/Guard/Fallback) — INSERTED;
                                                load-bearing for
                                                Era IV.5 + FEU-FX

Era IX (OT integration)
  Day 64-68 — needs Era V + Era VI

Era X (∞-frontier)
  Day 69-78 — needs Era V + Era VI

Era T (causal site explicit / temporal substrate) — INSERTED
  Day 78.5 → 78.6 → 78.7 → 78.8 → 78.9
  needs Era I + Era IV.5 + Era X (SDG dependency on Day 72)

Era XI (synthetic physical)
  Day 79-88 — needs Era X + Era T (smooth_manifold site instance)

Era R (reflection layer) — INSERTED
  Day 88.5 → 88.6 → 88.7 → 88.8 → 88.9
  needs Era V (foundational kernel) + Era X Day 75 (synthetic Tait)

Era XII (algorithm discovery)
  Day 89-96 — needs Era IX + Era VI
  Day 93.A (e-graph 4th encoding column) — INSERTED;
                                            cross-Era artifact
                                            (Era IX + V + VI + XII)

Era W (world-as-type layer) — INSERTED
  Day 96.5 → 96.6 → 96.7 → 96.8 → 96.9
  needs Era R (B1-B3 reflection foundations) + Era VII (WMM
  → step-indexed worlds)

Era XIII (beyond beyond)
  Day 97+ exploratory; selective extensions

Verticals A-H + Vertical I (FEU-FX co-design) run parallel to Eras
after Era IV closes; Vertical I in particular pairs with Era IV.5
multi-level hardware framework + Era T FEU_hardware site instance.
```

**Critical path total** (updated):
```
Days 10 → 17 → 31 → 31.9 → 40 → 47 → 62 → 72 → 78.9 → 82 → 88.9
     → 90 → 96.9 ≈ 7-8 years elapsed at single-team pace.
```

**Maximum parallelism**: ~12-18 parallel tracks given staffing
(increased from ~10-15 due to Vertical I + Era IV.5/T/R/W
parallel-feasibility).

**New cross-Era dependency arrows**:
- Era IV.5 → Era V: spacetime-typed Step ctors live on Era IV.5
  multi-level substrate
- Era V D38.A/B → Era IV.5 D31.9: change calculus + energy
  cross-reference into multi-level calculus
- Era VIII D63.A → Era IV.5 + FEU-FX: Promise/Guard/Fallback
  consumed by hardware abstraction-functor soundness conditions
- Era T → Era VII / IV.5 / XI / XII: cross-Era reframings
  (4-instance WMM, multi-level as site stratification, smooth-
  manifold for physics, asymptotic-BigO for discovery)
- Era R → B13 bootstrap: FX-in-FX self-hosting unblocked
- Era W → distributed-systems / file-system / consensus
  verification (selective per application)
- Vertical I → Era IV.5 + Era T: FEU as concrete hardware
  instance of the multi-level + site-parametric framework

---

## Strict-harness extensions

| Era | Gate | Function |
|-----|------|----------|
| I   | STRICT-22 | Polygraph well-formedness (RawPolyTerm/PolyTerm) |
| I   | STRICT-23 | Dim-1 cell typing consistency (Step ⇌ Dim1Cell parity) |
| I   | STRICT-24 | Dim-2 cell parallelism (cd_lemma ⇌ Dim2Cell) |
| I   | STRICT-25 | Dim-3 strategy coherence (pentagon law) |
| III | STRICT-26 | Sharing-cell well-formedness (Lamping fans/brackets/croissants in PolyTerm) |
| IV  | STRICT-27 | Realization equivalence (`⟦impl s⟧ = ⟦s⟧` per HardwareTarget) |
| V   | STRICT-28 | Sharing-graph well-foundedness (optimal reduction) |
| S   | STRICT-29-S1 | Tait reducibility predicate well-formedness (RC inductive) |
| S   | STRICT-30-S2 | ValueTerm closure-purity (no host functions in ctors) |
| S   | STRICT-31-S3 | NbE/Conv decision parity (`Conv t1 t2 ⇔ nbe t1 = nbe t2`) |
| VI  | STRICT-32 | Tactic-as-β termination |
| VII | STRICT-33 | DRF preservation under WMM β |
| VIII| STRICT-34 | Dim-5 refinement-functor well-formedness |
| X   | STRICT-35 | n-cell decidability (∞-groupoid up to n=4) |
| X   | STRICT-36 | Self-reference soundness (synthetic Tait, Sterling 2021) |
| XII | STRICT-37 | Dim-6 algorithm-equivalence well-formedness |
| XII | STRICT-38 | User β-rule confluence verifier (Knuth-Bendix completion) |
| XII | STRICT-39 | User β-rule termination verifier (MPO/DP method) |
| XII | STRICT-40 | User β-rule SR verifier |
| IV.5 | STRICT-41-IV5-Maxwell | Maxwell + RLC polygraph well-formedness; F_M→RLC quasi-static condition |
| IV.5 | STRICT-42-IV5-STA | STA event polygraph; tropical (ℝ⁺,max,+) graded morphisms; light-cone constraint min_delay ≥ length/c_material |
| IV.5 | STRICT-43-IV5-Digital | (Node × Cycle) polygraph; spacetime-typed primitives Charge/Wire/Register/Instruction; Kirchhoff KCL Noether-derived; hazards-as-type-errors |
| IV.5 | STRICT-44-IV5-μArch | μArch + side-channel typing (Timing/Power/EM/Cache/Speculation/Thermal/Acoustic); Spectre/Rowhammer/Meltdown 2-cell witnesses |
| T   | STRICT-45-T-Site | CausalSite well-formedness (parallelism witnesses + structure-flag coherence) |
| T   | STRICT-46-T-Morphism | Site-morphism functoriality + structure preservation + soundness witness |
| T   | STRICT-47-T-Cohesion | Temporal cohesion ◯⊣▷⊣⟐⊣ℑ adjunction triangles + naturality |
| T   | STRICT-48-T-Coverage | Cross-Era reframing coverage (Era VII WMM + IV.5 multi-level + XI physics + XII discovery as site instances) |
| R   | STRICT-49-R-Refl | Reflection roundtrip (reify ; elaborate = .ok ∘ pack at all 75 Term ctors) |
| R   | STRICT-50-R-Tactic | Tactic correctness (successful tactic ⟹ verified Term proof zero-axiom) |
| R   | STRICT-51-R-Bootstrap | B13 bootstrap-readiness (FX-in-FX checker ≡ native kernel) |
| W   | STRICT-52-W-World | World-type well-formedness; effect-as-world-transition iso |
| W   | STRICT-53-W-Effect | Effect migration soundness (existing FX programs ≡ world-typed lifts on observables) |
| W   | STRICT-54-W-Examples | Iris-style verified examples (file system, concurrent counter, consensus stub) zero-axiom |
| IX  | STRICT-55-IX-EGraph | E-graph encoding well-formedness; congruence-closure soundness; saturation termination at depth d ≤ 10 (Willsey et al. 2021) |
| IX  | STRICT-56-IX-Extract | Extraction soundness: argmin-cost representative ∈ e-class (per cost function) |
| V   | STRICT-57-V-Energy | Dimension-23 energy arithmetic; finite EnergyModel certificate checking; conditional Landauer-style lower-bound verification |
| V   | STRICT-58-V-SideChannel | Per-channel constant-trace verification (Timing/Power/EM/Cache/Speculation/Thermal/Acoustic) |
| V   | STRICT-59-V-Incremental | Dimension-24 ILC change calculus; derivative law correctness (Df ≅ ∂f / ∂Δ) |
| VIII| STRICT-60-VIII-PromiseGuard | Promise/Guard/Fallback effect soundness (compile-bound + runtime guard + adaptive fallback) |
| VIII| STRICT-61-VIII-PerChip | Per-chip characterization parameter compatibility (typed against post-fab calibration data) |
| Vertical I | STRICT-62-FEU-Polygraph | FEU POLYGRAPH compute mode soundness |
| Vertical I | STRICT-63-FEU-MerkleHash | Merkle-trie content-addressed cell-hashing correctness |
| Vertical I | STRICT-64-FEU-MultiDie | 27-die ternary cube parallel-strategy distribution |

Each gate ships with the corresponding Era's first day and remains
load-bearing throughout subsequent Eras. **Era S adds 3 gates
specifically for the ValueTerm/NbE infrastructure**, ensuring no
host-function leak (which would invite funext as a requirement) and
no propext-via-quotient leak (which would invite Quot.sound).

---

## Cross-cutting Mathematical Commitments

Preserved verbatim from errratas Part III. These commitments apply
across all Eras and constrain every Day's deliverable.

### §C1. Categorical model

**Choice**: FX is modeled in a **cubical (∞,1)-topos with cohesive
structure**.

**Soundness theorem**:
```
Soundness: if Γ ⊢ t : A in FX, then ⟦t⟧ : ⟦A⟧ in M
```
where M is the chosen cohesive (∞,1)-topos.

**Reference models**:
- **CCHM cubical model**: PSh(□) with cubical structure.
- **ABCFHL Cartesian cubical model**: variant with cleaner regularity.
- **Schreiber's cohesive ∞-topos**: SuperFormalSmooth∞Grpd for
  physics.

### §C2. Universe polymorphism

**Choice**: FX has cumulative Nat-indexed universe levels (D1.2
shipped).

**Predicativity**: FX is **predicative** (no Type:Type, no
impredicative Prop), matching cubical Agda's stance and avoiding
Girard's paradox.

**Univalence at every level**: holds for each universe level
independently.

### §C3. Cohesive structure

**Commitment**: 4-modality cohesion ♭ ⊣ ◇ ⊣ □ ⊣ ♯ extends Schreiber-
Shulman's 3-modality ∫ ⊣ ♭ ⊣ ♯.

**Why 4-modality**: the additional ◇ provides a distinct "diamond"
modality that interpolates between flat and shape, useful for FX's
dimensional grading.

**For physics (Era XI)**: extend to differential cohesion
∫ ⊣ ♭ ⊣ ♯ + ℜ ⊣ ⊝ ⊣ ℑ.

### §C4. Mode theory

**Framework**: MTT (Multimodal Type Theory) by Gratzer-Birkedal-
Cavallo-Mannaa 2020.

**Mode theory**: small 2-category M with:
- Objects = modes (strict, observational, univalent, cohesive♭,
  cohesive♯)
- 1-cells = modalities
- 2-cells = modal transformations (Day D4.0a TwoCell shipped)

### §C5. Equivalence relations

**Per-Era choice**:

| Era | Use | Equivalence |
|-----|-----|-------------|
| I-II | retrofit | Strict isomorphism |
| III | hypergraph | Bisimulation |
| IV | hardware | Observational equivalence on closed terms |
| V | reductions | Diamond + CR |
| S  | semantic substrate | β/η equivalence (Stage 1 Tait, Stage 2 NF equality) |
| VI-VII | tactics, WMM | Trace equivalence |
| VIII | refinement feedback | Cost-tropical equivalence |
| IX | OT | Wasserstein-2 equivalence |
| X | ∞-frontier | Path equivalence (HoTT) |
| XI | physics | Cohomology class equivalence |
| XII | discovery | Asymptotic equivalence |

### §C6. Termination measures

**Standard machinery available**:
- Multiset Path Order (MPO) — Dershowitz 1979
- Lexicographic Path Order (LPO) — Kamin-Lévy 1980
- Recursive Path Order (RPO) — Plaisted 1978
- Polynomial interpretations — Lankford 1979
- Dependency Pair method — Arts-Giesl 2000

**FX commitment**: ship MPO + DP method as primary; LPO as
specialization; polynomial interpretations as backup for
non-orderable cases.

### §C7. Decidability complexity

**Per-judgment bounds** for the bounded/certificate-checked kernel
fragment. Rows involving search or external solvers are budgeted
procedures unless a total checker/certificate is supplied.

| Judgment | Worst-case | Typical-case |
|----------|------------|---------------|
| Type-check `Γ ⊢ t : A` | PSPACE | poly(|t|) |
| Conv `t ≡ t'` | poly via SN+CR | linear in NF size |
| Decidable predicate | depends on instance | constant |
| Refinement obligation | undecidable in general | poly only for bounded certificate-checked fragments |
| Active grade-vector check (target 24 dimensions) | per active dimension | constant only for finite enum dimensions |
| Strategy search (dim 3) | exp in graph size | poly with pruning |
| Hardware retrofit (dim 4) | model-check constant per target | realization-dependent |
| Refinement functor (dim 5) | poly per refinement | poly |
| Algorithm discovery (dim 6) | semi-decidable | exp with ML guidance |

### §C8. Free polygraph operad

**Reference**: Batanin 1998 globular operads.

**Statement**: polygraphs assemble into an **operad** in globular
sets. Rules at dim n+1 are "n-disk" operations. This is the modern
way to specify ∞-categories.

**FX integration**: Era I's polygraph is implicitly an algebra over
the globular operad of constructor-driven dispatch.

### §C9. Initial algebra semantics for HITs

**For each HIT shipped (D3.8-D3.9)**:

| HIT | Initial algebra of |
|-----|---------------------|
| Quot A R | endofunctor F(X) = A + (a, b : A) × R a b × X² |
| propTrunc A | endofunctor F(X) = A + X² (saturated to prop) |
| setTrunc A | endofunctor F(X) = A + X² + ... (to set) |
| S¹ | endofunctor F(X) = 1 + X² + paths-from-base-to-base |
| Pushout f g | endofunctor F(X) = A + B + (a : A) × (b : B) × paths |
| Coequalizer f g | endofunctor with coequalizer paths |
| Suspension A | endofunctor with two basepoints + paths-from-A |

**Universal property**: each HIT is the **initial algebra** of its
corresponding endofunctor, satisfying the recursion principle.

### §C10. Coherence theorems applicable

| Coherence | Applicable Era |
|-----------|----------------|
| MacLane pentagon | Day 14 (strategy assoc) |
| Joyal-Street hexagon | Day 14 (braided strategies) |
| Gurski tricategorical | Era X ((∞,n)-categories) |
| Squier polygraphic | All Eras (rule confluence) |
| Lurie cobordism hypothesis | Era XI (physics) |

---

## Risk register

| Risk | Mitigation |
|------|------------|
| Polygraph retrofit causes regression | Strict performance gates: polygraph form within 5% of tree form; existing benchmarks must stay green |
| (∞,n)-polygraph too abstract for kernel | Limit to n=6 in practice; defer (∞,∞) to Era XIII |
| Hypergraph IR adds memory overhead | Sharing-aware encoding offsets; verified sharing reduces total memory for typical workloads |
| B200 realization requires NVIDIA library trust | TCB extension documented; cross-check via reference implementations; future RISC-V / open-hardware alternatives |
| Sync barrier limits parallelism | Hierarchical sync + speculation + memoization mitigations stacked |
| η + β confluence proof complexity | Geuvers 1992 well-trodden; fallback to Option H par-only η |
| WMM verification too complex | Prior art (CompCert-TSO, Promising Semantics) mature |
| Auto-proof tactics-as-β explode compile times | Per-tactic timeout budgets; ML-guided pruning; incremental cache |
| Refinement feedback false positives | Confidence thresholds + kernel re-verification + user-confirmation gates |
| OT integration adds research-grade complexity | Defer GW + Wasserstein gradient flows to Era XII if Era IX core is sufficient |
| ∞-groupoid coherence beyond dim 4 infeasible | Stop at dim 4; defer higher to Era XIII |
| fx-mtheory needs physics + HoTT collaboration | Engage Schreiber group / n-Lab community; multi-PhD collaboration |
| Algorithm discovery search space explodes | ML-guided pruning; stop-criteria; user-budget-bound search |
| User-extensible β rules introduce subtle bugs | STRICT-35/36/37 gates verify before global commit; sandbox-mode opt-in |
| Lean 4 itself has bugs | Cross-check via Lean4Lean; standard TCB assumption |
| Bootstrapping circularity (FX-in-FX) | Synthetic Tait (Era X Day 75) + Era R reflection (Day 88.5–88.9) layered defenses; full bootstrap is B13 milestone |
| Per-chip ENOB variation (analog accelerator) | Promise/Guard/Fallback effect (Era VIII D63.A) handles compile-time loose bound + runtime measurement + adaptive precision-mode escalation; STRICT-60-VIII-PromiseGuard verifies the pattern |
| F_M→RLC quasi-static condition unmet at high freq | At 5 GHz on 13×17.3 mm die, diam/λ ≈ 0.7 — NOT strict QS regime; F_M→RLC sound only for local metal regions ≤ 3 mm; global wires require transmission-line treatment (Era IV.5 D31.6 STA event polygraph) |
| Iris step-indexed soundness only on constructive fragment | Era W Day 96.7 documents fragment limits; full Iris parity (higher-order classical concurrent invariants) deferred to Era XIII selective extensions per application |
| Reflection / FX-in-FX bootstrap schedule risk | Era R Day 88.5–88.9 depends on Era X Day 75 synthetic Tait being shipped; cascading delay if Era X slips |
| Site-parametric kernel performance degradation | Era T Day 78.5 standardSite_equiv_existing zero-axiom theorem ensures existing FX programs continue with no perf regression; alternative-site programs may have different perf profiles |
| Cell-category parametric extensions cascade | Adding new cell categories (Prob, Hilb, Cont) is foundational rework; deferred to Era XIII selective extensions when applications demand |
| FEU v5.1 / v6 tape-out schedule | Vertical I 18-24 month + 12 month additional for v6; ~3-4 years total to FEU-FX hardware availability; FX kernel work proceeds independently with FEU as planning target |
| Promise/Guard/Fallback false-positive rate at runtime | Adaptive fallback policies (re-calibrate / escalate / reduce-frequency / fall-back-to-digital) provide graceful degradation; runtime monitor tuning per application |
| E-graph saturation explodes at depth d > 10 | Saturation termination theorem (Day 93.A) bounds size; programmer / LLM agent chooses depth budget; Pareto-frontier extraction provides multi-objective optimization |
| Energy dim-23 overclaims physical truth | Landauer-style statements are model theorems over explicit finite thermodynamic models; practical analog hardware has additional kT/C noise (~11.7 µV at 30 pF), PVT variation, and calibration drift; Promise/Guard plus measurement certificates handle runtime reality |
| Side-channel typing incomplete for novel attacks | 7 channels (Timing/Power/EM/Cache/Speculation/Thermal/Acoustic) cover known classes; future attack discoveries require effect catalog extension |
| Multi-die ternary cube (FEU 27-die) latency variance | PAM-3 SerDes 5-10 ns per hop fundamental; Era T site morphisms verify cross-die naturality but cannot eliminate physical latency |
| Counterfactual operators leak observable side effects | Era W Day 96.8 verified non-interference theorem zero-axiom; counterfactual is "imagined" only, no observable mutation of actual world |

---

## Phased commitment levels

**Tier 1 (must ship)**: Eras I-V (Days 10-40) + **Era IV.5
(Days 31.5-31.9)** + **Era V D38.A/B/C extensions** — polygraph
substrate + kernel retrofit + sharing cells / BSP + hardware
retrofit + multi-level hardware polygraph (Maxwell-grounded) +
reduction completion + Incrementality dim-24 + Energy dim-23 as a
finite model/certificate interface + side-channel typing. Without
this, FX is not beyond-frontier and
hardware verification has no honest substrate.

**Tier 2 (should ship)**: Eras VI-IX (Days 47-68) + **Era VIII
D63.A Promise/Guard/Fallback** + **Era IX Day 93.A e-graph (cross-
ref'd from Era XII)** — auto-proof + WMM + refinement feedback +
OT integration + runtime-property handling + 4th encoding column.
This is what makes FX practically dominant and load-bearing for
FEU-FX hardware co-design (Vertical I).

**Tier 3 (productize selectively)**: Era X (Days 69-78) + **Era T
(Days 78.5-78.9)** — ∞-frontier + site-parametric kernel +
temporal cohesion + verified site catalog. Establishes academic
mind-share, unlocks Era XI physics + Era XII discovery as
specific site instances, and provides the parametric foundation
for cross-domain applications (distributed, ML, biology, brain,
economics, climate per Appendix E).

**Tier 4 (research)**: Era XI-XII (Days 79-96) + **Era R reflection
(Days 88.5-88.9)** — synthetic physical mechanization + algorithm
discovery + reflection layer + tactics-as-reflective-programs +
B13 FX-in-FX bootstrap. Builds FX's foundational research
reputation.

**Tier 5 (verticals)**: A-H industrial libraries + **Vertical I
FEU-FX co-design super-accelerator**. Drive adoption + hardware
super-acceleration of FX kernel work.

**Tier 6 (selective extensions)**: **Era W world-as-type (Days
96.5-96.9)** — distributed systems / Iris-style step-indexed
verification / counterfactual reasoning. Selective per
application demand; full Iris parity deferred to Era XIII.

**Tier 7 (speculative)**: Era XIII (Day 97+). Optional. Establishes
FX as research frontier; cell-category-parametric kernel
generalization (Set/Cont/Smooth∞/Prob/Hilb/Vec_R/Type/Lawvere_Th/
Fuzzy/Tropical/Causet/Game per Appendix E) deferred here.

---

## Tier dependency graph

```
Tier 1 (foundational, must ship)
   │
   ├── Tier 2 (practical dominance, should ship)
   │      │
   │      └── Vertical I (FEU-FX co-design, depends on
   │           Tier 1 D31.5-31.9 + Tier 2 D63.A)
   │
   ├── Tier 3 (productize selectively)
   │      │
   │      └── Tier 4 (research)
   │             │
   │             └── Tier 6 (selective extensions, world-as-type)
   │
   └── Tier 5 (verticals A-I, parallel adoption)
```

---

## Bootstrap milestones

* **B0** (pre-Day-10, kernel-sprint v1.0): FX1.check_sound shipped
  (per `kernel-metaplan.md`) — minimal lambda-Pi kernel verified
  zero-axiom; trust anchor for all subsequent Bridge promotions
* **B1** (Day 15, Era I close-out): operadic polygraph substrate
  (`PolyCell`/`RawPolyTerm`/`PolyTerm`) operational at Layer P;
  kernel processes simple FX programs via PolyTerm; STRICT-22/23/24/
  25 green
* **B2** (Day 25, Era III close-out): sharing cells in PolyTerm +
  stratification + BSP execution model verified (subsumes
  HyperTerm)
* **B3** (Day 31, Era IV close-out): B200-cluster execution with
  verified hardware retrofit; cross-architecture equivalence (CPU
  vs B200 vs FPGA produce same NF); 22nd grading dimension
  (Belnap-Dunn FOUR) operational
* **B4** (Day 40, Era V close-out): full kernel reduction surface
  complete (β+η+ι+δ+ζ+proj+cubical+FX-unique β+optimal); every
  type former in FX has both β AND η as Step ctor + dim-1 cell
* **B5** (Day 43, Era S Stage 1): **M04 strong normalization
  shipped** via Tait reducibility (`RC : Ty → Term → Prop` +
  fundamental theorem); #1273 closed
* **B6** (Day 46, Era S Stage 2): **ValueTerm encoding +
  decidable Conv via NF equality** shipped; third encoding column
  live; ValueTerm closures structurally η-normal by construction
* **B7** (Day 53, Era VI close-out): auto-proof tactics handle
  80%+ of common refinement obligations
* **B8** (Day 63, Era VIII close-out): refinement feedback API
  operational for LLM agents
* **B9** (Day 68, Era IX close-out): ML-guided polygraph search
  with kernel verification
* **B10** (Day 75, Era X Day 75): synthetic Tait — kernel proves
  itself internally (B5 was external-Lean SN; B10 is FX-internal)
* **B11** (Day 88, Era XI close-out): fx-mtheory v0.1 — first
  kernel-verified explicit M-theory-inspired model fragment;
  Sati-Schreiber-style theorem zero-axiom inside the encoded model
* **B12** (Day 96, Era XII close-out): full algorithm-discovery
  operational on representative benchmarks; user-extensible β
  rules with STRICT-35/36/37 verification gates
* **B13** (Day 88.9 → 100+, Era R close-out + bootstrap):
  full FX-in-FX bootstrap; compiler self-hosts via reflection
  (`Term.reify` + `ReflTerm.elaborate` + Tactic monad); self-
  consistency theorem (FX-in-FX checker ≡ native Lean 4 kernel
  on inputs)
* **B14** (Day 31.9, Era IV.5 close-out): multi-level hardware
  polygraph operational (Maxwell → RLC → STA → Digital → μArch with
  verified abstraction functors); spacetime-typed primitives
  Charge / Wire / Register / Instruction; discrete Stokes at the
  formal-model level; Landauer/energy via checked finite-model
  certificates
* **B15** (Day 78.9, Era T close-out): site-parametric kernel
  operational (`Term : CausalSite → Ctx → Ty → RawTerm → Type`);
  10+ site instances in catalog; cross-Era reframings (Era VII,
  IV.5, XI, XII) verified; temporal cohesion ◯⊣▷⊣⟐⊣ℑ
* **B16** (Day 88.9, Era R close-out): reflection layer +
  tactics-as-reflective-programs + macros + DSL embedding +
  FX-in-FX self-hosting (= B13 milestone unblocked from this)
* **B17** (Day 96.9, Era W close-out): world-as-type layer on
  constructive + step-indexed fragment; Iris-style Kripke
  invariants; verified file-system / concurrent-counter / consensus
  examples
* **B18** (FEU-FX vertical year-1): FEU v5.1 with 12 cheap
  adjustments (POLYGRAPH compute mode, Merkle cell-hashing,
  time-triggered FX kernel scheduler, multi-die cube, PAM-3 native
  PolyTerm transport, embedded-calibration polygraph soundness,
  cubical IGZO-plane intervals, coupled-settling fix-point primitive,
  per-tile FX kernel state, effect-bit graded extension, dual
  Term+ValueTerm IGZO storage, NCL session-type ISA primitives);
  ~10⁹ polygraph cells/μs target verified
* **B19** (FEU-FX vertical year-2+): FEU v6 with 3 medium-cost
  hardware additions (Trip-A+/S extended ISA, 8 dedicated Polygraph
  Tiles, FX1.check_sound hardware fast path); 27-die ternary cube
  multi-die scaling; full Sati-Schreiber theorem mechanization
  hardware-accelerated

Each milestone is a major release event. B0-B12 sequence the
v1.0+ trust spine; B13-B19 sequence the parametric / reflective /
worldly / hardware-co-designed extensions.

---

## Acceptance criteria for "polygraph-substrate FX"

By Day ~96.9 (Era W close-out), FX should uncontestably be
polygraph-substrate + parametric + reflective + worldly iff:

1. ✓ FX1.check_sound shipped zero-axiom (B0; v1.0 trust anchor
   from kernel-sprint)
2. ✓ Operadic PolyTerm at Layer P with verified embedding to
   RawTerm/Term + sharing-cell extension (subsumes HyperTerm)
3. ✓ Existing kernel operations all expressible as polygraph cells
4. ✓ Stratified BSP execution model verified
5. ✓ B200 cluster realization with cross-architecture equivalence
   (CPU vs B200 vs FPGA produce same NF)
6. ✓ 22nd grading dimension (Belnap-Dunn FOUR) operational
7. ✓ Full β+η+ι+δ+ζ+proj+cubical+FX-unique reduction surface;
   every type former has β AND η as Step ctor + dim-1 cell
8. ✓ M04 strong normalization shipped (Path 2 Stage 1, Tait RC)
9. ✓ ValueTerm encoding + decidable Conv via NF equality (Path 2
   Stage 2); β/η on ValueTerm structurally absorbed
10. ✓ Auto-proof tactics shipping as polygraph cells
11. ✓ WMM verified across 3+ architectures
12. ✓ Refinement feedback API with structured LLM output
13. ✓ OT-augmented soft search with verified extraction
14. ✓ ∞-groupoid coherences at finite dimensions
15. ✓ Synthetic Tait operational (kernel proves itself internally)
16. ✓ fx-mtheory mechanizing an explicit Sati-Schreiber-style model
   theorem, with physical adequacy handled by comparison/search
   certificates
17. ✓ Algorithm discovery operational on at least one benchmark
18. ✓ User-extensible β-rule database with STRICT-35/36/37 gates
19. ✓ All theorems zero-axiom per `computability-rules.md`
20. ✓ **Multi-level hardware polygraph (Era IV.5)**: Maxwell at
    Level 0 + RLC + STA + Digital + μArch with 4 verified
    abstraction functors as explicit models; spacetime-typed
    primitives Charge/Wire/Register/Instruction; discrete Stokes as
    formal calculus theorem; Landauer/energy only through explicit
    finite-model certificates
21. ✓ **Site-parametric kernel (Era T)**: `Term @ S` for
    finitely-presented (∞,n)-polygraph sites that supply the
    required finite generators, typed source/target maps,
    substitution/renaming actions, reduction measure, and
    critical-pair witnesses; 10+ site instances in catalog;
    temporal cohesion ◯⊣▷⊣⟐⊣ℑ; 8-modality spacetime cohesion
    combining with spatial ♭⊣◇⊣□⊣♯
22. ✓ **Reflection layer (Era R)**: ReflTerm + Term.reify +
    ReflTerm.elaborate roundtrip zero-axiom at all 75 ctors;
    Tactic monad with verified-correctness theorem; macros + DSL
    embedding; FX-in-FX self-hosting (B13 unblocked)
23. ✓ **World-as-type (Era W)**: World sealed interface +
    peek/poke + Iris-style step-indexed Kripke worlds
    (constructive fragment);
    effect-as-world-transition iso; counterfactual operators with
    verified non-interference
24. ✓ **Four encoding columns**: Tree + PolyTerm + ValueTerm +
    EGraph with verified subsumption lattice + extraction
25. ✓ **24-dim grade vector**: 21 original + 22 (consistency/Belnap-
    Dunn) + 23 (energy/Landauer) + 24 (incrementality/ILC)
26. ✓ **Side-channel typing**: 7 channels (Timing/Power/EM/Cache/
    Speculation/Thermal/Acoustic) as effect annotations with
    SideChannelFree composite type
27. ✓ **Promise/Guard/Fallback**: runtime properties (ENOB,
    timing, power, calibration accuracy) handled via compile-time
    loose bound + runtime guard + adaptive fallback per Era VIII
    extension D63.A
28. ✓ **Per-chip characterization**: type-parametric in post-fab
    calibration data (FG-AUTOCAL cells) so per-die operations
    typecheck against their characterization
29. ✓ **FEU-FX vertical**: FEU v5.1 with 12 cheap polygraph-aware
    adjustments operational; ~10⁹ polygraph cells/μs verified

If 25+ of 29 hold, FX has demonstrably achieved the full
polygraph-substrate + parametric-site + reflective + worldly
+ hardware-co-designed vision with four-encoding-column
architecture and 24-dim grade vector.

---

## Cross-references

* `kernel-sprint.md` — Day 0–9 sprint (current MVP path to v1.0)
* `kernel-metaplan.md` — FX1/FX0 trust spine (orthogonal axis;
  load-bearing for "Root-FX1" promotion in this roadmap)
* `ROADMAP.md` — current-day phasing within v1.0 sprint
* `roadmap-beyond-frontier.md` — superseded by this document;
  retained for historical reference
* `errratas.md` — **fully merged into this document** (Part I, Part
  VI, Appendix C, Bibliography); file deleted post-merge
* `computability-rules.md` — invariants maintained across all Eras
  (BHK ∞-categorical interpretation, 22-dim decidability, strict
  harness)
* `AXIOMS.md` — strict zero-axiom commitment (no exceptions)
* `WORKING_RULES.md` — kernel discipline applicable to every new
  cell introduced in any Era
* `ARCHITECTURE.md` — 13-layer DAG (to be updated with Layer P
  + ValueTerm column)

---

## Appendix A — The dimensional anatomy of FX's polygraph

For reference, the dimensions of the (∞,6)-polygraph FX targets:

| Dim | Cells | Computational role | GEMM-encodable? |
|-----|-------|---------------------|------------------|
| 0 | terms, types, contexts | data layer | yes (sparse adjacency) |
| 1 | rewrites (Step ctors) | reduction layer | yes (rule database matrix) |
| 2 | confluence proofs (cd_lemma) | equivalence-of-rewrites | yes (Squier coherence) |
| 3 | strategy equivalences | search layer | yes (tropical semiring) |
| 4 | hardware fibres | retrofit layer | yes (per-target tensor) |
| 5 | refinement functors | feedback layer | yes (constraint→speedup matrix) |
| 6 | algorithm equivalences | discovery layer | partial (cross-class costs) |

Each dimension contributes its own cost reduction:
- Dim 3: ~10× over naive compilation
- Dim 4: ~3× via hardware-specialization
- Dim 5: ~5× via refinement (when programmer/LLM cooperates)
- Dim 6: ~?× — can be infinite (cross-complexity-class win)

Composed: **150× speedup over naive compilation**, before
algorithm-rewriting at dim 6.

---

## Appendix B — Computational substrate summary

Every dimension of the polygraph reduces to **idempotent semiring
matrix algebra**:

- (Bool, ∨, ∧) for reachability / decidability
- (ℝ̂, min, +) for cost / shortest-path
- (LogSumExp, ε) for soft / differentiable search
- (BigO, ⊕, ⊗) for complexity-class comparison
- Custom semirings for refinement evaluation, charge quantization
  (Burnside ring), grade arithmetic

This unification — same hardware kernel, multiple semiring
applications — is what makes the SHK-B200 design payoff
**multiplicative across all of FX's verticals**.

---

## Appendix C — Reduction Zoo Catalog

Preserved verbatim from errratas Part IV. Full enumeration of all
reductions committed at the lowest level (Layer P operadic
polygraph). This Appendix is the source-of-truth reference for which
β/η/ι/δ/ζ/proj rules ship in which Era.

### §R1. Lambda calculus reductions

```
β-app:        app (lam b) a   →  b[a / 0]
β-appPi:      appPi (lamPi b) a   →  b[a / 0]
η-lam:        lam (app f.weaken (var 0))   →  f
η-lamPi:      lamPi (app f.weaken (var 0))   →  f
ζ-let:        let x = a in b   →  b[a / x]
δ-def:        c (def)   →  body_of(c)
```

### §R2. Inductive type reductions

```
ι-natElim-zero:    natElim natZero z s   →   z
ι-natElim-succ:    natElim (natSucc n) z s   →   s n (natElim n z s)
ι-natRec-zero:     natRec natZero z s   →   z
ι-natRec-succ:     natRec (natSucc n) z s   →   s (natRec n z s)
ι-listElim-nil:    listElim listNil n c   →   n
ι-listElim-cons:   listElim (listCons h t) n c   →   c h t (listElim t n c)
ι-boolElim-true:   boolElim boolTrue th el   →   th
ι-boolElim-false:  boolElim boolFalse th el   →   el
ι-optionMatch-none: optionMatch optionNone n s   →   n
ι-optionMatch-some: optionMatch (optionSome v) n s   →   s v
ι-eitherMatch-inl: eitherMatch (eitherInl v) l r   →   l v
ι-eitherMatch-inr: eitherMatch (eitherInr v) l r   →   r v
```

### §R3. Pair / Σ type reductions

```
β-fst-pair:      fst (pair a b)   →   a
β-snd-pair:      snd (pair a b)   →   b
η-pair:          pair (fst p) (snd p)   →   p
β-Σ-fst:         Σ.fst (Σ.intro a b)   →   a
β-Σ-snd:         Σ.snd (Σ.intro a b)   →   b
η-Σ:             Σ.intro (Σ.fst p) (Σ.snd p)   →   p
```

### §R4. Record reductions

```
β-recordProj:    recordProj (recordIntro fields) k   →   fields[k]
η-record:        recordIntro {f_1 := r.f_1, ..., f_n := r.f_n}   →   r
```

### §R5. Identity type reductions

```
β-idJ-refl:      idJ (refl x) base   →   base
β-J-refl:        J motive (refl x) base   →   base
```

### §R6. Cubical reductions

```
β-pathApp-pathLam: pathApp (pathLam body) i   →   body[i / 0]
β-transpRefl:    transp (pathLam A.weaken) src   →   src
β-transpPi:      transp (pathLam (pi A B)) f   →   lam-app contractum
β-transpSigma:   transp (pathLam (sigma A B)) p   →   pair contractum
β-transpUnit:    transp (pathLam unit.weaken) ()   →   ()
β-transpBool:    transp (pathLam bool.weaken) b   →   b
β-transpNat:     transp (pathLam nat.weaken) n   →   n
β-transpListType: transp (pathLam (list A)) xs   →   map (transp A) xs
β-hcompCap:      hcomp sides (just-cap) at i=0   →   cap
β-glueElim:      glueElim (glueIntro b _)   →   b
β-uaToEquiv-refl: uaToEquiv (refl _)   →   idEquiv
ua-β:            transp (uaToEquiv e) src   →   e.fwd src
```

### §R7. Modal reductions

```
β-modElim-modIntro: modElim (modIntro v)   →   v
η-modal:           modIntro (modElim m)   →   m  (when allowed)
β-subsume-modIntro: subsume (modIntro v)   →   v_in_target_mode
```

### §R8. Effect reductions

```
β-effectHandle:    handle (perform op args) k   →   handler.case_op args k
β-effectErase:     g (f : T with E)   →   g (f : T)  (when g doesn't observe E)
```

### §R9. Refinement reductions

```
β-refineIntro:     refineIntro v p   →   v  (with proof p attached)
β-refineElim:      refineElim (refineIntro v p)   →   v
β-refineNarrow:    (x : {n : ℕ | P n}).inner   →   x
                   (when P n decidable and proven)
```

### §R10. Cross-mode reductions (FX-unique)

```
β-modeCoerce:      coerce_strict_to_obs A x   →   x_in_obs
                   (when A is mode-uniform)
β-modeCoerce-back: coerce_obs_to_strict A x   →   x_in_strict
                   (when A is observationally-classical)
```

### §R11. Hardware bit-level reductions

```
β-bits-concat-proj: bits {a, b}[k:0]   →   slice(a, b, k, 0)
β-bits-zero-ext:    zext n (bits b)   →   bits (b ++ 0^n)
β-bits-sign-ext:    sext n (bits b)   →   bits (b ++ msb(b)^n)
β-bits-slice-merge: merge (slice a) (slice b) [k:0] [m:k+1]   →   slice (a ++ b)
β-bits-reduce:      reduce_op (bits b)   →   reduced_value
```

### §R12. Grade-aware reductions (FX-unique)

```
β-linear-consume:  consume(x) ; e[x]   →   consume(x) ; e[absurd]
β-grade-erase:     (x : T)_0 ; e   →   e  (grade-0 erased after consume)
β-grade-coerce:    (x : T)_g ; e   →   (x : T)_g' ; e[grade_coercion]
                   (when grade subsumption holds)
```

### §R13. WMM reductions (Era VII)

```
β-relax-relax-reorder:  load(x)_R ; load(y)_R   →   load(y)_R ; load(x)_R  (TSO)
β-acquire-fence-elide:  acquire ; expr   →   expr  (when SC-DRF)
β-release-fence-elide:  expr ; release   →   expr  (when SC-DRF)
β-rmw-fuse:             load(x) ; modify ; store(x)   →   atomic-RMW(x, modify)
```

### §R14. Tactical reductions (Era VI)

```
β-tactic-decide:    decide P   →   Decidable P   (when constructive)
β-tactic-omega:     omega goal   →   proof  (when Presburger fragment)
β-tactic-linarith:  linarith goal   →   proof  (when linear arithmetic)
β-tactic-ring:      ring goal   →   proof  (when ring equation)
β-tactic-field:     field goal   →   proof  (when field equation)
β-tactic-polyrith:  polyrith goal   →   proof  (when polynomial)
β-tactic-aesop:     aesop goal   →   proof  (when tractable)
```

### §R15. Confluence properties

| Reduction family | Confluence | Termination |
|------------------|------------|-------------|
| §R1 (β, η, ζ, δ) | CR (Geuvers 1992 for βη) | SN (Tait reducibility) |
| §R2 (ι recursors) | CR (constructor-driven) | SN (structural recursion) |
| §R3 (pair Σ) | CR | SN (structural) |
| §R4 (record) | CR | SN |
| §R5 (identity) | CR | SN |
| §R6 (cubical) | CR (CCHM 2017) | SN (CCHM normalization) |
| §R7 (modal) | CR (Gratzer-Birkedal) | SN |
| §R8 (effect) | CR (Pretnar handlers) | SN with productivity |
| §R9 (refinement) | CR via Decidable | SN |
| §R10 (mode) | CR (decidable mode-uniformity) | SN |
| §R11 (bits) | CR (bit-vector decidable) | SN |
| §R12 (grade) | CR (grade arithmetic decidable) | SN |
| §R13 (WMM) | CR per WMM axioms | SN |
| §R14 (tactics) | CR (tactic determinism) | SN with timeout budget |

---

## Bibliography

Preserved verbatim from errratas Part V.

### Foundational

- **Burroni 1993**, "Higher dimensional word problems with applications to equational logic", TCS 115.
- **Métayer 2003**, "Resolutions by polygraphs", Theory and Applications of Categories 11.
- **Squier 1987**, "Word problems and a homological finiteness condition for monoids", JPAA 49.
- **Métayer 2008**, "Cofibrant objects among higher-dimensional categories", HHA 10.
- **Lafont 1990**, "Interaction nets", POPL.

### Confluence + Termination

- **Newman 1942**, "On theories with a combinatorial definition of equivalence", Annals of Math.
- **Hindley 1969**, "An abstract form of the Church-Rosser theorem", JSL.
- **Tait 1967, Martin-Löf 1972**, parallel reduction CR.
- **Knuth-Bendix 1970**, "Simple word problems in universal algebras", in Computational Problems in Abstract Algebra.
- **Dershowitz 1979**, "A note on simplification orderings", IPL 9.
- **Arts-Giesl 2000**, "Termination of term rewriting using dependency pairs", TCS 236.

### Lambda calculus + interaction nets

- **Tait 1967**, intensional models for SN.
- **Lévy 1978**, "Réductions correctes et optimales dans le lambda-calcul", PhD thesis.
- **Lamping 1990**, "An algorithm for optimal lambda calculus reduction", POPL.
- **Asperti-Mascari-Guerrini 1998**, "BOHM: A simple lambda calculus compiler", JFP.
- **Klop 1980**, "Combinatory reduction systems", PhD thesis (βη confluence).
- **Geuvers 1992**, "The Calculus of Constructions and Higher Order Logic", PhD thesis (βη SN for CC).

### Type theory + HoTT

- **Martin-Löf 1984**, "Intuitionistic Type Theory" (Bibliopolis).
- **HoTT-book 2013**, "Homotopy Type Theory: Univalent Foundations of Mathematics".
- **CCHM 2017**, Cohen-Coquand-Huber-Mörtberg, "Cubical Type Theory".
- **ABCFHL 2019**, Angiuli-Brunerie-Coquand-Favonia-Harper-Licata, "Syntax and Models of Cartesian Cubical Type Theory".
- **Sterling 2021**, PhD thesis on synthetic Tait computability.
- **Riehl-Shulman 2017**, "A type theory for synthetic ∞-categories".

### Modal type theory

- **Gratzer-Birkedal-Cavallo-Mannaa 2020**, "Multimodal Dependent Type Theory" (MTT).
- **Schreiber 2013**, "Differential cohomology in a cohesive ∞-topos".
- **Schreiber-Shulman 2014**, "Quantum gauge field theory in cohesive homotopy type theory".
- **Lawvere 1991**, axiomatic cohesion.

### Graded + linear

- **Atkey 2018**, "Syntax and Semantics of Quantitative Type Theory".
- **Wood-Atkey 2022**, "A Linear Algebra Approach to Linear Metatheory".
- **McBride 2016**, "I Got Plenty o' Nuttin'" (graded modal types).
- **Riley 2022**, PhD thesis on linear HoTT.

### NbE / Tait reducibility / synthetic computability

- **Berger-Schwichtenberg 1991**, "An inverse of the evaluation functional for typed λ-calculus", LICS.
- **Abel 2013**, "Normalization by Evaluation: Dependent Types and Impredicativity", Habilitation.
- **Coquand 1996**, "An algorithm for type-checking dependent types", SCP 26.
- **Sterling-Harper 2021**, "Logical Relations as Types: Proof-Relevant Parametricity for Program Modules", JACM.
- **Sterling 2021**, "Higher-order functions and Brouwer's thesis", JFP (synthetic Tait computability).
- **Carneiro lean4lean**, mechanized Lean 4 kernel reference (Tait reducibility precedent).

### Optimal transport

- **Cuturi 2013**, "Sinkhorn distances: Lightspeed computation of optimal transport", NeurIPS.
- **Mémoli 2011**, "Gromov-Wasserstein distances and the metric approach to object matching".
- **Peyré-Cuturi 2019**, "Computational Optimal Transport".
- **Jordan-Kinderlehrer-Otto 1998**, "The variational formulation of the Fokker-Planck equation".

### Memory models

- **Adve-Hill 1990**, "Weak ordering — a new definition".
- **Sevcik 2009**, PhD thesis on CompCert-TSO.
- **Kang-Hur-Lahav-Vafeiadis 2017**, "A promising semantics for relaxed-memory concurrency", POPL.
- **Lahav-Vafeiadis 2017**, "Repairing sequential consistency in C/C++11".

### Physics mechanization

- **Sati-Schreiber 2019**, "Equivariant Cohomotopy implies orientifold tadpole cancellation", arXiv:1909.12277.
- **Schreiber 2018**, "Differential cohomology in a cohesive ∞-topos".
- **Lurie 2009**, "Higher Topos Theory".
- **Lurie 2017**, "Higher Algebra".

### Algorithm discovery

- **AlphaTensor (Fawzi et al. 2022)**, "Discovering faster matrix multiplication algorithms with reinforcement learning", Nature.
- **Solar-Lezama 2008**, PhD thesis on sketch-style synthesis.
- **Pugh 1991**, "The Omega test: a fast and practical integer programming algorithm for dependence analysis".

### Strict harness

- All STRICT-1 through STRICT-64 gates documented per Era; foundational principles in `computability-rules.md`.

### Multi-level hardware (Era IV.5)

- **Jackson 1999**, "Classical Electrodynamics" 3rd ed., §6.7 (quasi-static expansion).
- **Yee 1966**, "Numerical solution of initial boundary value problems involving Maxwell's equations in isotropic media", IEEE Trans. Antennas Propag. (FDTD origin).
- **Taflove-Hagness 2005**, "Computational Electrodynamics: The Finite-Difference Time-Domain Method", 3rd ed.
- **Frankel 2011**, "The Geometry of Physics: An Introduction" 3rd ed. (Faraday tensor, gauge invariance).
- **Sapatnekar 2004**, "Timing", Springer.
- **Brummayer-Biere 2009**, "Boolector: An efficient SMT solver for bit-vectors and arrays", TACAS (QF_BV theory).
- **Hennessy-Patterson 6th ed.**, "Computer Architecture: A Quantitative Approach" §C.2 (pipelining hazards).
- **Tofte-Talpin 1997**, "Region-based memory management", Information & Computation (analog for linear-resource discipline).
- **Spivak 1965**, "Calculus on Manifolds" (Stokes theorem).
- **Hirani 2003**, "Discrete Exterior Calculus", PhD thesis Caltech.
- **Bobenko-Suris 2008**, "Discrete Differential Geometry: Integrable Structure", AMS.

### Side-channel attacks + verified constant-time (Era IV.5 D31.8 + V D38.C)

- **Bernstein 2005**, "Cache-timing attacks on AES" (technical report).
- **Yarom-Falkner 2014**, "FLUSH+RELOAD: A High Resolution, Low Noise, L3 Cache Side-Channel Attack", USENIX Security.
- **Kocher et al. 2019**, "Spectre Attacks: Exploiting Speculative Execution", IEEE S&P (CVE-2017-5753, -5715).
- **Lipp et al. 2018**, "Meltdown: Reading Kernel Memory from User Space", USENIX Security (CVE-2017-5754).
- **Kim et al. 2014**, "Flipping Bits in Memory Without Accessing Them: An Experimental Study of DRAM Disturbance Errors", ISCA (Rowhammer).
- **Kwong-Genkin-Gruss-Yarom 2020**, "RAMBleed: Reading Bits in Memory Without Accessing Them", IEEE S&P.
- **Almeida-Barbosa-Barthe-Dupressoir 2016**, "Verifying Constant-Time Implementations", USENIX Security.
- **Sevcik 2009**, "CompCert-TSO: A verified compiler for relaxed-memory concurrency", PhD thesis Cambridge.

### Causal sites + temporal type theory (Era T)

- **Burroni 1993**, "Higher dimensional word problems with applications to equational logic", TCS 115.
- **Métayer 2008**, "Cofibrant objects among higher-dimensional categories", HHA 10.
- **Mac Lane 1971**, "Categories for the Working Mathematician", Springer §VII (monoidal).
- **Joyal-Street 1993**, "Braided tensor categories", Adv. Math.
- **Selinger 2007**, "Dagger compact closed categories and completely positive maps", ENTCS.
- **Bénabou 1967**, "Introduction to bicategories", Reports of the Midwest Category Seminar.
- **Coecke-Duncan 2008**, "Interacting quantum observables: categorical algebra and diagrammatics" (POPL ZX-calculus).
- **Schultz-Spivak-Vasilakopoulou 2017**, "Dynamical systems and sheaves", arXiv:1609.08086.
- **Sorkin-Bombelli 1987**, "Spacetime as a causal set", Phys. Rev. Lett. 59:521.
- **Henson 2009**, "The Causal Set Approach to Quantum Gravity", in Approaches to Quantum Gravity, ed. Oriti.
- **Leroy 2009**, "Formal verification of a realistic compiler", CACM (CompCert).
- **Lurie 2009**, "Higher Topos Theory", Princeton (∞-functor framework).

### Temporal cohesion + later modality (Era T D78.7)

- **Nakano 2000**, "A modality for recursion", LICS (later modality ▷).
- **Schreiber 2013**, "Differential cohomology in a cohesive ∞-topos", arXiv:1310.7930.
- **Schreiber-Shulman 2014**, "Quantum gauge field theory in cohesive homotopy type theory", QPL.
- **Bahr-Graulund-Møgelberg 2019**, "Simply RaTT: A fitch-style modal calculus for reactive programming without space leaks", ICFP.
- **Birkedal-Mogelberg-Schwinghammer-Stovring 2013**, "First steps in synthetic guarded domain theory", LICS.

### Reflection in DTT (Era R)

- **Boutin 1997**, "Using reflection to build efficient and certified decision procedures", TYPES.
- **Christiansen-Brady 2016**, "Elaborator reflection: extending Idris in Idris", ICFP.
- **Sozeau et al. 2020**, "MetaCoq: A certified meta-programming framework for Coq", POPL/JAR 2024.
- **Ziliani et al. 2015**, "Mtac: A monad for typed tactic programming in Coq", ICFP.
- **Mahboubi-Strub 2016**, "Mathematical Components reflection", chapter in "Mathematical Components" book.
- **Limperg 2023**, "Aesop: White-Box Best-First Proof Search for Lean".

### World-as-type / Iris (Era W)

- **O'Hearn-Reynolds 2001**, "Algebra-vantage origin of separation logic", LICS.
- **Plotkin-Power 2002**, "Notions of computation determine monads", FoSSaCS (algebraic effects).
- **Bauer-Pretnar 2015**, "Programming with algebraic effects and handlers", JLAMP.
- **Lindley-McBride-McLaughlin 2017**, "Do unto others", JFP (effects + handlers).
- **Smolka et al. 2020**, "Algebraic effect handlers in Coq", ITP.
- **Jung-Krebbers-Jourdan-Bizjak-Birkedal-Dreyer 2018**, "Iris from the ground up: A modular foundation for higher-order concurrent separation logic", JFP.
- **Krebbers et al. 2017**, "Interactive proofs in higher-order concurrent separation logic", POPL.
- **Jung-Sieczkowski-Birkedal 2017**, "HOCAP: Higher-order concurrent abstract predicates", ESOP.

### E-graphs / equality saturation (Era XII Day 93.A)

- **Willsey-Nandi-Wang-Stepp-Tatlock-Panchekha 2021**, "egg: Fast and extensible equality saturation", POPL.
- **Tate-Stepp-Tatlock-Lerner 2009**, "Equality saturation: a new approach to optimization", POPL.
- **Nelson-Oppen 1979**, "Simplification by cooperating decision procedures", TOPLAS (congruence closure).
- **Detlefs-Nelson-Saxe 2005**, "Simplify: A theorem prover for program checking", JACM.

### Incrementality / change calculus (Era V D38.A)

- **Cai-Giarrusso-Rendel-Ostermann 2014**, "A theory of changes for higher-order languages: Incrementalizing λ-calculi by static differentiation", ICFP.
- **Hammer-Acar 2007**, "Self-adjusting computation", PhD thesis CMU.
- **Cockett-Cruttwell-Lemay 2014**, "Differential categories", Math. Struct. Comput. Sci.

### Energy / Landauer / reversible computing (Era V D38.B)

- **Landauer 1961**, "Irreversibility and heat generation in the computing process", IBM J. Res. Dev.
- **Bennett 1973**, "Logical reversibility of computation", IBM J.
- **Fredkin-Toffoli 1982**, "Conservative logic", Int. J. Theor. Phys.
- **Frank 2017**, "Foundations of generalized reversible computing", RC.

### Promise/Guard/Fallback (Era VIII D63.A)

- Synthesis from gradual-typing literature: Siek-Taha 2006 (gradual typing); Garcia-Clark-Tanter 2016 (abstracting gradual typing); Findler-Felleisen 2002 (contracts for higher-order functions).

### FEU-FX co-design (Vertical I)

- FEU v5 design document (`design_0.3.txt` in this repository, ~2300 lines).
- 399 SPICE testbenches (`layout/spice/`).
- 24 OSDI compact models (`include/models/`) compiled via OpenVAF-Reloaded.
- BSIM-BULK 107.2.2 (28 nm PDK, upstream).
- IGZO_VA Verilog-A model (custom, calibrated to COMSOL at 3 bias points).

---

## Appendix D — Diabolical implications catalog

A catalog of theorem-shaped claims that follow from the Era I-W
+ FEU-FX framework. Each is stated precisely, with a refutability
condition. Most are research-grade conjectures; a few are
nearly-provable from existing Era machinery. Documentation only —
not implementation tasks.

### D.1 Site-parametric Term as meta-language for type theories

```
Conjecture (Site-meta-language): For every dependently-typed system L
with a finite/certificate-checkable polygraphic presentation and the
Era T site-transfer hypotheses (typed source/target, substitution,
renaming, reduction measure, critical-pair witnesses), ∃ a CausalSite
S(L) such that:
  Term @ S(L) conservatively embeds the represented fragment of L.

Specific instances:
  Site_MLTT     ≅ Martin-Löf TT (Π/Σ/Id, no path types)
  Site_HoTT     ≅ HoTT (paths invertible)
  Site_cubical  ≅ CCHM cubical TT
  Site_linear   ≅ Linear logic
  Site_modal4   ≅ Schreiber 4-modality cohesion
  Site_quantum  ≅ ZX-calculus (dagger compact, Coecke-Duncan 2008)
```
Refutability: find a finite/certificate-checkable represented
fragment L for which no site satisfying the Era T transfer hypotheses
admits a conservative embedding.

### D.2 Verified compilers as site morphisms (CompCert-generalized)

```
Conjecture / design target (Compiler-as-morphism, Leroy 2009
generalized): A verified compiler from Term @ SourceSite to Term @
TargetSite is represented by a verified site morphism plus a
soundness witness:
  Compiler(Source, Target) := SiteMorphism Source Target
                              with cond_F = "semantic preservation"

Cross-architecture (CPU vs B200 vs FPGA per Era IV D31.3) is the
naturality square of these morphisms.
```
Refutability: find a semantics-preserving compiler optimization for
the represented fragment that cannot be encoded as a site morphism
without adding unjustified structure.

### D.3 CAP theorem as cohomological obstruction

```
Theorem (CAP-as-cohomology):
For Site_dist with N processes and partition P modeled as 2-cocycle,
  Consistency ∧ Availability ∧ Partition-tolerance
  ⟺ [P]_consistency = 0 in H¹(Site_dist; ConsistencyConstraint)

Generic partitions yield non-zero classes ⟹ CAP impossibility.
```
Consensus protocols (Paxos, Raft, BFT) are specific cocycle
splittings; provably-optimal consensus = cohomology-class-minimal.

### D.4 Quantum mechanics as one specific site choice

```
For Site_quantum := dagger compact symmetric monoidal on f.d. Hilbert:
  Term @ Site_quantum ≅ ZX-calculus (Coecke-Duncan 2008)
  Step in Site_quantum ≅ ZX rewrite rules
  Decoherence : Site_quantum → Site_classical (non-invertible)

Quantum advantage: observable in Site_quantum whose pre-image in
Site_classical requires super-poly time; complete proof of
BQP ≠ BPP reduces to a theorem about specific site morphisms.
```

### D.5 Compiler hallucinates verified mathematics

```
With Era XII user-extensible β-rules + Era IX ML-guided OT polygraph
search + STRICT-35/36/37 verification gates:
  Discoverer : MLAgent → ProposedRule → {Verified | Refused}
  Verified ⟹ rule preserves SR ∧ confluent ∧ terminating
  Refused ⟹ explicit critical-pair / counterexample witness

For initial S₀ + budget B + ML model M:
  Th(S₀, B, M) ⊋ Th(S₀)  monotonically in B
```
Empirically testable: define the function, run the experiment,
measure theorem-set growth.

### D.6 Bugs as missing 2-cells, debugging as 2-cell construction

```
Bug := unwanted Step bad : t → t' with ¬ P(t')
Fix := 2-cell α : bad ⇒ correct in polygraph dim 2

Patch theory (Mimram-Di Cosmo 2013) generalizes from specific
languages to ALL programs.
Git becomes a 2-category (patches as 1-cells, three-way merges as
2-cell compositions).
Two patches commute iff their 2-cells satisfy interchange
(Eckmann-Hilton).
```

### D.7 Refactoring becomes decidable (e-graph saturation)

```
With Era XII Day 93.A e-graph saturation:
  refactor(p, cost, depth) := argmin_{c ∈ saturate p depth} cost(c)

Complexity: O(|p|^d × catalog_size) for depth d ≤ 10.
Pareto-frontier of (cost1, cost2) computable via lex search.
```

### D.8 Energy as model-checked graded dimension

```
Model theorem (Landauer-style certificate): For irreversible Step s
inside an explicit finite thermodynamic model M,
  s.energy_cost ≥ k_B · T · s.entropy_decrease · ln 2

T = 298.15 K: ≥ 2.85 × 10⁻²¹ J / bit erased.
Reversible Steps (Bennett 1973, Fredkin-Toffoli 1982): cost floor
0 only inside models that prove the reversibility hypotheses.

Compiler can search for energy-minimal equivalent programs.
Quantum unitary evolution is represented by finite-dimensional
unitary model certificates, not a kernel-global assumption.
```

### D.9 Bounded normalization decidable in certified finite sites

```
For finitely-presented (∞,n)-polygraph site S with bounded dim
n ≤ 6, finite generators per dim, a well-founded reduction
measure, and complete critical-pair witnesses:
  NF_reachable_within_bound(p, B) is decidable by finite search
  M04-style total normalization is decidable only when S supplies
  the reducibility interpretation / SN proof required by Era S.

This does NOT contradict Turing's theorem (universal machine site
does not supply the SN certificate). For FX programs in certified
finite/SN sites, normalization is decidable because the site carries
the termination proof. Era S Day 43 M04 SN is the specialization for
FX.standardSite.

Tradeoff: certified finite/SN sites vs unbounded universal
interpreters. FX keeps the kernel decidable and represents unbounded
languages through explicit fuel, coinduction/productivity, or
external execution boundaries.
```

### D.10 Gödel monotonically removable via on-demand site extension

```
Each finitely-presented site S_n is incomplete. But Era XII user-
extensible mechanism allows S_n → S_{n+1} adding missing
statements:

For consistent extension S_n → S_{n+1}:
  Th(S_n) ⊆ Th(S_{n+1})
Inconsistent extensions caught by STRICT-35 (induced critical pair
fails to join).

Set-theoretic axiom-extension: dangerous (must check independence).
FX site-extension: safe (mechanically verified).
```

### D.11 Continuum Hypothesis as site choice

```
Site_GodelL ⟹ CH provable (constructible-universe site)
Site_CohenForcing ⟹ ¬CH provable (Cohen-forced site)

Both consistent. Independence becomes a SITE DIAL.
```

### D.12 Privacy / side-channels as geometry

```
Side-channel attack = 2-cell α : intended ⇒ unintended in silicon
polygraph absent from spec polygraph.

Spectre v1: speculation_window leaks secret to cache_state via
unintended 2-cell.
Rowhammer: DRAM refresh-coupling violates row-independence via
unintended 2-cell.

Differential privacy = bounded-curvature on security manifold.
GDPR-compliance = verified site morphism preserving anonymization.
```

### D.13 Agentic LLM as path through polygraph; reasoning is geodesic

```
LLMSession := sequence of edits = path through polygraph
agent_optimal_complexity(T) := inf over paths reaching goal of
                                cost_tropical(path)

LLM is task-optimal on T iff produces sessions with cost equal
to this infimum.

Chain-of-thought = path projection.
RL fine-tuning = reward shaping on cost-tropical metric.
Whole field of LLM agents reduces to discrete differential
geometry on polygraph.
```

### D.14 Free-energy principle as kernel-level theorem

```
Friston's free-energy principle (Nat Rev Neuroscience 2010)
becomes:
  variational_free_energy : Site → Program → ℝ
  SelfOrganizing := program with gradient_flow descending on
                    variational_free_energy

The set of self-organizing programs forms a sub-category of FX
polygraph, closed under composition.
```

### D.15 P vs NP as polygraph search depth

```
Conjecture (P-vs-NP-as-polygraph):
  P ≠ NP ⟺ ∃ language L ∈ NP, ∃ instance class C ⊆ L,
            ∀ poly p, ∀ depth d ≤ p(|x|), ∀ x ∈ C,
              no polygraph path of depth d witnesses x ∈ L
  (depth-bounded polygraph reachability is Σ¹-incomplete)
```
Polygraph-search-depth complexity reframes the question; doesn't
resolve it (same difficulty as classical P-vs-NP).

### D.16 Curry-Howard-Lambek-Lawvere extends to physics

```
Programs ≅ Proofs ≅ Categorical-objects ≅ Physical-configurations
        ≅ Measurement-sequences ≅ Wavefunctions
        ≅ Information-states ≅ Thermodynamic-ensembles

Each ≅ via specific site choice. CS, logic, math, physics, info
theory, thermodynamics specializations of one polygraph framework.
```

### D.17 Hardware bugs as silicon-level 2-cells

```
Hardware bug := 1-cell in silicon polygraph not matching spec
                polygraph's 1-cell
Side-channels := unintended 2-cells (Spectre, Rowhammer, RAMBleed,
                 Meltdown all instances).
Silicon validation := SiteMorphism F_silicon→spec verifies the
                      embedding faithful.
Hardware Trojans := inserted 1-cells absent from spec polygraph.
```

### D.18 Time becomes negotiable across observers

```
Different observers (LLM, hardware, distributed system, human)
experience the same computation at different time-scales.

TimeDilation := SiteMorphism Site_observer1_time Site_observer2_time
                with non-linear cycle scaling factor c ∈ ℝ⁺

Real-time systems := constraints on rate of site morphisms.
Race conditions := non-natural site morphisms (causally
                    inconsistent).
Clock skew := measurable cohomology class on time-site.
Lorentz transformation := infinitesimal form; FX discrete version
                          more general (no metric required).
```

### D.19 Computational thermodynamics as model theorem

```
For explicit finite thermodynamic model M and checked reduction path:
  energy_consumed(path) = ∑ energy_cost(step over path)
                        ≥ k_B · T · entropy_decrease(comp) · ln 2

with equality iff M proves every step is reversible and the supplied
model laws have tight certificates.

Reversible computing target for energy-optimal compilation.
Quantum computing enters through explicit finite unitary-model
certificates.
```

### D.20 2-Site as universal arena for all formal reasoning

```
The 2-category 2-Site has:
  0-cells: sites (universes / programming languages / DTT systems)
  1-cells: site morphisms (compilers, translations, abstractions)
  2-cells: modifications (optimizations, equivalences, refactorings)
  ... up to dim 6 per FX commitment

Sub-2-categories specialize to:
  Compiler theory (II)        → 1-cells of 2-Site
  Distributed systems (III)   → cohomology of 2-Site at partition
  Quantum (IV)                → particular site
  ML / discovery (V)          → ML-guided 2-cell construction
  Debugging / git (VI)        → 2-cell construction in patch-2-cat
  Refactoring (VII)           → cost-min representative in eq-class
  Energy (VIII)               → grade dim 23 with finite model certificates
  Halting (IX)                → reachability in finite sites
  Set-theoretic indep (XI)    → site dial
  Privacy / side-channel (XII)→ unintended 2-cell detection
  Agentic LLM (XIII)          → geodesic in cost-tropical metric
  Free-energy (XIV)           → variational descent on programs
  P vs NP (XV)                → depth-bounded polygraph search
  CHL → physics (XVI)         → site-parametric correspondence
  Hardware bugs (XVII)        → unintended polygraph cells
  Real-time (XVIII)           → temporal-site cohomology
  Thermodynamics (XIX)        → energy-graded path cost

Lurie's higher topos theory applied to programming.
```

---

## Appendix E — Cell-category instantiations catalog

The full catalog of cell categories C for which `Polygraph(C)`
specializes to a known computational framework. Each instantiation
inherits FX's polygraph machinery (composition, dim-by-dim
structure, conservation via Noether) with C-specific decidability.

| Cell Category | Polygraph Type | Application Domain | Cost Algebra | Decidability |
|---------------|----------------|--------------------|--------------|--------------|
| `Set` (sets, functions) | Discrete polygraph | Standard CS, type theory | (ℕ, +, ·) | poly via finite enumeration |
| `Cont` (cont functions on metric) | Topological polygraph | Continuous dynamics | real analysis | numerical, with Lipschitz convergence |
| `Smooth∞` (smooth ∞-groupoids) | Smooth polygraph | Differential geometry, GR | de Rham cohomology | requires SDG (Era X Day 72) |
| `Prob` (probability spaces) | Stochastic polygraph | Bayesian inference, RL, MDPs | (ℝ⁺, +, ·) integration | tractable for treewidth-bounded |
| `Hilb` (f.d. Hilbert spaces) | Quantum polygraph | Quantum computation, ZX | (ℂ, +, ·) tensor algebra | NP-hard general; MPS-tractable bounded |
| `Vec_R` (vector spaces over ℝ) | Linear polygraph | Linear algebra, ML linear | tensor contractions | poly for fixed dim |
| `Type` (FX types) | Type-theoretic polygraph | FX kernel itself | term equivalence | decidable for FX kernel |
| `Lawvere_Th` (Lawvere theories) | Algebraic polygraph | Universal algebra | term rewriting | decidable for finite presentations |
| `Fuzzy` (fuzzy [0,1]) | Fuzzy polygraph | Approximate reasoning | ([0,1], max, ·) Łukasiewicz | poly for finite supports |
| `Tropical` (sets w/ tropical) | Tropical polygraph | Optimization, shortest paths | (ℝ̂, min, +) | poly per Bellman-Ford |
| `Causet` (locally finite posets) | Causal-set polygraph | Discrete spacetime physics | order arithmetic | decidable for finite causets |
| `Game` (game positions) | Game polygraph | Game theory, dialogue | game-tree value | decidable for bounded depth |

Domain-by-domain map of multi-level applications:

### Distributed systems (Cell = Set, time = causal poset)

| Level | Time | Space | Calculus |
|-------|------|-------|----------|
| 0 | continuous | network topology | continuous-time message-passing models |
| 1 | per-message events | nodes | tropical (latency-min-plus) |
| 2 | atomic actions (TLA+) | processes | discrete event simulation |
| 3 | rounds (Paxos) | replica groups | round-by-round invariants |
| 4 | algorithm-level | single agreement | high-level state machine |

### ML training dynamics (Cell = Vec or Prob)

| Level | Time | Space | Calculus |
|-------|------|-------|----------|
| 0 | continuous gradient flow | parameter manifold | gradient descent ODE |
| 1 | SGD steps | mini-batches | tropical loss accumulation, Adam moments |
| 2 | epochs | full training set | epoch-level loss landscape |
| 3 | training runs | hyperparameter space | meta-learning |
| 4 | model lineage | model families | scaling laws |

JKO scheme (per Era IX Day 90) is the F_0_to_1 functor.

### Biology (Cell = Cont)

| Level | Time | Space | Calculus |
|-------|------|-------|----------|
| 0 | molecular dynamics | atomic positions | force-field PDEs |
| 1 | biochemical reactions | molecular pools | reaction-rate ODEs |
| 2 | cellular signaling | organelles, membranes | discrete-event signal cascades |
| 3 | tissue / organ | functional units | physiological models |
| 4 | organism | whole-organism behavior | behavioral rules |

### Operating systems (Cell = Set)

| Level | Time | Space | Calculus |
|-------|------|-------|----------|
| 0 | clock cycles | CPU registers | hardware Era IV.5 reused |
| 1 | system calls | kernel data structures | event-driven |
| 2 | process scheduling | runqueues | scheduling theory |
| 3 | services | service mesh | request/response |
| 4 | applications | user behavior | usage analytics |

### Brain function (Cell = Prob or Cont)

| Level | Time | Space | Calculus |
|-------|------|-------|----------|
| 0 | continuous (ms) | individual neurons | Hodgkin-Huxley ODEs |
| 1 | spike events | neuronal populations | spike-timing tropical |
| 2 | gamma/theta cycles | cortical columns | neural population dynamics |
| 3 | cognitive operations | brain regions | functional neuroimaging |
| 4 | behavior | whole brain | cognitive psychology |

Friston's free-energy principle (D.14) is a cross-level statement
about variational descent.

### Economics / Markets (Cell = Prob)

| Level | Time | Space | Calculus |
|-------|------|-------|----------|
| 0 | tick-level transactions | order book entries | continuous limit-order dynamics |
| 1 | trades (event-time) | symbols | price-impact tropical |
| 2 | minute-bar OHLC | symbol universes | technical analysis |
| 3 | sectors | market segments | macro analysis |
| 4 | regimes | global economy | DSGE models |

### Climate / Earth systems (Cell = Cont)

| Level | Time | Space | Calculus |
|-------|------|-------|----------|
| 0 | molecular thermal | gas particles | statistical mechanics |
| 1 | weather (hourly) | atmospheric grid | Navier-Stokes PDEs |
| 2 | climate (daily) | climate-model cells | climatology |
| 3 | climate trends (decadal) | regions | trend analysis |
| 4 | geological epochs | global Earth | paleoclimate |

All seven domains have the same structural shape: stratified
polygraphs + abstraction functors + per-level calculus + cross-
level naturality. FX's parametric kernel handles them all
uniformly via Era T site-parametric machinery + Era IV.5
multi-level abstraction functor framework.

---

End of extended-roadmap.md.
