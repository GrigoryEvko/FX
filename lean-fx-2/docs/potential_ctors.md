# Potential Term constructors — voracious kernel survey

**Status**: forward-looking architectural survey for `LeanFX2.Term` extension.
**Goal**: enumerate every defensible kernel constructor candidate so that FX
can adopt a "single Term, voracious semantics" architecture — one inductive
that captures the full computational + mathematical universe FX wants to
verify.

**Audience**: future FX kernel maintainers planning multi-year roadmap;
domain leads scoping their layer's kernel needs; Codex/AI co-engineers
needing context for kernel-extension proposals.

---

## 0. The "single Term" philosophy

FX's design commitment (per `fx_design.md` §6 / §27 / Appendix H) is that
every verifiable phenomenon — from refl-paths to RISC-V instructions to
Bayesian inference — lives as a typed `Term` in one unified kernel. That
isn't aesthetic preference; it's a verification commitment. The same
SR-cascade infrastructure must apply to crypto protocols and to clock
domains and to differential forms. Separate sub-kernels would fragment
the proof ecosystem.

But the cascade cost is real: each new `Term` ctor adds work across
roughly 16 files (Term.rename, Term.subst, Step.par, RawCdLemma,
Compat/*, RawParInversion, ConvBridge, Bridge, audit gates, smoke
logs, etc.). Empirically: ~600-1000 LoC of kernel work per ctor. Going
from today's 78 ctors to, say, 200 ctors is ~100K LoC of new kernel
work — a multi-year undertaking that must be RIGOROUSLY prioritized.

### The "earns kernel place" criterion

A constructor candidate earns kernel place iff it satisfies ALL FOUR:

1. **Definitional behavior gap**: encoding via existing Term ctors +
   library code loses some equation that subject reduction or term
   inversion requires. E.g., quotient β-rule `Quot.rec f h (Quot.mk a)
   ≡ f a` is definitional; library encoding via setoids loses this.

2. **Subject-reduction coherence**: the candidate must interact
   cleanly with the existing `Step.par` reduction graph. Adding a ctor
   that breaks confluence or termination is a non-starter regardless
   of how voracious FX wants to be.

3. **Downstream amortization**: at least one downstream era (K12+
   reducibility, K13 NbE, K14 e-graph, K17+ FX1 bridge, or one of the
   voracious-domain layers — crypto, ML, network, hardware, physics,
   finance, military, quantum) extracts proof value from the candidate
   that justifies its cascade cost. Speculative additions without a
   committed consumer should stay in honorable mentions.

4. **Orthogonality**: the candidate's semantics is not subsumed by an
   existing ctor + light library. If `Term.X` is reducible to
   `Term.lam (Term.app f g)` modulo a library, prefer the library.

### Architectural envelope

Realistic upper bound, given engineering productivity constraints:

```
                   Current        +Tier★★★★★      +Tier★★★★      +Tier★★★      Pragmatic ceiling
Term ctors:        78             ~108            ~145           ~170          ~180
Cumulative LoC:    0 baseline     ~25K            ~55K           ~80K          ~95K
Wall time:         baseline       6-12 mo         18-30 mo       30-48 mo      4-5 years
```

Beyond ~180 ctors, polynomial-functor unification becomes mandatory
(see §9): the kernel REFACTORS to use a parameterized family of
inductive ctors, paradoxically reducing the count while expanding the
semantic range. That's the architectural endgame.

---

## 1. Current kernel state (78 ctors)

For reference, the existing `LeanFX2.Term` (committed under
`LeanFX2/Term.lean`) covers these families:

### 1.1 MLTT-spine (core dependent type theory)

* **Variables + atoms**: `var`, `unit`, `boolTrue`, `boolFalse`,
  `natZero`, `natSucc`, `interval0`, `interval1`
* **Π / Σ formers**: `lam`, `app`, `lamPi`, `appPi`, `pair`, `fst`, `snd`
* **Sum / dependent**: `eitherInl`, `eitherInr`, `eitherMatch`
* **Inductives**: `listNil`, `listCons`, `listElim`, `optionNone`,
  `optionSome`, `optionMatch`, `boolElim`, `natElim`, `natRec`
* **Universes + cumulativity**: `cumulUp`, `universeCode`
* **Type codes**: `arrowCode`, `piTyCode`, `sigmaTyCode`, `productCode`,
  `sumCode`, `listCode`, `optionCode`, `eitherCode`, `idCode`, `equivCode`

### 1.2 HoTT spine

* **Identity types**: `refl`, `idJ`
* **Observational equality**: `oeqRefl`, `oeqJ`, `oeqFunext`
* **Strict identity**: `idStrictRefl`, `idStrictRec`
* **Equivalences**: `equivReflId`, `equivIntroHet`, `equivReflIdAtId`,
  `equivApp`, `equivApply`, `equivCompose`, `idToEquiv`
* **Funext fragments**: `funextRefl`, `funextReflAtId`, `funextIntroHet`
* **Univalence introduction**: `uaToEquiv`, `uaIntroHet`
* **Path operations**: `pathLam`, `pathApp`, `pathCompose`
* **OEq transitivity**: `oeqTrans`

### 1.3 Cubical spine

* **Kan operations**: `transp`, `transpFill`, `hcomp`, `hcompPath`
* **Glue / unglue**: `glueIntro`, `glueElim`
* **Interval algebra**: `intervalMeet`, `intervalJoin`, `intervalOpp`

### 1.4 Modal calculus

* **Mode coercion**: `modIntro`, `modElim`, `subsume`

### 1.5 Refinement + record + codata + session + effect

* **Refinement**: `refineIntro`, `refineElim`
* **Record**: `recordIntro`, `recordProj`
* **Codata**: `codataUnfold`, `codataDest`
* **Session**: `sessionSend`, `sessionRecv`
* **Effect**: `effectPerform`

### 1.6 Architectural law for current 78

Every existing ctor satisfies the four-criteria test for `LeanFX2.Term`:
the closure under reduction (Step.par) is structurally complete for the
MLTT + HoTT + cubical + modal + refinement spine that FX commits to.
Future ctors must EARN their place by the same criteria.

---

## 2. Tier ★★★★★ — Must-have foundational extensions

These constructors unblock multiple downstream eras simultaneously and
have no viable library encoding. Recommended for adoption in the next
6-12 months.

### 2.1 Computational Quotients (5 ctors)

The most-requested HoTT extension. Currently FX has no kernel quotient
type — quotient structures are encoded via library setoids, which loses
the DEFINITIONAL β-reduction `Quot.rec f h (Quot.mk a) ≡ f a`. Adding
quotients structurally enables `ℤ/nℤ`, `ℚ`, `ℝ` (as Cauchy quotient),
gauge quotients in physics, fairness quotients in mechanism design, and
constructive analysis foundations.

**Constructor sketch**:

```lean
| quotMk {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (relation : Ty level scope)  -- equivalence relation index
    {valueRaw : RawTerm scope}
    (value : Term context carrier valueRaw) :
    Term context (Ty.quot carrier relation)
                 (RawTerm.quotMk valueRaw)

| quotEqAxiom {...}
    (witness : Term context (relation a b) ...)  -- equivalence witness
    : Term context (Ty.id (Ty.quot carrier relation)
                          (Term.quotMk a)
                          (Term.quotMk b)) ...

| quotRec {...}
    (motive : Ty level scope)
    (kernelFn : Term context (carrier →ᵢ motive) ...)
    (respectsRel : Term context (... respect-equivalence proof ...) ...) :
    Term context (Ty.quot carrier relation →ᵢ motive) ...

| quotElim {...}  -- dependent eliminator
    (depMotive : Ty level (scope + 1)) ...

-- And the β-reduction at Step.par:
| Step.par.betaQuotRec :
    Step.par (Term.quotRec motive kernelFn respectsRel @ Term.quotMk a)
             (Term.app kernelFn a)
```

**Cascade cost**: ~3500 LoC.

**Downstream consumers**:
- Crypto: `ℤ/pℤ` definitional, `GF(2^n)` finite field
- ML: weight-equivalence classes, gauge invariance
- Finance: decimal-epsilon equivalence
- Physics: gauge field quotients, modular spaces
- Mathematics: any algebraic quotient (rings, groups, modules)

**Why kernel and not library**: definitional β-reduction. Library
setoid encoding gives propositional equality only, breaking subject
reduction for quotient-eliminator-applied-to-injected-element.

### 2.2 Universal Pushout HIT (4 ctors + β-rules)

The most economical HIT addition: pushout is the UNIVERSAL HIT, from
which all others derive. Adding ONE pushout family unlocks suspension,
coequalizer, sphere, smash, wedge, join — all as library definitions
over the kernel pushout.

**Constructor sketch**:

```lean
-- Pushout of span A ←f B →g C
| pushInl {...}
    {targetTy : Ty level scope}  -- A
    {middleTy : Ty level scope}  -- B
    {rightTy : Ty level scope}   -- C
    (left : Term context targetTy ...)
    : Term context (Ty.pushout f g) (RawTerm.pushInl ...)

| pushInr {...}
    (right : Term context rightTy ...)
    : Term context (Ty.pushout f g) ...

| pushGlue {...}
    (middle : Term context middleTy ...)
    : Term context (Ty.id (Ty.pushout f g)
                          (Term.pushInl (f @ middle))
                          (Term.pushInr (g @ middle))) ...

| pushRec {...}  -- non-dependent eliminator with coherence obligation
    (motiveTy : Ty level scope)
    (caseInl : Term context (targetTy →ᵢ motiveTy) ...)
    (caseInr : Term context (rightTy →ᵢ motiveTy) ...)
    (caseGlue : Term context (... compat-with-glue proof ...) ...) :
    Term context (Ty.pushout f g →ᵢ motiveTy) ...
```

**Library derivations** (no new kernel ctors needed):

```
Suspension ΣA          := pushout (A → 1) (A → 1)
Coequalizer A ⇉ B / ~  := pushout-like over A × A
Sphere S^(n+1)         := suspension of S^n
Smash A ∧ B            := pushout of (A → 1) (B → A × B)
Wedge A ∨ B            := pushout of (1 → A) (1 → B)
Join A * B             := pushout of (A × B → A) (A × B → B)
```

**Cascade cost**: ~3000 LoC for pushout alone; ~1500 LoC for the
library derivations of suspension/coeq/sphere/smash/wedge/join.

**Downstream consumers**: synthetic homotopy theorem proving (π_n
computations), homotopy type-theoretic universe constructions,
classical mathematics formalization.

### 2.3 Truncations (4 ctors)

Propositional + set + n-truncation, sharing a single kernel
infrastructure parameterized by truncation level.

**Constructor sketch**:

```lean
-- Generic n-truncation
| truncIntro {...}
    (truncLevel : Nat)  -- -1 = propositional, 0 = set, 1 = groupoid, ...
    (carrier : Ty level scope)
    {valueRaw : RawTerm scope}
    (value : Term context carrier valueRaw) :
    Term context (Ty.trunc truncLevel carrier)
                 (RawTerm.truncIntro truncLevel valueRaw)

| truncCoh {...}  -- n-coherence: any two trunc'd elements are (n-1)-truncated equal
    (level : Nat) ...

| truncRec {...}
    (level : Nat)
    (motive : Ty level scope) -- must be (level)-truncated codomain
    (kernelFn : Term context (carrier →ᵢ motive) ...) :
    Term context (Ty.trunc level carrier →ᵢ motive) ...

| Step.par.betaTruncRec : ...
```

**Cascade cost**: ~2800 LoC (single ctor family for all truncation
levels — vs. 3× cost if propositional, set, and n-truncation were
shipped separately).

**Downstream consumers**:
- `∃` as `‖Σ‖_-1` (propositional truncation gives mere existence)
- "set" notion as `‖A‖_0` (HoTT-style sets)
- Crypto: ZK-style "exists a witness without revealing it"
- Foundational mathematics: setoid-free constructions

**Why kernel and not library**: truncation level induction interacts
with reduction (e.g., propositional truncation's two-elements-equal
must hold definitionally for the eliminator to compute). Library
encoding via "wrap value, ignore identity" loses the elimination
β-rule.

### 2.4 Polynomial Functors (5 ctors — THE refactor candidate)

This is the deepest architectural bet in the proposal. Polynomial
functors describe ALL inductive data types uniformly: `P(X) = Σ_{a:A}
X^{B(a)}` parametrizes a shape A with positions B(a). Every existing
ctor (`list`, `option`, `either`, `nat`, `record`, `codata`) is an
instance.

Adopting polynomial functors enables:
- Generic recursion / fold / unfold operations
- Container calculus (zippers, lenses, derivatives) for free
- One subject-reduction proof covers ALL inductive ctors
- Future inductive types added at LIBRARY level, not kernel

**Constructor sketch**:

```lean
-- Polynomial functor: shape A with position family B
| polyFunctor {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (shapeType : Ty level scope)
    (positionFamily : Ty level (scope + 1)) :  -- B : shape → Type
    Term context (Ty.poly shapeType positionFamily) ...

| polyApply {...}
    (polyTerm : Term context (Ty.poly A B) ...)
    (carrierTy : Ty level scope) :
    Term context (Ty.polyApply polyTerm carrierTy) ...
  -- Computes Σ a:A. (B(a) → carrierTy)

| polyMu {...}
    (polyTerm : Term context (Ty.poly A B) ...) :
    Term context (Ty.polyMu polyTerm) ...
  -- Initial algebra: μP (generalizes W-types)

| polyNu {...}
    (polyTerm : Term context (Ty.poly A B) ...) :
    Term context (Ty.polyNu polyTerm) ...
  -- Terminal coalgebra: νP (generalizes M-types)

| polyMap {...}  -- functorial action
    (mapFn : Term context (carrierA →ᵢ carrierB) ...) :
    Term context (Ty.polyApply P carrierA →ᵢ Ty.polyApply P carrierB) ...
```

**Cascade cost**: ~5000 LoC initially, BUT enables ~10K LoC of
subsequent removal because existing inductive ctors (list/option/etc.)
can be redefined as library instances over Poly.

**Refactor potential**: post-Poly adoption, the kernel could SHRINK
from current 78 + new ctors → ~55-60 ctors total, doing strictly more
semantic work. This is the architectural sweet spot.

**Downstream consumers**:
- Generic programming infrastructure (lenses, optics, zippers, traversals)
- E-graph canonicalization (K14): polynomial functors give canonical
  shape decomposition
- Reflection / metaprogramming (K15): reify uses Poly uniformly
- Self-hosting (K20): FX-in-FX type-theory encoded as Poly

**Why kernel and not library**: parameterized inductives with mutual
definitions need kernel support for SR. Library encoding via
hand-rolled W-types loses generic-recursion structure.

### 2.5 σ-Algebra + Measure (3 ctors)

Foundation for analytic mathematics. Currently FX has decimal/frac
arithmetic but no measure-theoretic infrastructure. Adding σ-algebra
and abstract measure unlocks Lebesgue integration, probability theory,
information theory, and harmonic analysis.

**Constructor sketch**:

```lean
| sigmaAlgebra {...}
    (carrier : Ty level scope)
    (closureWitness : Term context (... σ-algebra closure laws ...) ...) :
    Term context (Ty.sigmaAlg carrier) ...

| measureSpace {...}
    (carrier : Ty level scope)
    (algebra : Term context (Ty.sigmaAlg carrier) ...)
    (measureMap : Term context (... measurable-set → ℝ_≥0 ...) ...)
    (countableAdditivity : Term context (... countable additivity ...) ...) :
    Term context (Ty.measureSpace carrier algebra) ...

| lebesgueInt {...}
    (space : Term context (Ty.measureSpace carrier algebra) ...)
    (integrand : Term context (carrier →ᵢ Ty.real) ...) :
    Term context Ty.real (RawTerm.lebesgueInt ...)
```

**Cascade cost**: ~3000 LoC.

**Downstream consumers**:
- ML: variational inference, KL divergence, ELBO
- Finance: option pricing (Black-Scholes via stochastic integrals)
- Physics: path integrals, statistical mechanics
- Crypto: probabilistic proofs, ZK protocols
- Quantum: probability of measurement outcomes

**Why kernel and not library**: Lebesgue integration's linearity +
monotonicity must be definitional for analytic proofs to compose
cleanly. Library encoding via Riemann sums loses convergence properties.

### 2.6 Temporal Logic Kernel (5 ctors)

LTL/CTL operators as first-class kernel ctors. Currently FX has
`always`/`eventually` at the machine-level (§13.5), but kernel-level
temporal operators enable verified real-time, reactive, and protocol
proofs structurally.

**Constructor sketch**:

```lean
| nextT {...}
    (proposition : Ty level scope) :  -- temporal predicate
    Term context (Ty.next proposition) ...
  -- "X A" — A holds at next step

| alwaysT {...}
    (proposition : Ty level scope) :
    Term context (Ty.always proposition) ...
  -- "□ A" — A holds forever (LTL-style)

| eventuallyT {...}
    (proposition : Ty level scope) :
    Term context (Ty.eventually proposition) ...
  -- "◇ A" — A holds at some future step

| untilT {...}
    (left right : Ty level scope) :
    Term context (Ty.until left right) ...
  -- "A U B" — A holds until B

| sinceT {...}  -- past-tense LTL
    (left right : Ty level scope) :
    Term context (Ty.since left right) ...
```

**Cascade cost**: ~3500 LoC.

**Downstream consumers**:
- Aerospace: ARINC 653 verified scheduling
- Automotive: ISO 26262 ASIL-D verified control
- Medical: IEC 62304 verified medical devices
- Networking: BGP convergence proofs, TCP state machines
- Protocols: consensus protocols (Raft, HotStuff, Tendermint)
- Reactive systems: UIs, IoT controllers
- Hardware: temporal protocol verification

**Why kernel and not library**: temporal Step.par reductions become
structural. Library encoding via traces/automata loses
composition-of-temporal-modalities.

### 2.7 Synthetic Differentials (Lawvere) (4 ctors)

Kernel-level encoding of nilpotent infinitesimals. Foundation for
synthetic calculus, autodiff, differential geometry. Currently FX has
no kernel infinitesimals — every numerical computation hands off to
library decimal arithmetic.

**Constructor sketch**:

```lean
| infinitesimal {...}
    (carrier : Ty level scope) :  -- usually ℝ
    Term context (Ty.infinitesimal carrier) ...
  -- D := {x : R | x² = 0}

| microcanc {...}
    (carrier : Ty level scope)
    (fn : Term context (Ty.infinitesimal carrier →ᵢ carrier) ...) :
    Term context (Ty.id ... (uniqueLinearForm fn) ...) ...
  -- Kock-Lawvere axiom: every D→R is uniquely a + bd

| tangentSpace {...}
    (manifold : Ty level scope)
    (basePoint : Term context manifold ...) :
    Term context (Ty.tangent manifold basePoint) ...
  -- T_x M

| diffOp {...}
    (manifold : Ty level scope)
    (fn : Term context (manifold →ᵢ Ty.real) ...) :
    Term context (Ty.tangent manifold _ →ᵢ Ty.real) ...
  -- d : C^∞(M) → Ω^1(M)
```

**Cascade cost**: ~3000 LoC.

**Downstream consumers**:
- Physics: classical mechanics, general relativity, gauge theory
- ML: backpropagation as kernel reduction, neural ODEs
- Robotics: configuration space dynamics, controller verification
- Finance: portfolio sensitivity (the "Greeks") via verified autodiff
- Control theory: Lyapunov stability proofs

**Why kernel and not library**: Kock-Lawvere axiom requires
definitional β-reduction on D-arrow. Library encoding via dual numbers
loses functoriality.

**Tier ★★★★★ total**: 30 ctors, ~22K LoC cascade. This is the
"voracious foundation" — without these, FX cannot pursue the full
verification ambition.

---

## 3. Tier ★★★★ — Domain-completion additions

These complete specific voracious-FX domains. Each addition is
high-impact for ONE primary domain and moderate-impact for others.

### 3.1 Session protocol completion (5 ctors)

FX has `sessionSend`/`sessionRecv` but the session calculus is
incomplete. Adding the missing operators enables full π-calculus-style
verified protocols (TLS handshake, Raft consensus, payment networks).

**Constructor sketch**:

```lean
| sessionSelect {...}
    (channel : Term context (Ty.session ...) ...)
    (choice : Term context Ty.choiceLabel ...) :
    Term context (Ty.session sessionStateB ...) (RawTerm.sessionSelect ...)

| sessionOffer {...}
    (channel : Term context (Ty.session ...) ...)
    (branchesCovered : Term context (... exhaustive-branches ...) ...) :
    Term context ... (RawTerm.sessionOffer ...)

| sessionClose {...}
    (channel : Term context (Ty.session Ty.sessionEnd) ...) :
    Term context Ty.unit (RawTerm.sessionClose ...)

| channelSplit {...}
    (channel : Term context (Ty.session ...) ...) :
    Term context (Ty.product (Ty.session ...) (Ty.session ...)) ...

| channelJoin {...}
    (leftCh rightCh : Term context (Ty.session ...) ...) :
    Term context (Ty.session ...) ...
```

**Cascade cost**: ~3500 LoC.

**Primary consumer**: networking — `fx-net` verified TLS 1.3, Tor, QUIC.

**Cross-domain value**: distributed-systems consensus, payment-channel
networks, federated learning protocols.

### 3.2 Hardware register / clock core (6 ctors)

Currently FX hardware semantics live partially in Step.par (combinational
+ sequential) and partially in surface syntax. Adding kernel ctors for
register state + clock advancement + pipeline stage makes RTL→ISA
refinement proofs STRUCTURAL.

**Constructor sketch**:

```lean
| regRead {...}
    (registerId : Term context Ty.regId ...)
    (cycle : Term context Ty.clockCycle ...) :
    Term context (Ty.bits width) (RawTerm.regRead ...)

| regWrite {...}
    (registerId : Term context Ty.regId ...)
    (newValue : Term context (Ty.bits width) ...)
    (cycle : Term context Ty.clockCycle ...) :
    Term context Ty.unit ...

| clockTick {...}
    (clockDomain : Ty level scope) :  -- which clock advances
    Term context (Ty.clockCycle clockDomain) ...

| stageLatch {...}
    (stageInput : Term context ... ...)
    (clockEdge : Term context Ty.clockEdge ...) :
    Term context ... ...

| wireCombinational {...}
    (combinationalLogic : Term context ... ...) :
    Term context (Ty.bits width) ...

| clockDomainCross {...}
    (sourceClock targetClock : Ty level scope)
    (signal : Term context (Ty.bits width) ...)
    (synchronizer : Term context Ty.syncWitness ...) :
    Term context (Ty.bits width) ...
```

**Cascade cost**: ~4500 LoC.

**Primary consumer**: `fx-chip` verified RISC-V core (RTL→ISA bisimulation).

**Cross-domain value**: any hardware-software co-verification (device
drivers, FPGAs, ASIC verification, formal SystemVerilog equivalents).

### 3.3 Computational Reals (3 ctors)

Beyond `decimal` arbitrary-precision, computational reals enable
constructive analysis: limits, continuity, derivatives, integrals with
RIGOROUS error bounds.

**Constructor sketch**:

```lean
| realCauchy {...}
    (cauchySeq : Term context (Ty.natural →ᵢ Ty.decimal) ...)
    (convergenceRate : Term context (... Cauchy-rate witness ...) ...) :
    Term context Ty.real (RawTerm.realCauchy ...)
  -- ℝ as quotient of rapidly-converging Cauchy sequences

| realLimit {...}
    (sequence : Term context (Ty.natural →ᵢ Ty.real) ...)
    (convergenceWitness : Term context (... limit existence ...) ...) :
    Term context Ty.real ...

| realCompare {...}
    (left right : Term context Ty.real ...)
    (epsilon : Term context Ty.positiveReal ...) :
    Term context (Ty.decidable (Ty.lt left right)) ...
  -- ε-decidable comparison
```

**Cascade cost**: ~2500 LoC, but PRESUPPOSES Tier 2.1 (computational
quotients) since ℝ is structurally a quotient.

**Primary consumer**: verified scientific computing (numerical
analysis, optimization, PDE solvers).

**Cross-domain value**: physics simulation, ML optimization, finance
derivatives pricing, control theory.

### 3.4 Probability Kernel (3 ctors)

Builds on Tier 2.5 (measure space) but specializes to probability with
sampling + expectation + conditional probability primitives.

**Constructor sketch**:

```lean
| probSpace {...}
    (outcomeType : Ty level scope)
    (probMeasure : Term context (Ty.measureSpace outcomeType _) ...)
    (totalMassOne : Term context (Ty.id ... (totalMeasure probMeasure) Term.one) ...) :
    Term context (Ty.probSpace outcomeType) ...

| sampleP {...}
    (space : Term context (Ty.probSpace outcomeType) ...) :
    Term context (Ty.distOver outcomeType) (RawTerm.sampleP ...)

| expectE {...}
    (space : Term context (Ty.probSpace outcomeType) ...)
    (randomVariable : Term context (outcomeType →ᵢ Ty.real) ...) :
    Term context Ty.real (RawTerm.expectE ...)
```

**Cascade cost**: ~3000 LoC.

**Primary consumer**: verified Bayesian inference, MCMC, variational ML.

**Cross-domain value**: verified randomized algorithms, differential
privacy, financial Monte Carlo, statistical mechanics.

### 3.5 p-adic Numbers (3 ctors)

For verified post-quantum cryptography (lattice-based, isogeny-based)
and analytic number theory.

**Constructor sketch**:

```lean
| padicNum {...}
    (prime : Term context Ty.prime ...)
    (numerator denominator : Term context Ty.integer ...) :
    Term context (Ty.padic prime) (RawTerm.padicNum ...)

| padicValuation {...}
    (prime : Term context Ty.prime ...)
    (value : Term context (Ty.padic prime) ...) :
    Term context Ty.integer ...

| localGlobalBridge {...}
    (rationalProblem : Term context Ty.diophantineEq ...)
    (everyLocalSolution : Term context (... ∀p, local sol exists ...) ...) :
    Term context (Ty.option Ty.globalSolution) ...
```

**Cascade cost**: ~2500 LoC.

**Primary consumer**: verified PQC (Kyber/Dilithium/Falcon), verified
isogeny crypto (SIKE/CSIDH replacements).

### 3.6 Universal Composability (UC) (4 ctors)

Canetti's framework for compositional crypto security proofs. The most
rigorous foundation for modern verified crypto.

**Constructor sketch**:

```lean
| idealFunctionality {...}
    (interface : Ty level scope) :
    Term context (Ty.idealFunc interface) ...

| realProtocol {...}
    (protocolBody : Term context (Ty.protocol ...) ...) :
    Term context (Ty.realProto interface) ...

| ucSimulator {...}
    (realProto : Term context (Ty.realProto interface) ...)
    (idealFunc : Term context (Ty.idealFunc interface) ...)
    (simulator : Term context (Ty.adversary →ᵢ Ty.adversary) ...)
    (indistinguishability : Term context (... distinguishing-advantage bound ...) ...) :
    Term context (Ty.ucRealizes realProto idealFunc) ...

| ucCompose {...}  -- UC composition theorem witness
    ... :
    Term context (... compositional security ...) ...
```

**Cascade cost**: ~5000 LoC.

**Primary consumer**: verified TLS 1.3, verified MPC protocols, verified
zero-knowledge systems.

### 3.7 Information Theory (4 ctors)

Shannon's foundation + modern info-theoretic ML.

**Constructor sketch**:

```lean
| shannonEntropy {...}
    (distribution : Term context (Ty.distOver carrier) ...) :
    Term context Ty.real (RawTerm.shannonEntropy ...)

| mutualInfo {...}
    (jointDist : Term context (Ty.distOver (Ty.product A B)) ...) :
    Term context Ty.real ...

| klDivergence {...}
    (p q : Term context (Ty.distOver carrier) ...) :
    Term context Ty.real ...  -- D_KL(p ‖ q)

| channelCapacity {...}
    (channel : Term context (Ty.channel input output) ...) :
    Term context Ty.real ...
```

**Cascade cost**: ~3500 LoC.

**Primary consumer**: verified ML loss functions, verified
information-theoretic security proofs.

**Cross-domain value**: verified communication systems (Shannon
capacity bounds), verified coding theory, verified compression.

### 3.8 Spectral Theory (4 ctors)

For verified quantum mechanics + signal processing + PCA/spectral ML.

**Constructor sketch**:

```lean
| hilbertSpace {...}
    (innerProduct : Term context (... inner-product witness ...) ...)
    (completeness : Term context (... Cauchy-completeness ...) ...) :
    Term context Ty.hilbertSpace ...

| boundedOperator {...}
    (sourceHilbert targetHilbert : Term context Ty.hilbertSpace ...)
    (linearMap : Term context (... linear map ...) ...)
    (normBound : Term context Ty.realNonNeg ...) :
    Term context (Ty.boundedOp sourceHilbert targetHilbert) ...

| spectralDecomp {...}
    (selfAdjointOp : Term context (Ty.boundedOp h h) ...)
    (selfAdjointWitness : Term context (... A = A* ...) ...) :
    Term context (Ty.spectrum h) ...

| unitaryOp {...}
    (op : Term context (Ty.boundedOp h h) ...)
    (unitarityWitness : Term context (... U* U = I ...) ...) :
    Term context (Ty.unitary h) ...
```

**Cascade cost**: ~4500 LoC.

**Primary consumer**: verified quantum mechanics (energy spectra,
Hamiltonian eigenvalues).

**Cross-domain value**: verified PCA / kernel methods, verified signal
processing (FFT correctness), verified linear-algebra-heavy ML.

### 3.9 Causal Calculus (Pearl) (3 ctors)

For verified causal inference, AI interpretability, scientific method
formalization.

**Constructor sketch**:

```lean
| causalNet {...}
    (variables : Term context (Ty.list Ty.variable) ...)
    (parents : Term context (Ty.variable →ᵢ Ty.set Ty.variable) ...)
    (mechanisms : Term context (... per-variable mechanism ...) ...) :
    Term context (Ty.causalNet variables) ...

| doOperator {...}
    (network : Term context (Ty.causalNet vars) ...)
    (intervention : Term context (... intervention spec ...) ...) :
    Term context (Ty.causalNet vars) ...  -- post-do(X:=x) graph

| counterfactual {...}
    (network : Term context (Ty.causalNet vars) ...)
    (factual : Term context ... ...)  -- observed world
    (intervention : Term context ... ...) :  -- alternative world
    Term context Ty.distOverOutcomes ...
```

**Cascade cost**: ~3000 LoC.

**Primary consumer**: verified causal ML (Pearl's do-calculus), AI
fairness proofs.

**Cross-domain value**: scientific method (verified randomized
controlled trials, observational study soundness), policy analysis,
econometric models.

**Tier ★★★★ total**: 35 ctors, ~32K LoC cascade.

---

## 4. Tier ★★★ — Mathematical completeness

These additions complete FX's mathematical foundation. Not all
voracious-FX domains need them, but each is essential for a major
mathematical sub-area.

### 4.1 Circle + Higher Path Operations (6 ctors)

Specific named HITs that get used often enough to deserve direct kernel
ctors rather than derivation-via-pushout.

**Constructor sketch**:

```lean
| circleBase {...} : Term context Ty.circle ...
| circleLoop {...} : Term context (Ty.id Ty.circle Term.circleBase Term.circleBase) ...
| circleRec {...} (motive ...) (baseCase) (loopCase) : ...

| pathInverse {...} : Term context (Ty.id A x y →ᵢ Ty.id A y x) ...
| pathWhiskerLeft {...} (path : ...) (whisker : ...) : Term context (Ty.id ...) ...
| pathWhiskerRight {...} (path : ...) (whisker : ...) : Term context (Ty.id ...) ...
```

**Cascade cost**: ~4000 LoC.

**Consumer**: synthetic homotopy theory (π_1(S¹) = ℤ, π_n calculations).

### 4.2 Cohesive Modalities (4 ctors)

Schreiber-Shulman cohesive modalities: ♭ ⊣ ◇ ⊣ □ ⊣ ♯ adjoint chain.
Already on the FX roadmap (D4); making them kernel ctors gives
reducible behavior.

**Constructor sketch**:

```lean
| shapeModality {...} (carrier : Ty level scope) : ...  -- ʃA fundamental ∞-groupoid
| flatModality {...} (carrier : Ty level scope) : ...   -- ♭A discrete part
| sharpModality {...} (carrier : Ty level scope) : ...  -- ♯A codiscrete part
| cohesiveAdjunctionUnit {...} (modality) : ...  -- A → ♯A etc.
```

**Cascade cost**: ~3500 LoC.

**Consumer**: synthetic differential cohesion, gauge theory, geometric
realization of types.

### 4.3 Quotient Inductive-Inductive Types (QIITs) (2 ctors)

For defining models of type theory inside type theory — the K20-era
FX-in-FX self-hosting needs QIITs to encode FX's syntax cleanly.

**Constructor sketch**:

```lean
| qiitIntro {...}
    (mutualSpec : ... mutual QIIT specification ...) :
    Term context (Ty.qiit mutualSpec) ...

| qiitElim {...}
    (qiitValue : Term context (Ty.qiit mutualSpec) ...)
    (motive : ...)
    (caseHandlers : ...) :
    Term context ... ...
```

**Cascade cost**: ~3000 LoC.

**Consumer**: FX-in-FX self-hosting (K20.1-K20.10), 2LTT inner-layer
models, verified type-theory implementations.

### 4.4 Two-Level Type Theory (2LTT) (3 ctors)

Inner univalent layer + outer strict layer with explicit bridges. FX's
existing Mode discipline (strict / observational / univalent) partially
achieves this; making the layer transitions kernel ctors completes the
architecture.

**Constructor sketch**:

```lean
| liftInnerToOuter {...} (innerTerm : ...) : Term context (Ty.outer innerType) ...
| lowerOuterToInner {...} (outerTerm : ...) (cofibrancy : ...) : ...
| modalityLayerMarker {...} (modality : ...) : ...
```

**Cascade cost**: ~3000 LoC.

**Consumer**: clean inner/outer separation for meta-theoretic work.

### 4.5 Quantum gates (5 ctors)

For verified quantum algorithms — Shor's, Grover's, QFT, error
correction codes, variational quantum eigensolver (VQE).

**Constructor sketch**:

```lean
| qubit {...} : Term context Ty.qubit ...
| gate {...} (gateType : Ty.unitaryGate) (qubits : ...) : ...
| measure {...} (qubits : ...) (outcome : Ty.classicalBit) : ...
| entangle {...} (qubits : ...) (noCloningEnforcement : ...) : ...
| decohere {...} (qubits : ...) (noiseModel : ...) (fidelityBound : ...) : ...
```

**Cascade cost**: ~5000 LoC.

**Consumer**: verified quantum algorithms, verified quantum error
correction (surface codes), quantum complexity proofs.

### 4.6 Game Semantics (3 ctors)

For semantically-rigorous sequential algorithm semantics. Useful for
verified compiler optimization, PCF semantics, higher-order program
verification.

**Constructor sketch**:

```lean
| game {...} (positionTree : ...) : Term context (Ty.game positionTree) ...
| strategy {...} (game : ...) (decisionTree : ...) : ...
| playOut {...} (strat1 strat2 : ...) : ...
```

**Cascade cost**: ~2500 LoC.

**Consumer**: full-PCF semantics, parallel-OR + control operators,
sequential algorithm verification.

### 4.7 Process Calculi (4 ctors)

CCS/CSP/π-calculus primitives for verified concurrent / distributed
systems.

**Constructor sketch**:

```lean
| processCalc {...} (processDef : ...) : ...
| parallelComp {...} (left right : ...) : ...  -- P || Q
| processCommit {...} (rendezvous : ...) : ...
| bisimulationWitness {...} (left right : ...) (witnessRelation : ...) : ...
```

**Cascade cost**: ~4000 LoC.

**Consumer**: verified concurrent algorithms (Paxos, Raft, HotStuff,
BFT), verified shared-memory concurrency.

**Tier ★★★ total**: 27 ctors, ~25K LoC cascade.

---

## 5. Tier ★★ — Honorable mentions (specialty completeness)

These are coherent kernel candidates that lose the ROI fight against
Tiers ★★★★★/★★★★/★★★ at current FX priorities. They're catalogued so
future engineers can revisit when their consumer eras arrive.

### 5.1 Cubical Kan Completion (2 ctors)

FX has `hcomp` and `transp` but full Cubical TT needs:

```lean
| compCubical {...} : ...  -- full Kan composition (more general than hcomp)
| transpHigherDim {...} : ...  -- higher-dimensional transport
```

**Cascade**: ~2000 LoC. **Consumer**: full cubical type theory parity.

### 5.2 Algebraic Kernel Structures (3 ctors)

Group, ring, field structures as kernel ctors for synthetic algebra:

```lean
| groupAlg {...} (carrier : Ty) (mul : ...) (inv : ...) (laws : ...) : ...
| ringAlg {...} (carrier : Ty) (add mul : ...) (laws : ...) : ...
| moduleAlg {...} (ring : ...) (carrier : ...) (scalarMul : ...) : ...
```

**Cascade**: ~2500 LoC. **Consumer**: accelerated crypto (Z/pZ, GF(2^n),
elliptic curves), verified algebra (Mathlib-style algebra without
library setoid encoding).

### 5.3 Type Derivatives / Container Calculus (3 ctors)

McBride's container derivatives — `∂T` is "T with a hole":

```lean
| containerDeriv {...} (poly : ...) : Term context Ty.poly ...  -- ∂P
| zipperType {...} (base : ...) : ...  -- zipper as kernel type
| plugOp {...} (zipper : ...) (value : ...) : ...  -- fill the hole
```

**Cascade**: ~3000 LoC. **Consumer**: verified UI editors, verified
database query optimization, verified optics libraries.

### 5.4 Differential Lambda (3 ctors)

Ehrhard-Regnier categorical foundation for differentiable programming:

```lean
| diffLambda {...} (body : ...) : ...  -- ∂(λx.M)
| diffApply {...} (linearArg : ...) (point : ...) : ...
| differentialCategory {...} (witness : ...) : ...
```

**Cascade**: ~4000 LoC. **Consumer**: theoretical foundations of
differentiable programming (paired with Tier 2.7 SDG).

### 5.5 Linear / Substructural Logic (4 ctors)

Beyond FX's grade-based linearity:

```lean
| bangModality {...} (carrier : Ty) : ...  -- !A
| whyNotModality {...} (carrier : Ty) : ...  -- ?A
| linearArrow {...} (source target : Ty) : ...  -- A ⊸ B
| tensorProduct {...} (left right : Ty) : ...  -- A ⊗ B
```

**Cascade**: ~4000 LoC. **Consumer**: verified resource-aware
programming, linear-logic-based session types.

### 5.6 Provability / Dynamic Logic (2 ctors)

For program logic + Gödel's provability:

```lean
| provability {...} (statement : Ty) : ...  -- GL-style box
| dynamicLogic {...} (program : ...) (postcondition : ...) : ...  -- [α]φ
```

**Cascade**: ~2500 LoC. **Consumer**: verified Hoare-logic-based
program reasoning, formal incompleteness proofs.

### 5.7 Domain Theory CPO (4 ctors)

For Scott domains + denotational semantics:

```lean
| cpo {...} (carrier : Ty) (order : ...) (lubsExist : ...) : ...
| bottomElem {...} (cpo : ...) : ...
| scottContinuous {...} (cpo : ...) (fn : ...) (continuity : ...) : ...
| fixedPoint {...} (cpo : ...) (continuousFn : ...) : ...  -- μ-operator
```

**Cascade**: ~4000 LoC. **Consumer**: verified compiler denotational
semantics, verified partial recursive functions.

### 5.8 Hyperreal Numbers (3 ctors)

Robinson's non-standard analysis — alternative to SDG (Tier 2.7):

```lean
| hyperreal {...} : Term context Ty.hyperreal ...
| starOp {...} (operation : ...) : ...  -- star-transfer
| standardPart {...} (hyper : Ty.hyperreal) : Term context Ty.real ...
```

**Cascade**: ~3000 LoC. **Consumer**: alternative analysis foundation
(some communities prefer non-standard to synthetic differential).

### 5.9 Cellular Automata + Reversible Computation (3 ctors)

For verified parallel + reversible computation models:

```lean
| cellularAutomaton {...} (rule : ...) (universe : ...) : ...
| interactionNet {...} (agents : ...) (rules : ...) : ...  -- Lafont
| reversibleOp {...} (op : ...) (invertibilityWitness : ...) : ...
```

**Cascade**: ~3000 LoC. **Consumer**: novel computational architectures,
verified parallel algorithms, reversible computing research.

### 5.10 Synthetic Complexity Theory (3 ctors)

Beyond FX's grade-based complexity dimension:

```lean
| bigO {...} (f g : Ty.nat →ᵢ Ty.nat) (witnessConstant : ...) : ...
| polyTimeWitness {...} (algorithm : ...) (polyBound : ...) : ...
| npComplete {...} (problem : ...) (reductionWitness : ...) : ...
```

**Cascade**: ~3000 LoC. **Consumer**: verified complexity-theoretic
crypto assumptions (DDH, LWE), verified algorithm complexity bounds.

**Tier ★★ total**: 30 ctors, ~31K LoC cascade. *Honorable mention —
adopt selectively when domain pull justifies cost.*

---

## 6. Tier ★ — Honorable mentions (research-grade)

These are coherent but speculative. They earn kernel place only if a
specific research program explicitly funds them.

### 6.1 Forcing / Independence Proofs (3 ctors)

For Cohen-style independence results (Continuum Hypothesis, AC, etc.):

```lean
| forcingNotation {...} (posetOfConditions : ...) : ...
| genericFilter {...} (forcing : ...) : ...
| independenceProof {...} (statement : ...) (independenceWitness : ...) : ...
```

**Cascade**: ~3000 LoC. **Consumer**: foundational mathematics research.

### 6.2 Surreal Numbers / Combinatorial Game Theory (3 ctors)

Conway's surreals + combinatorial games:

```lean
| surrealNum {...} (leftOptions rightOptions : ...) : ...
| gameValue {...} (combinatorialGame : ...) : ...
| gameSum {...} (left right : ...) : ...
```

**Cascade**: ~3000 LoC. **Consumer**: game theory (chess engines, Go AI
formal analysis), combinatorial game theory research.

### 6.3 Vertex Operator Algebras (3 ctors)

For verified conformal field theory + string theory:

```lean
| vertexAlgebra {...} (stateSpace : ...) (vertexOps : ...) : ...
| conformalWeight {...} (state : ...) : ...
| opeProduct {...} (left right : ...) : ...
```

**Cascade**: ~3000 LoC. **Consumer**: mathematical physics research
(super-niche).

### 6.4 Higher Categorical Primitives (3 ctors)

For ∞-category theory + ω-groupoids:

```lean
| nCell {...} (dimension : Nat) (source target : ...) : ...
| compositionNCell {...} (cell1 cell2 : ...) (coherence : ...) : ...
| adjointPair {...} (left right : ...) (unitCounit : ...) : ...
```

**Cascade**: ~3500 LoC. **Consumer**: synthetic ∞-mathematics, research
credibility.

### 6.5 Realizability Types (3 ctors)

For extracting computational content from classical proofs:

```lean
| realizer {...} (proposition : ...) (witness : ...) : ...
| extractRealizer {...} (classicalProof : ...) : ...
| forcingNotationKreisel {...} : ...
```

**Cascade**: ~2500 LoC. **Consumer**: verified compiler-correctness
chains, deciding independence, Kreisel-style classical-to-constructive
extraction.

### 6.6 FRP Behaviors / Events (3 ctors)

For continuous-time / reactive systems:

```lean
| behaviorT {...} (carrier : Ty) : ...  -- Time → A
| eventT {...} (carrier : Ty) : ...     -- (Time, A) stream
| frpCombinator {...} (switch snapshot filter : ...) : ...
```

**Cascade**: ~3000 LoC. **Consumer**: verified GUIs, IoT controllers,
reactive web servers (overlaps with Tier 2.6 Temporal Logic for
discrete-time variants).

### 6.7 Combinatorial Species (3 ctors)

Joyal's theory — type-level combinatorics:

```lean
| species {...} (labelledStructureFunctor : ...) : ...
| genFunction {...} (species : ...) : ...  -- generating function
| cycleIndex {...} (species : ...) : ...
```

**Cascade**: ~3000 LoC. **Consumer**: verified algorithm analysis
(counting arguments), combinatorial enumeration.

### 6.8 Cohesion Beyond 4 Modalities (4 ctors)

Generalized cohesive modal type theory:

```lean
| cohesionWitness {...} : ...   -- abstract cohesion
| infinitesimalShape {...} : ... -- infinitesimal modality ℑ
| reducedShape {...} : ...      -- reduced modality &
| etaleShape {...} : ...        -- étale modality ʃ_dR
```

**Cascade**: ~4000 LoC. **Consumer**: synthetic algebraic geometry,
differential cohesion research.

**Tier ★ total**: 25 ctors, ~25K LoC cascade. *Research-grade — most
won't ship.*

---

## 7. Explicitly REJECTED — what stays library or DSL

To prevent kernel bloat, these candidates are PERMANENTLY library-level
(no future re-evaluation):

| Candidate | Why library, not kernel |
|-----------|-------------------------|
| Cryptographic algorithms (AES, SHA-3, Ed25519, ChaCha20-Poly1305) | Library over kernel finite-field + bit-vector primitives — no SR involvement |
| Neural network layers (Dense, Conv, Attention) | Library over kernel tensor + autodiff primitives |
| Specific physics models (Newton, Maxwell, Einstein) | Library over Tier 2.7 SDG + 2.5 measure theory |
| Financial derivatives (Black-Scholes, options Greeks) | Library over kernel decimal + stochastic primitives |
| Smart contract languages (Solidity, Vyper) | Library — semantics encoded as state machines + library types |
| Specific consensus protocols (Raft, Paxos, HotStuff) | Library over Tier 3.1 sessions + Tier 4.7 process calculi |
| ODE/PDE solvers (RK4, FEM) | Library over Tier 2.7 SDG + 3.3 computational reals |
| Compiler optimization passes | Library — each pass as proof-carrying transformation over kernel Term |
| Specific algorithms (sort, search, graph) | Library — verified algorithm libraries grow indefinitely |
| Surface syntax extensions | NEVER kernel — FX hard rule §25.7 (no dialect) |
| Database query optimization | Library — relational algebra encoded over kernel types |
| Specific PL semantics (TypeScript, Python type checking) | Library via reflection / encoding bridge (K15 / K19 eras) |

**Architectural principle**: the kernel is for things that NEED kernel
infrastructure (SR, definitional equality, reduction rules); everything
else lives one layer up.

---

## 8. Cross-domain consumer matrix

This matrix shows which Tier candidates each voracious-FX domain
actually needs. It's the "earn kernel place" check from §0 made
concrete.

| Domain → | Cryp | ML | Net | HW | Phys | Fin | Mil | QM | Math | AI |
|----------|------|----|----|----|----|----|----|----|----|----|
| **Tier ★★★★★** |  |  |  |  |  |  |  |  |  |  |
| 2.1 Computational Quotients | ✓ | ✓ | ✓ | ◐ | ✓ | ✓ | ◐ | ✓ | ✓✓ | ✓ |
| 2.2 Pushout HIT | ◐ | ◐ | ◐ | ◐ | ✓ | ◐ | ◐ | ✓ | ✓✓ | ◐ |
| 2.3 Truncations | ✓ | ◐ | ◐ | ◐ | ◐ | ◐ | ✓ | ◐ | ✓✓ | ✓ |
| 2.4 Polynomial Functors | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓✓ | ✓ |
| 2.5 σ-Algebra + Measure | ✓ | ✓✓ | ◐ | ◐ | ✓✓ | ✓✓ | ◐ | ✓ | ✓✓ | ✓ |
| 2.6 Temporal Logic | ◐ | ◐ | ✓✓ | ✓✓ | ✓ | ✓ | ✓✓ | ◐ | ◐ | ✓ |
| 2.7 Synthetic Differentials | ◐ | ✓✓ | ◐ | ◐ | ✓✓ | ✓ | ◐ | ✓ | ✓ | ✓ |
| **Tier ★★★★** |  |  |  |  |  |  |  |  |  |  |
| 3.1 Session protocols | ◐ | ◐ | ✓✓ | ✓ | – | ✓ | ✓ | ◐ | – | ◐ |
| 3.2 Hardware regs | – | – | ◐ | ✓✓ | – | – | ✓ | ✓ | – | – |
| 3.3 Computational Reals | – | ✓ | – | – | ✓✓ | ✓✓ | ◐ | ✓ | ✓ | ✓ |
| 3.4 Probability Kernel | ✓ | ✓✓ | ◐ | – | ✓ | ✓✓ | ◐ | ✓ | ✓ | ✓ |
| 3.5 p-adic Numbers | ✓✓ | – | – | – | – | – | ◐ | – | ✓ | – |
| 3.6 Universal Composability | ✓✓ | ◐ | ✓ | – | – | ◐ | ✓✓ | ◐ | – | – |
| 3.7 Information Theory | ✓ | ✓✓ | ✓ | ◐ | ✓ | ◐ | ✓ | ✓ | ✓ | ✓ |
| 3.8 Spectral Theory | ◐ | ✓ | ◐ | ◐ | ✓✓ | ✓ | ◐ | ✓✓ | ✓ | ✓ |
| 3.9 Causal Calculus | – | ✓✓ | – | – | ✓ | ✓ | ◐ | – | ◐ | ✓✓ |

Legend: ✓✓ = critical, ✓ = useful, ◐ = occasional, – = unused.

**Insight**: Tier 2.4 (Polynomial Functors) is the only ctor family
that's "✓ for every voracious domain". That's the strongest signal
that it should be the FIRST architectural refactor.

---

## 9. The polynomial-functor architectural endgame

The deepest move in this proposal isn't ADDING ctors — it's
REFACTORING the kernel via polynomial functors so that most existing
inductive ctors become library definitions over a generic Poly
framework.

### Pre-Poly kernel (current 78 ctors, much in inductive families)

```
nat: natZero, natSucc, natElim, natRec
list: listNil, listCons, listElim
option: optionNone, optionSome, optionMatch
either: eitherInl, eitherInr, eitherMatch
record: recordIntro, recordProj
codata: codataUnfold, codataDest
```

→ Six independent families, each with own SR proofs, own
rename/subst arms, own cd_lemma cases. Roughly 20 ctors × 800 LoC = 16K
LoC of cascade.

### Post-Poly kernel (~50 ctors, polynomial-unified)

```
Poly framework: polyFunctor, polyApply, polyMu, polyNu, polyMap
+ Step.par.betaPolyRec — ONE β-rule covers all inductive elimination
+ Step.par.betaPolyUnfold — ONE β-rule for coinductive observation
```

Library definitions:
```
nat := polyMu (1 + X)
list A := polyMu (1 + A × X)
option A := polyMu (1 + A)
either A B := polyMu (A + B)
record (fields) := library record over Σ
codata := polyNu (...)
```

→ 5 kernel ctors instead of 20. ONE SR proof. Reductions auto-derive.
~13K LoC less cascade overall.

### Net kernel size after Poly refactor

```
Current:                              78 ctors
+ Tier ★★★★★ (excl. Poly):           +25 ctors
+ Tier ★★★★ (selectively):           +25 ctors
+ Poly REPLACES ~15 existing:         -15 ctors
                                      ===========
Post-refactor pragmatic ceiling:     ~113 ctors
```

That's well within sustainable kernel territory while accommodating
the full voracious-FX semantic ambition.

### Risk

Polynomial-functor encoding has known pain points in Lean 4: parameterized
mutual inductives, dependent fibers, decidable equality propagation.
The refactor would need careful prototyping (3-6 months) before
production adoption. But it's the only architectural move that allows
the voracious FX to fit within engineering budget.

---

## 10. Recommended roadmap

Year-by-year shipping order for the voracious-FX kernel:

### Year 1 (next 6-12 months)

* Q1: Tier 2.1 Computational Quotients (5 ctors) — foundation
* Q2: Tier 2.2 Pushout HIT (4 ctors) — universal HIT
* Q3: Tier 2.3 Truncations (4 ctors)
* Q4: Tier 2.6 Temporal Logic (5 ctors) — independent track

End-of-year-1 kernel: 78 + 18 = **96 ctors**. Full HoTT shipped. Real-time + reactive proofs unlocked.

### Year 2

* Q1: Tier 2.4 Polynomial Functors (5 ctors + REFACTOR existing 15-20 ctors)
* Q2: Tier 2.5 Measure Theory (3 ctors)
* Q3: Tier 2.7 Synthetic Differentials (4 ctors)
* Q4: Tier 3.1 Session completion (5 ctors)

End-of-year-2 kernel: ~96 + 17 - 15 (Poly refactor reduction) = **~98 ctors**. ML + physics + verified protocols unlocked.

### Year 3

* Q1: Tier 3.2 Hardware regs (6 ctors) — fx-chip
* Q2: Tier 3.4 Probability + Tier 3.7 Information Theory (7 ctors)
* Q3: Tier 3.6 UC + Tier 3.5 p-adic (7 ctors)
* Q4: Tier 4.3 QIITs + Tier 4.4 2LTT (5 ctors) — bootstrap-ready

End-of-year-3 kernel: ~98 + 25 = **~123 ctors**. Verified crypto + hardware + Bayesian + FX-in-FX shipped.

### Year 4

* Q1-Q2: Tier 4.5 Quantum gates + Tier 3.8 Spectral (9 ctors)
* Q3: Tier 4.1 Circle + Higher Path (6 ctors)
* Q4: Tier 4.2 Cohesive Modalities (4 ctors)

End-of-year-4 kernel: ~123 + 19 = **~142 ctors**. Verified quantum + synthetic homotopy shipped.

### Year 5

* Tier 4.6 Game Semantics + Tier 4.7 Process Calculi (7 ctors)
* Selective Tier ★★ honorable mentions (3-5 ctors)
* Audit gates + library buildout consolidation

End-of-year-5 kernel: **~150-155 ctors**. Voracious-FX core complete.

### Beyond Year 5

* Selective Tier ★ research-grade additions only when funded
* Library + DSL ecosystem buildout (~500K+ LoC of library code)
* External bridges (Layer 4) to Lean/Coq/Agda/Isabelle/SMT solvers
* Stretch goals: synthetic AI alignment, synthetic DP, synthetic
  mechanism design

---

## 11. Architectural principles (summary)

The following design rules govern Term constructor additions:

1. **Earns-kernel-place criterion**: a ctor candidate must satisfy ALL
   four sub-criteria (definitional behavior gap, SR coherence,
   downstream amortization, orthogonality). Failure on any one means
   library-level instead.

2. **Cascade-cost reality**: each kernel ctor costs ~600-1000 LoC of
   work across 16 files. Plan additions in tranches of 5-10 ctors with
   intermediate audit gates.

3. **Polynomial-functor preference**: when possible, prefer adding a
   parameterized framework over multiple specialized ctors. Polynomial
   functors are the canonical example.

4. **Library encoding rule**: every domain-specific algorithm (crypto
   primitives, ML layers, physics models, financial derivatives,
   compiler passes) lives at library level. Kernel ctors only for
   things that need definitional behavior.

5. **DSL embedding rule**: domain-specific syntactic conveniences live
   at K15 reflection layer / K3 DSL layer, never kernel.

6. **External bridge rule**: cross-system reasoning (FX ↔ Lean,
   FX ↔ Coq, FX ↔ SMT) lives at K17+ bridge layer.

7. **Pragmatic ceiling**: ~150 ctors is the engineering-sustainable
   maximum without polynomial-functor refactor; ~180 ctors with the
   refactor. Beyond that, productivity collapses.

8. **Zero-axiom discipline**: ALL kernel ctors must support
   `#print axioms` reporting clean. No `propext`/`Quot.sound`/
   `Classical.choice` allowed. Every cascade theorem zero-axiom.

9. **ASCII-only, ≥4-char names**: per `WORKING_RULES.md`.

10. **Cascade gate discipline**: kernel-only `lake build LeanFX2` per
    commit; full `lake build LeanFX2Audit` at end of each tranche.

---

## 12. Closing — the voracious-coherent FX

FX wants to be everything: crypto, ML, network, hardware, physics,
finance, military, quantum, mathematics, AI. This doc enumerates the
~150-180 kernel constructors that earn their place toward that vision.

The architecture isn't "monolithic everything-kernel". It's:

* **~150 kernel ctors** (small trusted core)
* **~500K LoC library** (vast ecosystem)
* **~50K LoC reflective DSLs** (per-domain syntax)
* **~50K LoC external bridges** (Lean / Coq / Agda / SMT / hardware)

Each layer scales differently. The kernel grows SLOWLY (~150 ctors
over 5 years). The library + DSL + bridge layers grow VORACIOUSLY
(unbounded, multi-decade).

The kernel's role is to be the trust anchor. Library and DSLs
compose on top. Bridges extract to other verified systems. This is
the same architectural shape as Lean (small kernel, vast Mathlib),
Rocq (small kernel, vast packages), Agda (small kernel, vast standard
library) — but with FX's distinctive 21-dimensional graded modal type
theory providing strictly more semantic richness per ctor.

Going from 78 to 150 ctors is the next 5-year architectural commitment.
Beyond that, polynomial-functor refactor + library scale-out + DSL
proliferation + external bridges = the voracious-coherent FX endpoint.

The Term constructor proposals in this doc — across Tiers ★★★★★ ★★★★
★★★ ★★ ★ — are the concrete enumeration of that commitment.

---

## Appendix A — Quick reference: all candidates sorted by tier

```
Tier ★★★★★ (30 ctors, ~22K LoC, recommended Year 1-2):
  2.1 Computational Quotients (5)
  2.2 Universal Pushout HIT (4)
  2.3 Truncations (4)
  2.4 Polynomial Functors (5)
  2.5 σ-Algebra + Measure (3)
  2.6 Temporal Logic (5)
  2.7 Synthetic Differentials (4)

Tier ★★★★ (35 ctors, ~32K LoC, recommended Year 2-3):
  3.1 Session protocol completion (5)
  3.2 Hardware register / clock core (6)
  3.3 Computational Reals (3)
  3.4 Probability Kernel (3)
  3.5 p-adic Numbers (3)
  3.6 Universal Composability (4)
  3.7 Information Theory (4)
  3.8 Spectral Theory (4)
  3.9 Causal Calculus (3)

Tier ★★★ (27 ctors, ~25K LoC, recommended Year 3-5):
  4.1 Circle + Higher Path Operations (6)
  4.2 Cohesive Modalities (4)
  4.3 QIITs (2)
  4.4 2LTT (3)
  4.5 Quantum gates (5)
  4.6 Game Semantics (3)
  4.7 Process Calculi (4)

Tier ★★ honorable mentions (30 ctors, ~31K LoC, selective):
  5.1 Cubical Kan Completion (2)
  5.2 Algebraic Kernel Structures (3)
  5.3 Type Derivatives / Container Calculus (3)
  5.4 Differential Lambda (3)
  5.5 Linear / Substructural Logic (4)
  5.6 Provability / Dynamic Logic (2)
  5.7 Domain Theory CPO (4)
  5.8 Hyperreal Numbers (3)
  5.9 Cellular Automata + Reversible (3)
  5.10 Synthetic Complexity Theory (3)

Tier ★ research-grade honorable mentions (25 ctors, ~25K LoC, on-demand):
  6.1 Forcing / Independence (3)
  6.2 Surreal Numbers / CGT (3)
  6.3 Vertex Operator Algebras (3)
  6.4 Higher Categorical Primitives (3)
  6.5 Realizability Types (3)
  6.6 FRP Behaviors / Events (3)
  6.7 Combinatorial Species (3)
  6.8 Cohesion Beyond 4 (4)

EXPLICITLY REJECTED (stays library/DSL):
  Crypto algorithms (AES, SHA, Ed25519, etc.)
  ML layers (Dense, Conv, Attention)
  Specific physics models (Newton, Maxwell)
  Financial derivatives (Black-Scholes)
  Smart contract languages
  Consensus protocol specifics
  ODE/PDE solvers
  Compiler optimization passes
  Specific algorithms (sort, graph)
  Surface syntax extensions
  Database query optimization
  Specific PL semantics
```

**Cumulative kernel total** if all Tiers ★★★★★ + ★★★★ + ★★★ adopted:
78 + 92 = **170 ctors**.

**With polynomial-functor refactor** reducing ~15 existing inductive
ctors to Poly instances: **~155 ctors**.

This is the voracious-FX kernel ceiling. Beyond it, polynomial-functor
+ library + DSL scale-out + external bridges become mandatory.

---

## Appendix B — Cross-references

* `lean-fx-2/CLAUDE.md` — kernel discipline, zero-axiom commitment
* `lean-fx-2/AXIOMS.md` — per-axiom catastrophe analysis
* `lean-fx-2/ROADMAP.md` — phase-by-phase shipping
* `lean-fx-2/docs/T2_CLOSURE_PLAN.md` — Phase α/β/γ for T2 closure
  (companion doc; specific blocker resolution)
* `fx_design.md` §6 / §27 / Appendix H — MTT spine + axiom discipline
* `fx_design.md` §13 — state machines, temporal logic, refinement
* `fx_design.md` §17-§18 — hardware semantics, bit-level types
* `fx_design.md` §28 — six reference implementations (fx-chip, fx-driver,
  fx-net, fx-db, fx-image, fx-numeric)

---

**Document author**: Claude (Opus 4.7) via FX kernel ultrathink session.
**Last updated**: 2026-05-21.
**Status**: forward-looking architectural survey; subject to revision
as voracious-FX domain priorities evolve.
**License**: Internal FX engineering doc; standard FX repository licensing.
