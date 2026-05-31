import FX1Poly.Universe.LevelExpr
import FX1Poly.Universe.UniverseFlag

/-! # FX1Poly/Core/GeneratorCore — Generator substrate (no typed-term dep)

The 74-summand Generator enum + arity + binderShifts + discipline lemma.
This carrier is deliberately free of any TYPED-TERM import: it is the
Allais universe-of-syntaxes descriptor (arXiv:2001.11001) that every
PolyCell layer inducts over ONCE, and `RawTerm` is defined OVER it — so a
typed-term import would be a cycle.  That cycle, not imports in general, is
what the invariant guards against.

## Payload-alphabet discipline

`Generator.payload` assigns each generator its local scalar type.  Per the
Allais pattern the descriptor is PARAMETERIZED by this payload alphabet, so
the alphabet's types are legitimate imports here — PROVIDED each is a
foundational LEAF: combinatorial, self-contained, and typed-term-free (it
cannot reach `RawTerm`, hence cannot close the guarded cycle).  The current
alphabet is `Fin` / `Nat` / `Unit` (from Init) plus `LevelExpr × UniverseFlag`
for `gen_universeCode` — the universe-level polynomial + Setzer-Rathjen
strength flag (§11.8.2), both self-contained inductives in the Universe
layer.  Rich payloads (cubical `FaceFormula`, guarded clocks) may
join the alphabet ONLY if they too are leaves.  The serialized `List Nat`
wire form for FX0 certificates is produced at the FX1->FX0 boundary
(`UniversePayloadSerialize`), NOT smeared into this descriptor. -/

namespace FX1Poly.Core

/-- Full 74-summand polygraph generator enum.  Mirrors
`FX1Poly.Core.RawTerm`'s 74 constructors one-to-one (see
`FX1Poly/Core/RawTerm.lean`).  Grouped by family with comments
matching the RawTerm source's grouping.

Each Generator name is the RawTerm ctor name prefixed with
`gen_`.  This preserves the bijection at the name level: a
reader who knows RawTerm's vocabulary recognizes every summand
immediately. -/
inductive Generator : Type
  -- Variable + unit
  | gen_var
  | gen_unit
  -- Function intro/elim (covers arrow and Π applications)
  | gen_lam
  | gen_app
  -- Pair intro/elim (covers non-dep and Σ)
  | gen_pair
  | gen_fst
  | gen_snd
  -- Booleans
  | gen_boolTrue
  | gen_boolFalse
  | gen_boolElim
  -- Naturals
  | gen_natZero
  | gen_natSucc
  | gen_natElim
  | gen_natRec
  -- Lists
  | gen_listNil
  | gen_listCons
  | gen_listElim
  -- Options
  | gen_optionNone
  | gen_optionSome
  | gen_optionMatch
  -- Eithers
  | gen_eitherInl
  | gen_eitherInr
  | gen_eitherMatch
  -- Identity types
  | gen_refl
  | gen_idJ
  -- Modal
  | gen_modIntro
  | gen_modElim
  | gen_subsume
  -- Cubical interval endpoints + lattice operations
  | gen_interval0
  | gen_interval1
  | gen_intervalOpp
  | gen_intervalMeet
  | gen_intervalJoin
  -- Cubical path types (intro = lambda over interval, elim = path app)
  | gen_pathLam
  | gen_pathApp
  -- Cubical glue + transport / composition
  | gen_glueIntro
  | gen_glueElim
  | gen_transp
  | gen_hcomp
  -- Observational equality (set-level OEq) — refl, J eliminator, funext
  | gen_oeqRefl
  | gen_oeqJ
  | gen_oeqFunext
  -- Strict (definitional) identity — refl + eliminator
  | gen_idStrictRefl
  | gen_idStrictRec
  -- Type equivalence
  | gen_equivIntro
  | gen_equivApp
  -- Refinement types
  | gen_refineIntro
  | gen_refineElim
  -- Record types
  | gen_recordIntro
  | gen_recordProj
  -- Codata
  | gen_codataUnfold
  | gen_codataDest
  -- Session-typed channels
  | gen_sessionSend
  | gen_sessionRecv
  -- Algebraic effects
  | gen_effectPerform
  -- Universe-code term (LevelExpr × UniverseFlag payload, no RawTerm children)
  | gen_universeCode
  -- Per-shape type-code constructors (atom-shape)
  | gen_arrowCode
  -- Per-shape type-code constructors (binder-shape)
  | gen_piTyCode
  | gen_sigmaTyCode
  -- More atom-shape codes
  | gen_productCode
  | gen_sumCode
  | gen_listCode
  | gen_optionCode
  | gen_eitherCode
  | gen_idCode
  | gen_equivCode
  -- Cumulativity marker
  | gen_cumulUpMarker
  -- Univalence-to-equiv vocabulary
  | gen_uaToEquiv
  | gen_equivApply
  -- Cubical/HoTT composition vocabulary
  | gen_pathCompose
  | gen_idToEquiv
  | gen_oeqTrans
  | gen_equivCompose
  -- Cubical fill operation
  | gen_transpFill
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★★ extensions (28 ctors): voracious foundation
  --   docs/potential_ctors.md §2 — must-have for 5-year roadmap
  -- ═══════════════════════════════════════════════════════════════
  -- 2.1 Computational Quotients (HoTT structural ℤ/nℤ, ℚ, ℝ, gauges)
  | gen_quotMk
  | gen_quotEqAxiom
  | gen_quotRec
  | gen_quotElim
  -- 2.2 Universal Pushout HIT (suspension/coeq/sphere/smash/wedge/join library-derived)
  | gen_pushInl
  | gen_pushInr
  | gen_pushGlue
  | gen_pushRec
  -- 2.3 Truncations (propositional/set/n-truncation, single family parameterized by level)
  | gen_truncIntro
  | gen_truncCoh
  | gen_truncRec
  -- 2.4 Polynomial Functors (the architectural refactor candidate)
  | gen_polyFunctor
  | gen_polyApply
  | gen_polyMu
  | gen_polyNu
  | gen_polyMap
  -- 2.5 σ-Algebra + Measure (Lebesgue integration foundation)
  | gen_sigmaAlgebra
  | gen_measureSpace
  | gen_lebesgueInt
  -- 2.6 Temporal Logic (LTL/CTL kernel operators for real-time + reactive proofs)
  | gen_nextT
  | gen_alwaysT
  | gen_eventuallyT
  | gen_untilT
  | gen_sinceT
  -- 2.7 Synthetic Differentials (Kock-Lawvere, synthetic calculus + autodiff)
  | gen_infinitesimal
  | gen_microcanc
  | gen_tangentSpace
  | gen_diffOp
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★ extensions (35 ctors): domain completion
  --   docs/potential_ctors.md §3 — high-impact per-domain
  -- ═══════════════════════════════════════════════════════════════
  -- 3.1 Session protocol completion (π-calculus: TLS, Raft, payments)
  | gen_sessionSelect
  | gen_sessionOffer
  | gen_sessionClose
  | gen_channelSplit
  | gen_channelJoin
  -- 3.2 Hardware register / clock core (fx-chip RTL↔ISA structural)
  | gen_regRead
  | gen_regWrite
  | gen_clockTick
  | gen_stageLatch
  | gen_wireCombinational
  | gen_clockDomainCross
  -- 3.3 Computational Reals (constructive analysis with rigorous error bounds)
  | gen_realCauchy
  | gen_realLimit
  | gen_realCompare
  -- 3.4 Probability Kernel (Bayesian inference, MCMC, variational ML)
  | gen_probSpace
  | gen_sampleP
  | gen_expectE
  -- 3.5 p-adic Numbers (verified PQC: Kyber/Dilithium/Falcon)
  | gen_padicNum
  | gen_padicValuation
  | gen_localGlobalBridge
  -- 3.6 Universal Composability (Canetti UC — verified TLS/MPC/ZK)
  | gen_idealFunctionality
  | gen_realProtocol
  | gen_ucSimulator
  | gen_ucCompose
  -- 3.7 Information Theory (entropy, MI, KL, capacity)
  | gen_shannonEntropy
  | gen_mutualInfo
  | gen_klDivergence
  | gen_channelCapacity
  -- 3.8 Spectral Theory (Hilbert spaces, bounded ops, quantum mechanics)
  | gen_hilbertSpace
  | gen_boundedOperator
  | gen_spectralDecomp
  | gen_unitaryOp
  -- 3.9 Causal Calculus (Pearl do-calculus, counterfactuals)
  | gen_causalNet
  | gen_doOperator
  | gen_counterfactual
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★ extensions (27 ctors): mathematical completeness
  --   docs/potential_ctors.md §4 — essential for specific math sub-areas
  -- ═══════════════════════════════════════════════════════════════
  -- 4.1 Circle + Higher Path Operations (synthetic homotopy: π₁(S¹) = ℤ)
  | gen_circleBase
  | gen_circleLoop
  | gen_circleRec
  | gen_pathInverse
  | gen_pathWhiskerLeft
  | gen_pathWhiskerRight
  -- 4.2 Cohesive Modalities (Schreiber-Shulman ♭ ⊣ ◇ ⊣ □ ⊣ ♯)
  | gen_shapeModality
  | gen_flatModality
  | gen_sharpModality
  | gen_cohesiveAdjunctionUnit
  -- 4.3 Quotient Inductive-Inductive Types (FX-in-FX bootstrap)
  | gen_qiitIntro
  | gen_qiitElim
  -- 4.4 Two-Level Type Theory (inner univalent / outer strict bridges)
  | gen_liftInnerToOuter
  | gen_lowerOuterToInner
  | gen_modalityLayerMarker
  -- 4.5 Quantum gates (Shor, Grover, QFT, error correction)
  | gen_qubit
  | gen_quantumGate
  | gen_quantumMeasure
  | gen_quantumEntangle
  | gen_quantumDecohere
  -- 4.6 Game Semantics (sequential algorithm semantics, full-PCF)
  | gen_game
  | gen_strategy
  | gen_playOut
  -- 4.7 Process Calculi (CCS/CSP/π — Paxos, Raft, HotStuff, BFT)
  | gen_processCalc
  | gen_parallelComp
  | gen_processCommit
  | gen_bisimulationWitness
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★ extensions (30 ctors): honorable-mention completeness
  --   docs/potential_ctors.md §5 — adopted opportunistically
  -- ═══════════════════════════════════════════════════════════════
  -- 5.1 Cubical Kan Completion (full CTT parity beyond hcomp/transp)
  | gen_compCubical
  | gen_transpHigherDim
  -- 5.2 Algebraic Structures (groups, rings, modules — synthetic algebra)
  | gen_groupAlg
  | gen_ringAlg
  | gen_moduleAlg
  -- 5.3 Container Calculus (McBride derivatives, zippers, optics)
  | gen_containerDeriv
  | gen_zipperType
  | gen_plugOp
  -- 5.4 Differential Lambda (Ehrhard-Regnier categorical autodiff)
  | gen_diffLambda
  | gen_diffApply
  | gen_differentialCategory
  -- 5.5 Linear / Substructural Logic (!A, ?A, A⊸B, A⊗B)
  | gen_bangModality
  | gen_whyNotModality
  | gen_linearArrow
  | gen_tensorProduct
  -- 5.6 Provability / Dynamic Logic (GL-box, Hoare-style program logic)
  | gen_provabilityModality
  | gen_dynamicLogic
  -- 5.7 Domain Theory CPO (Scott domains, denotational semantics)
  | gen_cpoStructure
  | gen_bottomElem
  | gen_scottContinuous
  | gen_fixedPoint
  -- 5.8 Hyperreal Numbers (Robinson non-standard analysis)
  | gen_hyperreal
  | gen_starOp
  | gen_standardPart
  -- 5.9 Cellular Automata + Reversible Computation (Lafont interaction nets)
  | gen_cellularAutomaton
  | gen_interactionNet
  | gen_reversibleOp
  -- 5.10 Synthetic Complexity Theory (BigO, polytime witness, NP-completeness)
  | gen_bigOh
  | gen_polyTimeWitness
  | gen_npComplete
  deriving DecidableEq

/-- The child count per `Generator`.  Each entry equals the
number of `RawTerm`-valued payload fields in the corresponding
`RawTerm` constructor.  `var` carries a `Fin scope` position but
that does NOT count as a child (it lives at the variable layer,
not the polygraph fold input).  `universeCode` carries a `Nat`
payload, similarly not a child. -/
def Generator.arity : Generator → Nat
  -- Variable + unit (no RawTerm children)
  | .gen_var          => 0  -- Fin scope payload, not a child
  | .gen_unit         => 0
  -- Function
  | .gen_lam          => 1  -- body
  | .gen_app          => 2  -- functionTerm, argumentTerm
  -- Pair
  | .gen_pair         => 2  -- firstValue, secondValue
  | .gen_fst          => 1  -- pairTerm
  | .gen_snd          => 1  -- pairTerm
  -- Booleans
  | .gen_boolTrue     => 0
  | .gen_boolFalse    => 0
  | .gen_boolElim     => 3  -- scrutinee, thenBranch, elseBranch
  -- Naturals
  | .gen_natZero      => 0
  | .gen_natSucc      => 1  -- predecessor
  | .gen_natElim      => 3  -- scrutinee, zeroBranch, succBranch
  | .gen_natRec       => 3  -- scrutinee, zeroBranch, succBranch
  -- Lists
  | .gen_listNil      => 0
  | .gen_listCons     => 2  -- headTerm, tailTerm
  | .gen_listElim     => 3  -- scrutinee, nilBranch, consBranch
  -- Options
  | .gen_optionNone   => 0
  | .gen_optionSome   => 1  -- valueTerm
  | .gen_optionMatch  => 3  -- scrutinee, noneBranch, someBranch
  -- Eithers
  | .gen_eitherInl    => 1  -- valueTerm
  | .gen_eitherInr    => 1  -- valueTerm
  | .gen_eitherMatch  => 3  -- scrutinee, leftBranch, rightBranch
  -- Identity types
  | .gen_refl         => 1  -- rawWitness
  | .gen_idJ          => 2  -- baseCase, witness
  -- Modal
  | .gen_modIntro     => 1  -- raw
  | .gen_modElim      => 1  -- raw
  | .gen_subsume      => 1  -- raw
  -- Cubical interval
  | .gen_interval0    => 0
  | .gen_interval1    => 0
  | .gen_intervalOpp  => 1  -- intervalTerm
  | .gen_intervalMeet => 2  -- leftInterval, rightInterval
  | .gen_intervalJoin => 2  -- leftInterval, rightInterval
  -- Cubical path
  | .gen_pathLam      => 1  -- body
  | .gen_pathApp      => 2  -- pathTerm, intervalArg
  -- Cubical glue / transport / composition
  | .gen_glueIntro    => 2  -- baseValue, partialValue
  | .gen_glueElim     => 1  -- gluedValue
  | .gen_transp       => 2  -- path, source
  | .gen_hcomp        => 2  -- sides, cap
  -- Observational equality
  | .gen_oeqRefl      => 1  -- witness
  | .gen_oeqJ         => 2  -- baseCase, witness
  | .gen_oeqFunext    => 1  -- pointwiseEquality
  -- Strict identity
  | .gen_idStrictRefl => 1  -- witness
  | .gen_idStrictRec  => 2  -- baseCase, witness
  -- Type equivalence
  | .gen_equivIntro   => 2  -- forwardFn, backwardFn
  | .gen_equivApp     => 2  -- equivTerm, argument
  -- Refinement
  | .gen_refineIntro  => 2  -- rawValue, predicateProof
  | .gen_refineElim   => 1  -- refinedValue
  -- Record
  | .gen_recordIntro  => 1  -- firstField
  | .gen_recordProj   => 1  -- recordValue
  -- Codata
  | .gen_codataUnfold => 2  -- initialState, transition
  | .gen_codataDest   => 1  -- codataValue
  -- Sessions
  | .gen_sessionSend  => 2  -- channel, payload
  | .gen_sessionRecv  => 1  -- channel
  -- Effects
  | .gen_effectPerform => 2 -- operationTag, arguments
  -- Universe code (Nat payload, no RawTerm children)
  | .gen_universeCode => 0
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    => 2  -- domainCode, codomainCode
  -- Per-shape type codes (binder-shape)
  | .gen_piTyCode     => 2  -- domainCode, codomainCode (codomain at scope+1)
  | .gen_sigmaTyCode  => 2  -- domainCode, codomainCode (codomain at scope+1)
  -- More atom-shape codes
  | .gen_productCode  => 2  -- firstCode, secondCode
  | .gen_sumCode      => 2  -- leftCode, rightCode
  | .gen_listCode     => 1  -- elementCode
  | .gen_optionCode   => 1  -- elementCode
  | .gen_eitherCode   => 2  -- leftCode, rightCode
  | .gen_idCode       => 3  -- typeCode, leftRaw, rightRaw
  | .gen_equivCode    => 2  -- leftTypeCode, rightTypeCode
  -- Cumulativity marker
  | .gen_cumulUpMarker => 1 -- innerCodeRaw
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv    => 1  -- proofRaw
  | .gen_equivApply   => 2  -- equivRaw, argRaw
  -- Composition vocabulary
  | .gen_pathCompose  => 2  -- leftPathRaw, rightPathRaw
  | .gen_idToEquiv    => 1  -- proofRaw
  | .gen_oeqTrans     => 2  -- firstProof, secondProof
  | .gen_equivCompose => 2  -- firstEquiv, secondEquiv
  -- Cubical fill
  | .gen_transpFill   => 3  -- pathTy, currentInterval, source
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 2.1 Computational Quotients
  | .gen_quotMk        => 1  -- value
  | .gen_quotEqAxiom   => 1  -- equivalenceWitness
  | .gen_quotRec       => 3  -- kernelFn, respectsRel, scrutinee
  | .gen_quotElim      => 3  -- depMotive, depKernel, scrutinee
  -- 2.2 Universal Pushout HIT
  | .gen_pushInl       => 1  -- leftValue
  | .gen_pushInr       => 1  -- rightValue
  | .gen_pushGlue      => 1  -- middleValue
  | .gen_pushRec       => 4  -- caseInl, caseInr, caseGlue, scrutinee
  -- 2.3 Truncations
  | .gen_truncIntro    => 1  -- value (level in payload)
  | .gen_truncCoh      => 2  -- leftElem, rightElem (level in payload)
  | .gen_truncRec      => 2  -- kernelFn, scrutinee (level in payload)
  -- 2.4 Polynomial Functors
  | .gen_polyFunctor   => 2  -- shapeType, positionFamily (positionFamily at scope+1)
  | .gen_polyApply     => 2  -- polyValue, carrierType
  | .gen_polyMu        => 1  -- polyValue
  | .gen_polyNu        => 1  -- polyValue
  | .gen_polyMap       => 2  -- mapFn, polyValue
  -- 2.5 σ-Algebra + Measure
  | .gen_sigmaAlgebra  => 1  -- closureWitness
  | .gen_measureSpace  => 3  -- algebra, measureMap, countableAdditivity
  | .gen_lebesgueInt   => 2  -- space, integrand
  -- 2.6 Temporal Logic
  | .gen_nextT         => 1  -- proposition
  | .gen_alwaysT       => 1  -- proposition
  | .gen_eventuallyT   => 1  -- proposition
  | .gen_untilT        => 2  -- leftProp, rightProp
  | .gen_sinceT        => 2  -- leftProp, rightProp
  -- 2.7 Synthetic Differentials
  | .gen_infinitesimal => 1  -- carrier
  | .gen_microcanc     => 1  -- fn (D → R)
  | .gen_tangentSpace  => 2  -- manifold, basePoint
  | .gen_diffOp        => 2  -- manifold, fn
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 3.1 Sessions
  | .gen_sessionSelect => 2  -- channel, choice
  | .gen_sessionOffer  => 2  -- channel, branches
  | .gen_sessionClose  => 1  -- channel
  | .gen_channelSplit  => 1  -- channel
  | .gen_channelJoin   => 2  -- leftChannel, rightChannel
  -- 3.2 Hardware
  | .gen_regRead       => 2  -- registerId, cycle
  | .gen_regWrite      => 3  -- registerId, newValue, cycle
  | .gen_clockTick     => 1  -- clockDomain (a type)
  | .gen_stageLatch    => 2  -- stageInput, clockEdge
  | .gen_wireCombinational => 1  -- combinationalLogic
  | .gen_clockDomainCross  => 4  -- sourceClock, targetClock, signal, synchronizer
  -- 3.3 Computational Reals
  | .gen_realCauchy    => 2  -- cauchySeq, convergenceRate
  | .gen_realLimit     => 2  -- sequence, convergenceWitness
  | .gen_realCompare   => 3  -- left, right, epsilon
  -- 3.4 Probability
  | .gen_probSpace     => 2  -- probMeasure, totalMassOne
  | .gen_sampleP       => 1  -- space
  | .gen_expectE       => 2  -- space, randomVariable
  -- 3.5 p-adic
  | .gen_padicNum      => 3  -- prime, numerator, denominator
  | .gen_padicValuation => 2  -- prime, value
  | .gen_localGlobalBridge => 2  -- rationalProblem, everyLocalSolution
  -- 3.6 UC
  | .gen_idealFunctionality => 1  -- interface (a type)
  | .gen_realProtocol  => 1  -- protocolBody
  | .gen_ucSimulator   => 4  -- realProto, idealFunc, simulator, indistinguishability
  | .gen_ucCompose     => 2  -- innerUcWitness, outerUcWitness
  -- 3.7 Info Theory
  | .gen_shannonEntropy => 1  -- distribution
  | .gen_mutualInfo    => 1  -- jointDist
  | .gen_klDivergence  => 2  -- pDist, qDist
  | .gen_channelCapacity => 1  -- channel
  -- 3.8 Spectral
  | .gen_hilbertSpace  => 2  -- innerProduct, completeness
  | .gen_boundedOperator => 4  -- sourceHilbert, targetHilbert, linearMap, normBound
  | .gen_spectralDecomp => 2  -- selfAdjointOp, selfAdjointWitness
  | .gen_unitaryOp     => 2  -- op, unitarityWitness
  -- 3.9 Causal
  | .gen_causalNet     => 3  -- variables, parents, mechanisms
  | .gen_doOperator    => 2  -- network, intervention
  | .gen_counterfactual => 3  -- network, factual, intervention
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 4.1 Circle + Higher Paths
  | .gen_circleBase    => 0
  | .gen_circleLoop    => 0
  | .gen_circleRec     => 3  -- motive, baseCase, loopCase
  | .gen_pathInverse   => 1  -- pathValue
  | .gen_pathWhiskerLeft  => 2  -- pathValue, whiskerPath
  | .gen_pathWhiskerRight => 2  -- pathValue, whiskerPath
  -- 4.2 Cohesive Modalities
  | .gen_shapeModality => 1  -- carrier
  | .gen_flatModality  => 1  -- carrier
  | .gen_sharpModality => 1  -- carrier
  | .gen_cohesiveAdjunctionUnit => 1  -- modalityValue
  -- 4.3 QIITs
  | .gen_qiitIntro     => 1  -- mutualSpec
  | .gen_qiitElim      => 3  -- qiitValue, motive, caseHandlers
  -- 4.4 2LTT
  | .gen_liftInnerToOuter => 1  -- innerTerm
  | .gen_lowerOuterToInner => 2  -- outerTerm, cofibrancy
  | .gen_modalityLayerMarker => 1  -- modalityTag
  -- 4.5 Quantum
  | .gen_qubit         => 0
  | .gen_quantumGate   => 2  -- gateType, qubits
  | .gen_quantumMeasure => 2  -- qubits, outcome
  | .gen_quantumEntangle => 2  -- qubits, noCloningEnforcement
  | .gen_quantumDecohere => 3  -- qubits, noiseModel, fidelityBound
  -- 4.6 Game Semantics
  | .gen_game          => 1  -- positionTree
  | .gen_strategy      => 2  -- game, decisionTree
  | .gen_playOut       => 2  -- strategy1, strategy2
  -- 4.7 Process Calculi
  | .gen_processCalc   => 1  -- processDef
  | .gen_parallelComp  => 2  -- leftProcess, rightProcess
  | .gen_processCommit => 1  -- rendezvous
  | .gen_bisimulationWitness => 3  -- leftProcess, rightProcess, witnessRelation
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 5.1 Cubical Kan
  | .gen_compCubical   => 2  -- pathFamily, sides
  | .gen_transpHigherDim => 2  -- pathFamily, source
  -- 5.2 Algebraic Structures
  | .gen_groupAlg      => 4  -- carrier, mul, inv, laws
  | .gen_ringAlg       => 4  -- carrier, add, mul, laws
  | .gen_moduleAlg     => 3  -- ring, carrier, scalarMul
  -- 5.3 Container Calculus
  | .gen_containerDeriv => 1  -- polynomial
  | .gen_zipperType    => 1  -- baseType
  | .gen_plugOp        => 2  -- zipper, value
  -- 5.4 Differential Lambda
  | .gen_diffLambda    => 1  -- body (under one binder)
  | .gen_diffApply     => 2  -- linearArg, point
  | .gen_differentialCategory => 1  -- witness
  -- 5.5 Linear Logic
  | .gen_bangModality  => 1  -- carrier
  | .gen_whyNotModality => 1  -- carrier
  | .gen_linearArrow   => 2  -- source, target
  | .gen_tensorProduct => 2  -- leftFactor, rightFactor
  -- 5.6 Provability / Dynamic Logic
  | .gen_provabilityModality => 1  -- statement
  | .gen_dynamicLogic  => 2  -- program, postcondition
  -- 5.7 Domain Theory
  | .gen_cpoStructure  => 3  -- carrier, order, lubsExist
  | .gen_bottomElem    => 1  -- cpo
  | .gen_scottContinuous => 3  -- cpo, fn, continuity
  | .gen_fixedPoint    => 2  -- cpo, continuousFn
  -- 5.8 Hyperreals
  | .gen_hyperreal     => 0
  | .gen_starOp        => 1  -- operation
  | .gen_standardPart  => 1  -- hyper
  -- 5.9 CA / Reversible
  | .gen_cellularAutomaton => 2  -- rule, universe
  | .gen_interactionNet => 2  -- agents, rules
  | .gen_reversibleOp  => 2  -- op, invertibilityWitness
  -- 5.10 Synthetic Complexity
  | .gen_bigOh         => 3  -- f, g, witnessConstant
  | .gen_polyTimeWitness => 2  -- algorithm, polyBound
  | .gen_npComplete    => 2  -- problem, reductionWitness

/-- The per-child binder shifts as a non-dependent `List Nat`
table.  The list length equals `Generator.arity g` (by
construction, verified by `binderShifts_length_eq_arity`).  Each
list entry is the number of fresh binders introduced over the
corresponding child.

**Non-zero entries** (only four constructors carry binders):

* `gen_lam` — body lives under one fresh value binder, shift `1`.
* `gen_pathLam` — body lives under one fresh interval binder,
  shift `1`.
* `gen_piTyCode` — codomain lives at `scope + 1`, shift on the
  second child is `1`.  Mirrors `RawTerm.piTyCode`'s codomain
  index.
* `gen_sigmaTyCode` — codomain lives at `scope + 1`, shift on the
  second child is `1`.  Mirrors `RawTerm.sigmaTyCode`'s codomain
  index.

All other ctors have all-zero shifts.

**Why a `List Nat` rather than `Fin g.arity → Nat`**:
indexed-by-arity-zero Fin destructuring leaks propext via Lean's
match compilation (see `feedback_lean_zero_axiom_match.md`).
Returning a `List Nat` keeps the function arity-independent at the
type level, so each arm is a closed term — no dependent reduction,
no propext.  The length-check theorem
`binderShifts_length_eq_arity` recovers the total-function
discipline. -/
def Generator.binderShifts : Generator → List Nat
  -- Variable + unit
  | .gen_var          => []
  | .gen_unit         => []
  -- Function
  | .gen_lam          => [1]                 -- body under one fresh binder
  | .gen_app          => [0, 0]
  -- Pair
  | .gen_pair         => [0, 0]
  | .gen_fst          => [0]
  | .gen_snd          => [0]
  -- Booleans
  | .gen_boolTrue     => []
  | .gen_boolFalse    => []
  | .gen_boolElim     => [0, 0, 0]
  -- Naturals
  | .gen_natZero      => []
  | .gen_natSucc      => [0]
  | .gen_natElim      => [0, 0, 0]
  | .gen_natRec       => [0, 0, 0]
  -- Lists
  | .gen_listNil      => []
  | .gen_listCons     => [0, 0]
  | .gen_listElim     => [0, 0, 0]
  -- Options
  | .gen_optionNone   => []
  | .gen_optionSome   => [0]
  | .gen_optionMatch  => [0, 0, 0]
  -- Eithers
  | .gen_eitherInl    => [0]
  | .gen_eitherInr    => [0]
  | .gen_eitherMatch  => [0, 0, 0]
  -- Identity types
  | .gen_refl         => [0]
  | .gen_idJ          => [0, 0]
  -- Modal
  | .gen_modIntro     => [0]
  | .gen_modElim      => [0]
  | .gen_subsume      => [0]
  -- Cubical interval
  | .gen_interval0    => []
  | .gen_interval1    => []
  | .gen_intervalOpp  => [0]
  | .gen_intervalMeet => [0, 0]
  | .gen_intervalJoin => [0, 0]
  -- Cubical path
  | .gen_pathLam      => [1]                 -- body under one fresh interval binder
  | .gen_pathApp      => [0, 0]
  -- Cubical glue / transport / composition
  | .gen_glueIntro    => [0, 0]
  | .gen_glueElim     => [0]
  | .gen_transp       => [0, 0]
  | .gen_hcomp        => [0, 0]
  -- Observational equality
  | .gen_oeqRefl      => [0]
  | .gen_oeqJ         => [0, 0]
  | .gen_oeqFunext    => [0]
  -- Strict identity
  | .gen_idStrictRefl => [0]
  | .gen_idStrictRec  => [0, 0]
  -- Type equivalence
  | .gen_equivIntro   => [0, 0]
  | .gen_equivApp     => [0, 0]
  -- Refinement
  | .gen_refineIntro  => [0, 0]
  | .gen_refineElim   => [0]
  -- Record
  | .gen_recordIntro  => [0]
  | .gen_recordProj   => [0]
  -- Codata
  | .gen_codataUnfold => [0, 0]
  | .gen_codataDest   => [0]
  -- Sessions
  | .gen_sessionSend  => [0, 0]
  | .gen_sessionRecv  => [0]
  -- Effects
  | .gen_effectPerform => [0, 0]
  -- Universe code
  | .gen_universeCode => []
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    => [0, 0]
  -- Per-shape type codes (binder-shape)
  | .gen_piTyCode     => [0, 1]              -- codomain at scope + 1
  | .gen_sigmaTyCode  => [0, 1]              -- codomain at scope + 1
  -- More atom-shape codes
  | .gen_productCode  => [0, 0]
  | .gen_sumCode      => [0, 0]
  | .gen_listCode     => [0]
  | .gen_optionCode   => [0]
  | .gen_eitherCode   => [0, 0]
  | .gen_idCode       => [0, 0, 0]
  | .gen_equivCode    => [0, 0]
  -- Cumulativity marker
  | .gen_cumulUpMarker => [0]
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv    => [0]
  | .gen_equivApply   => [0, 0]
  -- Composition vocabulary
  | .gen_pathCompose  => [0, 0]
  | .gen_idToEquiv    => [0]
  | .gen_oeqTrans     => [0, 0]
  | .gen_equivCompose => [0, 0]
  -- Cubical fill
  | .gen_transpFill   => [0, 0, 0]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_quotMk        => [0]
  | .gen_quotEqAxiom   => [0]
  | .gen_quotRec       => [0, 0, 0]
  | .gen_quotElim      => [0, 0, 0]
  | .gen_pushInl       => [0]
  | .gen_pushInr       => [0]
  | .gen_pushGlue      => [0]
  | .gen_pushRec       => [0, 0, 0, 0]
  | .gen_truncIntro    => [0]
  | .gen_truncCoh      => [0, 0]
  | .gen_truncRec      => [0, 0]
  | .gen_polyFunctor   => [0, 1]              -- positionFamily at scope + 1
  | .gen_polyApply     => [0, 0]
  | .gen_polyMu        => [0]
  | .gen_polyNu        => [0]
  | .gen_polyMap       => [0, 0]
  | .gen_sigmaAlgebra  => [0]
  | .gen_measureSpace  => [0, 0, 0]
  | .gen_lebesgueInt   => [0, 0]
  | .gen_nextT         => [0]
  | .gen_alwaysT       => [0]
  | .gen_eventuallyT   => [0]
  | .gen_untilT        => [0, 0]
  | .gen_sinceT        => [0, 0]
  | .gen_infinitesimal => [0]
  | .gen_microcanc     => [0]
  | .gen_tangentSpace  => [0, 0]
  | .gen_diffOp        => [0, 0]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_sessionSelect => [0, 0]
  | .gen_sessionOffer  => [0, 0]
  | .gen_sessionClose  => [0]
  | .gen_channelSplit  => [0]
  | .gen_channelJoin   => [0, 0]
  | .gen_regRead       => [0, 0]
  | .gen_regWrite      => [0, 0, 0]
  | .gen_clockTick     => [0]
  | .gen_stageLatch    => [0, 0]
  | .gen_wireCombinational => [0]
  | .gen_clockDomainCross  => [0, 0, 0, 0]
  | .gen_realCauchy    => [0, 0]
  | .gen_realLimit     => [0, 0]
  | .gen_realCompare   => [0, 0, 0]
  | .gen_probSpace     => [0, 0]
  | .gen_sampleP       => [0]
  | .gen_expectE       => [0, 0]
  | .gen_padicNum      => [0, 0, 0]
  | .gen_padicValuation => [0, 0]
  | .gen_localGlobalBridge => [0, 0]
  | .gen_idealFunctionality => [0]
  | .gen_realProtocol  => [0]
  | .gen_ucSimulator   => [0, 0, 0, 0]
  | .gen_ucCompose     => [0, 0]
  | .gen_shannonEntropy => [0]
  | .gen_mutualInfo    => [0]
  | .gen_klDivergence  => [0, 0]
  | .gen_channelCapacity => [0]
  | .gen_hilbertSpace  => [0, 0]
  | .gen_boundedOperator => [0, 0, 0, 0]
  | .gen_spectralDecomp => [0, 0]
  | .gen_unitaryOp     => [0, 0]
  | .gen_causalNet     => [0, 0, 0]
  | .gen_doOperator    => [0, 0]
  | .gen_counterfactual => [0, 0, 0]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_circleBase    => []
  | .gen_circleLoop    => []
  | .gen_circleRec     => [0, 0, 0]
  | .gen_pathInverse   => [0]
  | .gen_pathWhiskerLeft  => [0, 0]
  | .gen_pathWhiskerRight => [0, 0]
  | .gen_shapeModality => [0]
  | .gen_flatModality  => [0]
  | .gen_sharpModality => [0]
  | .gen_cohesiveAdjunctionUnit => [0]
  | .gen_qiitIntro     => [0]
  | .gen_qiitElim      => [0, 0, 0]
  | .gen_liftInnerToOuter => [0]
  | .gen_lowerOuterToInner => [0, 0]
  | .gen_modalityLayerMarker => [0]
  | .gen_qubit         => []
  | .gen_quantumGate   => [0, 0]
  | .gen_quantumMeasure => [0, 0]
  | .gen_quantumEntangle => [0, 0]
  | .gen_quantumDecohere => [0, 0, 0]
  | .gen_game          => [0]
  | .gen_strategy      => [0, 0]
  | .gen_playOut       => [0, 0]
  | .gen_processCalc   => [0]
  | .gen_parallelComp  => [0, 0]
  | .gen_processCommit => [0]
  | .gen_bisimulationWitness => [0, 0, 0]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_compCubical   => [0, 0]
  | .gen_transpHigherDim => [0, 0]
  | .gen_groupAlg      => [0, 0, 0, 0]
  | .gen_ringAlg       => [0, 0, 0, 0]
  | .gen_moduleAlg     => [0, 0, 0]
  | .gen_containerDeriv => [0]
  | .gen_zipperType    => [0]
  | .gen_plugOp        => [0, 0]
  | .gen_diffLambda    => [1]                 -- body under one fresh binder
  | .gen_diffApply     => [0, 0]
  | .gen_differentialCategory => [0]
  | .gen_bangModality  => [0]
  | .gen_whyNotModality => [0]
  | .gen_linearArrow   => [0, 0]
  | .gen_tensorProduct => [0, 0]
  | .gen_provabilityModality => [0]
  | .gen_dynamicLogic  => [0, 0]
  | .gen_cpoStructure  => [0, 0, 0]
  | .gen_bottomElem    => [0]
  | .gen_scottContinuous => [0, 0, 0]
  | .gen_fixedPoint    => [0, 0]
  | .gen_hyperreal     => []
  | .gen_starOp        => [0]
  | .gen_standardPart  => [0]
  | .gen_cellularAutomaton => [0, 0]
  | .gen_interactionNet => [0, 0]
  | .gen_reversibleOp  => [0, 0]
  | .gen_bigOh         => [0, 0, 0]
  | .gen_polyTimeWitness => [0, 0]
  | .gen_npComplete    => [0, 0]

/-- The `binderShifts` table has length exactly `arity g`.
Proof is case-analysis on `g`; each of the 74 arms closes via
`rfl` (`[].length = 0`, `[x].length = 1`, etc.).  Recovers the
total-function discipline that a `Fin g.arity → Nat` signature
would carry at the type level (but at the cost of a propext
leak — see `binderShifts`'s docstring). -/
theorem Generator.binderShifts_length_eq_arity (g : Generator) :
    g.binderShifts.length = g.arity := by
  cases g <;> rfl

/-- Per-generator local-scalar payload type, indexed by scope.
`gen_var` maps to `Fin scope` (scope-safe BY CONSTRUCTION — no
`index < scope` side-condition needed).  `gen_universeCode` maps to
`LevelExpr × UniverseFlag` — the universe-level polynomial plus the
Setzer-Rathjen strength flag (§11.8.2); carrying the level in a
structured payload (rather than a bare `Nat`) keeps `Universe :
Universe` syntactically inadmissible (no Girard's paradox at the
admission level).  The truncation generators (`gen_truncIntro`,
`gen_truncCoh`, `gen_truncRec`) map to `Nat` (the truncation level);
all other ctors map to `Unit`.  Full enumeration, no wildcard. -/
def Generator.payload : Generator → Nat → Type
  | .gen_var, scope => Fin scope
  | .gen_universeCode, _ => FX1Poly.Universe.LevelExpr × FX1Poly.Universe.UniverseFlag
  | .gen_unit, _ => Unit
  | .gen_lam, _ => Unit
  | .gen_app, _ => Unit
  | .gen_pair, _ => Unit
  | .gen_fst, _ => Unit
  | .gen_snd, _ => Unit
  | .gen_boolTrue, _ => Unit
  | .gen_boolFalse, _ => Unit
  | .gen_boolElim, _ => Unit
  | .gen_natZero, _ => Unit
  | .gen_natSucc, _ => Unit
  | .gen_natElim, _ => Unit
  | .gen_natRec, _ => Unit
  | .gen_listNil, _ => Unit
  | .gen_listCons, _ => Unit
  | .gen_listElim, _ => Unit
  | .gen_optionNone, _ => Unit
  | .gen_optionSome, _ => Unit
  | .gen_optionMatch, _ => Unit
  | .gen_eitherInl, _ => Unit
  | .gen_eitherInr, _ => Unit
  | .gen_eitherMatch, _ => Unit
  | .gen_refl, _ => Unit
  | .gen_idJ, _ => Unit
  | .gen_modIntro, _ => Unit
  | .gen_modElim, _ => Unit
  | .gen_subsume, _ => Unit
  | .gen_interval0, _ => Unit
  | .gen_interval1, _ => Unit
  | .gen_intervalOpp, _ => Unit
  | .gen_intervalMeet, _ => Unit
  | .gen_intervalJoin, _ => Unit
  | .gen_pathLam, _ => Unit
  | .gen_pathApp, _ => Unit
  | .gen_glueIntro, _ => Unit
  | .gen_glueElim, _ => Unit
  | .gen_transp, _ => Unit
  | .gen_hcomp, _ => Unit
  | .gen_oeqRefl, _ => Unit
  | .gen_oeqJ, _ => Unit
  | .gen_oeqFunext, _ => Unit
  | .gen_idStrictRefl, _ => Unit
  | .gen_idStrictRec, _ => Unit
  | .gen_equivIntro, _ => Unit
  | .gen_equivApp, _ => Unit
  | .gen_refineIntro, _ => Unit
  | .gen_refineElim, _ => Unit
  | .gen_recordIntro, _ => Unit
  | .gen_recordProj, _ => Unit
  | .gen_codataUnfold, _ => Unit
  | .gen_codataDest, _ => Unit
  | .gen_sessionSend, _ => Unit
  | .gen_sessionRecv, _ => Unit
  | .gen_effectPerform, _ => Unit
  | .gen_arrowCode, _ => Unit
  | .gen_piTyCode, _ => Unit
  | .gen_sigmaTyCode, _ => Unit
  | .gen_productCode, _ => Unit
  | .gen_sumCode, _ => Unit
  | .gen_listCode, _ => Unit
  | .gen_optionCode, _ => Unit
  | .gen_eitherCode, _ => Unit
  | .gen_idCode, _ => Unit
  | .gen_equivCode, _ => Unit
  | .gen_cumulUpMarker, _ => Unit
  | .gen_uaToEquiv, _ => Unit
  | .gen_equivApply, _ => Unit
  | .gen_pathCompose, _ => Unit
  | .gen_idToEquiv, _ => Unit
  | .gen_oeqTrans, _ => Unit
  | .gen_equivCompose, _ => Unit
  | .gen_transpFill, _ => Unit
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_quotMk, _ => Unit
  | .gen_quotEqAxiom, _ => Unit
  | .gen_quotRec, _ => Unit
  | .gen_quotElim, _ => Unit
  | .gen_pushInl, _ => Unit
  | .gen_pushInr, _ => Unit
  | .gen_pushGlue, _ => Unit
  | .gen_pushRec, _ => Unit
  -- Truncation level lives in the payload as a `Nat`.
  | .gen_truncIntro, _ => Nat
  | .gen_truncCoh, _ => Nat
  | .gen_truncRec, _ => Nat
  | .gen_polyFunctor, _ => Unit
  | .gen_polyApply, _ => Unit
  | .gen_polyMu, _ => Unit
  | .gen_polyNu, _ => Unit
  | .gen_polyMap, _ => Unit
  | .gen_sigmaAlgebra, _ => Unit
  | .gen_measureSpace, _ => Unit
  | .gen_lebesgueInt, _ => Unit
  | .gen_nextT, _ => Unit
  | .gen_alwaysT, _ => Unit
  | .gen_eventuallyT, _ => Unit
  | .gen_untilT, _ => Unit
  | .gen_sinceT, _ => Unit
  | .gen_infinitesimal, _ => Unit
  | .gen_microcanc, _ => Unit
  | .gen_tangentSpace, _ => Unit
  | .gen_diffOp, _ => Unit
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_sessionSelect, _ => Unit
  | .gen_sessionOffer, _ => Unit
  | .gen_sessionClose, _ => Unit
  | .gen_channelSplit, _ => Unit
  | .gen_channelJoin, _ => Unit
  | .gen_regRead, _ => Unit
  | .gen_regWrite, _ => Unit
  | .gen_clockTick, _ => Unit
  | .gen_stageLatch, _ => Unit
  | .gen_wireCombinational, _ => Unit
  | .gen_clockDomainCross, _ => Unit
  | .gen_realCauchy, _ => Unit
  | .gen_realLimit, _ => Unit
  | .gen_realCompare, _ => Unit
  | .gen_probSpace, _ => Unit
  | .gen_sampleP, _ => Unit
  | .gen_expectE, _ => Unit
  | .gen_padicNum, _ => Unit
  | .gen_padicValuation, _ => Unit
  | .gen_localGlobalBridge, _ => Unit
  | .gen_idealFunctionality, _ => Unit
  | .gen_realProtocol, _ => Unit
  | .gen_ucSimulator, _ => Unit
  | .gen_ucCompose, _ => Unit
  | .gen_shannonEntropy, _ => Unit
  | .gen_mutualInfo, _ => Unit
  | .gen_klDivergence, _ => Unit
  | .gen_channelCapacity, _ => Unit
  | .gen_hilbertSpace, _ => Unit
  | .gen_boundedOperator, _ => Unit
  | .gen_spectralDecomp, _ => Unit
  | .gen_unitaryOp, _ => Unit
  | .gen_causalNet, _ => Unit
  | .gen_doOperator, _ => Unit
  | .gen_counterfactual, _ => Unit
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_circleBase, _ => Unit
  | .gen_circleLoop, _ => Unit
  | .gen_circleRec, _ => Unit
  | .gen_pathInverse, _ => Unit
  | .gen_pathWhiskerLeft, _ => Unit
  | .gen_pathWhiskerRight, _ => Unit
  | .gen_shapeModality, _ => Unit
  | .gen_flatModality, _ => Unit
  | .gen_sharpModality, _ => Unit
  | .gen_cohesiveAdjunctionUnit, _ => Unit
  | .gen_qiitIntro, _ => Unit
  | .gen_qiitElim, _ => Unit
  | .gen_liftInnerToOuter, _ => Unit
  | .gen_lowerOuterToInner, _ => Unit
  | .gen_modalityLayerMarker, _ => Unit
  | .gen_qubit, _ => Unit
  | .gen_quantumGate, _ => Unit
  | .gen_quantumMeasure, _ => Unit
  | .gen_quantumEntangle, _ => Unit
  | .gen_quantumDecohere, _ => Unit
  | .gen_game, _ => Unit
  | .gen_strategy, _ => Unit
  | .gen_playOut, _ => Unit
  | .gen_processCalc, _ => Unit
  | .gen_parallelComp, _ => Unit
  | .gen_processCommit, _ => Unit
  | .gen_bisimulationWitness, _ => Unit
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  | .gen_compCubical, _ => Unit
  | .gen_transpHigherDim, _ => Unit
  | .gen_groupAlg, _ => Unit
  | .gen_ringAlg, _ => Unit
  | .gen_moduleAlg, _ => Unit
  | .gen_containerDeriv, _ => Unit
  | .gen_zipperType, _ => Unit
  | .gen_plugOp, _ => Unit
  | .gen_diffLambda, _ => Unit
  | .gen_diffApply, _ => Unit
  | .gen_differentialCategory, _ => Unit
  | .gen_bangModality, _ => Unit
  | .gen_whyNotModality, _ => Unit
  | .gen_linearArrow, _ => Unit
  | .gen_tensorProduct, _ => Unit
  | .gen_provabilityModality, _ => Unit
  | .gen_dynamicLogic, _ => Unit
  | .gen_cpoStructure, _ => Unit
  | .gen_bottomElem, _ => Unit
  | .gen_scottContinuous, _ => Unit
  | .gen_fixedPoint, _ => Unit
  | .gen_hyperreal, _ => Unit
  | .gen_starOp, _ => Unit
  | .gen_standardPart, _ => Unit
  | .gen_cellularAutomaton, _ => Unit
  | .gen_interactionNet, _ => Unit
  | .gen_reversibleOp, _ => Unit
  | .gen_bigOh, _ => Unit
  | .gen_polyTimeWitness, _ => Unit
  | .gen_npComplete, _ => Unit

end FX1Poly.Core
