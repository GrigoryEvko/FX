import FX1Poly.Core.GeneratorCore
import FX1Poly.Core.CellSort

/-! # Foundation/PolyCell/Core/GeneratorMetadata — sort + child metadata

This file ships the generator metadata layer on top of `GeneratorCore`'s
74-summand `Generator` enum.  Three deliverables:

* `Generator.cellSort : Generator → CellSort` — the 74-arm output-sort table.
  Each generator's result inhabits exactly one sort from the `CellSort` enum;
  this is FX's structural typing discipline at the generator level.  Adding a
  feature is one new arm here (plus the matching `SupportedGenerator` arm in
  the admission layer), never a new `PolyCell` constructor.

* `Generator.childSpecs : Generator → List ChildSpec` — the 74-arm
  child-spec table.  Each generator declares the expected `(cellSort,
  cellDimension, scopeShift)` of every child position.  Length equals
  `Generator.arity`; `scopeShift` entries equal `Generator.binderShifts`.

* `Generator.childSpecs_scopeShifts_eq_binderShifts` — the coherence lemma
  tying the two metadata views.  Mechanically `cases g <;> rfl` since both
  tables are defined by structural enumeration over the same enum.

The structure `ChildSpec` carries no dependency on `PolyTerm.lean`.

Imports: `GeneratorCore` (for `Generator` + `arity` + `binderShifts`) and
`CellSort` (for the sort vocabulary). -/

namespace FX1Poly.Core

/-- One expected child position of a generator.

Carries no dependency on a dim-indexed `PolyTerm` inductive.  Three fields:

* `cellSort` — which sort the child must inhabit (term / type / context /
  mode / effect / grade / protocol).
* `cellDimension` — the child's dimension (all current generators produce
  dim-0 children; positive-dim children appear only at the `RuleSpec` /
  `generatingCell` layer).
* `scopeShift` — the de Bruijn scope offset relative to the parent.  A
  lambda body's child has `scopeShift = 1` (one fresh binder); a pi-type
  codomain's child has `scopeShift = 1` (one fresh type binder); all other
  current generators have `scopeShift = 0` per the `Generator.binderShifts`
  table.

Carrier-free by construction: this struct doesn't store a cell, it only
describes what the certifier should expect at this child position. -/
structure ChildSpec where
  cellSort : CellSort
  cellDimension : Nat
  scopeShift : Nat
  deriving DecidableEq

namespace ChildSpec

/-- A child at the parent scope with dimension zero, any sort. -/
@[reducible] def sameScopeDimZero (sort : CellSort) : ChildSpec where
  cellSort := sort
  cellDimension := 0
  scopeShift := 0

/-- A child under exactly one new binder, dimension zero. -/
@[reducible] def underOneBinderDimZero (sort : CellSort) : ChildSpec where
  cellSort := sort
  cellDimension := 0
  scopeShift := 1

/-- Same-scope term child (dim 0, scope shift 0). -/
@[reducible] def termSameScope : ChildSpec := sameScopeDimZero .term

/-- Term child under one fresh binder (dim 0, scope shift 1). -/
@[reducible] def termUnderBinder : ChildSpec := underOneBinderDimZero .term

/-- Same-scope type child (dim 0, scope shift 0). -/
@[reducible] def typeSameScope : ChildSpec := sameScopeDimZero .type

/-- Type child under one fresh binder (dim 0, scope shift 1). -/
@[reducible] def typeUnderBinder : ChildSpec := underOneBinderDimZero .type

end ChildSpec

/-- Output sort of each generator.  74 arms, one per `Generator` ctor.

Classification rationale:

* Most generators are TERM constructors: they build runtime values.  This
  covers `var`, `lam`, `app`, all data-type intro/elim families (bool, nat,
  list, option, either), identity-type witnesses, modal operations, cubical
  values + operations, observational equality witnesses, strict identity,
  refinement intro/elim, record intro/projection, codata, sessions, effects,
  and the composition vocabulary (`uaToEquiv`, `equivApply`, `pathCompose`,
  etc.).

* TYPE-CODE generators produce reified type values whose cellSort is `.type`:
  `universeCode`, `arrowCode`, `piTyCode`, `sigmaTyCode`, `productCode`,
  `sumCode`, `listCode`, `optionCode`, `eitherCode`, `idCode`, `equivCode`,
  and the cumulativity marker `cumulUpMarker` which lifts a type code to a
  higher universe.

No generator currently produces a `.context`, `.mode`, `.effect`, `.grade`,
or `.protocol` cell directly — those sorts populate when the corresponding
RawTerm fragments (beyond term/type) are folded in. -/
def Generator.cellSort : Generator → CellSort
  -- Variable + unit
  | .gen_var          => .term
  | .gen_unit         => .term
  -- Function intro/elim
  | .gen_lam          => .term
  | .gen_app          => .term
  -- Pair intro/elim
  | .gen_pair         => .term
  | .gen_fst          => .term
  | .gen_snd          => .term
  -- Booleans
  | .gen_boolTrue     => .term
  | .gen_boolFalse    => .term
  | .gen_boolElim     => .term
  -- Naturals
  | .gen_natZero      => .term
  | .gen_natSucc      => .term
  | .gen_natElim      => .term
  | .gen_natRec       => .term
  -- Lists
  | .gen_listNil      => .term
  | .gen_listCons     => .term
  | .gen_listElim     => .term
  -- Options
  | .gen_optionNone   => .term
  | .gen_optionSome   => .term
  | .gen_optionMatch  => .term
  -- Eithers
  | .gen_eitherInl    => .term
  | .gen_eitherInr    => .term
  | .gen_eitherMatch  => .term
  -- Identity-type witnesses + eliminator
  | .gen_refl         => .term
  | .gen_idJ          => .term
  -- Modal intro/elim/subsume — all term-level
  | .gen_modIntro     => .term
  | .gen_modElim      => .term
  | .gen_subsume      => .term
  -- Cubical interval endpoints + lattice ops
  | .gen_interval0    => .term
  | .gen_interval1    => .term
  | .gen_intervalOpp  => .term
  | .gen_intervalMeet => .term
  | .gen_intervalJoin => .term
  -- Cubical path
  | .gen_pathLam      => .term
  | .gen_pathApp      => .term
  -- Cubical glue + transport + composition
  | .gen_glueIntro    => .term
  | .gen_glueElim     => .term
  | .gen_transp       => .term
  | .gen_hcomp        => .term
  -- Observational equality witnesses
  | .gen_oeqRefl      => .term
  | .gen_oeqJ         => .term
  | .gen_oeqFunext    => .term
  -- Strict identity
  | .gen_idStrictRefl => .term
  | .gen_idStrictRec  => .term
  -- Type equivalence
  | .gen_equivIntro   => .term
  | .gen_equivApp     => .term
  -- Refinement intro/elim
  | .gen_refineIntro  => .term
  | .gen_refineElim   => .term
  -- Record intro/projection
  | .gen_recordIntro  => .term
  | .gen_recordProj   => .term
  -- Codata
  | .gen_codataUnfold => .term
  | .gen_codataDest   => .term
  -- Sessions
  | .gen_sessionSend  => .term
  | .gen_sessionRecv  => .term
  -- Effects
  | .gen_effectPerform => .term
  -- Universe code — a type code (output sort .type)
  | .gen_universeCode => .type
  -- Universe-mode codes — type codes (output sort .type)
  | .gen_universeU    => .type
  | .gen_universeS    => .type
  | .gen_universeD    => .type
  | .gen_universeOmega => .type
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    => .type
  -- Per-shape type codes (binder-shape)
  | .gen_piTyCode     => .type
  | .gen_sigmaTyCode  => .type
  -- More atom-shape codes
  | .gen_productCode  => .type
  | .gen_sumCode      => .type
  | .gen_listCode     => .type
  | .gen_optionCode   => .type
  | .gen_eitherCode   => .type
  | .gen_idCode       => .type
  | .gen_equivCode    => .type
  | .gen_emptyCode    => .type
  | .gen_boolCode     => .type
  | .gen_natCode      => .type
  | .gen_unitCode     => .type
  -- Cumulativity marker on a type code
  | .gen_cumulUpMarker => .type
  -- Univalence-to-equiv vocabulary — term-level operations
  | .gen_uaToEquiv    => .term
  | .gen_equivApply   => .term
  -- Composition vocabulary — term-level
  | .gen_pathCompose  => .term
  | .gen_idToEquiv    => .term
  | .gen_oeqTrans     => .term
  | .gen_equivCompose => .term
  -- Cubical fill — term-level
  | .gen_transpFill   => .term
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 2.1 Quotients (all term-level: quotient elements + equality witnesses + eliminators)
  | .gen_quotMk        => .term
  | .gen_quotEqAxiom   => .term
  | .gen_quotRec       => .term
  | .gen_quotElim      => .term
  -- 2.2 Pushout HIT (term-level intro/glue/eliminator)
  | .gen_pushInl       => .term
  | .gen_pushInr       => .term
  | .gen_pushGlue      => .term
  | .gen_pushRec       => .term
  -- 2.3 Truncations (term-level — the truncated value is itself a term)
  | .gen_truncIntro    => .term
  | .gen_truncCoh      => .term
  | .gen_truncRec      => .term
  -- 2.4 Polynomial Functors (type-level: polynomials AND their μ/ν fixpoints are types)
  | .gen_polyFunctor   => .type
  | .gen_polyApply     => .type
  | .gen_polyMu        => .type
  | .gen_polyNu        => .type
  -- polyMap is term-level (functorial action on values)
  | .gen_polyMap       => .term
  -- 2.5 Measure (structures stored as terms with internal proofs)
  | .gen_sigmaAlgebra  => .term
  | .gen_measureSpace  => .term
  | .gen_lebesgueInt   => .term
  -- 2.6 Temporal Logic (LTL operators produce TYPES = temporal predicates)
  | .gen_nextT         => .type
  | .gen_alwaysT       => .type
  | .gen_eventuallyT   => .type
  | .gen_untilT        => .type
  | .gen_sinceT        => .type
  -- 2.7 Synthetic Differentials (mostly types; microcanc + diffOp are terms)
  | .gen_infinitesimal => .type
  | .gen_microcanc     => .term
  | .gen_tangentSpace  => .type
  | .gen_diffOp        => .term
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 3.1 Sessions (term-level channel/session-state operations)
  | .gen_sessionSelect => .term
  | .gen_sessionOffer  => .term
  | .gen_sessionClose  => .term
  | .gen_channelSplit  => .term
  | .gen_channelJoin   => .term
  -- 3.2 Hardware (all term-level register/clock/wire/stage operations)
  | .gen_regRead       => .term
  | .gen_regWrite      => .term
  | .gen_clockTick     => .term
  | .gen_stageLatch    => .term
  | .gen_wireCombinational => .term
  | .gen_clockDomainCross  => .term
  -- 3.3 Computational Reals (term-level — a real is a value)
  | .gen_realCauchy    => .term
  | .gen_realLimit     => .term
  | .gen_realCompare   => .term
  -- 3.4 Probability (term-level: spaces, samples, expectations are all values)
  | .gen_probSpace     => .term
  | .gen_sampleP       => .term
  | .gen_expectE       => .term
  -- 3.5 p-adic (term-level numeric values)
  | .gen_padicNum      => .term
  | .gen_padicValuation => .term
  | .gen_localGlobalBridge => .term
  -- 3.6 UC (term-level functionalities, protocols, simulators)
  | .gen_idealFunctionality => .term
  | .gen_realProtocol  => .term
  | .gen_ucSimulator   => .term
  | .gen_ucCompose     => .term
  -- 3.7 Info Theory (term-level — entropy/MI/KL/capacity are real values)
  | .gen_shannonEntropy => .term
  | .gen_mutualInfo    => .term
  | .gen_klDivergence  => .term
  | .gen_channelCapacity => .term
  -- 3.8 Spectral (term-level Hilbert spaces with internal proofs)
  | .gen_hilbertSpace  => .term
  | .gen_boundedOperator => .term
  | .gen_spectralDecomp => .term
  | .gen_unitaryOp     => .term
  -- 3.9 Causal (term-level networks and interventions)
  | .gen_causalNet     => .term
  | .gen_doOperator    => .term
  | .gen_counterfactual => .term
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 4.1 Circle + Paths (term-level: circle points, loop witnesses, eliminators, path ops)
  | .gen_circleBase    => .term
  | .gen_circleLoop    => .term
  | .gen_circleRec     => .term
  | .gen_pathInverse   => .term
  | .gen_pathWhiskerLeft  => .term
  | .gen_pathWhiskerRight => .term
  -- 4.2 Cohesive Modalities (type-level: ʃA/♭A/♯A are TYPES; unit is a term)
  | .gen_shapeModality => .type
  | .gen_flatModality  => .type
  | .gen_sharpModality => .type
  | .gen_cohesiveAdjunctionUnit => .term
  -- 4.3 QIITs (term-level intro/elim over QIIT values)
  | .gen_qiitIntro     => .term
  | .gen_qiitElim      => .term
  -- 4.4 2LTT (term-level layer transitions)
  | .gen_liftInnerToOuter => .term
  | .gen_lowerOuterToInner => .term
  | .gen_modalityLayerMarker => .term
  -- 4.5 Quantum (all term-level: qubits, gates, measurements, entanglement, decoherence)
  | .gen_qubit         => .term
  | .gen_quantumGate   => .term
  | .gen_quantumMeasure => .term
  | .gen_quantumEntangle => .term
  | .gen_quantumDecohere => .term
  -- 4.6 Game Semantics (term-level games, strategies, plays)
  | .gen_game          => .term
  | .gen_strategy      => .term
  | .gen_playOut       => .term
  -- 4.7 Process Calculi (term-level processes, parallel composition, commits, bisimulations)
  | .gen_processCalc   => .term
  | .gen_parallelComp  => .term
  | .gen_processCommit => .term
  | .gen_bisimulationWitness => .term
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 5.1 Cubical Kan Completion (term-level full Kan ops)
  | .gen_compCubical   => .term
  | .gen_transpHigherDim => .term
  -- 5.2 Algebraic Structures (term-level — algebraic carriers stored with internal proofs)
  | .gen_groupAlg      => .term
  | .gen_ringAlg       => .term
  | .gen_moduleAlg     => .term
  -- 5.3 Container Calculus (type-level derivatives + zipper types; plug is term-level)
  | .gen_containerDeriv => .type
  | .gen_zipperType    => .type
  | .gen_plugOp        => .term
  -- 5.4 Differential Lambda (term-level smooth λ-calculus operations)
  | .gen_diffLambda    => .term
  | .gen_diffApply     => .term
  | .gen_differentialCategory => .term
  -- 5.5 Linear Logic (type-level modalities and linear connectives)
  | .gen_bangModality  => .type
  | .gen_whyNotModality => .type
  | .gen_linearArrow   => .type
  | .gen_tensorProduct => .type
  -- 5.6 Provability / Dynamic Logic (type-level — both are propositional)
  | .gen_provabilityModality => .type
  | .gen_dynamicLogic  => .type
  -- 5.7 Domain Theory CPO (term-level structures and witnesses)
  | .gen_cpoStructure  => .term
  | .gen_bottomElem    => .term
  | .gen_scottContinuous => .term
  | .gen_fixedPoint    => .term
  -- 5.8 Hyperreals (type for the carrier; term-level for star + standard part)
  | .gen_hyperreal     => .type
  | .gen_starOp        => .term
  | .gen_standardPart  => .term
  -- 5.9 Cellular Automata / Reversible (term-level — automata and rules are values)
  | .gen_cellularAutomaton => .term
  | .gen_interactionNet => .term
  | .gen_reversibleOp  => .term
  -- 5.10 Synthetic Complexity (term-level — bounds are values with witnesses)
  | .gen_bigOh         => .term
  | .gen_polyTimeWitness => .term
  | .gen_npComplete    => .term

/-- Expected child positions for each generator.  74 arms, one per
`Generator` ctor.

Two invariants tie this table to `GeneratorCore.lean`:

1. `(childSpecs g).length = arity g` — proved by `cases g <;> rfl`.
2. `(childSpecs g).map (·.scopeShift) = binderShifts g` — proved as
   `Generator.childSpecs_scopeShifts_eq_binderShifts` below, the load-bearing
   coherence lemma.

Sort classification of children:

* Term-producing generators with structural children: every child is a term
  (function/argument, predecessor, scrutinee + branches, head + tail,
  optional value, etc.).  Lambda's body is a term under one binder; path
  lambda's body is a term under one interval binder.

* Type-code generators with structural children: every child is a type code
  (domain + codomain for arrow/pi/sigma; element type for list/option;
  left/right for product/sum/either/equiv).  Two exceptions:

  - `gen_idCode` (arity 3) has children `[type, term, term]` — a type code
    for the carrier type plus two terms of that type whose equality is
    asserted.

  - `gen_transpFill` (arity 3) has children `[type, term, term]` — a type
    code (the path-type to transport along) plus the current interval point
    and the source term.

The scope-shift entries match `binderShifts` arm-for-arm: `gen_lam` (Church-style,
domain annotation at shift `0` + body at shift `1`) mirrors `gen_piTyCode` and
`gen_sigmaTyCode` (shift-`1` codomain after a shift-`0` domain); `gen_pathLam`
has a `1`-shifted body; everything else uses `0`. -/
def Generator.childSpecs : Generator → List ChildSpec
  -- Variable + unit
  | .gen_var          => []
  | .gen_unit         => []
  -- Function
  | .gen_lam          => [ChildSpec.termSameScope, ChildSpec.termUnderBinder]
  | .gen_app          => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Pair
  | .gen_pair         => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_fst          => [ChildSpec.termSameScope]
  | .gen_snd          => [ChildSpec.termSameScope]
  -- Booleans
  | .gen_boolTrue     => []
  | .gen_boolFalse    => []
  | .gen_boolElim     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- Naturals
  | .gen_natZero      => []
  | .gen_natSucc      => [ChildSpec.termSameScope]
  | .gen_natElim      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_natRec       =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- Lists
  | .gen_listNil      => []
  | .gen_listCons     => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_listElim     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- Options
  | .gen_optionNone   => []
  | .gen_optionSome   => [ChildSpec.termSameScope]
  | .gen_optionMatch  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- Eithers
  | .gen_eitherInl    => [ChildSpec.termSameScope]
  | .gen_eitherInr    => [ChildSpec.termSameScope]
  | .gen_eitherMatch  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- Identity-type witnesses + eliminator
  | .gen_refl         => [ChildSpec.termSameScope]
  | .gen_idJ          => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Modal
  | .gen_modIntro     => [ChildSpec.termSameScope]
  | .gen_modElim      => [ChildSpec.termSameScope]
  | .gen_subsume      => [ChildSpec.termSameScope]
  -- Cubical interval
  | .gen_interval0    => []
  | .gen_interval1    => []
  | .gen_intervalOpp  => [ChildSpec.termSameScope]
  | .gen_intervalMeet =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_intervalJoin =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Cubical path
  | .gen_pathLam      => [ChildSpec.termUnderBinder]
  | .gen_pathApp      => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Cubical glue / transport / composition
  | .gen_glueIntro    => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_glueElim     => [ChildSpec.termSameScope]
  | .gen_transp       => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_hcomp        => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Observational equality witnesses
  | .gen_oeqRefl      => [ChildSpec.termSameScope]
  | .gen_oeqJ         => [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_oeqFunext    => [ChildSpec.termSameScope]
  -- Strict identity
  | .gen_idStrictRefl => [ChildSpec.termSameScope]
  | .gen_idStrictRec  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Type equivalence
  | .gen_equivIntro   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_equivApp     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Refinement intro/elim
  | .gen_refineIntro  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_refineElim   => [ChildSpec.termSameScope]
  -- Record intro/projection
  | .gen_recordIntro  => [ChildSpec.termSameScope]
  | .gen_recordProj   => [ChildSpec.termSameScope]
  -- Codata
  | .gen_codataUnfold =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_codataDest   => [ChildSpec.termSameScope]
  -- Sessions
  | .gen_sessionSend  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_sessionRecv  => [ChildSpec.termSameScope]
  -- Effects
  | .gen_effectPerform =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Universe code (Nat payload, no children)
  | .gen_universeCode => []
  -- Universe-mode codes (payload-only, no children)
  | .gen_universeU    => []
  | .gen_universeS    => []
  | .gen_universeD    => []
  | .gen_universeOmega => []
  -- Empty type code (nullary)
  | .gen_emptyCode    => []
  -- Bool type code (nullary)
  | .gen_boolCode     => []
  -- Nat type code (nullary)
  | .gen_natCode      => []
  -- Unit type code (nullary)
  | .gen_unitCode     => []
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  -- Per-shape type codes (binder-shape: codomain at scope + 1)
  | .gen_piTyCode     =>
    [ChildSpec.typeSameScope, ChildSpec.typeUnderBinder]
  | .gen_sigmaTyCode  =>
    [ChildSpec.typeSameScope, ChildSpec.typeUnderBinder]
  -- More atom-shape codes
  | .gen_productCode  =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  | .gen_sumCode      =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  | .gen_listCode     => [ChildSpec.typeSameScope]
  | .gen_optionCode   => [ChildSpec.typeSameScope]
  | .gen_eitherCode   =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  -- Identity type code: carrier-type, leftRaw, rightRaw
  | .gen_idCode       =>
    [ChildSpec.typeSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- Equivalence type code: two carrier types
  | .gen_equivCode    =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  -- Cumulativity marker: one inner type code
  | .gen_cumulUpMarker => [ChildSpec.typeSameScope]
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv    => [ChildSpec.termSameScope]
  | .gen_equivApply   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Composition vocabulary
  | .gen_pathCompose  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_idToEquiv    => [ChildSpec.termSameScope]
  | .gen_oeqTrans     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_equivCompose =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- Cubical fill: pathTy + currentInterval + source
  | .gen_transpFill   =>
    [ChildSpec.typeSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 2.1 Quotients
  | .gen_quotMk        => [ChildSpec.termSameScope]
  | .gen_quotEqAxiom   => [ChildSpec.termSameScope]
  | .gen_quotRec       =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_quotElim      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- 2.2 Pushout HIT
  | .gen_pushInl       => [ChildSpec.termSameScope]
  | .gen_pushInr       => [ChildSpec.termSameScope]
  | .gen_pushGlue      => [ChildSpec.termSameScope]
  | .gen_pushRec       =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 2.3 Truncations (level lives in Nat payload, not as child)
  | .gen_truncIntro    => [ChildSpec.termSameScope]
  | .gen_truncCoh      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_truncRec      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 2.4 Polynomial Functors (positionFamily at scope+1)
  | .gen_polyFunctor   =>
    [ChildSpec.typeSameScope, ChildSpec.typeUnderBinder]
  | .gen_polyApply     =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  | .gen_polyMu        => [ChildSpec.typeSameScope]
  | .gen_polyNu        => [ChildSpec.typeSameScope]
  | .gen_polyMap       =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 2.5 Measure
  | .gen_sigmaAlgebra  => [ChildSpec.termSameScope]
  | .gen_measureSpace  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_lebesgueInt   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 2.6 Temporal Logic (propositions are types)
  | .gen_nextT         => [ChildSpec.typeSameScope]
  | .gen_alwaysT       => [ChildSpec.typeSameScope]
  | .gen_eventuallyT   => [ChildSpec.typeSameScope]
  | .gen_untilT        =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  | .gen_sinceT        =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  -- 2.7 Synthetic Differentials
  | .gen_infinitesimal => [ChildSpec.typeSameScope]
  | .gen_microcanc     => [ChildSpec.termSameScope]
  | .gen_tangentSpace  =>
    [ChildSpec.typeSameScope, ChildSpec.termSameScope]
  | .gen_diffOp        =>
    [ChildSpec.typeSameScope, ChildSpec.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 3.1 Sessions
  | .gen_sessionSelect =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_sessionOffer  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_sessionClose  => [ChildSpec.termSameScope]
  | .gen_channelSplit  => [ChildSpec.termSameScope]
  | .gen_channelJoin   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 3.2 Hardware
  | .gen_regRead       =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_regWrite      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_clockTick     => [ChildSpec.typeSameScope]  -- clockDomain is a type
  | .gen_stageLatch    =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_wireCombinational => [ChildSpec.termSameScope]
  | .gen_clockDomainCross  =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope,
     ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 3.3 Computational Reals
  | .gen_realCauchy    =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_realLimit     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_realCompare   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- 3.4 Probability
  | .gen_probSpace     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_sampleP       => [ChildSpec.termSameScope]
  | .gen_expectE       =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 3.5 p-adic
  | .gen_padicNum      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_padicValuation =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_localGlobalBridge =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 3.6 UC (interface is a type; protocols/simulators are terms)
  | .gen_idealFunctionality => [ChildSpec.typeSameScope]
  | .gen_realProtocol  => [ChildSpec.termSameScope]
  | .gen_ucSimulator   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_ucCompose     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 3.7 Info Theory
  | .gen_shannonEntropy => [ChildSpec.termSameScope]
  | .gen_mutualInfo    => [ChildSpec.termSameScope]
  | .gen_klDivergence  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_channelCapacity => [ChildSpec.termSameScope]
  -- 3.8 Spectral
  | .gen_hilbertSpace  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_boundedOperator =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_spectralDecomp =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_unitaryOp     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 3.9 Causal
  | .gen_causalNet     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_doOperator    =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_counterfactual =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 4.1 Circle + Higher Paths
  | .gen_circleBase    => []
  | .gen_circleLoop    => []
  | .gen_circleRec     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_pathInverse   => [ChildSpec.termSameScope]
  | .gen_pathWhiskerLeft  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_pathWhiskerRight =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 4.2 Cohesive Modalities (carriers are types; adjunction unit operates on terms)
  | .gen_shapeModality => [ChildSpec.typeSameScope]
  | .gen_flatModality  => [ChildSpec.typeSameScope]
  | .gen_sharpModality => [ChildSpec.typeSameScope]
  | .gen_cohesiveAdjunctionUnit => [ChildSpec.termSameScope]
  -- 4.3 QIITs
  | .gen_qiitIntro     => [ChildSpec.termSameScope]
  | .gen_qiitElim      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- 4.4 2LTT
  | .gen_liftInnerToOuter => [ChildSpec.termSameScope]
  | .gen_lowerOuterToInner =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_modalityLayerMarker => [ChildSpec.termSameScope]
  -- 4.5 Quantum
  | .gen_qubit         => []
  | .gen_quantumGate   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_quantumMeasure =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_quantumEntangle =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_quantumDecohere =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- 4.6 Game Semantics
  | .gen_game          => [ChildSpec.termSameScope]
  | .gen_strategy      =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_playOut       =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 4.7 Process Calculi
  | .gen_processCalc   => [ChildSpec.termSameScope]
  | .gen_parallelComp  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_processCommit => [ChildSpec.termSameScope]
  | .gen_bisimulationWitness =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 5.1 Cubical Kan
  | .gen_compCubical   =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_transpHigherDim =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 5.2 Algebraic Structures (carriers are types; operations + laws are terms)
  | .gen_groupAlg      =>
    [ChildSpec.typeSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_ringAlg       =>
    [ChildSpec.typeSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_moduleAlg     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  -- 5.3 Container Calculus (derivative + zipper operate on type polynomials)
  | .gen_containerDeriv => [ChildSpec.typeSameScope]
  | .gen_zipperType    => [ChildSpec.typeSameScope]
  | .gen_plugOp        =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 5.4 Differential Lambda (body under one binder; mirrors gen_lam)
  | .gen_diffLambda    => [ChildSpec.termUnderBinder]
  | .gen_diffApply     =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_differentialCategory => [ChildSpec.termSameScope]
  -- 5.5 Linear Logic (modalities on types; linear arrow / tensor are type-level)
  | .gen_bangModality  => [ChildSpec.typeSameScope]
  | .gen_whyNotModality => [ChildSpec.typeSameScope]
  | .gen_linearArrow   =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  | .gen_tensorProduct =>
    [ChildSpec.typeSameScope, ChildSpec.typeSameScope]
  -- 5.6 Provability / Dynamic Logic (statement is type; dynamic logic is [program] postcondition)
  | .gen_provabilityModality => [ChildSpec.typeSameScope]
  | .gen_dynamicLogic  =>
    [ChildSpec.termSameScope, ChildSpec.typeSameScope]
  -- 5.7 Domain Theory (carrier is type; structure/operations are terms)
  | .gen_cpoStructure  =>
    [ChildSpec.typeSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_bottomElem    => [ChildSpec.termSameScope]
  | .gen_scottContinuous =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_fixedPoint    =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 5.8 Hyperreals
  | .gen_hyperreal     => []
  | .gen_starOp        => [ChildSpec.termSameScope]
  | .gen_standardPart  => [ChildSpec.termSameScope]
  -- 5.9 CA / Reversible
  | .gen_cellularAutomaton =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_interactionNet =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_reversibleOp  =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  -- 5.10 Synthetic Complexity
  | .gen_bigOh         =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope,
     ChildSpec.termSameScope]
  | .gen_polyTimeWitness =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]
  | .gen_npComplete    =>
    [ChildSpec.termSameScope, ChildSpec.termSameScope]

/-- The `childSpecs` table has length exactly `arity g`.  Proof by
case-analysis: each of the 74 arms closes via `rfl` on
`[].length = 0`, `[_].length = 1`, `[_,_].length = 2`, `[_,_,_].length = 3`. -/
theorem Generator.childSpecs_length_eq_arity (generator : Generator) :
    generator.childSpecs.length = generator.arity := by
  cases generator <;> rfl

/-- The coherence lemma between `childSpecs` and `binderShifts`: extracting
the per-child scope shift from the child-spec list yields exactly the
non-dependent `binderShifts` list.  Together with
`binderShifts_length_eq_arity` (in `GeneratorCore`) and
`childSpecs_length_eq_arity` (above) this pins the discipline:

  arity g = (childSpecs g).length = (binderShifts g).length

and the per-position scope-shift agrees between both views.

Mechanically a `cases g <;> rfl` since both tables enumerate the same enum
in the same order with literal-list bodies; per arm the `List.map` reduces
on `[]` / `[x]` / `[x, y]` / `[x, y, z]` and each `ChildSpec`'s
`scopeShift` projection is also a literal. -/
theorem Generator.childSpecs_scopeShifts_eq_binderShifts
    (generator : Generator) :
    (generator.childSpecs.map ChildSpec.scopeShift) =
      generator.binderShifts := by
  cases generator <;> rfl

end FX1Poly.Core
