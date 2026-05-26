import LeanFX2.Foundation.PolyCell.Core.GeneratorCore
import LeanFX2.Foundation.PolyCell.Core.CellSort

/-! # Foundation/PolyCell/Core/GeneratorMetadataV2 — sort + child metadata for v2

This file ships the v2 generator metadata layer on top of `GeneratorCore`'s
74-summand `Generator` enum.  Three deliverables (tasks V2-L1.1 / V2-L1.2 /
V2-L1.3):

* `Generator.cellSort : Generator → CellSort` — the 74-arm output-sort table.
  Each generator's result inhabits exactly one sort from the `CellSort` enum;
  this is FX's structural typing discipline at the generator level.  Adding a
  feature is one new arm here (plus the matching `SupportedGeneratorV2` arm in
  the admission layer), never a new `PolyCellV2` constructor.

* `Generator.childSpecs : Generator → List ChildSpecV2` — the 74-arm
  child-spec table.  Each generator declares the expected `(cellSort,
  cellDimension, scopeShift)` of every child position.  Length equals
  `Generator.arity`; `scopeShift` entries equal `Generator.binderShifts`.

* `Generator.childSpecs_scopeShifts_eq_binderShifts` — the coherence lemma
  tying the two metadata views.  Mechanically `cases g <;> rfl` since both
  tables are defined by structural enumeration over the same enum.

The structure `ChildSpecV2` is a v2-pure parallel to v1's
`GeneratorSpec.ChildSpec`: same fields, but living in this file so the v2
layer has no transitive dependency on `PolyTerm.lean` (the v1 dim-indexed
inductive).  At Stage 6 (v1 deletion + V2 suffix drop) the structure will be
renamed to `ChildSpec`.

Imports: `GeneratorCore` (for `Generator` + `arity` + `binderShifts`) and
`CellSort` (for the sort vocabulary).  No `PolyTerm`, no v1 metadata. -/

namespace LeanFX2.Foundation.PolyCell.Core

/-- One expected child position of a v2 generator.

Parallel to v1 `ChildSpec` but carrying no dependency on the v1 dim-indexed
`PolyTerm` inductive.  Three fields:

* `cellSort` — which sort the child must inhabit (term / type / context /
  mode / effect / grade / protocol).
* `cellDimension` — the child's dimension (current v2 generators all produce
  dim-0 children; positive-dim children appear only at the `RuleSpec` /
  `generatingCell` layer).
* `scopeShift` — the de Bruijn scope offset relative to the parent.  A
  lambda body's child has `scopeShift = 1` (one fresh binder); a pi-type
  codomain's child has `scopeShift = 1` (one fresh type binder); all other
  current v2 generators have `scopeShift = 0` per the `Generator.binderShifts`
  table.

Carrier-free by construction: this struct doesn't store a cell, it only
describes what the certifier should expect at this child position. -/
structure ChildSpecV2 where
  cellSort : CellSort
  cellDimension : Nat
  scopeShift : Nat
  deriving DecidableEq

namespace ChildSpecV2

/-- A child at the parent scope with dimension zero, any sort. -/
@[reducible] def sameScopeDimZero (sort : CellSort) : ChildSpecV2 where
  cellSort := sort
  cellDimension := 0
  scopeShift := 0

/-- A child under exactly one new binder, dimension zero. -/
@[reducible] def underOneBinderDimZero (sort : CellSort) : ChildSpecV2 where
  cellSort := sort
  cellDimension := 0
  scopeShift := 1

/-- Same-scope term child (dim 0, scope shift 0). -/
@[reducible] def termSameScope : ChildSpecV2 := sameScopeDimZero .term

/-- Term child under one fresh binder (dim 0, scope shift 1). -/
@[reducible] def termUnderBinder : ChildSpecV2 := underOneBinderDimZero .term

/-- Same-scope type child (dim 0, scope shift 0). -/
@[reducible] def typeSameScope : ChildSpecV2 := sameScopeDimZero .type

/-- Type child under one fresh binder (dim 0, scope shift 1). -/
@[reducible] def typeUnderBinder : ChildSpecV2 := underOneBinderDimZero .type

end ChildSpecV2

/-- Output sort of each v2 generator.  74 arms, one per `Generator` ctor.

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
or `.protocol` cell directly — those sorts will populate when the
corresponding RawTerm fragments are folded into v2 (Stage 1 extensions
beyond term/type). -/
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

/-- Expected child positions for each v2 generator.  74 arms, one per
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

The scope-shift entries match `binderShifts` arm-for-arm: `gen_lam` and
`gen_pathLam` have a `1`-shifted body; `gen_piTyCode` and `gen_sigmaTyCode`
have a `1`-shifted codomain; everything else uses `0`. -/
def Generator.childSpecs : Generator → List ChildSpecV2
  -- Variable + unit
  | .gen_var          => []
  | .gen_unit         => []
  -- Function
  | .gen_lam          => [ChildSpecV2.termUnderBinder]
  | .gen_app          => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Pair
  | .gen_pair         => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_fst          => [ChildSpecV2.termSameScope]
  | .gen_snd          => [ChildSpecV2.termSameScope]
  -- Booleans
  | .gen_boolTrue     => []
  | .gen_boolFalse    => []
  | .gen_boolElim     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Naturals
  | .gen_natZero      => []
  | .gen_natSucc      => [ChildSpecV2.termSameScope]
  | .gen_natElim      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_natRec       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Lists
  | .gen_listNil      => []
  | .gen_listCons     => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_listElim     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Options
  | .gen_optionNone   => []
  | .gen_optionSome   => [ChildSpecV2.termSameScope]
  | .gen_optionMatch  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Eithers
  | .gen_eitherInl    => [ChildSpecV2.termSameScope]
  | .gen_eitherInr    => [ChildSpecV2.termSameScope]
  | .gen_eitherMatch  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Identity-type witnesses + eliminator
  | .gen_refl         => [ChildSpecV2.termSameScope]
  | .gen_idJ          => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Modal
  | .gen_modIntro     => [ChildSpecV2.termSameScope]
  | .gen_modElim      => [ChildSpecV2.termSameScope]
  | .gen_subsume      => [ChildSpecV2.termSameScope]
  -- Cubical interval
  | .gen_interval0    => []
  | .gen_interval1    => []
  | .gen_intervalOpp  => [ChildSpecV2.termSameScope]
  | .gen_intervalMeet =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_intervalJoin =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Cubical path
  | .gen_pathLam      => [ChildSpecV2.termUnderBinder]
  | .gen_pathApp      => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Cubical glue / transport / composition
  | .gen_glueIntro    => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_glueElim     => [ChildSpecV2.termSameScope]
  | .gen_transp       => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_hcomp        => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Observational equality witnesses
  | .gen_oeqRefl      => [ChildSpecV2.termSameScope]
  | .gen_oeqJ         => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_oeqFunext    => [ChildSpecV2.termSameScope]
  -- Strict identity
  | .gen_idStrictRefl => [ChildSpecV2.termSameScope]
  | .gen_idStrictRec  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Type equivalence
  | .gen_equivIntro   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_equivApp     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Refinement intro/elim
  | .gen_refineIntro  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_refineElim   => [ChildSpecV2.termSameScope]
  -- Record intro/projection
  | .gen_recordIntro  => [ChildSpecV2.termSameScope]
  | .gen_recordProj   => [ChildSpecV2.termSameScope]
  -- Codata
  | .gen_codataUnfold =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_codataDest   => [ChildSpecV2.termSameScope]
  -- Sessions
  | .gen_sessionSend  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_sessionRecv  => [ChildSpecV2.termSameScope]
  -- Effects
  | .gen_effectPerform =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Universe code (Nat payload, no children)
  | .gen_universeCode => []
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- Per-shape type codes (binder-shape: codomain at scope + 1)
  | .gen_piTyCode     =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeUnderBinder]
  | .gen_sigmaTyCode  =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeUnderBinder]
  -- More atom-shape codes
  | .gen_productCode  =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  | .gen_sumCode      =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  | .gen_listCode     => [ChildSpecV2.typeSameScope]
  | .gen_optionCode   => [ChildSpecV2.typeSameScope]
  | .gen_eitherCode   =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- Identity type code: carrier-type, leftRaw, rightRaw
  | .gen_idCode       =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Equivalence type code: two carrier types
  | .gen_equivCode    =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- Cumulativity marker: one inner type code
  | .gen_cumulUpMarker => [ChildSpecV2.typeSameScope]
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv    => [ChildSpecV2.termSameScope]
  | .gen_equivApply   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Composition vocabulary
  | .gen_pathCompose  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_idToEquiv    => [ChildSpecV2.termSameScope]
  | .gen_oeqTrans     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_equivCompose =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Cubical fill: pathTy + currentInterval + source
  | .gen_transpFill   =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 2.1 Quotients
  | .gen_quotMk        => [ChildSpecV2.termSameScope]
  | .gen_quotEqAxiom   => [ChildSpecV2.termSameScope]
  | .gen_quotRec       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_quotElim      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- 2.2 Pushout HIT
  | .gen_pushInl       => [ChildSpecV2.termSameScope]
  | .gen_pushInr       => [ChildSpecV2.termSameScope]
  | .gen_pushGlue      => [ChildSpecV2.termSameScope]
  | .gen_pushRec       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 2.3 Truncations (level lives in Nat payload, not as child)
  | .gen_truncIntro    => [ChildSpecV2.termSameScope]
  | .gen_truncCoh      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_truncRec      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 2.4 Polynomial Functors (positionFamily at scope+1)
  | .gen_polyFunctor   =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeUnderBinder]
  | .gen_polyApply     =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  | .gen_polyMu        => [ChildSpecV2.typeSameScope]
  | .gen_polyNu        => [ChildSpecV2.typeSameScope]
  | .gen_polyMap       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 2.5 Measure
  | .gen_sigmaAlgebra  => [ChildSpecV2.termSameScope]
  | .gen_measureSpace  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_lebesgueInt   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 2.6 Temporal Logic (propositions are types)
  | .gen_nextT         => [ChildSpecV2.typeSameScope]
  | .gen_alwaysT       => [ChildSpecV2.typeSameScope]
  | .gen_eventuallyT   => [ChildSpecV2.typeSameScope]
  | .gen_untilT        =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  | .gen_sinceT        =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- 2.7 Synthetic Differentials
  | .gen_infinitesimal => [ChildSpecV2.typeSameScope]
  | .gen_microcanc     => [ChildSpecV2.termSameScope]
  | .gen_tangentSpace  =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope]
  | .gen_diffOp        =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 3.1 Sessions
  | .gen_sessionSelect =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_sessionOffer  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_sessionClose  => [ChildSpecV2.termSameScope]
  | .gen_channelSplit  => [ChildSpecV2.termSameScope]
  | .gen_channelJoin   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 3.2 Hardware
  | .gen_regRead       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_regWrite      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_clockTick     => [ChildSpecV2.typeSameScope]  -- clockDomain is a type
  | .gen_stageLatch    =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_wireCombinational => [ChildSpecV2.termSameScope]
  | .gen_clockDomainCross  =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope,
     ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 3.3 Computational Reals
  | .gen_realCauchy    =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_realLimit     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_realCompare   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- 3.4 Probability
  | .gen_probSpace     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_sampleP       => [ChildSpecV2.termSameScope]
  | .gen_expectE       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 3.5 p-adic
  | .gen_padicNum      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_padicValuation =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_localGlobalBridge =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 3.6 UC (interface is a type; protocols/simulators are terms)
  | .gen_idealFunctionality => [ChildSpecV2.typeSameScope]
  | .gen_realProtocol  => [ChildSpecV2.termSameScope]
  | .gen_ucSimulator   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_ucCompose     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 3.7 Info Theory
  | .gen_shannonEntropy => [ChildSpecV2.termSameScope]
  | .gen_mutualInfo    => [ChildSpecV2.termSameScope]
  | .gen_klDivergence  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_channelCapacity => [ChildSpecV2.termSameScope]
  -- 3.8 Spectral
  | .gen_hilbertSpace  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_boundedOperator =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_spectralDecomp =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_unitaryOp     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 3.9 Causal
  | .gen_causalNet     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_doOperator    =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_counterfactual =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 4.1 Circle + Higher Paths
  | .gen_circleBase    => []
  | .gen_circleLoop    => []
  | .gen_circleRec     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_pathInverse   => [ChildSpecV2.termSameScope]
  | .gen_pathWhiskerLeft  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_pathWhiskerRight =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 4.2 Cohesive Modalities (carriers are types; adjunction unit operates on terms)
  | .gen_shapeModality => [ChildSpecV2.typeSameScope]
  | .gen_flatModality  => [ChildSpecV2.typeSameScope]
  | .gen_sharpModality => [ChildSpecV2.typeSameScope]
  | .gen_cohesiveAdjunctionUnit => [ChildSpecV2.termSameScope]
  -- 4.3 QIITs
  | .gen_qiitIntro     => [ChildSpecV2.termSameScope]
  | .gen_qiitElim      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- 4.4 2LTT
  | .gen_liftInnerToOuter => [ChildSpecV2.termSameScope]
  | .gen_lowerOuterToInner =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_modalityLayerMarker => [ChildSpecV2.termSameScope]
  -- 4.5 Quantum
  | .gen_qubit         => []
  | .gen_quantumGate   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_quantumMeasure =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_quantumEntangle =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_quantumDecohere =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- 4.6 Game Semantics
  | .gen_game          => [ChildSpecV2.termSameScope]
  | .gen_strategy      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_playOut       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 4.7 Process Calculi
  | .gen_processCalc   => [ChildSpecV2.termSameScope]
  | .gen_parallelComp  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_processCommit => [ChildSpecV2.termSameScope]
  | .gen_bisimulationWitness =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- ═══════════════════════════════════════════════════════════════
  -- Tier ★★ extensions
  -- ═══════════════════════════════════════════════════════════════
  -- 5.1 Cubical Kan
  | .gen_compCubical   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_transpHigherDim =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 5.2 Algebraic Structures (carriers are types; operations + laws are terms)
  | .gen_groupAlg      =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_ringAlg       =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_moduleAlg     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- 5.3 Container Calculus (derivative + zipper operate on type polynomials)
  | .gen_containerDeriv => [ChildSpecV2.typeSameScope]
  | .gen_zipperType    => [ChildSpecV2.typeSameScope]
  | .gen_plugOp        =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 5.4 Differential Lambda (body under one binder; mirrors gen_lam)
  | .gen_diffLambda    => [ChildSpecV2.termUnderBinder]
  | .gen_diffApply     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_differentialCategory => [ChildSpecV2.termSameScope]
  -- 5.5 Linear Logic (modalities on types; linear arrow / tensor are type-level)
  | .gen_bangModality  => [ChildSpecV2.typeSameScope]
  | .gen_whyNotModality => [ChildSpecV2.typeSameScope]
  | .gen_linearArrow   =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  | .gen_tensorProduct =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- 5.6 Provability / Dynamic Logic (statement is type; dynamic logic is [program] postcondition)
  | .gen_provabilityModality => [ChildSpecV2.typeSameScope]
  | .gen_dynamicLogic  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.typeSameScope]
  -- 5.7 Domain Theory (carrier is type; structure/operations are terms)
  | .gen_cpoStructure  =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_bottomElem    => [ChildSpecV2.termSameScope]
  | .gen_scottContinuous =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_fixedPoint    =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 5.8 Hyperreals
  | .gen_hyperreal     => []
  | .gen_starOp        => [ChildSpecV2.termSameScope]
  | .gen_standardPart  => [ChildSpecV2.termSameScope]
  -- 5.9 CA / Reversible
  | .gen_cellularAutomaton =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_interactionNet =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_reversibleOp  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- 5.10 Synthetic Complexity
  | .gen_bigOh         =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_polyTimeWitness =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_npComplete    =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]

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
on `[]` / `[x]` / `[x, y]` / `[x, y, z]` and each `ChildSpecV2`'s
`scopeShift` projection is also a literal. -/
theorem Generator.childSpecs_scopeShifts_eq_binderShifts
    (generator : Generator) :
    (generator.childSpecs.map ChildSpecV2.scopeShift) =
      generator.binderShifts := by
  cases generator <;> rfl

end LeanFX2.Foundation.PolyCell.Core
