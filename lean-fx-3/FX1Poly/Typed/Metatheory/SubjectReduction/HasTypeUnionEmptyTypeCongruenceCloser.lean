import FX1Poly.Typed.Engine.Union.HasTypeUnionEmptyCanonicalForms
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSingleStepSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLeaves

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionEmptyTypeCongruenceCloser
    — the empty-type congruence closer, reduced to the eliminator arm — TYTAB-2-FT gate-2 congruence half

The remaining residual of the native consistency route (`EmptyTypeConsistencyNativeUnion.lean`) is the
`UnionCongruenceCloser` AT THE EMPTY TYPE: when one child of a `.mkGen` cell typed at `emptyTypeCell` steps,
re-type the parent.  The general congruence closer is a per-arm induction over the seven union arms (the
native mountain) — but at the classifier `emptyTypeCell` FOUR of the seven arms collapse VACUOUSLY, exactly as
in the shipped gate-3 canonicity `HasTypeUnion.closedNormalNoInhabitantAtEmptyType`:

  * `var` — closedness (`Fin scope → False`);
  * `universeFormation` / `formationRule` — every formation classifier is a UNIVERSE code, head-distinct from
    `gen_emptyCode` (`Conv.universeCode_not_emptyTypeCode`);
  * `intro` — every introducer classifier is a head-stable DATA code, never `Conv emptyTypeCell`
    (`refuteConvToEmptyFromStableHead`); the `pathLam` row's `bridgeTypeCell` classifier is handled the SAME
    way via the new `headReaches_bridgeTypeCell` (so NO `pathLam`-freedom hypothesis is needed — unlike the
    canonicity proof, whose `pathLam` row rode the normal-form's containment-freedom).

The derivation is reflected to the `ofGrown`-free native judgment (`toNativeOnly`) and inducted over all SIX
native-union arms — no `ofGrown` arm; a host-typed stepping cell reflects into the native former / intro / elim
arm, each of which already handles the congruence, so the former grown-SR re-typing is unnecessary.  The two
SURVIVING arms re-type rather than refute:

  * `conv` — recurses (absorbing the conversion through `converts.trans`);
  * `elim` — the GENUINE residual: the eliminator congruence (re-type an eliminator cell when one child
    steps).  Exposed as the named gate `UnionElimCongruenceClosesToEmptyType`.

So this file ships the empty-type congruence closer **modulo the single eliminator arm** — the gate-2
congruence half is now ONE arm (`elim`) instead of seven.  Combined with native SN (gate 1) and the discharged
redex half, native consistency rests on native SN + the eliminator-congruence closer only.

## Zero-axiom

The four refuting arms copy the shipped canonicity refuters (`refuteConvToEmptyFromStableHead`,
`Conv.universeCode_not_emptyTypeCode`, the formation-output universe lemmas, the `headReaches_*`
head-stabilities); `conv` recurses; `elim` defers (its native obligations re-embedded via `toUnion`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionEmptyTypeCongruenceCloser.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Every reduct of a bridge code keeps the `gen_bridgeCode` head.**  The `headReaches_idTypeCell` twin for
the term-indexed bridge former (`bridgeTypeCell typeCode left right = .mkGen gen_bridgeCode () [typeCode, left,
right]`): head-stability under `StepStar` via `shapeStable_bridgeTypeGeneral`.  Lets the `pathLam` introducer
row refute `Conv … emptyTypeCell` by head-distinctness, UNIFORMLY with the other data introducer rows — no
`pathLam`-freedom hypothesis. -/
theorem headReaches_bridgeTypeCell {scope : Nat} {typeCode leftEndpoint rightEndpoint : RawTerm scope}
    {reduct : RawTerm scope}
    (chain : StepStar (bridgeTypeCell typeCode leftEndpoint rightEndpoint) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_bridgeCode := by
  obtain ⟨_typeAfter, _leftAfter, _rightAfter, reductEq, _typeStar, _leftStar, _rightStar⟩ :=
    StepStar.shapeStable_bridgeTypeGeneral chain typeCode leftEndpoint rightEndpoint rfl
  rw [reductEq]
  rfl

/-- **A `variableCell` admits no congruence step.**  `variableCell index = .mkGen gen_var index .childNil`
has the empty child spine, so any `.mkGen` whose head/children match it has `before = childNil`, and
`StepChildren childNil _` is impossible (`noStepChildren_childNil`).  A reusable leaf-vacuity brick for the
`var` arm of any union congruence closer — no classifier hypothesis needed. -/
theorem variableCellHasNoCongruenceStep {scope : Nat} {index : Fin scope} {generator : Generator}
    {payload : generator.payload scope}
    {before after : RawTermChildren generator.binderShifts scope}
    (shape : variableCell index = RawTerm.mkGen generator payload before)
    (childStep : StepChildren before after) : False := by
  injection shape with _scopeEq generatorEq _payloadEq childrenEq
  subst generatorEq
  cases eq_of_heq childrenEq
  exact StepStar.noStepChildren_childNil childStep

/-- **A `universeCodeCell` admits no congruence step.**  `universeCodeCell L f = .mkGen gen_universeCode (L, f)
.childNil` has the empty child spine, so `before = childNil` and `StepChildren childNil _` is impossible.  The
`universeFormation` arm's leaf-vacuity twin of `variableCellHasNoCongruenceStep`. -/
theorem universeCodeCellHasNoCongruenceStep {scope : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {generator : Generator} {payload : generator.payload scope}
    {before after : RawTermChildren generator.binderShifts scope}
    (shape : universeCodeCell levelExpr flag = RawTerm.mkGen generator payload before)
    (childStep : StepChildren before after) : False := by
  injection shape with _scopeEq generatorEq _payloadEq childrenEq
  subst generatorEq
  cases eq_of_heq childrenEq
  exact StepStar.noStepChildren_childNil childStep

/-- **Gate interface — the eliminator-arm congruence closer at the empty type.**  When an eliminator cell
`rule.memberCell scope args` (whose output type converts to `emptyTypeCell`) is a `.mkGen` whose children step,
the re-formed cell is union-typed at a `Conv`-equal classifier.  This is the ONE genuine surviving arm of the
empty-type congruence closer — the native eliminator-congruence subject reduction.  Its premises are exactly
the `elim` arm's: the row hit, the union-typed obligations, closedness, and the congruence step. -/
def UnionElimCongruenceClosesToEmptyType (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : ElimRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    elimRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    (Fin scope → False) →
    ∀ {gen : Generator} {payload : gen.payload scope}
      {before after : RawTermChildren gen.binderShifts scope},
      rule.memberCell scope args = RawTerm.mkGen gen payload before →
      StepChildren before after →
      Conv (rule.outputType scope args params) (emptyTypeCell (scope := scope)) →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen gen payload after) pinned ∧
        Conv pinned (emptyTypeCell (scope := scope))

/-- **★ The empty-type congruence closer, modulo the eliminator arm (the generic, context-threaded core).**
A union typing of a `.mkGen` cell whose classifier converts to `emptyTypeCell`, one of whose children steps,
re-types at a `Conv`-equal classifier — given closedness (`Fin scope → False`), a well-formed context (threaded
to the `conv` recursion), and the eliminator-arm gate.  Reflected to the native judgment (`toNativeOnly`) and
inducted over all six native arms: `var`/`universeFormation`/`formationRule`/`intro` refute through the
empty-type rigidity copied from the gate-3 canonicity; `conv` recurses; `elim` delegates to the gate (its
carried obligations re-embedded via `toUnion`).  Stated over a free `subject`/`classifier` with a `subject = .mkGen …` pin and a
`Conv classifier emptyTypeCell` framing, so the empty-context closer is the `Conv.refl` specialization. -/
theorem HasTypeUnion.congruenceClosesToEmptyTypeAux {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier) :
    (Fin scope → False) →
    WfContextDescPi context →
    UnionElimCongruenceClosesToEmptyType profile →
    ∀ {gen : Generator} {payload : gen.payload scope}
      {before after : RawTermChildren gen.binderShifts scope},
      subject = RawTerm.mkGen gen payload before →
      StepChildren before after →
      Conv classifier (emptyTypeCell (scope := scope)) →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen gen payload after) pinned ∧
        Conv pinned (emptyTypeCell (scope := scope)) := by
  have nativeTyped := typed.toNativeOnly
  clear typed
  induction nativeTyped with
  | var _context index =>
      intro closed _wfDescPi _elimCloser _gen _payload _before _after _subjectShape _childStep _convToEmpty
      exact (closed index).elim
  | universeFormation _context _levelExpr _flag =>
      intro _closed _wfDescPi _elimCloser _gen _payload _before _after _subjectShape _childStep convToEmpty
      exact (Conv.universeCode_not_emptyTypeCode convToEmpty).elim
  | formationRule _fContext fGenerator _fPayload _fChildren rule levels _carrier _level flag
      isFormationRule _premisesHold _ihPremises =>
      intro _closed _wfDescPi _elimCloser _gen _payload _before _after _subjectShape _childStep convToEmpty
      cases rule with
      | baseType baseRule =>
          dsimp only [FormationRule.outputType] at convToEmpty
          rw [baseTypeRuleTableOutputIsType0 (formationRuleOf_baseType_inv isFormationRule)]
            at convToEmpty
          exact (Conv.universeCode_not_emptyTypeCode convToEmpty).elim
      | flat flatRule =>
          dsimp only [FormationRule.outputType] at convToEmpty
          rw [flatTypingRuleDescOf_outputIsUniverseFormer (formationRuleOf_flat_inv isFormationRule)]
            at convToEmpty
          dsimp only [universeFormerOutput] at convToEmpty
          exact (Conv.universeCode_not_emptyTypeCode convToEmpty).elim
      | cumulative cumulativeRule =>
          have isCumulative : typingRuleDescOf fGenerator = some cumulativeRule :=
            formationRuleOf_cumulative_inv isFormationRule
          dsimp only [FormationRule.outputType] at convToEmpty
          obtain ⟨_outputLevel, _outputFlag, outputEq⟩ :=
            typingRuleDescOf_output_isUniverseCode isCumulative _ levels flag
          rw [outputEq] at convToEmpty
          exact (Conv.universeCode_not_emptyTypeCode convToEmpty).elim
      | termIndexed termRule =>
          dsimp only [FormationRule.outputType] at convToEmpty
          rw [termIndexedFormerDescOf_outputIsUniverse (formationRuleOf_termIndexed_inv isFormationRule)]
            at convToEmpty
          exact (Conv.universeCode_not_emptyTypeCode convToEmpty).elim
  | intro _iContext iGenerator rule args params _level0 _level1 _flag isIntro _sideHolds
      _premisesHold _ihPremises =>
      intro _closed _wfDescPi _elimCloser _gen _payload _before _after _subjectShape _childStep convToEmpty
      rcases introRuleOf_cases isIntro with
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩
      · -- boolTrue
        subst generatorEq; subst ruleEq
        exact (refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_boolTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- boolFalse
        subst generatorEq; subst ruleEq
        exact (refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_boolTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- unit
        subst generatorEq; subst ruleEq
        exact (refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_unitCodeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- interval0
        subst generatorEq; subst ruleEq
        exact (refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_intervalTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- interval1
        subst generatorEq; subst ruleEq
        exact (refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_intervalTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- natZero
        subst generatorEq; subst ruleEq
        exact (refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_natTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- lam (the Pi-code classifier)
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _domainAnn (.childCons _body .childNil), .childCons _codomainCode .childNil =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_piTyCodeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- pathLam (the bridge-code classifier — refuted by bridge head-stability, no pathLam-freedom needed)
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _body .childNil, .childCons _carrierCode .childNil =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_bridgeTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- natSucc
        subst generatorEq; subst ruleEq
        exact (refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_natTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- listCons
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _headValue (.childCons _tailList .childNil), .childCons _elementType .childNil =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_listTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- optionSome
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _payload .childNil, .childCons _typeParam0 .childNil =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_optionTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- optionNone
        subst generatorEq; subst ruleEq
        match args, params with
        | .childNil, .childCons _typeParam0 .childNil =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_optionTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- listNil
        subst generatorEq; subst ruleEq
        match args, params with
        | .childNil, .childCons _typeParam0 .childNil =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_listTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- eitherInl
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _payload .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_eitherTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- eitherInr
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _payload .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_eitherTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- pair
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _firstComponent (.childCons _secondComponent .childNil),
          .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_productTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- refl
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _witness .childNil, .childCons _typeParam0 .childNil =>
          exact (refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_idTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)).elim
  | elim _eContext eGenerator rule args params level0 level1 flag isElim premisesHold _ihPremises =>
      intro closed _wfDescPi elimCloser _gen _payload _before _after subjectShape childStep convToEmpty
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact elimCloser eGenerator rule args params level0 level1 flag isElim premisesHold closed
        subjectShape childStep convToEmpty
  | conv _levelExpr _flag _innerTyped converts _reclassifierTyped ihTyped _ihReclassifier =>
      intro closed wfDescPi elimCloser _gen _payload _before _after subjectShape childStep convToEmpty
      exact ihTyped closed wfDescPi elimCloser subjectShape childStep (converts.trans convToEmpty)

/-- **★ The empty-type congruence closer, modulo the eliminator arm (the closer interface).**  Specializes
`congruenceClosesToEmptyTypeAux` to the EMPTY context and the literal `emptyTypeCell` classifier — the exact
`UnionCongruenceCloser` shape the consistency route consumes — given the eliminator-arm gate.  `Fin 0 → False`
is `elim0`; the grown well-formedness is `WfContextDescPi.emptyIsWellFormed`; the classifier is its own
`Conv.refl`.  So the gate-2 congruence half at the empty type is now exactly the eliminator congruence. -/
theorem HasTypeUnion.congruenceClosesToEmptyTypeModuloElim {profile : PolyProfile}
    (elimCloser : UnionElimCongruenceClosesToEmptyType profile) :
    UnionCongruenceCloser profile (TypingContext.empty : TypingContext profile 0)
      (emptyTypeCell (scope := 0)) := by
  intro generator payload childrenBefore childrenAfter typed childStep
  exact HasTypeUnion.congruenceClosesToEmptyTypeAux typed (fun emptyIndex => emptyIndex.elim0)
    WfContextDescPi.emptyIsWellFormed elimCloser rfl childStep (Conv.refl _)

end FX1Poly.Typed
