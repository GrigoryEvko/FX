import FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms
import FX1Poly.Typed.Ledger.Misc.EmptyTypeCodeConvRigidity

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionEmptyCanonicalForms
    — NATIVE closed-normal canonicity at the empty type (TYTAB-2-FT gate 3)

The lane master `HasTypeUnion.closedNormalLaneCanonicalForms` (this directory) covers the eight DATA lanes
(`bool`/`nat`/`option`/`either`/`product`/`id`/`pi`/`list`): a closed normal union-typed term whose classifier
converts to such a lane code IS a shallow value of that lane.  The empty type is deliberately ABSENT from
`IsLaneCode` — `LaneValue emptyType _` has no constructor, since the consistency claim is precisely that the
type is uninhabited.  Adding an `empty` arm to `IsLaneCode` would force a ninth `notEmpty` parameter onto the
shared `refuteConvFromStableHead` and break its dozen callers, so instead this file ships the empty case as a
DEDICATED mirror of the lane master — purely additive, touching no shipped declaration.

## The statement

`HasTypeUnion.closedNormalNoInhabitantAtEmptyType` : a closed normal `HasTypeUnion`-typed term on the core
beta/iota fragment (no `pathApp` / `pathLam` occurrence) whose classifier converts to `emptyTypeCell` yields
`False`.  One derivation induction over all seven union arms:

  * `var` dies on closedness (`Fin scope → False`);
  * `universeFormation` / `formationRule` die by universe-vs-empty rigidity (`Conv.universeCode_not_emptyTypeCode`):
    every formation classifier is a universe code, head-distinct from `gen_emptyCode`;
  * `ofGrown` mirrors the lane master's seven grown head cases (`closedNormalSubjectHead`), each classifier
    `Conv` a Π-code or universe code, refuted against `emptyTypeCell` by `Conv.piTyCode_not_emptyTypeCode` /
    `Conv.universeCode_not_emptyTypeCode`;
  * `intro` refutes each of the seventeen introducer rows uniformly: a data value's classifier is a head-stable
    data code (`headReaches_*`), distinct from the empty code (`Generator.noConfusion`), so it never converts to
    `emptyTypeCell` (`refuteConvToEmptyFromStableHead`); `pathLam` dies on the `gen_pathLam`-freedom hypothesis;
  * `elim` reuses the SHIPPED lane master on the scrutinee premise (pulled from `premisesHold`): a closed normal
    scrutinee at its data lane is a VALUE, so the eliminator is an iota redex — contradicting normality.  The
    eliminator arm is target-agnostic, so it copies the lane master verbatim with `premisesHold` replacing the
    induction hypothesis;
  * `conv` composes the conversion (`converts.trans`).

This is **gate 3 of the native consistency route** (`EmptyTypeConsistencyNativeUnion.lean`): the
`closedNormalCanonicity` hypothesis of `HasTypeUnion.consistencyOfNativeSubjectReduction`.  With native SN
(gate 1) and the single-step union SR master (gate 2) it makes native consistency unconditional.

## Zero-axiom

The shipped lane master + `Conv.{universeCode,piTyCode}_not_emptyTypeCode` + `Step.no_step_from_emptyCode` +
`Conv.refutedByDistinctStableHeads`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditEmptyTypeConsistencyNativeUnion`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The empty-type code is head-stable.**  `emptyTypeCell = .mkGen gen_emptyCode () .childNil` is a no-step
leaf (`Step.no_step_from_emptyCode`), so every reduct keeps the `gen_emptyCode` head — the empty-type analogue
of `headReaches_unitCodeCell`. -/
theorem headReaches_emptyTypeCell {scope : Nat} {reduct : RawTerm scope}
    (chain : StepStar (emptyTypeCell (scope := scope)) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_emptyCode := by
  have reductEq := StepStar.eq_of_noStep
    (fun _reduct step => Step.no_step_from_emptyCode step) chain
  rw [reductEq]
  rfl

/-- **The one-call empty-type refuter.**  A classifier whose every reduct keeps a head DISTINCT from
`gen_emptyCode` is never `Conv` the empty-type code.  Each data-introducer arm of the master supplies its own
head-stability witness (`headReaches_*`) plus one `Generator.noConfusion`.  The single-target analogue of the
lane master's `refuteConvFromStableHead`. -/
theorem refuteConvToEmptyFromStableHead {scope : Nat} {classifier : RawTerm scope}
    {classifierHead : Generator}
    (convToEmpty : Conv classifier (emptyTypeCell (scope := scope)))
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = classifierHead)
    (notEmpty : classifierHead = Generator.gen_emptyCode → False) : False :=
  Conv.refutedByDistinctStableHeads convToEmpty classifierStable
    (fun _reduct chain => headReaches_emptyTypeCell chain) notEmpty

/-- **★ NATIVE-38 consistency face: no closed-normal union inhabitant of the empty type.**  A closed normal
`HasTypeUnion`-typed term on the core beta/iota fragment (no `pathApp` / `pathLam` occurrence) whose classifier
converts to `emptyTypeCell` yields `False`.  The empty-type twin of `closedNormalLaneCanonicalForms`: one
derivation induction over all seven arms, refuting each through universe/empty rigidity (formation arms), the
grown empty rule-out (`ofGrown`), the data-code head-distinctness refuter (`intro`), and the SHIPPED lane
master on the scrutinee (`elim`, the iota-redex contradiction).  This is gate 3 of the native consistency
route. -/
theorem HasTypeUnion.closedNormalNoInhabitantAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier) :
    (Fin scope → False) →
    RawTerm.isStepNormalFormBool subject = true →
    RawTerm.containsGeneratorBool .gen_pathApp subject = false →
    RawTerm.containsGeneratorBool .gen_pathLam subject = false →
    Conv classifier (emptyTypeCell (scope := scope)) → False := by
  induction typed with
  | var _context index =>
      intro closed _normal _pathAppFree _pathLamFree _convToEmpty
      exact (closed index).elim
  | universeFormation _context _levelExpr _flag =>
      intro _closed _normal _pathAppFree _pathLamFree convToEmpty
      exact Conv.universeCode_not_emptyTypeCode convToEmpty
  | ofGrown hostTyped =>
      intro closed normal _pathAppFree _pathLamFree convToEmpty
      rcases HasTypeDescPi.closedNormalSubjectHead hostTyped normal closed with
          headLam | headPi | headSigma | headUniverse | headList | headOption | headUnit
      · obtain ⟨_domainAnn, _body, lamEq⟩ := eq_lamCell_of_headGenerator headLam
        rw [lamEq] at hostTyped
        obtain ⟨_codomainInner, _domainLevel, _codomainLevel, _flag,
            convToPiCode, _domainTyped, _codomainTyped, _bodyTyped⟩ :=
          HasTypeDescPi.invertLam hostTyped
        exact Conv.piTyCode_not_emptyTypeCode (convToPiCode.sym.trans convToEmpty)
      · obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
        rw [piEq] at hostTyped
        obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped,
            convToUniverseCode⟩ := HasTypeDescPi.invertPiTyCode hostTyped
        exact Conv.universeCode_not_emptyTypeCode (convToUniverseCode.sym.trans convToEmpty)
      · obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
        rw [sigmaEq] at hostTyped
        obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped,
            convToUniverseCode⟩ := HasTypeDescPi.invertSigmaTyCode hostTyped
        exact Conv.universeCode_not_emptyTypeCode (convToUniverseCode.sym.trans convToEmpty)
      · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
        rw [universeEq] at hostTyped
        exact Conv.universeCode_not_emptyTypeCode
          ((HasTypeDescPi.inversionUniverseCode hostTyped).sym.trans convToEmpty)
      · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
        rw [listEq] at hostTyped
        obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
          HasTypeDescPi.formerClassifierConvUniverseGeneric hostTyped typingRuleDescOf_listCode rfl
        exact Conv.universeCode_not_emptyTypeCode (convToUniverseCode.sym.trans convToEmpty)
      · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
        rw [optionEq] at hostTyped
        obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
          HasTypeDescPi.formerClassifierConvUniverseGeneric hostTyped typingRuleDescOf_optionCode rfl
        exact Conv.universeCode_not_emptyTypeCode (convToUniverseCode.sym.trans convToEmpty)
      · have unitEq := eq_unitCodeCell_of_headGenerator headUnit
        rw [unitEq] at hostTyped
        obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
          HasTypeDescPi.formerClassifierConvUniverseGeneric hostTyped typingRuleDescOf_unitCode rfl
        exact Conv.universeCode_not_emptyTypeCode (convToUniverseCode.sym.trans convToEmpty)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold ihPremises =>
      intro _closed _normal _pathAppFree _pathLamFree convToEmpty
      -- Every formation classifier IS a universe / type-code output (`rule.outputType`), head-distinct from the
      -- empty code: rewrite each row's output to its universe code and die through universe/empty rigidity,
      -- exactly as the lane master's `formationRule` arm dies through `notConvFromUniverse`.
      cases rule with
      | baseType baseRule =>
          dsimp only [FormationRule.outputType] at convToEmpty
          rw [baseTypeRuleTableOutputIsType0 (formationRuleOf_baseType_inv isFormationRule)]
            at convToEmpty
          exact Conv.universeCode_not_emptyTypeCode convToEmpty
      | flat flatRule =>
          dsimp only [FormationRule.outputType] at convToEmpty
          rw [flatTypingRuleDescOf_outputIsUniverseFormer (formationRuleOf_flat_inv isFormationRule)]
            at convToEmpty
          dsimp only [universeFormerOutput] at convToEmpty
          exact Conv.universeCode_not_emptyTypeCode convToEmpty
      | cumulative cumulativeRule =>
          have isCumulative : typingRuleDescOf generator = some cumulativeRule :=
            formationRuleOf_cumulative_inv isFormationRule
          dsimp only [FormationRule.outputType] at convToEmpty
          obtain ⟨_outputLevel, _outputFlag, outputEq⟩ :=
            typingRuleDescOf_output_isUniverseCode isCumulative _ levels flag
          rw [outputEq] at convToEmpty
          exact Conv.universeCode_not_emptyTypeCode convToEmpty
      | termIndexed termRule =>
          dsimp only [FormationRule.outputType] at convToEmpty
          rw [termIndexedFormerDescOf_outputIsUniverse (formationRuleOf_termIndexed_inv isFormationRule)]
            at convToEmpty
          exact Conv.universeCode_not_emptyTypeCode convToEmpty
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      intro _closed _normal _pathAppFree pathLamFree convToEmpty
      -- Each introducer row's classifier (`rule.outputType`) is a head-stable DATA code distinct from the empty
      -- code, so it never converts to `emptyTypeCell`; `pathLam` dies on the containment-freedom hypothesis.
      rcases introRuleOf_cases isIntro with
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩
      · -- **boolTrue**
        subst generatorEq; subst ruleEq
        exact refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_boolTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)
      · -- **boolFalse**
        subst generatorEq; subst ruleEq
        exact refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_boolTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)
      · -- **unit**
        subst generatorEq; subst ruleEq
        exact refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_unitCodeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)
      · -- **interval0**
        subst generatorEq; subst ruleEq
        exact refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_intervalTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)
      · -- **interval1**
        subst generatorEq; subst ruleEq
        exact refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_intervalTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)
      · -- **natZero**
        subst generatorEq; subst ruleEq
        exact refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_natTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)
      · -- **lam** (the Pi-code classifier)
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _domainAnn (.childCons _body .childNil), .childCons _codomainCode .childNil =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_piTyCodeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **pathLam** — the subject heads `gen_pathLam`, contradicting the containment-freedom hypothesis.
        subst generatorEq; subst ruleEq
        match args with
        | .childCons body .childNil =>
          exact Bool.noConfusion (pathLamFree.symm.trans
            (RawTerm.containsGeneratorBool_headHit .gen_pathLam () (.childCons body .childNil)))
      · -- **natSucc**
        subst generatorEq; subst ruleEq
        exact refuteConvToEmptyFromStableHead convToEmpty
          (fun _reduct chain => headReaches_natTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq)
      · -- **listCons**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _headValue (.childCons _tailList .childNil), .childCons _elementType .childNil =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_listTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **optionSome**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _payload .childNil, .childCons _typeParam0 .childNil =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_optionTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **optionNone**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childNil, .childCons _typeParam0 .childNil =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_optionTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **listNil**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childNil, .childCons _typeParam0 .childNil =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_listTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **eitherInl**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _payload .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_eitherTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **eitherInr**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _payload .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_eitherTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **pair**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _firstComponent (.childCons _secondComponent .childNil),
          .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_productTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
      · -- **refl**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons _witness .childNil, .childCons _typeParam0 .childNil =>
          exact refuteConvToEmptyFromStableHead convToEmpty
            (fun _reduct chain => headReaches_idTypeCell chain)
            (fun headsEq => Generator.noConfusion headsEq)
  | elim context generator rule args params level0 level1 flag isElim premisesHold ihPremises =>
      intro closed normal pathAppFree pathLamFree _convToEmpty
      -- The eliminator arm is TARGET-AGNOSTIC: a closed normal scrutinee at its data lane is a VALUE (the
      -- SHIPPED lane master applied to the scrutinee premise), so the eliminator cell is an iota redex —
      -- contradicting `normal`.  Copies the lane master's eliminator arm verbatim, with `premisesHold`
      -- feeding the lane master where the lane master fed its own induction hypothesis.
      rcases elimRuleOf_cases isElim with
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩
      · -- **app**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons function (.childCons argument .childNil),
          .childCons domainCode (.childCons codomainCode .childNil) =>
          have functionNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTerm.isStepNormalFormBool_children normal)
          have functionAppFree := RawTermChildren.containGeneratorBool_head
            (RawTerm.containsGeneratorBool_children pathAppFree)
          have functionLamFree := RawTermChildren.containGeneratorBool_head
            (RawTerm.containsGeneratorBool_children pathLamFree)
          have functionValue :
              LaneValue (piTyCodeCell domainCode codomainCode) function :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed functionNormal
              functionAppFree functionLamFree (IsLaneCode.pi domainCode codomainCode) (Conv.refl _)
          obtain ⟨domainAnn, lamBody, functionEq⟩ := functionValue.atPi
          rw [functionEq] at normal
          cases normal
      · -- **pathApp** — the subject heads `gen_pathApp`, contradicting the containment-freedom hypothesis.
        subst generatorEq; subst ruleEq
        match args with
        | .childCons path (.childCons argument .childNil) =>
          exact Bool.noConfusion (pathAppFree.symm.trans
            (RawTerm.containsGeneratorBool_headHit .gen_pathApp ()
              (.childCons path (.childCons argument .childNil))))
      · -- **natElim**
        subst generatorEq; subst ruleEq
        match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch
            (.childCons scrutinee .childNil))) =>
          have scrutineeNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTermChildren.areStepNormalFormsBool_tail
              (RawTermChildren.areStepNormalFormsBool_tail
                (RawTermChildren.areStepNormalFormsBool_tail
                  (RawTerm.isStepNormalFormBool_children normal))))
          have scrutineeAppFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathAppFree))))
          have scrutineeLamFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathLamFree))))
          have scrutineeValue : LaneValue (natTypeCell : RawTerm _) scrutinee :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed scrutineeNormal
              scrutineeAppFree scrutineeLamFree IsLaneCode.nat (Conv.refl _)
          rcases scrutineeValue.atNat with scrutineeEq | ⟨predecessor, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **natRec**
        subst generatorEq; subst ruleEq
        match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch
            (.childCons scrutinee .childNil))) =>
          have scrutineeNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTermChildren.areStepNormalFormsBool_tail
              (RawTermChildren.areStepNormalFormsBool_tail
                (RawTermChildren.areStepNormalFormsBool_tail
                  (RawTerm.isStepNormalFormBool_children normal))))
          have scrutineeAppFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathAppFree))))
          have scrutineeLamFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathLamFree))))
          have scrutineeValue : LaneValue (natTypeCell : RawTerm _) scrutinee :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed scrutineeNormal
              scrutineeAppFree scrutineeLamFree IsLaneCode.nat (Conv.refl _)
          rcases scrutineeValue.atNat with scrutineeEq | ⟨predecessor, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **boolElim** (dependent: paramShifts [] — no type-index params)
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons scrutinee (.childCons thenBranch
            (.childCons elseBranch .childNil))), .childNil =>
          have scrutineeNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTermChildren.areStepNormalFormsBool_tail
              (RawTermChildren.areStepNormalFormsBool_tail
                (RawTermChildren.areStepNormalFormsBool_tail
                  (RawTerm.isStepNormalFormBool_children normal))))
          have scrutineeAppFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathAppFree))))
          have scrutineeLamFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathLamFree))))
          have scrutineeValue : LaneValue (boolTypeCell : RawTerm _) scrutinee :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed scrutineeNormal
              scrutineeAppFree scrutineeLamFree IsLaneCode.bool (Conv.refl _)
          rcases scrutineeValue.atBool with scrutineeEq | scrutineeEq
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **optionMatch**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons noneBranch (.childCons someBranch
            (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          have scrutineeNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTermChildren.areStepNormalFormsBool_tail
              (RawTermChildren.areStepNormalFormsBool_tail
                (RawTermChildren.areStepNormalFormsBool_tail
                  (RawTerm.isStepNormalFormBool_children normal))))
          have scrutineeAppFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathAppFree))))
          have scrutineeLamFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathLamFree))))
          have scrutineeValue : LaneValue (optionTypeCell typeParamA) scrutinee :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed scrutineeNormal
              scrutineeAppFree scrutineeLamFree (IsLaneCode.option typeParamA) (Conv.refl _)
          rcases scrutineeValue.atOption with scrutineeEq | ⟨payload, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **eitherMatch**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons leftBranch (.childCons rightBranch
            (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          have scrutineeNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTermChildren.areStepNormalFormsBool_tail
              (RawTermChildren.areStepNormalFormsBool_tail
                (RawTermChildren.areStepNormalFormsBool_tail
                  (RawTerm.isStepNormalFormBool_children normal))))
          have scrutineeAppFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathAppFree))))
          have scrutineeLamFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathLamFree))))
          have scrutineeValue : LaneValue (eitherTypeCell typeParamA typeParamB) scrutinee :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed scrutineeNormal
              scrutineeAppFree scrutineeLamFree (IsLaneCode.either typeParamA typeParamB) (Conv.refl _)
          rcases scrutineeValue.atEither with ⟨payload, scrutineeEq⟩ | ⟨payload, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **idJ**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons endpoint (.childCons resultType .childNil)) =>
          have witnessNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTermChildren.areStepNormalFormsBool_tail
              (RawTermChildren.areStepNormalFormsBool_tail
                (RawTerm.isStepNormalFormBool_children normal)))
          have witnessAppFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTerm.containsGeneratorBool_children pathAppFree)))
          have witnessLamFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTerm.containsGeneratorBool_children pathLamFree)))
          have witnessValue : LaneValue (idTypeCell typeCode endpoint endpoint) witness :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed witnessNormal
              witnessAppFree witnessLamFree (IsLaneCode.identity typeCode endpoint endpoint)
              (Conv.refl _)
          obtain ⟨witnessPayload, witnessEq⟩ := witnessValue.atIdentity
          rw [witnessEq] at normal
          cases normal
      · -- **fst**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
          have pairNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTerm.isStepNormalFormBool_children normal)
          have pairAppFree := RawTermChildren.containGeneratorBool_head
            (RawTerm.containsGeneratorBool_children pathAppFree)
          have pairLamFree := RawTermChildren.containGeneratorBool_head
            (RawTerm.containsGeneratorBool_children pathLamFree)
          have pairValue : LaneValue (productTypeCell firstType secondType) pairTerm :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed pairNormal
              pairAppFree pairLamFree (IsLaneCode.product firstType secondType) (Conv.refl _)
          obtain ⟨firstComponent, secondComponent, pairEq⟩ := pairValue.atProduct
          rw [pairEq] at normal
          cases normal
      · -- **snd**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
          have pairNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTerm.isStepNormalFormBool_children normal)
          have pairAppFree := RawTermChildren.containGeneratorBool_head
            (RawTerm.containsGeneratorBool_children pathAppFree)
          have pairLamFree := RawTermChildren.containGeneratorBool_head
            (RawTerm.containsGeneratorBool_children pathLamFree)
          have pairValue : LaneValue (productTypeCell firstType secondType) pairTerm :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed pairNormal
              pairAppFree pairLamFree (IsLaneCode.product firstType secondType) (Conv.refl _)
          obtain ⟨firstComponent, secondComponent, pairEq⟩ := pairValue.atProduct
          rw [pairEq] at normal
          cases normal
      · -- **listElim**
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons scrutinee (.childCons nilBranch
            (.childCons consBranch .childNil))),
          .childCons elementType (.childCons resultType .childNil) =>
          have scrutineeNormal := RawTermChildren.areStepNormalFormsBool_head
            (RawTermChildren.areStepNormalFormsBool_tail
              (RawTermChildren.areStepNormalFormsBool_tail
                (RawTermChildren.areStepNormalFormsBool_tail
                  (RawTerm.isStepNormalFormBool_children normal))))
          have scrutineeAppFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathAppFree))))
          have scrutineeLamFree := RawTermChildren.containGeneratorBool_head
            (RawTermChildren.containGeneratorBool_tail
              (RawTermChildren.containGeneratorBool_tail
                (RawTermChildren.containGeneratorBool_tail
                  (RawTerm.containsGeneratorBool_children pathLamFree))))
          have scrutineeValue : LaneValue (listTypeCell elementType) scrutinee :=
            HasTypeUnion.closedNormalLaneCanonicalForms (premisesHold _ (.head _)) closed scrutineeNormal
              scrutineeAppFree scrutineeLamFree (IsLaneCode.list elementType) (Conv.refl _)
          rcases scrutineeValue.atList with scrutineeEq | ⟨headValue, tailList, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
  | conv levelExpr flag typed converts reclassifierTyped ihTyped ihReclassifier =>
      intro closed normal pathAppFree pathLamFree convToEmpty
      exact ihTyped closed normal pathAppFree pathLamFree (converts.trans convToEmpty)

/-- **★ Closed empty-type consistency face (closed scope).**  The headline specialization: NO closed normal
union-typed term on the core beta/iota fragment is classified by `emptyTypeCell`.  Gate 3 of the native
consistency route, packaged at the empty context with `Fin 0 → False` discharged by `elim0`. -/
theorem HasTypeUnion.closedNormalEmptyTypeHasNoInhabitant {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (emptyTypeCell (scope := 0)))
    (normal : RawTerm.isStepNormalFormBool subject = true)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    False :=
  typed.closedNormalNoInhabitantAtEmptyType (fun emptyIndex => emptyIndex.elim0) normal
    pathAppFree pathLamFree (Conv.refl _)

end FX1Poly.Typed
