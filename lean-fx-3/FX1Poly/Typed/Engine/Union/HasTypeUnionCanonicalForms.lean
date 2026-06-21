import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTable
import FX1Poly.Typed.Corpus.Progress.GrownClosedNormalClassifierShape
import FX1Poly.Typed.Metatheory.Canonicity.Forms.IdCanonicalForms
import FX1Poly.Typed.Engine.Formation.ConvFlatCodeInjectivity

/-! # FX1Poly/Typed/HasTypeUnionCanonicalForms — closed-normal canonical forms over the ONE judgment
    (NATIVE-38: canonicity collapses to the single union judgment).

The first canonical-forms theorem stated and proven over `HasTypeUnion` itself — no per-engine
`Or`, no `TypedByValueEngine` side union.  A closed normal union-typed term whose classifier converts to a
LANE code (`bool` / `nat` / `option` / `either` / `product` / `id` / `Pi`) is a VALUE of that lane.

## The honest fragment boundary: the core beta/iota Step relation

`RawTerm.isStepNormalForm` is normality for the CORE beta+iota `Step` relation.  The bridge fragment's
computation rule (endpoint-beta, `pathApp(pathLam b, i0) ↝ b[i0]`) lives in the table-driven `StepTable`
relation (the `pathBetaIotaRow` row) and is NOT a constructor of core `Step` — so `pathApp(pathLam(boolTrue),
interval0)` is union-typed at `boolCode`, closed, and core-Step-NORMAL, a genuine non-value inhabitant.
The theorem therefore carries the fragment boundary EXPLICITLY: the subject contains no `gen_pathApp` and
no `gen_pathLam` occurrence (`RawTerm.containsGeneratorBool`).  This is not a proof IOU — it is the true
boundary of the shipped core reduction relation; the hypotheses become dischargeable (and the theorem
total) exactly when endpoint-beta lands in core `Step`.

## Architecture (the single induction, not a per-lane mutual)

Per-lane canonicity is inherently MUTUAL across data types (a `natElim` can be typed at `boolCode` while
its scrutinee lives at `natCode`), so the master is ONE derivation induction with the lane as part of the
conclusion: `IsLaneCode target → Conv classifier target → LaneValue target subject`.  The unified `elim`
arm consumes the induction hypothesis at THEIR scrutinee's lane per eliminator row and refutes normality
(the iota redex fires on a constructor-headed scrutinee); the unified `intro` arm emits `LaneValue`
constructors directly per introducer row (SHALLOW — only the head shape is recorded, which is all an iota
rule inspects); the cross-lane classifier clashes die by the two-head-stable `Conv` rigidity route.

## Zero-axiom

The mutual containment Bool mirrors `isStepNormalFormBool`; all projections are `Bool` case splits; the
rigidity refuter destructs `Conv`'s common reduct and runs the shipped head-stability lemmas into
`Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditHasTypeUnionCanonicalForms.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Tier0.Syntax

/-! ## Generator-occurrence containment (the honest bridge-fragment boundary) -/

mutual

/-- Deep generator-occurrence test: does `targetGenerator` head any subterm of `sourceTerm`? -/
def RawTerm.containsGeneratorBool (targetGenerator : Generator) :
    {scope : Nat} → RawTerm scope → Bool
  | _, .mkGen generator _payload children =>
      (if generator = targetGenerator then true else false) ||
        RawTermChildren.containGeneratorBool targetGenerator children

/-- Deep generator-occurrence test over a child spine. -/
def RawTermChildren.containGeneratorBool (targetGenerator : Generator) :
    {binderShifts : List Nat} → {scope : Nat} → RawTermChildren binderShifts scope → Bool
  | _, _, .childNil => false
  | _, _, .childCons childHead childTail =>
      RawTerm.containsGeneratorBool targetGenerator childHead ||
        RawTermChildren.containGeneratorBool targetGenerator childTail

end

/-! ## Boolean conjunction / disjunction projections (local, propext-free) -/

/-- Left projection of a true conjunction. -/
theorem andProjectLeft {leftValue rightValue : Bool}
    (bothTrue : (leftValue && rightValue) = true) : leftValue = true := by
  cases leftValue
  · cases bothTrue
  · rfl

/-- Right projection of a true conjunction. -/
theorem andProjectRight {leftValue rightValue : Bool}
    (bothTrue : (leftValue && rightValue) = true) : rightValue = true := by
  cases leftValue
  · cases bothTrue
  · exact bothTrue

/-- Left projection of a false disjunction. -/
theorem orProjectLeftFalse {leftValue rightValue : Bool}
    (bothFalse : (leftValue || rightValue) = false) : leftValue = false := by
  cases leftValue
  · rfl
  · cases bothFalse

/-- Right projection of a false disjunction. -/
theorem orProjectRightFalse {leftValue rightValue : Bool}
    (bothFalse : (leftValue || rightValue) = false) : rightValue = false := by
  cases leftValue
  · exact bothFalse
  · cases bothFalse

/-- A cell whose head IS the target generator contains it (contrapositive: a containment-free
hypothesis refutes any arm whose subject is headed by the excluded generator). -/
theorem RawTerm.containsGeneratorBool_headHit {scope : Nat} (targetGenerator : Generator)
    (payload : targetGenerator.payload scope)
    (children : RawTermChildren targetGenerator.binderShifts scope) :
    RawTerm.containsGeneratorBool targetGenerator
      (.mkGen targetGenerator payload children) = true := by
  show ((if targetGenerator = targetGenerator then true else false) ||
      RawTermChildren.containGeneratorBool targetGenerator children) = true
  rw [if_pos rfl]
  rfl

/-- Containment-freedom of a cell projects to containment-freedom of its child spine. -/
theorem RawTerm.containsGeneratorBool_children {scope : Nat} {targetGenerator generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (cellFree : RawTerm.containsGeneratorBool targetGenerator
      (.mkGen generator payload children) = false) :
    RawTermChildren.containGeneratorBool targetGenerator children = false := by
  exact orProjectRightFalse cellFree

/-- Containment-freedom of a `childCons` spine projects to its head. -/
theorem RawTermChildren.containGeneratorBool_head {scope headShift : Nat}
    {restShifts : List Nat} {targetGenerator : Generator}
    {childHead : RawTerm (scope + headShift)}
    {childTail : RawTermChildren restShifts scope}
    (spineFree : RawTermChildren.containGeneratorBool targetGenerator
      (.childCons childHead childTail) = false) :
    RawTerm.containsGeneratorBool targetGenerator childHead = false := by
  exact orProjectLeftFalse spineFree

/-- Containment-freedom of a `childCons` spine projects to its tail. -/
theorem RawTermChildren.containGeneratorBool_tail {scope headShift : Nat}
    {restShifts : List Nat} {targetGenerator : Generator}
    {childHead : RawTerm (scope + headShift)}
    {childTail : RawTermChildren restShifts scope}
    (spineFree : RawTermChildren.containGeneratorBool targetGenerator
      (.childCons childHead childTail) = false) :
    RawTermChildren.containGeneratorBool targetGenerator childTail = false := by
  exact orProjectRightFalse spineFree

/-! ## Normality child projections -/

/-- Normality of a cell projects to normality of its child spine. -/
theorem RawTerm.isStepNormalFormBool_children {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (cellNormal : RawTerm.isStepNormalFormBool (.mkGen generator payload children) = true) :
    RawTermChildren.areStepNormalFormsBool children = true := by
  exact andProjectRight cellNormal

/-- Normality of a `childCons` spine projects to its head. -/
theorem RawTermChildren.areStepNormalFormsBool_head {scope headShift : Nat}
    {restShifts : List Nat} {childHead : RawTerm (scope + headShift)}
    {childTail : RawTermChildren restShifts scope}
    (spineNormal : RawTermChildren.areStepNormalFormsBool
      (.childCons childHead childTail) = true) :
    RawTerm.isStepNormalFormBool childHead = true := by
  exact andProjectLeft spineNormal

/-- Normality of a `childCons` spine projects to its tail. -/
theorem RawTermChildren.areStepNormalFormsBool_tail {scope headShift : Nat}
    {restShifts : List Nat} {childHead : RawTerm (scope + headShift)}
    {childTail : RawTermChildren restShifts scope}
    (spineNormal : RawTermChildren.areStepNormalFormsBool
      (.childCons childHead childTail) = true) :
    RawTermChildren.areStepNormalFormsBool childTail = true := by
  exact andProjectRight spineNormal

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0.Syntax FX1Poly.Universe

/-! ## Head-stability wrappers (every lane former reaches only its own head) -/

/-- `boolCode` is a no-step leaf: a nullary former admits no root rule and no child congruence. -/
theorem noStep_boolTypeCell {scope : Nat} {reduct : RawTerm scope}
    (reduction : Step (boolTypeCell : RawTerm scope) reduct) : False := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-- `natCode` is a no-step leaf. -/
theorem noStep_natTypeCell {scope : Nat} {reduct : RawTerm scope}
    (reduction : Step (natTypeCell : RawTerm scope) reduct) : False := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-- Every reduct of `boolTypeCell` keeps the `gen_boolCode` head (it IS `boolTypeCell`). -/
theorem headReaches_boolTypeCell {scope : Nat} {reduct : RawTerm scope}
    (chain : StepStar (boolTypeCell : RawTerm scope) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_boolCode := by
  have reductEq := StepStar.eq_of_noStep (fun _reduct step => noStep_boolTypeCell step) chain
  rw [reductEq]
  rfl

/-- Every reduct of `natTypeCell` keeps the `gen_natCode` head. -/
theorem headReaches_natTypeCell {scope : Nat} {reduct : RawTerm scope}
    (chain : StepStar (natTypeCell : RawTerm scope) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_natCode := by
  have reductEq := StepStar.eq_of_noStep (fun _reduct step => noStep_natTypeCell step) chain
  rw [reductEq]
  rfl

/-- Every reduct of a universe code keeps the `gen_universeCode` head. -/
theorem headReaches_universeCodeCell {scope : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {reduct : RawTerm scope}
    (chain : StepStar (universeCodeCell levelExpr flag : RawTerm scope) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_universeCode := by
  have reductEq := StepStar.eq_of_noStep
    (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) chain
  rw [reductEq]
  rfl

/-- Every reduct of an option code keeps the `gen_optionCode` head. -/
theorem headReaches_optionTypeCell {scope : Nat} {elementType : RawTerm scope}
    {reduct : RawTerm scope}
    (chain : StepStar (optionTypeCell elementType) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_optionCode := by
  obtain ⟨_elementAfter, reductEq, _elementStar⟩ :=
    StepStar.shapeStable_optionCodeGeneral chain elementType rfl
  rw [reductEq]
  rfl

/-- Every reduct of an either code keeps the `gen_eitherCode` head. -/
theorem headReaches_eitherTypeCell {scope : Nat} {leftType rightType : RawTerm scope}
    {reduct : RawTerm scope}
    (chain : StepStar (eitherTypeCell leftType rightType) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_eitherCode := by
  obtain ⟨_leftAfter, _rightAfter, reductEq, _leftStar, _rightStar⟩ :=
    StepStar.shapeStable_eitherCodeGeneral chain leftType rightType rfl
  rw [reductEq]
  rfl

/-- Every reduct of a product code keeps the `gen_productCode` head. -/
theorem headReaches_productTypeCell {scope : Nat} {firstType secondType : RawTerm scope}
    {reduct : RawTerm scope}
    (chain : StepStar (productTypeCell firstType secondType) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_productCode := by
  obtain ⟨_firstAfter, _secondAfter, reductEq, _firstStar, _secondStar⟩ :=
    StepStar.shapeStable_productCodeGeneral chain firstType secondType rfl
  rw [reductEq]
  rfl

/-- Every reduct of an identity code keeps the `gen_idCode` head. -/
theorem headReaches_idTypeCell {scope : Nat} {typeCode leftEndpoint rightEndpoint : RawTerm scope}
    {reduct : RawTerm scope}
    (chain : StepStar (idTypeCell typeCode leftEndpoint rightEndpoint) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_idCode := by
  obtain ⟨_typeAfter, _leftAfter, _rightAfter, reductEq, _typeStar, _leftStar, _rightStar⟩ :=
    StepStar.shapeStable_idCodeGeneral chain typeCode leftEndpoint rightEndpoint rfl
  rw [reductEq]
  rfl

/-- Every reduct of a Pi code keeps the `gen_piTyCode` head. -/
theorem headReaches_piTyCodeCell {scope : Nat} {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)} {reduct : RawTerm scope}
    (chain : StepStar (piTyCodeCell domainCode codomainCode) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_piTyCode := by
  obtain ⟨_domainAfter, _codomainAfter, reductEq, _domainStar, _codomainStar⟩ :=
    StepStar.shapeStable_piTyCodeGeneral chain domainCode codomainCode rfl
  rw [reductEq]
  rfl

/-- Every reduct of a list code keeps the `gen_listCode` head. -/
theorem headReaches_listTypeCell {scope : Nat} {elementType : RawTerm scope}
    {reduct : RawTerm scope}
    (chain : StepStar (listTypeCell elementType) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_listCode := by
  obtain ⟨_elementAfter, reductEq, _elementStar⟩ :=
    StepStar.shapeStable_listCodeGeneral chain elementType rfl
  rw [reductEq]
  rfl

/-- **The generic two-head-stable `Conv` refuter.**  Two terms whose every reduct keeps DISTINCT heads
are never convertible: the common reduct would carry both heads. -/
theorem Conv.refutedByDistinctStableHeads {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    {leftHead rightHead : Generator}
    (convertibility : Conv leftTerm rightTerm)
    (leftStable : ∀ reduct : RawTerm scope, StepStar leftTerm reduct →
      RawTerm.headGenerator reduct = leftHead)
    (rightStable : ∀ reduct : RawTerm scope, StepStar rightTerm reduct →
      RawTerm.headGenerator reduct = rightHead)
    (headsDiffer : leftHead = rightHead → False) : False := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := convertibility
  exact headsDiffer ((leftStable commonReduct leftChain).symm.trans
    (rightStable commonReduct rightChain))

/-! ## The lanes and their shallow values -/

/-- The LANE codes: the classifier shapes a union eliminator's recursive premise can demand.  These are
exactly the scrutinee/eliminated types of the union's own elimination arms (plus `bool`/`nat` as the
headline corollary targets) — including `list`, whose `listElim` scrutinee premise is union-recursive
since the NATIVE-42 re-shape.  `bridge`/`interval` are absent because the `pathApp` row is outside the
core-Step fragment boundary. -/
inductive IsLaneCode : {scope : Nat} → RawTerm scope → Prop where
  | bool {scope : Nat} : IsLaneCode (boolTypeCell : RawTerm scope)
  | nat {scope : Nat} : IsLaneCode (natTypeCell : RawTerm scope)
  | option {scope : Nat} (elementType : RawTerm scope) : IsLaneCode (optionTypeCell elementType)
  | either {scope : Nat} (leftType rightType : RawTerm scope) :
      IsLaneCode (eitherTypeCell leftType rightType)
  | product {scope : Nat} (firstType secondType : RawTerm scope) :
      IsLaneCode (productTypeCell firstType secondType)
  | identity {scope : Nat} (typeCode leftEndpoint rightEndpoint : RawTerm scope) :
      IsLaneCode (idTypeCell typeCode leftEndpoint rightEndpoint)
  | pi {scope : Nat} (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
      IsLaneCode (piTyCodeCell domainCode codomainCode)
  | list {scope : Nat} (elementType : RawTerm scope) : IsLaneCode (listTypeCell elementType)

/-- SHALLOW lane values: only the head constructor shape is recorded (an iota rule inspects exactly the
scrutinee's head), and the lane parameters are fully decoupled from the value's own components (no
coherence — coherence is the typing derivation's job, not canonicity's). -/
inductive LaneValue : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  | boolTrue {scope : Nat} : LaneValue (boolTypeCell : RawTerm scope) boolTrueCell
  | boolFalse {scope : Nat} : LaneValue (boolTypeCell : RawTerm scope) boolFalseCell
  | natZero {scope : Nat} : LaneValue (natTypeCell : RawTerm scope) natZeroCell
  | natSucc {scope : Nat} (predecessor : RawTerm scope) :
      LaneValue (natTypeCell : RawTerm scope) (natSuccCell predecessor)
  | optionNone {scope : Nat} (elementType : RawTerm scope) :
      LaneValue (optionTypeCell elementType) optionNoneCell
  | optionSome {scope : Nat} (elementType payload : RawTerm scope) :
      LaneValue (optionTypeCell elementType) (optionSomeCell payload)
  | eitherInl {scope : Nat} (leftType rightType payload : RawTerm scope) :
      LaneValue (eitherTypeCell leftType rightType) (eitherInlCell payload)
  | eitherInr {scope : Nat} (leftType rightType payload : RawTerm scope) :
      LaneValue (eitherTypeCell leftType rightType) (eitherInrCell payload)
  | pair {scope : Nat} (firstType secondType firstComponent secondComponent : RawTerm scope) :
      LaneValue (productTypeCell firstType secondType)
        (pairCell firstComponent secondComponent)
  | refl {scope : Nat} (typeCode leftEndpoint rightEndpoint witness : RawTerm scope) :
      LaneValue (idTypeCell typeCode leftEndpoint rightEndpoint) (reflCell witness)
  | lam {scope : Nat} (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
      (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) :
      LaneValue (piTyCodeCell domainCode codomainCode) (lamCell domainAnn body)
  | listNil {scope : Nat} (elementType : RawTerm scope) :
      LaneValue (listTypeCell elementType) listNilCell
  | listCons {scope : Nat} (elementType headValue tailList : RawTerm scope) :
      LaneValue (listTypeCell elementType) (listConsCell headValue tailList)

/-! ## Per-lane value extraction (index discrimination) -/

/-- A bool-lane value is one of the two Booleans. -/
theorem LaneValue.atBool {scope : Nat} {subject : RawTerm scope}
    (laneValue : LaneValue (boolTypeCell : RawTerm scope) subject) :
    subject = boolTrueCell ∨ subject = boolFalseCell := by
  cases laneValue
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A nat-lane value is `natZero` or a `natSucc`. -/
theorem LaneValue.atNat {scope : Nat} {subject : RawTerm scope}
    (laneValue : LaneValue (natTypeCell : RawTerm scope) subject) :
    subject = natZeroCell ∨ ∃ predecessor : RawTerm scope, subject = natSuccCell predecessor := by
  cases laneValue with
  | natZero => exact Or.inl rfl
  | natSucc predecessor => exact Or.inr ⟨predecessor, rfl⟩

/-- An option-lane value is `optionNone` or an `optionSome`. -/
theorem LaneValue.atOption {scope : Nat} {elementType subject : RawTerm scope}
    (laneValue : LaneValue (optionTypeCell elementType) subject) :
    subject = optionNoneCell ∨ ∃ payload : RawTerm scope, subject = optionSomeCell payload := by
  cases laneValue with
  | optionNone _ => exact Or.inl rfl
  | optionSome _ payload => exact Or.inr ⟨payload, rfl⟩

/-- An either-lane value is an `eitherInl` or an `eitherInr`. -/
theorem LaneValue.atEither {scope : Nat} {leftType rightType subject : RawTerm scope}
    (laneValue : LaneValue (eitherTypeCell leftType rightType) subject) :
    (∃ payload : RawTerm scope, subject = eitherInlCell payload) ∨
    (∃ payload : RawTerm scope, subject = eitherInrCell payload) := by
  cases laneValue with
  | eitherInl _ _ payload => exact Or.inl ⟨payload, rfl⟩
  | eitherInr _ _ payload => exact Or.inr ⟨payload, rfl⟩

/-- A product-lane value is a `pair`. -/
theorem LaneValue.atProduct {scope : Nat} {firstType secondType subject : RawTerm scope}
    (laneValue : LaneValue (productTypeCell firstType secondType) subject) :
    ∃ (firstComponent secondComponent : RawTerm scope),
      subject = pairCell firstComponent secondComponent := by
  cases laneValue with
  | pair _ _ firstComponent secondComponent => exact ⟨firstComponent, secondComponent, rfl⟩

/-- An identity-lane value is a `refl`. -/
theorem LaneValue.atIdentity {scope : Nat}
    {typeCode leftEndpoint rightEndpoint subject : RawTerm scope}
    (laneValue : LaneValue (idTypeCell typeCode leftEndpoint rightEndpoint) subject) :
    ∃ witness : RawTerm scope, subject = reflCell witness := by
  cases laneValue with
  | refl _ _ _ witness => exact ⟨witness, rfl⟩

/-- A Pi-lane value is a lambda. -/
theorem LaneValue.atPi {scope : Nat} {domainCode subject : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (laneValue : LaneValue (piTyCodeCell domainCode codomainCode) subject) :
    ∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
      subject = lamCell domainAnn body := by
  cases laneValue with
  | lam _ _ domainAnn body => exact ⟨domainAnn, body, rfl⟩

/-- A list-lane value is a `listNil` or a `listCons`. -/
theorem LaneValue.atList {scope : Nat} {elementType subject : RawTerm scope}
    (laneValue : LaneValue (listTypeCell elementType) subject) :
    subject = listNilCell ∨
    ∃ (headValue tailList : RawTerm scope), subject = listConsCell headValue tailList := by
  cases laneValue with
  | listNil _ => exact Or.inl rfl
  | listCons _ headValue tailList => exact Or.inr ⟨headValue, tailList, rfl⟩

/-! ## The lane-mismatch refuter (one call per cross-lane classifier clash) -/

/-- `unitCode` is a no-step leaf. -/
theorem noStep_unitCodeCell {scope : Nat} {reduct : RawTerm scope}
    (reduction : Step (.mkGen .gen_unitCode () .childNil : RawTerm scope) reduct) : False := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-- `intervalCode` is a no-step leaf. -/
theorem noStep_intervalTypeCell {scope : Nat} {reduct : RawTerm scope}
    (reduction : Step (intervalTypeCell : RawTerm scope) reduct) : False := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-- Every reduct of `unitCode` keeps the `gen_unitCode` head. -/
theorem headReaches_unitCodeCell {scope : Nat} {reduct : RawTerm scope}
    (chain : StepStar (.mkGen .gen_unitCode () .childNil : RawTerm scope) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_unitCode := by
  have reductEq := StepStar.eq_of_noStep (fun _reduct step => noStep_unitCodeCell step) chain
  rw [reductEq]
  rfl

/-- Every reduct of `intervalCode` keeps the `gen_intervalCode` head. -/
theorem headReaches_intervalTypeCell {scope : Nat} {reduct : RawTerm scope}
    (chain : StepStar (intervalTypeCell : RawTerm scope) reduct) :
    RawTerm.headGenerator reduct = Generator.gen_intervalCode := by
  have reductEq := StepStar.eq_of_noStep (fun _reduct step => noStep_intervalTypeCell step) chain
  rw [reductEq]
  rfl

/-- **The one-call cross-lane refuter.**  A classifier whose every reduct keeps a head DISTINCT from all
seven lane heads is never `Conv` a lane code.  Each classifier arm of the master supplies its own
head-stability witness plus seven `Generator.noConfusion` discriminations. -/
theorem IsLaneCode.refuteConvFromStableHead {scope : Nat} {classifier target : RawTerm scope}
    {classifierHead : Generator}
    (laneTarget : IsLaneCode target)
    (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = classifierHead)
    (notBool : classifierHead = .gen_boolCode → False)
    (notNat : classifierHead = .gen_natCode → False)
    (notOption : classifierHead = .gen_optionCode → False)
    (notEither : classifierHead = .gen_eitherCode → False)
    (notProduct : classifierHead = .gen_productCode → False)
    (notIdentity : classifierHead = .gen_idCode → False)
    (notPi : classifierHead = .gen_piTyCode → False)
    (notList : classifierHead = .gen_listCode → False) : False := by
  cases laneTarget with
  | bool =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain) notBool
  | nat =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain) notNat
  | option elementType =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain) notOption
  | either leftType rightType =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain) notEither
  | product firstType secondType =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain) notProduct
  | identity typeCode leftEndpoint rightEndpoint =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain) notIdentity
  | pi domainCode codomainCode =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain) notPi
  | list elementType =>
      exact Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain) notList

/-- A universe code is never `Conv` a lane code (the classifier shape of every former arm). -/
theorem IsLaneCode.notConvFromUniverse {scope : Nat} {target : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (laneTarget : IsLaneCode target)
    (convToTarget : Conv (universeCodeCell levelExpr flag) target) : False :=
  laneTarget.refuteConvFromStableHead convToTarget
    (fun _reduct chain => headReaches_universeCodeCell chain)
    (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
    (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
    (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
    (fun headsEq => Generator.noConfusion headsEq)
    (fun headsEq => Generator.noConfusion headsEq)

/-! ## The seven lane-pinning lemmas (a stable classifier head pins the lane uniquely) -/

/-- A `gen_boolCode`-stable classifier `Conv` a lane code pins the bool lane. -/
theorem IsLaneCode.pinnedByBoolHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_boolCode) :
    target = boolTypeCell := by
  cases laneTarget with
  | bool => rfl
  | nat =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | option elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | either leftType rightType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | product firstType secondType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | identity typeCode leftEndpoint rightEndpoint =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | pi domainCode codomainCode =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | list elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-- A `gen_natCode`-stable classifier `Conv` a lane code pins the nat lane. -/
theorem IsLaneCode.pinnedByNatHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_natCode) :
    target = natTypeCell := by
  cases laneTarget with
  | nat => rfl
  | bool =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | option elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | either leftType rightType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | product firstType secondType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | identity typeCode leftEndpoint rightEndpoint =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | pi domainCode codomainCode =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | list elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-- A `gen_optionCode`-stable classifier `Conv` a lane code pins the option lane. -/
theorem IsLaneCode.pinnedByOptionHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_optionCode) :
    ∃ elementType : RawTerm scope, target = optionTypeCell elementType := by
  cases laneTarget with
  | option elementType => exact ⟨elementType, rfl⟩
  | bool =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | nat =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | either leftType rightType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | product firstType secondType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | identity typeCode leftEndpoint rightEndpoint =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | pi domainCode codomainCode =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | list elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-- A `gen_eitherCode`-stable classifier `Conv` a lane code pins the either lane. -/
theorem IsLaneCode.pinnedByEitherHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_eitherCode) :
    ∃ (leftType rightType : RawTerm scope), target = eitherTypeCell leftType rightType := by
  cases laneTarget with
  | either leftType rightType => exact ⟨leftType, rightType, rfl⟩
  | bool =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | nat =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | option elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | product firstType secondType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | identity typeCode leftEndpoint rightEndpoint =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | pi domainCode codomainCode =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | list elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-- A `gen_productCode`-stable classifier `Conv` a lane code pins the product lane. -/
theorem IsLaneCode.pinnedByProductHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_productCode) :
    ∃ (firstType secondType : RawTerm scope), target = productTypeCell firstType secondType := by
  cases laneTarget with
  | product firstType secondType => exact ⟨firstType, secondType, rfl⟩
  | bool =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | nat =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | option elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | either leftType rightType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | identity typeCode leftEndpoint rightEndpoint =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | pi domainCode codomainCode =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | list elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-- A `gen_idCode`-stable classifier `Conv` a lane code pins the identity lane. -/
theorem IsLaneCode.pinnedByIdentityHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_idCode) :
    ∃ (typeCode leftEndpoint rightEndpoint : RawTerm scope),
      target = idTypeCell typeCode leftEndpoint rightEndpoint := by
  cases laneTarget with
  | identity typeCode leftEndpoint rightEndpoint => exact ⟨typeCode, leftEndpoint, rightEndpoint, rfl⟩
  | bool =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | nat =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | option elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | either leftType rightType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | product firstType secondType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | pi domainCode codomainCode =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | list elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-- A `gen_piTyCode`-stable classifier `Conv` a lane code pins the Pi lane. -/
theorem IsLaneCode.pinnedByPiHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_piTyCode) :
    ∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
      target = piTyCodeCell domainCode codomainCode := by
  cases laneTarget with
  | pi domainCode codomainCode => exact ⟨domainCode, codomainCode, rfl⟩
  | list elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_listTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | bool =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | nat =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | option elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | either leftType rightType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | product firstType secondType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | identity typeCode leftEndpoint rightEndpoint =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-! ## ★ The MASTER: closed-normal lane canonical forms over the ONE union judgment -/

/-- A `gen_listCode`-stable classifier `Conv` a lane code pins the list lane. -/
theorem IsLaneCode.pinnedByListHead {scope : Nat} {classifier target : RawTerm scope}
    (laneTarget : IsLaneCode target) (convToTarget : Conv classifier target)
    (classifierStable : ∀ reduct : RawTerm scope, StepStar classifier reduct →
      RawTerm.headGenerator reduct = Generator.gen_listCode) :
    ∃ elementType : RawTerm scope, target = listTypeCell elementType := by
  cases laneTarget with
  | list elementType => exact ⟨elementType, rfl⟩
  | bool =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_boolTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | nat =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_natTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | option elementType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_optionTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | either leftType rightType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_eitherTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | product firstType secondType =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_productTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | identity typeCode leftEndpoint rightEndpoint =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_idTypeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim
  | pi domainCode codomainCode =>
      exact (Conv.refutedByDistinctStableHeads convToTarget classifierStable
        (fun _reduct chain => headReaches_piTyCodeCell chain)
        (fun headsEq => Generator.noConfusion headsEq)).elim

/-- Table peel for the term-indexed former rows (`gen_bridgeCode` / `gen_idCode`): every hit carries
the shared carrier-level universe output, so the former arm's classifier is a universe code. -/
theorem termIndexedFormerDescOf_outputIsUniverse {generator : Generator}
    {rule : TermIndexedFormerDesc}
    (tableHit : termIndexedFormerDescOf generator = some rule) :
    rule = { outputType := termIndexedCarrierOutput } := by
  unfold termIndexedFormerDescOf at tableHit
  by_cases isBridge : generator = .gen_bridgeCode
  · rw [if_pos isBridge] at tableHit
    exact (Option.some.inj tableHit).symm
  · rw [if_neg isBridge] at tableHit
    by_cases isId : generator = .gen_idCode
    · rw [if_pos isId] at tableHit
      exact (Option.some.inj tableHit).symm
    · rw [if_neg isId] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-- Table peel for the recursive-eliminator rows: any hit is the `gen_natElim` row or the
`gen_natRec` row (mirrors `nativePathInductionRuleOf_cases`). -/
theorem nativeRecursiveElimRuleOf_cases {generator : Generator}
    {rule : NativeRecursiveElimRule}
    (tableHit : nativeRecursiveElimRuleOf generator = some rule) :
    (generator = .gen_natElim ∧ rule = natElimNativeRecursiveRule) ∨
      (generator = .gen_natRec ∧ rule = natRecNativeRecursiveRule) := by
  unfold nativeRecursiveElimRuleOf at tableHit
  by_cases isNatElim : generator = .gen_natElim
  · rw [if_pos isNatElim] at tableHit
    exact Or.inl ⟨isNatElim, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isNatElim] at tableHit
    by_cases isNatRec : generator = .gen_natRec
    · rw [if_pos isNatRec] at tableHit
      exact Or.inr ⟨isNatRec, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isNatRec] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-- **★ NATIVE-38: canonicity collapses to the single union judgment.**  A closed normal
`HasTypeUnion`-typed term on the core beta/iota fragment (no `pathApp` / `pathLam` occurrence —
the honest pre-WAVE-2 boundary, see the file header) whose classifier converts to a lane code is a
shallow VALUE of that lane.  One derivation induction over all 5 arms; the unified `elim` arm consumes the
induction hypothesis at its scrutinee's lane per eliminator row and refutes normality (the iota redex
fires), the unified `intro` arm emits `LaneValue` constructors per introducer row after the lane-pinning
lemmas, the `formationRule` arm dies by universe rigidity, and the `conv` arm composes `Conv`. -/
theorem HasTypeUnion.closedNormalLaneCanonicalForms {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier) :
    (Fin scope → False) →
    RawTerm.isStepNormalFormBool subject = true →
    RawTerm.containsGeneratorBool .gen_pathApp subject = false →
    RawTerm.containsGeneratorBool .gen_pathLam subject = false →
    ∀ {target : RawTerm scope}, IsLaneCode target → Conv classifier target →
    LaneValue target subject := by
  induction typed with
  | var _context index =>
      intro closed _normal _pathAppFree _pathLamFree _target _laneTarget _convToTarget
      exact (closed index).elim
  | universeFormation _context _levelExpr _flag =>
      intro _closed _normal _pathAppFree _pathLamFree _target laneTarget convToTarget
      exact (laneTarget.notConvFromUniverse convToTarget).elim
  | ofGrown hostTyped =>
      intro closed normal _pathAppFree _pathLamFree target laneTarget convToTarget
      rcases HasTypeDescPi.closedNormalSubjectHead hostTyped normal closed with
          headLam | headPi | headSigma | headUniverse | headList | headOption | headUnit
      · obtain ⟨domainAnn, body, lamEq⟩ := eq_lamCell_of_headGenerator headLam
        rw [lamEq] at hostTyped
        obtain ⟨codomainInner, _domainLevel, _codomainLevel, _flag,
            convToPiCode, _domainTyped, _codomainTyped, _bodyTyped⟩ :=
          HasTypeDescPi.invertLam hostTyped
        obtain ⟨domainCode, codomainCode, targetEq⟩ :=
          laneTarget.pinnedByPiHead (convToPiCode.sym.trans convToTarget)
            (fun _reduct chain => headReaches_piTyCodeCell chain)
        rw [targetEq, lamEq]
        exact LaneValue.lam domainCode codomainCode domainAnn body
      · obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
        rw [piEq] at hostTyped
        obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped,
            convToUniverseCode⟩ := HasTypeDescPi.invertPiTyCode hostTyped
        exact (laneTarget.notConvFromUniverse (convToUniverseCode.sym.trans convToTarget)).elim
      · obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
        rw [sigmaEq] at hostTyped
        obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped,
            convToUniverseCode⟩ := HasTypeDescPi.invertSigmaTyCode hostTyped
        exact (laneTarget.notConvFromUniverse (convToUniverseCode.sym.trans convToTarget)).elim
      · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
        rw [universeEq] at hostTyped
        exact (laneTarget.notConvFromUniverse
          ((HasTypeDescPi.inversionUniverseCode hostTyped).sym.trans convToTarget)).elim
      · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
        rw [listEq] at hostTyped
        obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
          HasTypeDescPi.formerClassifierConvUniverseGeneric hostTyped typingRuleDescOf_listCode rfl
        exact (laneTarget.notConvFromUniverse (convToUniverseCode.sym.trans convToTarget)).elim
      · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
        rw [optionEq] at hostTyped
        obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
          HasTypeDescPi.formerClassifierConvUniverseGeneric hostTyped typingRuleDescOf_optionCode rfl
        exact (laneTarget.notConvFromUniverse (convToUniverseCode.sym.trans convToTarget)).elim
      · have unitEq := eq_unitCodeCell_of_headGenerator headUnit
        rw [unitEq] at hostTyped
        obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
          HasTypeDescPi.formerClassifierConvUniverseGeneric hostTyped typingRuleDescOf_unitCode rfl
        exact (laneTarget.notConvFromUniverse (convToUniverseCode.sym.trans convToTarget)).elim
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold ihPremises =>
      intro _closed _normal _pathAppFree _pathLamFree target laneTarget convToTarget
      -- A `formationRule` subject is a TYPE-FORMER `.mkGen generator payload children` whose classifier
      -- IS the family's universe / type-code output (`rule.outputType`), so it clashes with any data-type
      -- lane code on its head: a REFUTATION case.  The proof reads only `convToTarget` + `isFormationRule`
      -- and dies through `notConvFromUniverse`; the union obligations (`premisesHold`) and their induction
      -- hypotheses (`ihPremises`) carry no information the head-clash needs, so they go unconsumed exactly
      -- as the TYTAB-2 arm-swap promoted them (mirrors the unused premise/IH discipline of `intro`/`elim`).
      cases rule with
      | baseType baseRule =>
          dsimp only [FormationRule.outputType] at convToTarget
          rw [baseTypeRuleTableOutputIsType0 (formationRuleOf_baseType_inv isFormationRule)]
            at convToTarget
          exact (laneTarget.notConvFromUniverse convToTarget).elim
      | flat flatRule =>
          dsimp only [FormationRule.outputType] at convToTarget
          rw [flatTypingRuleDescOf_outputIsUniverseFormer (formationRuleOf_flat_inv isFormationRule)]
            at convToTarget
          dsimp only [universeFormerOutput] at convToTarget
          exact (laneTarget.notConvFromUniverse convToTarget).elim
      | cumulative cumulativeRule =>
          -- TYTAB-2 wave U2: a cumulative type-former's classifier IS the family's universe output
          -- (`cumulativeRule.outputType`), a universe code for every row shape
          -- (`typingRuleDescOf_output_isUniverseCode`).  It clashes with any data-type lane code: rewrite the
          -- output to its universe code and die through `notConvFromUniverse`, exactly as the flat / base /
          -- term-indexed formation arms do.
          have isCumulative : typingRuleDescOf generator = some cumulativeRule :=
            formationRuleOf_cumulative_inv isFormationRule
          dsimp only [FormationRule.outputType] at convToTarget
          obtain ⟨_outputLevel, _outputFlag, outputEq⟩ :=
            typingRuleDescOf_output_isUniverseCode isCumulative _ levels flag
          rw [outputEq] at convToTarget
          exact (laneTarget.notConvFromUniverse convToTarget).elim
      | termIndexed termRule =>
          dsimp only [FormationRule.outputType] at convToTarget
          rw [termIndexedFormerDescOf_outputIsUniverse (formationRuleOf_termIndexed_inv isFormationRule)]
            at convToTarget
          exact (laneTarget.notConvFromUniverse convToTarget).elim
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      intro _closed _normal _pathAppFree pathLamFree target laneTarget convToTarget
      -- The unified introducer arm: `rcases` the table hit into the seventeen per-generator rows, then
      -- reconstruct each old per-generator outcome.  Boolean / nat / option / either / product / id / pi /
      -- list constructors are genuine canonical VALUES at their lane (surfaced via the lane-pinning
      -- lemmas); the unit / interval-endpoint constructors are not lane heads, so their classifier cannot
      -- be `Conv` a lane code (`refuteConvFromStableHead`); `pathLam` dies on the
      -- `gen_pathLam`-containment-freedom hypothesis (its endpoint-beta rule is outside core Step).
      rcases introRuleOf_cases isIntro with
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩
      · -- **boolTrue** — a bool-lane value.
        subst generatorEq; subst ruleEq
        cases args; cases params
        have targetEq := laneTarget.pinnedByBoolHead convToTarget
          (fun _reduct chain => headReaches_boolTypeCell chain)
        rw [targetEq]
        exact LaneValue.boolTrue
      · -- **boolFalse** — a bool-lane value.
        subst generatorEq; subst ruleEq
        cases args; cases params
        have targetEq := laneTarget.pinnedByBoolHead convToTarget
          (fun _reduct chain => headReaches_boolTypeCell chain)
        rw [targetEq]
        exact LaneValue.boolFalse
      · -- **unit** — `unitCode` is not a lane head, so its classifier is never `Conv` a lane code.
        subst generatorEq; subst ruleEq
        cases args; cases params
        exact (laneTarget.refuteConvFromStableHead convToTarget
          (fun _reduct chain => headReaches_unitCodeCell chain)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- **interval0** — `intervalCode` is not a lane head.
        subst generatorEq; subst ruleEq
        cases args; cases params
        exact (laneTarget.refuteConvFromStableHead convToTarget
          (fun _reduct chain => headReaches_intervalTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- **interval1** — `intervalCode` is not a lane head.
        subst generatorEq; subst ruleEq
        cases args; cases params
        exact (laneTarget.refuteConvFromStableHead convToTarget
          (fun _reduct chain => headReaches_intervalTypeCell chain)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq) (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq)
          (fun headsEq => Generator.noConfusion headsEq)).elim
      · -- **natZero** — a nat-lane value.
        subst generatorEq; subst ruleEq
        cases args; cases params
        have targetEq := laneTarget.pinnedByNatHead convToTarget
          (fun _reduct chain => headReaches_natTypeCell chain)
        rw [targetEq]
        exact LaneValue.natZero
      · -- **lam** — the Pi-lane lambda value (the graded-binder λ row).
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons domainAnn (.childCons body .childNil), .childCons _codomainCode .childNil =>
          obtain ⟨domainCode, codomainCode, targetEq⟩ :=
            laneTarget.pinnedByPiHead convToTarget
              (fun _reduct chain => headReaches_piTyCodeCell chain)
          rw [targetEq]
          exact LaneValue.lam domainCode codomainCode domainAnn body
      · -- **pathLam** — the subject heads `gen_pathLam`, contradicting the containment-freedom hypothesis.
        subst generatorEq; subst ruleEq
        match args with
        | .childCons body .childNil =>
          exact Bool.noConfusion (pathLamFree.symm.trans
            (RawTerm.containsGeneratorBool_headHit .gen_pathLam () (.childCons body .childNil)))
      · -- **natSucc** — a nat-lane value (recursive data constructor).
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons predecessor .childNil, .childNil =>
          have targetEq := laneTarget.pinnedByNatHead convToTarget
            (fun _reduct chain => headReaches_natTypeCell chain)
          rw [targetEq]
          exact LaneValue.natSucc predecessor
      · -- **listCons** — a list-lane value (recursive data constructor).
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons headValue (.childCons tailList .childNil), .childCons _elementType .childNil =>
          obtain ⟨targetElement, targetEq⟩ := laneTarget.pinnedByListHead convToTarget
            (fun _reduct chain => headReaches_listTypeCell chain)
          rw [targetEq]
          exact LaneValue.listCons targetElement headValue tailList
      · -- **optionSome** — an option-lane value (grown data constructor).
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons payload .childNil, .childCons _typeParam0 .childNil =>
          obtain ⟨targetElement, targetEq⟩ := laneTarget.pinnedByOptionHead convToTarget
            (fun _reduct chain => headReaches_optionTypeCell chain)
          rw [targetEq]
          exact LaneValue.optionSome targetElement payload
      · -- **optionNone** — an option-lane value.
        subst generatorEq; subst ruleEq
        match args, params with
        | .childNil, .childCons _typeParam0 .childNil =>
          obtain ⟨targetElement, targetEq⟩ := laneTarget.pinnedByOptionHead convToTarget
            (fun _reduct chain => headReaches_optionTypeCell chain)
          rw [targetEq]
          exact LaneValue.optionNone targetElement
      · -- **listNil** — a list-lane value.
        subst generatorEq; subst ruleEq
        match args, params with
        | .childNil, .childCons _typeParam0 .childNil =>
          obtain ⟨targetElement, targetEq⟩ := laneTarget.pinnedByListHead convToTarget
            (fun _reduct chain => headReaches_listTypeCell chain)
          rw [targetEq]
          exact LaneValue.listNil targetElement
      · -- **eitherInl** — an either-lane value (grown data constructor).
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons payload .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          obtain ⟨targetLeft, targetRight, targetEq⟩ := laneTarget.pinnedByEitherHead convToTarget
            (fun _reduct chain => headReaches_eitherTypeCell chain)
          rw [targetEq]
          exact LaneValue.eitherInl targetLeft targetRight payload
      · -- **eitherInr** — an either-lane value.
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons payload .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          obtain ⟨targetLeft, targetRight, targetEq⟩ := laneTarget.pinnedByEitherHead convToTarget
            (fun _reduct chain => headReaches_eitherTypeCell chain)
          rw [targetEq]
          exact LaneValue.eitherInr targetLeft targetRight payload
      · -- **pair** — a product-lane value (grown data constructor).
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons firstComponent (.childCons secondComponent .childNil),
          .childCons _typeParam0 (.childCons _typeParam1 .childNil) =>
          obtain ⟨targetFirst, targetSecond, targetEq⟩ := laneTarget.pinnedByProductHead convToTarget
            (fun _reduct chain => headReaches_productTypeCell chain)
          rw [targetEq]
          exact LaneValue.pair targetFirst targetSecond firstComponent secondComponent
      · -- **refl** — an identity-lane value (grown data constructor).
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons witness .childNil, .childCons _typeParam0 .childNil =>
          obtain ⟨targetType, targetLeft, targetRight, targetEq⟩ :=
            laneTarget.pinnedByIdentityHead convToTarget
              (fun _reduct chain => headReaches_idTypeCell chain)
          rw [targetEq]
          exact LaneValue.refl targetType targetLeft targetRight witness
  | elim context generator rule args params level0 level1 flag isElim premisesHold ihPremises =>
      intro closed normal pathAppFree pathLamFree target laneTarget convToTarget
      -- The unified eliminator arm: `rcases` the table hit into the eleven per-generator rows, then
      -- reconstruct each old per-generator refutation.  Every eliminator cell with a constructor-headed
      -- scrutinee is an iota redex (NOT step-normal), so the canonical-forms goal is discharged by
      -- feeding the scrutinee-obligation's induction hypothesis (`ihPremises` at the scrutinee's lane)
      -- through the lane value extractor and refuting `normal`.  The `pathApp` row dies on the
      -- `gen_pathApp`-containment-freedom hypothesis instead (its computation rule is outside core Step).
      rcases elimRuleOf_cases isElim with
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ |
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩
      · -- **app** — the eliminated function reaches the Pi lane, so it is a lambda; a redex follows.
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
            ihPremises _ (.head _) closed functionNormal functionAppFree functionLamFree
              (IsLaneCode.pi domainCode codomainCode) (Conv.refl _)
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
      · -- **natElim** — the scrutinee reaches the nat lane (zero or succ); either way a redex.
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch
            (.childCons scrutinee .childNil))), .childCons resultType .childNil =>
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
            ihPremises _ (.head _) closed scrutineeNormal scrutineeAppFree scrutineeLamFree
              IsLaneCode.nat (Conv.refl _)
          rcases scrutineeValue.atNat with scrutineeEq | ⟨predecessor, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **natRec** — the dependent recursor twin: same scrutinee-redex refutation.
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch
            (.childCons scrutinee .childNil))), .childCons resultType .childNil =>
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
            ihPremises _ (.head _) closed scrutineeNormal scrutineeAppFree scrutineeLamFree
              IsLaneCode.nat (Conv.refl _)
          rcases scrutineeValue.atNat with scrutineeEq | ⟨predecessor, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **boolElim** — scrutinee reaches the bool lane; the iota redex fires on either boolean.
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons scrutinee (.childCons thenBranch
            (.childCons elseBranch .childNil))),
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
          have scrutineeValue : LaneValue (boolTypeCell : RawTerm _) scrutinee :=
            ihPremises _ (.head _) closed scrutineeNormal scrutineeAppFree scrutineeLamFree
              IsLaneCode.bool (Conv.refl _)
          rcases scrutineeValue.atBool with scrutineeEq | scrutineeEq
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **optionMatch** — scrutinee reaches the option lane; the iota redex fires on none / some.
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
            ihPremises _ (.head _) closed scrutineeNormal scrutineeAppFree scrutineeLamFree
              (IsLaneCode.option typeParamA) (Conv.refl _)
          rcases scrutineeValue.atOption with scrutineeEq | ⟨payload, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **eitherMatch** — scrutinee reaches the either lane; the iota redex fires on inl / inr.
        subst generatorEq; subst ruleEq
        match args, params with
        | .childCons motive (.childCons leftBranch (.childCons rightBranch
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
          have scrutineeValue : LaneValue (eitherTypeCell typeParamA typeParamB) scrutinee :=
            ihPremises _ (.head _) closed scrutineeNormal scrutineeAppFree scrutineeLamFree
              (IsLaneCode.either typeParamA typeParamB) (Conv.refl _)
          rcases scrutineeValue.atEither with ⟨payload, scrutineeEq⟩ | ⟨payload, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
      · -- **idJ** — the witness reaches the identity lane (a `refl`); the path-induction redex fires.
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
            ihPremises _ (.head _) closed witnessNormal witnessAppFree witnessLamFree
              (IsLaneCode.identity typeCode endpoint endpoint) (Conv.refl _)
          obtain ⟨witnessPayload, witnessEq⟩ := witnessValue.atIdentity
          rw [witnessEq] at normal
          cases normal
      · -- **fst** — the pair term reaches the product lane; the first-projection redex fires.
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
            ihPremises _ (.head _) closed pairNormal pairAppFree pairLamFree
              (IsLaneCode.product firstType secondType) (Conv.refl _)
          obtain ⟨firstComponent, secondComponent, pairEq⟩ := pairValue.atProduct
          rw [pairEq] at normal
          cases normal
      · -- **snd** — the pair term reaches the product lane; the second-projection redex fires.
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
            ihPremises _ (.head _) closed pairNormal pairAppFree pairLamFree
              (IsLaneCode.product firstType secondType) (Conv.refl _)
          obtain ⟨firstComponent, secondComponent, pairEq⟩ := pairValue.atProduct
          rw [pairEq] at normal
          cases normal
      · -- **listElim** — scrutinee reaches the list lane (nil or cons); the list redex fires.
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
            ihPremises _ (.head _) closed scrutineeNormal scrutineeAppFree scrutineeLamFree
              (IsLaneCode.list elementType) (Conv.refl _)
          rcases scrutineeValue.atList with scrutineeEq | ⟨headValue, tailList, scrutineeEq⟩
          · rw [scrutineeEq] at normal
            cases normal
          · rw [scrutineeEq] at normal
            cases normal
  | conv levelExpr flag typed converts reclassifierTyped ihTyped ihReclassifier =>
      intro closed normal pathAppFree pathLamFree target laneTarget convToTarget
      exact ihTyped closed normal pathAppFree pathLamFree laneTarget
        (converts.trans convToTarget)

/-! ## The headline per-classifier corollaries -/

/-- **★ Closed-normal BOOL canonicity over the single union judgment** (core beta/iota fragment): a
closed normal `HasTypeUnion`-typed term at `boolCode` with no bridge-fragment occurrence is
`boolTrue` or `boolFalse`. -/
theorem HasTypeUnion.closedNormalBoolCanonicalForms {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject boolTypeCell)
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    subject = boolTrueCell ∨ subject = boolFalseCell :=
  LaneValue.atBool
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree IsLaneCode.bool (Conv.refl _))

/-- **★ Closed-normal NAT canonicity over the single union judgment** (core beta/iota fragment): a
closed normal union-typed term at `natCode` with no bridge-fragment occurrence is `natZero` or a
`natSucc`. -/
theorem HasTypeUnion.closedNormalNatCanonicalForms {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject natTypeCell)
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    subject = natZeroCell ∨ ∃ predecessor : RawTerm 0, subject = natSuccCell predecessor :=
  LaneValue.atNat
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree IsLaneCode.nat (Conv.refl _))

/-- **★ Closed-normal OPTION canonicity over the single union judgment** (core beta/iota fragment): a
closed normal union-typed term at `option(A)` with no bridge-fragment occurrence is `optionNone` or an
`optionSome` — the union restatement of the zoo-level `closedNormalOptionCanonicalForms`, freeing the
canonicity assembly from `HasTypeDescOptionIntro`. -/
theorem HasTypeUnion.closedNormalOptionCanonicalForms {profile : PolyProfile}
    {subject elementType : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (optionTypeCell elementType))
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    subject = optionNoneCell ∨ ∃ payload : RawTerm 0, subject = optionSomeCell payload :=
  LaneValue.atOption
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree (IsLaneCode.option elementType) (Conv.refl _))

/-- **★ Closed-normal EITHER canonicity over the single union judgment** (core beta/iota fragment): a
closed normal union-typed term at `either(A, B)` with no bridge-fragment occurrence is an `eitherInl`
or an `eitherInr`. -/
theorem HasTypeUnion.closedNormalEitherCanonicalForms {profile : PolyProfile}
    {subject leftType rightType : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (eitherTypeCell leftType rightType))
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    (∃ payload : RawTerm 0, subject = eitherInlCell payload) ∨
    (∃ payload : RawTerm 0, subject = eitherInrCell payload) :=
  LaneValue.atEither
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree (IsLaneCode.either leftType rightType) (Conv.refl _))

/-- **★ Closed-normal PRODUCT canonicity over the single union judgment** (core beta/iota fragment): a
closed normal union-typed term at `product(A, B)` with no bridge-fragment occurrence is a `pair`. -/
theorem HasTypeUnion.closedNormalProductCanonicalForms {profile : PolyProfile}
    {subject firstType secondType : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (productTypeCell firstType secondType))
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    ∃ (firstComponent secondComponent : RawTerm 0),
      subject = pairCell firstComponent secondComponent :=
  LaneValue.atProduct
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree (IsLaneCode.product firstType secondType) (Conv.refl _))

/-- **★ Closed-normal IDENTITY canonicity over the single union judgment** (core beta/iota fragment): a
closed normal union-typed term at `Id(T, a, b)` with no bridge-fragment occurrence is a `refl`. -/
theorem HasTypeUnion.closedNormalIdentityCanonicalForms {profile : PolyProfile}
    {subject typeCode leftEndpoint rightEndpoint : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (idTypeCell typeCode leftEndpoint rightEndpoint))
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    ∃ witness : RawTerm 0, subject = reflCell witness :=
  LaneValue.atIdentity
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree (IsLaneCode.identity typeCode leftEndpoint rightEndpoint)
      (Conv.refl _))

/-- **★ Closed-normal PI canonicity over the single union judgment** (core beta/iota fragment): a
closed normal union-typed term at `Pi(A, B)` with no bridge-fragment occurrence is a lambda. -/
theorem HasTypeUnion.closedNormalPiCanonicalForms {profile : PolyProfile}
    {subject domainCode : RawTerm 0} {codomainCode : RawTerm 1}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (piTyCodeCell domainCode codomainCode))
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    ∃ (domainAnn : RawTerm 0) (body : RawTerm 1), subject = lamCell domainAnn body :=
  LaneValue.atPi
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree (IsLaneCode.pi domainCode codomainCode) (Conv.refl _))

/-- **★ Closed-normal LIST canonicity over the single union judgment** (core beta/iota fragment): a
closed normal union-typed term at `list(A)` with no bridge-fragment occurrence is `listNil` or a
`listCons` — the lane the master was missing; the zoo-level `ListCanonicalForms` restated at the
union. -/
theorem HasTypeUnion.closedNormalListCanonicalForms {profile : PolyProfile}
    {subject elementType : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject (listTypeCell elementType))
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    subject = listNilCell ∨
    ∃ (headValue tailList : RawTerm 0), subject = listConsCell headValue tailList :=
  LaneValue.atList
    (typed.closedNormalLaneCanonicalForms (fun emptyIndex => emptyIndex.elim0) normal
      pathAppFree pathLamFree (IsLaneCode.list elementType) (Conv.refl _))

end FX1Poly.Typed
