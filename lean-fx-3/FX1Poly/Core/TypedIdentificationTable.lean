import FX1Poly.Core.EtaRuleTable

/-! # TypedIdentificationTable — ETA-T6 increment 3: type-directed
identifications as data (unit eta, ghost eta)

The eta-rule table carries the SYNTACTIC tier: rows that contract an
observation structure.  Unit eta and ghost eta have no observation
structure — no syntactic pattern exists at all — so they live one
layer up, as JUDGMENTAL-EQUALITY extensions (the
`BetaEtaConvGapStatement` census calls this "judgmental-equality
EXTENSION territory, not decision-procedure territory").  This module
makes that tier rules-as-data too:

  * `TypedIdentificationCondition` — the firing condition as a value:
    both sides typed at a given type-code head (unit eta), or both
    sides usage-grade ZERO (ghost eta);
  * `typedIdentificationTable` — the canonical two rows;
  * `ConvOverIdentifications` — the conversion extension: ONE
    `identify` arm interprets any row's condition, over an ABSTRACT
    `IdentificationSemantics` (the typing and grading readers the
    typed engine supplies when it lands) and an abstract base
    conversion.

**The ghost row is the FX-novel content**: usage-grade-0 definitional
irrelevance.  Two ERASED terms of the same type are definitionally
interchangeable — definitional proof irrelevance keyed by the GRADE
dimension rather than by a strict-proposition universe.  Spec
witnesses (`pre`/`post`/`decreases` payloads) stop blocking
conversion.  The grading reader is abstract here because the
`HasGradeOver` stack (dim-2 arc) currently grades the `Modal/`
mini-calculus, not `RawTerm` — discharging `hasUsageGradeZero` over
`RawTerm` typing is that arc's handoff, recorded as the explicit
semantic obligation.

Honesty: the extension carries explicit `symm`/`trans` constructors —
identifications are not reductions, so the join-based recipe (`Conv =
Join` of stars) does not apply; conservativity over the base is
therefore CONDITIONAL on the base being an equivalence on the
fragment considered (raw `BetaEtaConv` has transitivity only through
well-typed middles, and that is the known gap, not a defect here).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedIdentificationTable.lean`. -/

namespace FX1Poly.Core

/-! ## The condition and rule schema -/

/-- A type-directed identification's firing condition, as data. -/
inductive TypedIdentificationCondition : Type where
  /-- Both sides are typed at a type cell with the given TYPE-CODE
  head: any two such terms are identified (unit eta at
  `gen_unitCode`; future singleton/interval kin land as values). -/
  | termsTypedAtCode (typeHead : Generator)
  /-- Both sides carry usage grade ZERO: erased terms are
  definitionally irrelevant (ghost eta — the grade-keyed proof
  irrelevance). -/
  | termsBothGradeZero

/-- One identification rule: just its condition.  (No intro head, no
observations — identifications are headless by nature, which is
exactly why they are not `EtaRuleDesc` rows.) -/
structure TypedIdentificationRule : Type where
  condition : TypedIdentificationCondition

/-! ## The canonical rows -/

/-- Unit eta as an identification: any two unit-typed terms are
definitionally the same (the judgmental CONTENT of the flagged
`unitEtaRow`, which documents only the raw-tier absence). -/
def unitIdentificationRule : TypedIdentificationRule :=
  { condition := .termsTypedAtCode .gen_unitCode }

/-- ★ Ghost eta as an identification: usage-grade-0 terms are
definitionally interchangeable — the FX-novel grade-keyed
definitional irrelevance. -/
def ghostIdentificationRule : TypedIdentificationRule :=
  { condition := .termsBothGradeZero }

/-- The canonical identification table. -/
def typedIdentificationTable : List TypedIdentificationRule :=
  [unitIdentificationRule, ghostIdentificationRule]

theorem unitIdentificationRule_memTable :
    unitIdentificationRule ∈ typedIdentificationTable := .head _

theorem ghostIdentificationRule_memTable :
    ghostIdentificationRule ∈ typedIdentificationTable :=
  .tail _ (.head _)

/-- Stale-count guard: 2 identification rows. -/
theorem typedIdentificationTable_length :
    typedIdentificationTable.length = 2 := rfl

/-! ## The abstract semantics -/

/-- The semantic readers the identification layer consumes, kept
ABSTRACT so the judgment couples to no in-flux typing engine: the
typing reader (is this term typed at a type cell with this code
head?) and the grading reader (is this term usage-grade zero?).  The
typed engine instantiates `isTypedAtCodeHead`; the dim-2 grading arc
instantiates `hasUsageGradeZero` over `RawTerm`. -/
structure IdentificationSemantics (scope : Nat) : Type 1 where
  isTypedAtCodeHead : Generator → RawTerm scope → Prop
  hasUsageGradeZero : RawTerm scope → Prop

/-- A rule's condition, interpreted against the semantics — the ONE
reading every judgment arm uses (rules-as-data at the judgmental
layer). -/
def TypedIdentificationRule.ConditionHolds
    (rule : TypedIdentificationRule) {scope : Nat}
    (semantics : IdentificationSemantics scope)
    (source target : RawTerm scope) : Prop :=
  match rule.condition with
  | .termsTypedAtCode typeHead =>
      semantics.isTypedAtCodeHead typeHead source
        ∧ semantics.isTypedAtCodeHead typeHead target
  | .termsBothGradeZero =>
      semantics.hasUsageGradeZero source
        ∧ semantics.hasUsageGradeZero target

/-- Conditions are symmetric in the two sides by shape. -/
theorem TypedIdentificationRule.ConditionHolds.symm
    {rule : TypedIdentificationRule} {scope : Nat}
    {semantics : IdentificationSemantics scope}
    {source target : RawTerm scope}
    (conditionHolds : rule.ConditionHolds semantics source target) :
    rule.ConditionHolds semantics target source := by
  dsimp only [TypedIdentificationRule.ConditionHolds] at conditionHolds ⊢
  match conditionEq : rule.condition with
  | .termsTypedAtCode typeHead =>
      rw [conditionEq] at conditionHolds
      exact ⟨conditionHolds.right, conditionHolds.left⟩
  | .termsBothGradeZero =>
      rw [conditionEq] at conditionHolds
      exact ⟨conditionHolds.right, conditionHolds.left⟩

/-! ## The conversion extension -/

/-- ★ The judgmental-equality extension: the base conversion, plus ONE
identification arm interpreting any table row's condition, closed
under symmetry and transitivity (identifications are not reductions —
no join recipe applies). -/
inductive ConvOverIdentifications
    (idTable : List TypedIdentificationRule) {scope : Nat}
    (semantics : IdentificationSemantics scope)
    (baseConv : RawTerm scope → RawTerm scope → Prop) :
    RawTerm scope → RawTerm scope → Prop where
  | base {source target : RawTerm scope}
      (related : baseConv source target) :
      ConvOverIdentifications idTable semantics baseConv source target
  | identify {rule : TypedIdentificationRule} (isRow : rule ∈ idTable)
      {source target : RawTerm scope}
      (conditionHolds : rule.ConditionHolds semantics source target) :
      ConvOverIdentifications idTable semantics baseConv source target
  | symm {source target : RawTerm scope}
      (related :
        ConvOverIdentifications idTable semantics baseConv source
          target) :
      ConvOverIdentifications idTable semantics baseConv target source
  | trans {source middleTerm target : RawTerm scope}
      (left :
        ConvOverIdentifications idTable semantics baseConv source
          middleTerm)
      (right :
        ConvOverIdentifications idTable semantics baseConv middleTerm
          target) :
      ConvOverIdentifications idTable semantics baseConv source target

/-! ## Basic metatheory -/

/-- Reflexivity transfers from the base. -/
theorem ConvOverIdentifications.refl
    {idTable : List TypedIdentificationRule} {scope : Nat}
    {semantics : IdentificationSemantics scope}
    {baseConv : RawTerm scope → RawTerm scope → Prop}
    (baseIsReflexive : ∀ term, baseConv term term)
    (term : RawTerm scope) :
    ConvOverIdentifications idTable semantics baseConv term term :=
  .base (baseIsReflexive term)

/-- Monotone in the table: a judgment over a narrower table holds over
any wider table. -/
theorem ConvOverIdentifications.monotone
    {idTable widerTable : List TypedIdentificationRule}
    (isWider : ∀ {rule : TypedIdentificationRule}, rule ∈ idTable →
      rule ∈ widerTable)
    {scope : Nat} {semantics : IdentificationSemantics scope}
    {baseConv : RawTerm scope → RawTerm scope → Prop}
    {source target : RawTerm scope}
    (related :
      ConvOverIdentifications idTable semantics baseConv source
        target) :
    ConvOverIdentifications widerTable semantics baseConv source
      target := by
  induction related with
  | base related => exact .base related
  | identify isRow conditionHolds =>
      exact .identify (isWider isRow) conditionHolds
  | symm _related ih => exact .symm ih
  | trans _left _right leftIh rightIh => exact .trans leftIh rightIh

/-- ★ Empty-table conservativity: over a base that is already an
equivalence, the extension with NO identification rows is exactly the
base.  (The conditionality is honest: raw `BetaEtaConv` is transitive
only through well-typed middles, so the unconditional form is
unprovable — the known typed-fragment gap, not a defect of the
extension.) -/
theorem ConvOverIdentifications.emptyTable_iff
    {scope : Nat} {semantics : IdentificationSemantics scope}
    {baseConv : RawTerm scope → RawTerm scope → Prop}
    (baseIsSymmetric : ∀ {source target : RawTerm scope},
      baseConv source target → baseConv target source)
    (baseIsTransitive : ∀ {source middleTerm target : RawTerm scope},
      baseConv source middleTerm → baseConv middleTerm target →
      baseConv source target)
    {source target : RawTerm scope} :
    ConvOverIdentifications [] semantics baseConv source target
      ↔ baseConv source target := by
  refine ⟨fun related => ?_, fun related => .base related⟩
  induction related with
  | base related => exact related
  | identify isRow _conditionHolds => exact nomatch isRow
  | symm _related ih => exact baseIsSymmetric ih
  | trans _left _right leftIh rightIh =>
      exact baseIsTransitive leftIh rightIh

/-- The unit identification fires: two unit-typed terms convert in the
canonical table (any base, any semantics asserting the typing). -/
theorem ConvOverIdentifications.unitIdentification
    {scope : Nat} {semantics : IdentificationSemantics scope}
    {baseConv : RawTerm scope → RawTerm scope → Prop}
    {source target : RawTerm scope}
    (sourceTyped :
      semantics.isTypedAtCodeHead .gen_unitCode source)
    (targetTyped :
      semantics.isTypedAtCodeHead .gen_unitCode target) :
    ConvOverIdentifications typedIdentificationTable semantics baseConv
      source target :=
  .identify unitIdentificationRule_memTable ⟨sourceTyped, targetTyped⟩

/-- ★ The ghost identification fires: two ERASED terms convert in the
canonical table — grade-keyed definitional irrelevance, as one
constructor application over the data. -/
theorem ConvOverIdentifications.ghostIdentification
    {scope : Nat} {semantics : IdentificationSemantics scope}
    {baseConv : RawTerm scope → RawTerm scope → Prop}
    {source target : RawTerm scope}
    (sourceErased : semantics.hasUsageGradeZero source)
    (targetErased : semantics.hasUsageGradeZero target) :
    ConvOverIdentifications typedIdentificationTable semantics baseConv
      source target :=
  .identify ghostIdentificationRule_memTable
    ⟨sourceErased, targetErased⟩

end FX1Poly.Core
