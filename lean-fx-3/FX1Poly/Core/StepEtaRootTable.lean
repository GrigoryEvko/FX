import FX1Poly.Core.EtaTableOrthogonality
import FX1Poly.Core.StepEtaOverTable

/-! # StepEtaRootTable — ETA-T6 increment 5a: the root-only table eta
tier

The full-congruence table eta cannot enter the typed metatheory yet:
a deep eta step changes value-dependent classifiers only up to
ETA-conversion, which the typing engine's `conv` rule (beta/iota
`Conv`) cannot absorb — that absorption is exactly the eta-aware
judgmental-equality territory (`ConvOverIdentifications`, Path-A
NbE).  The shipped bespoke Geuvers results live on root-only eta
(`Step.eta` has no congruence arm), so their honest table
generalization quantifies over wf-table ROWS at the same root-only
tier: this module defines that tier — the `etaRedex` arm alone — with
its embedding into the full relation, a freed-subject inversion, and
its determinism (from the ETA-T4 distinct-roots certificate).

The cross-pair counterexamples do NOT bite here: they need an eta
redex buried at a scrutinee slot, which root-only eta cannot express
— consistent with the bespoke postponement having been provable.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStepEtaRootTable.lean`. -/

namespace FX1Poly.Core

/-- A raw-tier table eta contraction AT THE ROOT — the table twin of
the bespoke root-only `Step.eta`. -/
inductive StepEtaRootOverTable (table : List EtaRuleDesc) :
    {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  | etaRedex {scope : Nat} {rule : EtaRuleDesc} (isRow : rule ∈ table)
      (isRawTier : rule.requiresTypedFiring = false)
      (introPayload : rule.introGenerator.payload scope)
      {introChildren :
        RawTermChildren rule.introGenerator.binderShifts scope}
      {core : RawTerm scope}
      (contracts : rule.contractsOn? introChildren = some core) :
      StepEtaRootOverTable table
        (.mkGen rule.introGenerator introPayload introChildren) core

/-- The canonical instantiation. -/
abbrev StepEtaRootTable {scope : Nat}
    (source target : RawTerm scope) : Prop :=
  StepEtaRootOverTable etaRuleTable source target

/-- Root contractions embed into the full table eta relation. -/
theorem StepEtaRootOverTable.toStepEtaOverTable
    {table : List EtaRuleDesc} {scope : Nat}
    {source target : RawTerm scope}
    (rootStep : StepEtaRootOverTable table source target) :
    StepEtaOverTable table source target := by
  cases rootStep with
  | etaRedex isRow isRawTier introPayload contracts =>
      exact .etaRedex isRow isRawTier introPayload contracts

/-- Freed-subject inversion: the source shape and the contraction as
equations. -/
theorem StepEtaRootOverTable.invert {table : List EtaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (rootStep : StepEtaRootOverTable table source target) :
    ∃ (rule : EtaRuleDesc) (_ : rule ∈ table)
      (_ : rule.requiresTypedFiring = false)
      (introPayload : rule.introGenerator.payload scope)
      (introChildren :
        RawTermChildren rule.introGenerator.binderShifts scope),
      source = .mkGen rule.introGenerator introPayload introChildren
        ∧ rule.contractsOn? introChildren = some target := by
  cases rootStep with
  | etaRedex isRow isRawTier introPayload contracts =>
      exact ⟨_, isRow, isRawTier, introPayload, _, rfl, contracts⟩

/-- ★ **Root eta is deterministic** under the distinct-roots
certificate: two root contractions of the same cell produce the same
core (the shared head pins the rule via uniqueness; the contraction
reader is a function). -/
theorem StepEtaRootOverTable.deterministic {table : List EtaRuleDesc}
    (introRootsAreDistinct : allIntroRootsDistinct table = true)
    {scope : Nat} {source firstTarget secondTarget : RawTerm scope}
    (firstStep : StepEtaRootOverTable table source firstTarget)
    (secondStep : StepEtaRootOverTable table source secondTarget) :
    firstTarget = secondTarget := by
  obtain ⟨firstRule, firstIsRow, _firstRawTier, firstPayload,
    firstChildren, firstShape, firstContracts⟩ := firstStep.invert
  obtain ⟨secondRule, secondIsRow, _secondRawTier, secondPayload,
    secondChildren, secondShape, secondContracts⟩ := secondStep.invert
  have cellsAgree :
      RawTerm.mkGen firstRule.introGenerator firstPayload firstChildren
        = RawTerm.mkGen secondRule.introGenerator secondPayload
            secondChildren :=
    firstShape.symm.trans secondShape
  have headsAgree :
      firstRule.introGenerator = secondRule.introGenerator :=
    congrArg
      (fun cell => match cell with
        | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
      cellsAgree
  have rulesAgree : firstRule = secondRule :=
    allIntroRootsDistinct_memUnique table introRootsAreDistinct
      firstIsRow secondIsRow headsAgree
  subst rulesAgree
  injection cellsAgree with _scopeRefl _genRefl payloadEq childrenEq
  subst childrenEq
  exact Option.some.inj (firstContracts.symm.trans secondContracts)

end FX1Poly.Core
