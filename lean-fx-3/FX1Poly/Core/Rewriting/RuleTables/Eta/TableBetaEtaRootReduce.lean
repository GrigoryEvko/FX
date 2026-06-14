import FX1Poly.Core.Rewriting.RuleTables.Tables.TableReduceOnce
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaRootTable

/-! # TableBetaEtaRootReduce — the union one-step reducer for the
canonical table beta-eta-root relation

The first computable brick of the TABLE-NATIVE union beta-eta decider:
a sound + blocking-complete one-step reducer for the canonical union
`StepTableBetaEtaRoot = StepTable ∨ StepEtaRootTable`, re-based ENTIRELY
onto the rule tables — ZERO dependence on the bespoke
`Step.betaEta`/`reduceOnceBetaEta`/`fireRootEtaRedex?`.

The layering mirrors the bespoke `RawTerm.reduceOnceBetaEta`: fire the
FULL table iota relation (root + congruence) via the shipped
`reduceOnceOverTable iotaRuleTable`; only on an iota-normal term try a
TABLE root-eta contraction.  Where the bespoke layer's eta side called
`fireRootEtaRedex?` (producing a `Step.eta`), this file walks the
`etaRuleTable` rows directly — the EXACT eta twin of the iota
`IotaRuleDesc.fireAtRoot?` / `fireTableRedexOver` template — producing
`StepEtaRootTable` evidence.

* `EtaRuleDesc.fireAtRootEta?` — fire ONE raw-tier eta row at a
  `(generator, payload, children)` root (generator match, raw-tier
  guard, the row's `contractsOn?`);
* `fireEtaTableRedexOver` — walk a row list to the first eta firing,
  with generic soundness (a produced reduct is a `StepEtaRootOverTable`
  step) and generic completeness (a specific firing row forces the walk
  to return `some`);
* `RawTerm.fireRootEtaTableRedex?` — fire a root eta redex over the
  canonical `etaRuleTable`, with soundness and the blocking
  no-eta-step lemma (the genuinely-new INVERSION: a failed row walk
  refutes every hypothetical `StepEtaRootTable` step through
  `StepEtaRootOverTable.invert` + the walk completeness);
* `RawTerm.reduceOnceTableBetaEtaRoot?` — the union reducer
  (iota-first, eta-on-iota-normal), with `reduceOnceTableBetaEtaRoot?_sound`
  (`StepTableBetaEtaRoot`) and `reduceOnceTableBetaEtaRoot?_blocksStep`
  (`none` ⟹ no `StepTableBetaEtaRoot` step).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConvDecidable.lean`. -/

namespace FX1Poly.Core

/-- The Core-level union step relation: a full-congruence table iota
step, or a root table eta contraction.  Definitionally equal to the
Typed `StepTableBetaEtaRoot` (same `Or` of the two canonical table
relations) — the Typed decider bridges by unfolding, keeping this brick
in Core with NO Typed dependency. -/
def StepTableBetaEtaRootUnion {scope : Nat}
    (source target : RawTerm scope) : Prop :=
  StepTable source target ∨ StepEtaRootTable source target

/-! ## One eta row's root firing -/

/-- **Fire ONE raw-tier eta row at a raw `(generator, payload, children)`
root.**  When the generator IS the row's intro head (decided over
`Generator`) AND the row is raw-tier, coerce the spine to the row's intro
type and run the row's `contractsOn?`; otherwise this row does not apply.
The EXACT eta twin of `IotaRuleDesc.fireAtRoot?`. -/
def EtaRuleDesc.fireAtRootEta? (rule : EtaRuleDesc) {scope : Nat}
    (generator : Generator) (_payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    Option (RawTerm scope) :=
  if isIntroHead : generator = rule.introGenerator then
    if _isRawTier : rule.requiresTypedFiring = false then
      rule.contractsOn? (isIntroHead ▸ children)
    else none
  else none

/-- One eta row's root firing is sound: a produced reduct is a root
table eta step (for any table the row belongs to). -/
theorem EtaRuleDesc.fireAtRootEta?_sound {table : List EtaRuleDesc}
    {rule : EtaRuleDesc} (isRow : rule ∈ table) {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq : rule.fireAtRootEta? generator payload children = some reduct) :
    StepEtaRootOverTable table
      (.mkGen generator payload children) reduct := by
  dsimp only [EtaRuleDesc.fireAtRootEta?] at fireEq
  by_cases isIntroHead : generator = rule.introGenerator
  case pos =>
      subst isIntroHead
      rw [dif_pos rfl] at fireEq
      by_cases isRawTier : rule.requiresTypedFiring = false
      case pos =>
          rw [dif_pos isRawTier] at fireEq
          exact StepEtaRootOverTable.etaRedex isRow isRawTier payload fireEq
      case neg =>
          rw [dif_neg isRawTier] at fireEq
          injection fireEq
  case neg =>
      rw [dif_neg isIntroHead] at fireEq
      injection fireEq

/-! ## Walking the eta table -/

/-- Walk an eta-row list, returning the first matching firing's reduct
(the eta twin of `fireTableRedexOver`). -/
def fireEtaTableRedexOver {scope : Nat} :
    List EtaRuleDesc → (generator : Generator) →
    generator.payload scope →
    RawTermChildren generator.binderShifts scope → Option (RawTerm scope)
  | [], _, _, _ => none
  | rule :: restRows, generator, payload, children =>
      match rule.fireAtRootEta? generator payload children with
      | some reduct => some reduct
      | none => fireEtaTableRedexOver restRows generator payload children

/-- ★ **Generic eta root firing soundness** — a produced reduct is a
root table eta step over any table whose rows include the walked rows.
ONE proof, ZERO per-rule cases (the eta twin of
`fireTableRedexOver_sound`). -/
theorem fireEtaTableRedexOver_sound {table : List EtaRuleDesc}
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} :
    (rows : List EtaRuleDesc) →
    (rowsAreInTable : ∀ rule, rule ∈ rows → rule ∈ table) →
    {reduct : RawTerm scope} →
    fireEtaTableRedexOver rows generator payload children = some reduct →
    StepEtaRootOverTable table (.mkGen generator payload children) reduct
  | [], _, _, fireEq => by
      dsimp only [fireEtaTableRedexOver] at fireEq
      injection fireEq
  | rule :: restRows, rowsAreInTable, reduct, fireEq => by
      dsimp only [fireEtaTableRedexOver] at fireEq
      match headFireEq : rule.fireAtRootEta? generator payload children with
      | some headReduct =>
          rw [headFireEq] at fireEq
          obtain rfl := Option.some.inj fireEq
          exact rule.fireAtRootEta?_sound (rowsAreInTable rule (.head _))
            headFireEq
      | none =>
          rw [headFireEq] at fireEq
          exact fireEtaTableRedexOver_sound restRows
            (fun otherRule isInRest =>
              rowsAreInTable otherRule (.tail _ isInRest))
            fireEq

/-- ★ **Generic eta root firing completeness** — a specific row that
fires forces the walk to return `some` (the walk may return an earlier
overlapping row's reduct, hence `isSome`).  The eta twin of
`fireTableRedexOver_complete`. -/
theorem fireEtaTableRedexOver_complete {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {firingRule : EtaRuleDesc} {reduct : RawTerm scope}
    (firingFireEq :
      firingRule.fireAtRootEta? generator payload children = some reduct) :
    (rows : List EtaRuleDesc) →
    firingRule ∈ rows →
    (fireEtaTableRedexOver rows generator payload children).isSome = true
  | [], isRow => by cases isRow
  | rule :: restRows, isRow => by
      dsimp only [fireEtaTableRedexOver]
      match headFireEq : rule.fireAtRootEta? generator payload children with
      | some _ => rfl
      | none =>
          cases isRow with
          | head =>
              rw [firingFireEq] at headFireEq
              injection headFireEq
          | tail _ isInRest =>
              exact fireEtaTableRedexOver_complete firingFireEq restRows
                isInRest

/-! ## The canonical eta root firer -/

/-- **Fire a root eta redex over the canonical `etaRuleTable`.**  The
table twin of the bespoke `RawTerm.fireRootEtaRedex?`: destructure the
cell, then walk the eta rows. -/
def RawTerm.fireRootEtaTableRedex? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .mkGen generator payload children =>
      fireEtaTableRedexOver etaRuleTable generator payload children

/-- **The canonical eta firer is sound** — a produced reduct is a
`StepEtaRootTable` step. -/
theorem RawTerm.fireRootEtaTableRedex?_sound {scope : Nat}
    {term reduct : RawTerm scope}
    (fireEq : term.fireRootEtaTableRedex? = some reduct) :
    StepEtaRootTable term reduct := by
  match term with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.fireRootEtaTableRedex?] at fireEq
      exact fireEtaTableRedexOver_sound etaRuleTable (fun _ isRow => isRow)
        fireEq

/-- ★ **The canonical eta firer halts only on eta-inert terms.**  The
genuinely-new INVERSION: a `none` walk refutes every hypothetical
`StepEtaRootTable` step.  `StepEtaRootOverTable.invert` exposes the
fired row, its raw-tier verdict, the intro payload, the cell shape, and
the contraction; that reassembles the matching `fireAtRootEta?` firing,
whose `fireEtaTableRedexOver_complete` against the canonical table
forces the walk to be `some` — contradicting `none`. -/
theorem RawTerm.fireRootEtaTableRedex?_blocksStep {scope : Nat}
    {term : RawTerm scope}
    (halted : term.fireRootEtaTableRedex? = none) :
    ∀ next : RawTerm scope, ¬ StepEtaRootTable term next := by
  intro next etaStep
  obtain ⟨rule, isRow, isRawTier, introPayload, introChildren,
    sourceShape, contracts⟩ := etaStep.invert
  have rowFires :
      rule.fireAtRootEta? rule.introGenerator introPayload introChildren
        = some next := by
    dsimp only [EtaRuleDesc.fireAtRootEta?]
    rw [dif_pos rfl, dif_pos isRawTier]
    exact contracts
  have walkFires :=
    fireEtaTableRedexOver_complete rowFires etaRuleTable isRow
  have fireEqAtSource :
      term.fireRootEtaTableRedex?
        = fireEtaTableRedexOver etaRuleTable rule.introGenerator
            introPayload introChildren := by
    rw [sourceShape]
    rfl
  rw [fireEqAtSource] at halted
  rw [halted] at walkFires
  exact Bool.noConfusion walkFires

/-! ## The union one-step reducer -/

/-- **The union beta-eta-root one-step reducer**: fire the FULL table
iota relation first (the shipped leftmost-outermost
`reduceOnceOverTable iotaRuleTable`), then a root table eta redex on
iota-normal terms.  The table twin of the bespoke
`RawTerm.reduceOnceBetaEta` — every byte rule-table-driven. -/
def RawTerm.reduceOnceTableBetaEtaRoot? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match reduceOnceOverTable iotaRuleTable term with
  | some reduct => some reduct
  | none => term.fireRootEtaTableRedex?

/-- **The union reducer fires only real `StepTableBetaEtaRoot` steps** —
iota firings through `reduceOnceOverTable_sound` (`Or.inl`), eta firings
through `fireRootEtaTableRedex?_sound` (`Or.inr`). -/
theorem RawTerm.reduceOnceTableBetaEtaRoot?_sound {scope : Nat}
    {term reduct : RawTerm scope}
    (success : term.reduceOnceTableBetaEtaRoot? = some reduct) :
    StepTableBetaEtaRootUnion term reduct := by
  dsimp only [RawTerm.reduceOnceTableBetaEtaRoot?] at success
  match iotaEq : reduceOnceOverTable iotaRuleTable term with
  | some iotaReduct =>
      rw [iotaEq] at success
      obtain rfl := Option.some.inj success
      exact Or.inl (reduceOnceOverTable_sound iotaEq)
  | none =>
      rw [iotaEq] at success
      exact Or.inr (RawTerm.fireRootEtaTableRedex?_sound success)

/-- ★★ **The union reducer halts exactly at union normal forms**:
`none` means no table iota step ANYWHERE (`reduceOnceOverTable`
blocking completeness) AND no root table eta step
(`fireRootEtaTableRedex?_blocksStep`) — so no `StepTableBetaEtaRoot`
step at all. -/
theorem RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep {scope : Nat}
    {term : RawTerm scope}
    (halted : term.reduceOnceTableBetaEtaRoot? = none)
    {next : RawTerm scope} (unionStep : StepTableBetaEtaRootUnion term next) :
    False := by
  dsimp only [RawTerm.reduceOnceTableBetaEtaRoot?] at halted
  match iotaEq : reduceOnceOverTable iotaRuleTable term with
  | some iotaReduct =>
      rw [iotaEq] at halted
      nomatch halted
  | none =>
      rw [iotaEq] at halted
      cases unionStep with
      | inl iotaStep =>
          exact reduceOnceOverTable_eq_none_blocks_step iotaEq iotaStep
      | inr etaStep =>
          exact RawTerm.fireRootEtaTableRedex?_blocksStep halted next etaStep

end FX1Poly.Core
