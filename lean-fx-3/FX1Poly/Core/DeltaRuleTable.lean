import FX1Poly.Core.RawTermWeaken

/-! # DeltaRuleTable — RW-4: δ-rules as data, the defined-constant table

The THIRD rule-table family, parallel to `IotaRuleDesc`
(`IotaRuleTable.lean`, the β/ι table) and `EtaRuleDesc`
(`EtaRuleTable.lean`, the η table).  A δ-rule UNFOLDS a defined
constant to its closed definiens — the kernel-level model of a
top-level `let`/`def` binding.  The FX kernel has no named-constant
syntax in `RawTerm`; a δ-rule keys on a designated nullary RESERVED
generator (a stand-in "defined constant" with no other kernel
semantics — `gen_hyperreal`, `gen_qubit`) and rewrites its cell to a
CLOSED definiens weakened to the firing scope.

## Why δ is its OWN family (not an `IotaRuleDesc` / `EtaRuleDesc` row)

* ι contracts an ELIMINATOR applied to a CONSTRUCTOR (`natElim … (succ
  n) ↝ …`); its `ReductTemplate` DSL projects scrutinee children.  A
  δ-rule has no scrutinee — it replaces a LEAF by a stored term.
* η contracts an INTRO observed through ELIMINATORS, with a
  STRENGTHENING reduct.  δ neither observes nor strengthens.
* δ is the canonical NON-LEFT-OVERLAPPING rule: its redex is a nullary
  leaf, structurally disjoint from every β/ι/η redex shape — so δ
  commutes with the whole β/ι/η system (the postponement deliverable,
  a later RW-4 increment).

## Honesty: a STANDALONE sibling, ledger untouched

Like `StepEtaOverTable` before its ETA-T7 canonicality flip, this δ
relation is a SEPARATE object — it is NOT wired into the canonical
`Step` / `StepOver` relation, so `Generator.semanticTier` and the
`GeneratorHonestyLedger` are unchanged.  The constant heads stay
RESERVED (inert, untyped) in the canonical kernel; the δ-table is a
demonstration of the rule-table SCHEMA, not a kernel semantics change.
Wiring δ into the canonical bundle (and the consequent ledger flip on
the chosen constant heads) is a deliberate later step, exactly the
eta-tier discipline.

## SN honesty (the partial tier)

A δ-table is NOT strongly normalizing in general: an alias whose
definiens itself contains a table constant (`gen_qubit ↝ gen_hyperreal`
below, were `gen_hyperreal` also unfolded) need not decrease any leaf
count — the same reason `gen_fixedPoint` is `partialClass`.  This
increment ships the structural substrate; the size/measure tier
(δ-SN on the δ-FREE-definiens fragment), the typed δ-SR (the
ElimRuleDesc-analogue link), and δ/β postponement land as follow-on
RW-4 increments.

## Zero-axiom

Plain structural definitions, `rfl` firing equations (`weakenClosed`
at scope 0 is the identity by its first match arm), and `cases`-driven
inversions over the two-row table.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditDeltaRuleTable.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Closed-term weakening to the firing scope

A defined constant's definiens is CLOSED (`RawTerm 0`); firing inside a
scope-`n` term re-instantiates it at scope `n`.  Structural on the
scope so the result lands EXACTLY in `RawTerm scope` (no `0 + scope`
cast) and so scope-0 firing is the identity by `rfl`. -/

/-- Weaken a closed term to an arbitrary scope by iterating the
single-binder `RawTerm.weaken`.  `weakenClosed 0 = id` (the firing
pins reduce by `rfl`); `weakenClosed (n+1)` adds one fresh binder. -/
def RawTerm.weakenClosed : (scope : Nat) → RawTerm 0 → RawTerm scope
  | 0, closed => closed
  | scope + 1, closed => RawTerm.weaken (RawTerm.weakenClosed scope closed)

/-- Firing a defined constant in a CLOSED program reproduces the
definiens verbatim — `weakenClosed` at scope 0 is the identity. -/
theorem RawTerm.weakenClosed_zero (closed : RawTerm 0) :
    RawTerm.weakenClosed 0 closed = closed := rfl

/-! ## The rule descriptor -/

/-- One δ-rule as DATA: a defined-constant head (a nullary RESERVED
generator) plus its CLOSED definiens.  A cell headed by `constantHead`
unfolds to `definiens` weakened to the cell's scope. -/
structure DeltaRuleDesc where
  constantHead : Generator
  definiens : RawTerm 0

/-! ## The smoke table

`gen_hyperreal` and `gen_qubit` are nullary RESERVED markers (no
canonical reduction rule, no typing row).  We treat them as opaque
defined constants:

  * `gen_hyperreal := unit` — an acyclic alias: the definiens
    (`gen_unit`) is δ-FREE, so this rule alone is strongly normalizing.
  * `gen_qubit := gen_hyperreal` — the definiens IS another constant
    head, the honest NON-decreasing witness (chaining `qubit ↝
    hyperreal ↝ unit` terminates only because the SECOND rule's
    definiens is δ-free; a self-referential definiens would loop). -/

/-- The closed `unit` value, the δ-free definiens of `gen_hyperreal`. -/
@[reducible] def unitDefiniens : RawTerm 0 := .mkGen .gen_unit () .childNil

/-- The closed `gen_hyperreal` value, `gen_qubit`'s definiens. -/
@[reducible] def hyperrealDefiniens : RawTerm 0 :=
  .mkGen .gen_hyperreal () .childNil

/-- `gen_hyperreal := unit` (the acyclic, δ-free-definiens row). -/
def hyperrealDeltaRow : DeltaRuleDesc where
  constantHead := .gen_hyperreal
  definiens := unitDefiniens

/-- `gen_qubit := gen_hyperreal` (definiens is itself a constant). -/
def qubitDeltaRow : DeltaRuleDesc where
  constantHead := .gen_qubit
  definiens := hyperrealDefiniens

/-- The δ-rule smoke table: two defined-constant unfoldings. -/
def deltaRuleTable : List DeltaRuleDesc := [hyperrealDeltaRow, qubitDeltaRow]

/-- Stale-count guard: 2 δ rows. -/
theorem deltaRuleTable_length : deltaRuleTable.length = 2 := rfl

/-! ## The relation -/

mutual

/-- Single-step δ reduction OVER A RULE TABLE: a root unfolding is a
row of `table` whose constant head matches the cell, rewriting it to
the row's definiens weakened to the cell's scope; reduction is closed
under the same uniform child congruence as `StepEtaOverTable`. -/
inductive StepDeltaOverTable (table : List DeltaRuleDesc) :
    {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  /-- **A table row unfolds a defined constant at the root.** -/
  | deltaRedex {scope : Nat} {rule : DeltaRuleDesc} (isRow : rule ∈ table)
      (constantPayload : rule.constantHead.payload scope)
      (constantChildren :
        RawTermChildren rule.constantHead.binderShifts scope) :
      StepDeltaOverTable table
        (.mkGen rule.constantHead constantPayload constantChildren)
        (RawTerm.weakenClosed scope rule.definiens)
  /-- **Uniform congruence under any generator.** -/
  | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
      {children children' : RawTermChildren gen.binderShifts scope}
      (childStep : StepDeltaOverTableChildren table children children') :
      StepDeltaOverTable table (.mkGen gen payload children)
        (.mkGen gen payload children')

/-- A δ table step at some position in a children spine. -/
inductive StepDeltaOverTableChildren (table : List DeltaRuleDesc) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      {head head' : RawTerm (parentScope + headShift)}
      (rest : RawTermChildren restShifts parentScope)
      (childStep : StepDeltaOverTable table head head') :
      StepDeltaOverTableChildren table
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head' rest)
  | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      (head : RawTerm (parentScope + headShift))
      {rest rest' : RawTermChildren restShifts parentScope}
      (restStep : StepDeltaOverTableChildren table rest rest') :
      StepDeltaOverTableChildren table
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head rest')

end

/-- THE δ table relation: `StepDeltaOverTable` at the canonical
two-row `deltaRuleTable`. -/
abbrev StepDeltaTable {scope : Nat} (source target : RawTerm scope) : Prop :=
  StepDeltaOverTable deltaRuleTable source target

/-! ## Monotonicity -/

mutual

/-- A δ step over a table is a step over any wider table. -/
theorem StepDeltaOverTable.monotone {table widerTable : List DeltaRuleDesc}
    (isWider : ∀ {rule : DeltaRuleDesc}, rule ∈ table → rule ∈ widerTable)
    {scope : Nat} {source target : RawTerm scope}
    (deltaStep : StepDeltaOverTable table source target) :
    StepDeltaOverTable widerTable source target :=
  match deltaStep with
  | .deltaRedex isRow constantPayload constantChildren =>
      .deltaRedex (isWider isRow) constantPayload constantChildren
  | .cong gen payload childStep =>
      .cong gen payload
        (StepDeltaOverTableChildren.monotone isWider childStep)

/-- Spine companion of `StepDeltaOverTable.monotone`. -/
theorem StepDeltaOverTableChildren.monotone
    {table widerTable : List DeltaRuleDesc}
    (isWider : ∀ {rule : DeltaRuleDesc}, rule ∈ table → rule ∈ widerTable)
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep : StepDeltaOverTableChildren table children children') :
    StepDeltaOverTableChildren widerTable children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepDeltaOverTable.monotone isWider headStep)
  | .there head restStep =>
      .there head (StepDeltaOverTableChildren.monotone isWider restStep)

end

/-! ## The freed-subject inversion -/

/-- **δ table-step inversion at a known cell**: a step out of
`.mkGen gen payload children` is either a ROOT CONSTANT UNFOLDING (the
row, its membership, and the reduct identified as the weakened
definiens, with the cell identification) or a CHILD CONGRUENCE. -/
theorem StepDeltaOverTable.invertOrCong {table : List DeltaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (deltaStep : StepDeltaOverTable table source target)
    {gen : Generator} {payload : gen.payload scope}
    {children : RawTermChildren gen.binderShifts scope}
    (sourceShape : source = .mkGen gen payload children) :
    (∃ (rule : DeltaRuleDesc) (_ : rule ∈ table)
        (constantPayload : rule.constantHead.payload scope)
        (constantChildren :
          RawTermChildren rule.constantHead.binderShifts scope),
        RawTerm.mkGen rule.constantHead constantPayload constantChildren
            = RawTerm.mkGen gen payload children
        ∧ target = RawTerm.weakenClosed scope rule.definiens)
    ∨ (∃ children', target = .mkGen gen payload children'
        ∧ StepDeltaOverTableChildren table children children') := by
  cases deltaStep with
  | deltaRedex isRow constantPayload constantChildren =>
      exact Or.inl ⟨_, isRow, constantPayload, constantChildren,
        sourceShape, rfl⟩
  | cong congGen congPayload childrenStep =>
      have headsAgree : congGen = gen := congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        sourceShape
      subst headsAgree
      injection sourceShape with _scopeRefl _genRefl payloadEq childrenEq
      subst payloadEq
      subst childrenEq
      exact Or.inr ⟨_, rfl, childrenStep⟩

/-! ## Row memberships -/

theorem hyperrealDeltaRow_memTable : hyperrealDeltaRow ∈ deltaRuleTable :=
  .head _
theorem qubitDeltaRow_memTable : qubitDeltaRow ∈ deltaRuleTable :=
  .tail _ (.head _)

/-! ## The firing pins — the GO gate

Each row unfolds its constant at scope 0; `weakenClosed 0` is the
identity so the reduct is the definiens verbatim, and the equations
close by `rfl`. -/

/-- `gen_hyperreal ↝ unit` fires. -/
theorem hyperrealDeltaRow_fires :
    StepDeltaTable (scope := 0)
      (.mkGen .gen_hyperreal () .childNil)
      (.mkGen .gen_unit () .childNil) :=
  .deltaRedex hyperrealDeltaRow_memTable () .childNil

/-- `gen_qubit ↝ gen_hyperreal` fires (the definiens is itself a
constant head — the non-decreasing witness). -/
theorem qubitDeltaRow_fires :
    StepDeltaTable (scope := 0)
      (.mkGen .gen_qubit () .childNil)
      (.mkGen .gen_hyperreal () .childNil) :=
  .deltaRedex qubitDeltaRow_memTable () .childNil

/-! ## Conservativity over the δ-free fragment

A δ step out of a cell whose head matches NO table row must be a child
congruence — the root cannot unfold.  Hence on a term with no
table-constant occurrence the δ relation is empty: δ is conservative
over the δ-free fragment (and trivially SN there). -/

/-- **Head-not-a-constant ⇒ no root unfolding.**  Any δ step out of a
cell whose head is not the constant head of any table row is forced to
be a child congruence. -/
theorem StepDeltaOverTable.invert_headNotConstant {table : List DeltaRuleDesc}
    {scope : Nat} {gen : Generator} {payload : gen.payload scope}
    {children : RawTermChildren gen.binderShifts scope} {target : RawTerm scope}
    (deltaStep : StepDeltaOverTable table (.mkGen gen payload children) target)
    (headFresh : ∀ {rule : DeltaRuleDesc}, rule ∈ table →
      rule.constantHead = gen → False) :
    ∃ children', target = .mkGen gen payload children'
      ∧ StepDeltaOverTableChildren table children children' := by
  cases deltaStep.invertOrCong rfl with
  | inl rootUnfolding =>
      obtain ⟨rule, isRow, _constantPayload, _constantChildren,
        cellEq, _reductEq⟩ := rootUnfolding
      have headsAgree : rule.constantHead = gen := congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        cellEq
      exact absurd headsAgree (fun eq => headFresh isRow eq)
  | inr congShape => exact congShape

/-- **The δ-free `unit` value never δ-steps.**  Its head is neither
constant, and a nullary cell has no child to step — concrete
conservativity over a closed δ-free term. -/
theorem unitValue_noDeltaStep {scope : Nat} {target : RawTerm scope} :
    ¬ StepDeltaTable (.mkGen .gen_unit () .childNil) target := by
  intro deltaStep
  obtain ⟨_children', _targetShape, childStep⟩ :=
    deltaStep.invert_headNotConstant (by
      intro rule isRow headEq
      cases isRow with
      | head => exact nomatch headEq
      | tail _ isRow => cases isRow with
        | head => exact nomatch headEq
        | tail _ isRow => cases isRow)
  exact nomatch childStep

/-! ## Non-vacuity: the congruence arm fires

A δ unfolding INSIDE a child position: `pair gen_hyperreal unit`
δ-steps to `pair unit unit` in the first component. -/

theorem stepDeltaTable_congSmoke :
    StepDeltaTable (scope := 0)
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_hyperreal () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))) :=
  .cong .gen_pair () (.here _ hyperrealDeltaRow_fires)

end FX1Poly.Core
