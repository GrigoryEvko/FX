import FX1Poly.Core.StepOverTable

/-! # FX1Poly/Core/TableFireRoot — IOTA-T4: generic root firing over the table

The computational firing function for the table relation, replacing the
twelve-deep `dite`-chains of `RawTerm.fireRootRedex` and
`RawTerm.hasRootStepSource` with ONE table walk and ZERO per-rule
cases.  A row fires at the root exactly when its eliminator head
matches and its left-linear pattern fires; the reduct is the row's
interpreted target (`firesOn?`).

  * `fireTableRedexOver` — walk the rows, return the first matching
    firing's reduct.  `fireTableRedexOver_sound` : `= some reduct ⟹
    StepOverTable`.
  * `hasTableRedexRootOver` — the membership/detection predicate
    (`(fire …).isSome`); detection and firing coincide by definition.
  * `detectsHeadAtRoot` — the cheap Bool head test (eliminator key +
    `scrutineesFire`, no reduct built); a firing is always head-detected
    (`fireTableRedexOver_isSome_imp_headDetected`).
  * `fireTableRedexOver_complete` — a specific row that fires forces the
    walk to return `some`.

Instantiated at the canonical 18-row table as `StepTable.fireRoot` etc.,
and bridged to the kernel `Step` relation via the shipped
`stepOverTable_iff_step` adequacy.

## Zero-axiom verification

`dite` on `DecidableEq Generator` (never a >100-ctor wildcard `match`),
the `▸` generator-coercion the existing `firesOn?` substrate already
uses, single-`Option` matches, and structural recursion over the row
list.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTableFireRoot.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## One row's root firing -/

/-- Fire ONE row at a raw `(generator, payload, children)` root: when
the generator IS the row's eliminator (decided over `Generator`), coerce
the payload and spine to the row's eliminator type and run the row's
`firesOn?`; otherwise this row does not apply. -/
def IotaRuleDesc.fireAtRoot? (rule : IotaRuleDesc) {scope : Nat}
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    Option (RawTerm scope) :=
  if isElimHead : generator = rule.elimGenerator then
    rule.firesOn? (isElimHead ▸ payload) (isElimHead ▸ children)
  else none

/-- One row's root firing is sound: a produced reduct is a table redex
step (for any table the row belongs to). -/
theorem IotaRuleDesc.fireAtRoot?_sound {table : List IotaRuleDesc}
    {rule : IotaRuleDesc} (isRow : rule ∈ table) {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq : rule.fireAtRoot? generator payload children = some reduct) :
    StepOverTable table (.mkGen generator payload children) reduct := by
  dsimp only [IotaRuleDesc.fireAtRoot?] at fireEq
  by_cases isElimHead : generator = rule.elimGenerator
  case pos =>
      subst isElimHead
      rw [dif_pos rfl] at fireEq
      exact StepOverTable.tableRedex isRow payload fireEq
  case neg =>
      rw [dif_neg isElimHead] at fireEq
      injection fireEq

/-- The cheap Bool detector for ONE row: the eliminator key matches and
the left-linear pattern fires — no reduct is built. -/
def IotaRuleDesc.detectsHeadAtRoot (rule : IotaRuleDesc) {scope : Nat}
    (generator : Generator)
    (children : RawTermChildren generator.binderShifts scope) : Bool :=
  if isElimHead : generator = rule.elimGenerator then
    rule.scrutineesFire (isElimHead ▸ children) rule.scrutinees
  else false

/-- A produced reduct is head-detected: firing implies the pattern
fired, which is exactly what the cheap detector tests. -/
theorem IotaRuleDesc.fireAtRoot?_isSome_imp_detectsHeadAtRoot
    {rule : IotaRuleDesc} {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq : rule.fireAtRoot? generator payload children = some reduct) :
    rule.detectsHeadAtRoot generator children = true := by
  dsimp only [IotaRuleDesc.fireAtRoot?] at fireEq
  by_cases isElimHead : generator = rule.elimGenerator
  case pos =>
      subst isElimHead
      rw [dif_pos rfl] at fireEq
      dsimp only [IotaRuleDesc.detectsHeadAtRoot]
      rw [dif_pos rfl]
      exact rule.firesOn?_some_scrutineesFire fireEq
  case neg =>
      rw [dif_neg isElimHead] at fireEq
      injection fireEq

/-! ## Walking the table -/

/-- Walk a row list, returning the first matching firing's reduct. -/
def fireTableRedexOver {scope : Nat} :
    List IotaRuleDesc → (generator : Generator) →
    generator.payload scope →
    RawTermChildren generator.binderShifts scope → Option (RawTerm scope)
  | [], _, _, _ => none
  | rule :: restRows, generator, payload, children =>
      match rule.fireAtRoot? generator payload children with
      | some reduct => some reduct
      | none => fireTableRedexOver restRows generator payload children

/-- ★ **Generic root firing soundness** — a produced reduct is a table
redex step over any table whose rows include the walked rows.  ONE
proof, ZERO per-rule cases. -/
theorem fireTableRedexOver_sound {table : List IotaRuleDesc}
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} :
    (rows : List IotaRuleDesc) →
    (rowsAreInTable : ∀ rule, rule ∈ rows → rule ∈ table) →
    {reduct : RawTerm scope} →
    fireTableRedexOver rows generator payload children = some reduct →
    StepOverTable table (.mkGen generator payload children) reduct
  | [], _, _, fireEq => by
      dsimp only [fireTableRedexOver] at fireEq
      injection fireEq
  | rule :: restRows, rowsAreInTable, reduct, fireEq => by
      dsimp only [fireTableRedexOver] at fireEq
      match headFireEq : rule.fireAtRoot? generator payload children with
      | some headReduct =>
          rw [headFireEq] at fireEq
          obtain rfl := Option.some.inj fireEq
          exact rule.fireAtRoot?_sound (rowsAreInTable rule (.head _))
            headFireEq
      | none =>
          rw [headFireEq] at fireEq
          exact fireTableRedexOver_sound restRows
            (fun otherRule isInRest =>
              rowsAreInTable otherRule (.tail _ isInRest))
            fireEq

/-- ★ **Generic root firing completeness** — a specific row that fires
forces the walk to return `some` (the walk may return an earlier
overlapping row's reduct, hence `isSome` rather than the exact
reduct). -/
theorem fireTableRedexOver_complete {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {firingRule : IotaRuleDesc} {reduct : RawTerm scope}
    (firingFireEq :
      firingRule.fireAtRoot? generator payload children = some reduct) :
    (rows : List IotaRuleDesc) →
    firingRule ∈ rows →
    (fireTableRedexOver rows generator payload children).isSome = true
  | [], isRow => by cases isRow
  | rule :: restRows, isRow => by
      dsimp only [fireTableRedexOver]
      match headFireEq : rule.fireAtRoot? generator payload children with
      | some _ => rfl
      | none =>
          cases isRow with
          | head =>
              rw [firingFireEq] at headFireEq
              injection headFireEq
          | tail _ isInRest =>
              exact fireTableRedexOver_complete firingFireEq restRows
                isInRest

/-- The table detection predicate: some row fires (and produces a
reduct).  Detection and firing coincide by definition. -/
def hasTableRedexRootOver {scope : Nat} (rows : List IotaRuleDesc)
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) : Bool :=
  (fireTableRedexOver rows generator payload children).isSome

/-- The cheap Bool head detector over the whole table: some row's
eliminator key matches and its pattern fires. -/
def detectsHeadRedexRootOver {scope : Nat} (rows : List IotaRuleDesc)
    (generator : Generator)
    (children : RawTermChildren generator.binderShifts scope) : Bool :=
  rows.any (fun rule => rule.detectsHeadAtRoot generator children)

/-- A firing is head-detected by the cheap Bool detector — generic. -/
theorem fireTableRedexOver_isSome_imp_headDetected {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} :
    (rows : List IotaRuleDesc) →
    (fireTableRedexOver rows generator payload children).isSome = true →
    detectsHeadRedexRootOver rows generator children = true
  | [], fireSome => by
      dsimp only [fireTableRedexOver] at fireSome
      exact Bool.noConfusion fireSome
  | rule :: restRows, fireSome => by
      dsimp only [fireTableRedexOver] at fireSome
      dsimp only [detectsHeadRedexRootOver, List.any]
      match headFireEq : rule.fireAtRoot? generator payload children with
      | some headReduct =>
          have headDetected :
              rule.detectsHeadAtRoot generator children = true :=
            rule.fireAtRoot?_isSome_imp_detectsHeadAtRoot headFireEq
          rw [headDetected]
          rfl
      | none =>
          rw [headFireEq] at fireSome
          have restDetected :=
            fireTableRedexOver_isSome_imp_headDetected restRows fireSome
          dsimp only [detectsHeadRedexRootOver] at restDetected
          rw [restDetected]
          exact Bool.or_true _

/-! ## The canonical 18-row instantiation -/

/-- Root firing at the canonical table. -/
def StepTable.fireRoot {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    Option (RawTerm scope) :=
  fireTableRedexOver iotaRuleTable generator payload children

/-- ★ Canonical root firing soundness: a produced reduct is a
`StepTable` step. -/
theorem StepTable.fireRoot_sound {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq : StepTable.fireRoot generator payload children = some reduct) :
    StepTable (.mkGen generator payload children) reduct :=
  fireTableRedexOver_sound iotaRuleTable (fun _ isRow => isRow) fireEq

/-- Canonical root detection. -/
def StepTable.hasRedexRoot {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) : Bool :=
  hasTableRedexRootOver iotaRuleTable generator payload children

/-- Canonical cheap head detection. -/
def StepTable.detectsHeadRoot {scope : Nat} (generator : Generator)
    (children : RawTermChildren generator.binderShifts scope) : Bool :=
  detectsHeadRedexRootOver iotaRuleTable generator children

/-- A canonical firing is head-detected. -/
theorem StepTable.fireRoot_isSome_imp_detectsHeadRoot {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (fireSome :
      (StepTable.fireRoot generator payload children).isSome = true) :
    StepTable.detectsHeadRoot generator children = true :=
  fireTableRedexOver_isSome_imp_headDetected iotaRuleTable fireSome

/-- Legacy-table root firing — the 17 rows that have a bespoke kernel
`Step` constructor (the full table additionally carries the
table-native endpoint-β `pathBeta`, which has no `Step`). -/
def StepTable.fireRootLegacy {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    Option (RawTerm scope) :=
  fireTableRedexOver legacyIotaRuleTable generator payload children

end FX1Poly.Core
