import FX1Poly.Core.TableReduceOnce

/-! # IotaTableHonesty — IOTA-T9: reduction-rule honesty DERIVED from
the table

The honesty seam of the canonicality flip: "which generators have a
reduction rule" stops being folklore and becomes a LOOKUP —
`Generator.hasReductionRule generator = (iotaRuleDescOf generator).isSome`,
with `iotaRuleDescOf` the first-matching-row walk over `iotaRuleTable`.
Adding an iota rule updates the honesty ledger automatically; a
generator the table does not eliminate is PROVABLY rule-free.

* `iotaRuleDescOfOver` / `iotaRuleDescOf` — the row lookup by
  eliminator head (hand-rolled walk; core `List.find?` lemmas are
  unaudited for axioms);
* inversion + completeness — the lookup succeeds EXACTLY when some row
  eliminates the head;
* `Generator.hasReductionRule` + the existential characterization;
* per-head pins: the eliminator heads (β, endpoint-β, the data/identity
  eliminators) are `true` by `rfl`; variables, binders, constructors,
  formers are `false` by `rfl`; **`gen_fixedPoint` is pinned `false`** —
  the kernel's deliberate no-general-fixpoint omission, now a checked
  fact rather than a comment;
* `fireTableRedexOver_someInversion` + root-firing honesty: a cell
  whose head has no reduction rule NEVER root-fires.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditIotaTableHonesty.lean`. -/

namespace FX1Poly.Core

/-! ## The row lookup -/

/-- Walk a row list, returning the first row whose eliminator head is
the given generator. -/
def iotaRuleDescOfOver : List IotaRuleDesc → Generator → Option IotaRuleDesc
  | [], _ => none
  | rule :: restRows, generator =>
      if rule.elimGenerator = generator then some rule
      else iotaRuleDescOfOver restRows generator

/-- The canonical-table row lookup by eliminator head. -/
def iotaRuleDescOf (generator : Generator) : Option IotaRuleDesc :=
  iotaRuleDescOfOver iotaRuleTable generator

/-- A successful lookup names a member row eliminating the head. -/
theorem iotaRuleDescOfOver_someInversion {generator : Generator}
    {rule : IotaRuleDesc} :
    (rows : List IotaRuleDesc) →
    iotaRuleDescOfOver rows generator = some rule →
    rule ∈ rows ∧ rule.elimGenerator = generator
  | [], lookupEq => nomatch lookupEq
  | headRule :: restRows, lookupEq => by
      dsimp only [iotaRuleDescOfOver] at lookupEq
      by_cases isElimHead : headRule.elimGenerator = generator
      · rw [if_pos isElimHead] at lookupEq
        obtain rfl := Option.some.inj lookupEq
        exact ⟨.head _, isElimHead⟩
      · rw [if_neg isElimHead] at lookupEq
        obtain ⟨isInRest, elimEq⟩ :=
          iotaRuleDescOfOver_someInversion restRows lookupEq
        exact ⟨.tail _ isInRest, elimEq⟩

/-- A member row eliminating the head forces the lookup to succeed (the
walk may return an EARLIER row with the same head, hence `isSome`). -/
theorem iotaRuleDescOfOver_complete {generator : Generator}
    {rule : IotaRuleDesc} (elimEq : rule.elimGenerator = generator) :
    (rows : List IotaRuleDesc) → rule ∈ rows →
    (iotaRuleDescOfOver rows generator).isSome = true
  | [], isRow => by cases isRow
  | headRule :: restRows, isRow => by
      dsimp only [iotaRuleDescOfOver]
      by_cases isElimHead : headRule.elimGenerator = generator
      · rw [if_pos isElimHead]
        rfl
      · rw [if_neg isElimHead]
        cases isRow with
        | head => exact absurd elimEq isElimHead
        | tail _ isInRest =>
            exact iotaRuleDescOfOver_complete elimEq restRows isInRest

/-! ## The honesty classifier -/

/-- **The reduction-rule honesty Bool, DERIVED from the table**: a
generator has a reduction rule exactly when some `iotaRuleTable` row
eliminates it. -/
def Generator.hasReductionRule (generator : Generator) : Bool :=
  (iotaRuleDescOf generator).isSome

/-- The existential characterization: `hasReductionRule` holds exactly
when some member row eliminates the head. -/
theorem Generator.hasReductionRule_iff_existsRow {generator : Generator} :
    Generator.hasReductionRule generator = true
      ↔ ∃ rule, rule ∈ iotaRuleTable ∧ rule.elimGenerator = generator := by
  constructor
  · intro hasRule
    dsimp only [Generator.hasReductionRule, iotaRuleDescOf] at hasRule
    cases lookupEq : iotaRuleDescOfOver iotaRuleTable generator with
    | none =>
        rw [lookupEq] at hasRule
        exact Bool.noConfusion hasRule
    | some rule =>
        obtain ⟨isRow, elimEq⟩ :=
          iotaRuleDescOfOver_someInversion iotaRuleTable lookupEq
        exact ⟨rule, isRow, elimEq⟩
  · intro existsRow
    obtain ⟨rule, isRow, elimEq⟩ := existsRow
    exact iotaRuleDescOfOver_complete elimEq iotaRuleTable isRow

/-! ## Per-head pins -/

/-- The eliminator heads have rules. -/
theorem hasReductionRule_app :
    Generator.hasReductionRule .gen_app = true := rfl
theorem hasReductionRule_pathApp :
    Generator.hasReductionRule .gen_pathApp = true := rfl
theorem hasReductionRule_boolElim :
    Generator.hasReductionRule .gen_boolElim = true := rfl
theorem hasReductionRule_fst :
    Generator.hasReductionRule .gen_fst = true := rfl
theorem hasReductionRule_snd :
    Generator.hasReductionRule .gen_snd = true := rfl
theorem hasReductionRule_natElim :
    Generator.hasReductionRule .gen_natElim = true := rfl
theorem hasReductionRule_natRec :
    Generator.hasReductionRule .gen_natRec = true := rfl
theorem hasReductionRule_listElim :
    Generator.hasReductionRule .gen_listElim = true := rfl
theorem hasReductionRule_optionMatch :
    Generator.hasReductionRule .gen_optionMatch = true := rfl
theorem hasReductionRule_eitherMatch :
    Generator.hasReductionRule .gen_eitherMatch = true := rfl
theorem hasReductionRule_idJ :
    Generator.hasReductionRule .gen_idJ = true := rfl
theorem hasReductionRule_idStrictRec :
    Generator.hasReductionRule .gen_idStrictRec = true := rfl

/-- **The IOTA-T10 ledger flips**: the three demo eliminators went
operationally LIVE by table rows alone. -/
theorem hasReductionRule_quotRec :
    Generator.hasReductionRule .gen_quotRec = true := rfl
theorem hasReductionRule_quotElim :
    Generator.hasReductionRule .gen_quotElim = true := rfl
theorem hasReductionRule_truncRec :
    Generator.hasReductionRule .gen_truncRec = true := rfl

/-- Variables, binders, constructors, formers have no rules. -/
theorem hasReductionRule_var :
    Generator.hasReductionRule .gen_var = false := rfl
theorem hasReductionRule_lam :
    Generator.hasReductionRule .gen_lam = false := rfl
theorem hasReductionRule_pathLam :
    Generator.hasReductionRule .gen_pathLam = false := rfl
theorem hasReductionRule_pair :
    Generator.hasReductionRule .gen_pair = false := rfl
theorem hasReductionRule_unit :
    Generator.hasReductionRule .gen_unit = false := rfl
theorem hasReductionRule_universeCode :
    Generator.hasReductionRule .gen_universeCode = false := rfl

/-- **The deliberate no-general-fixpoint omission, as a checked fact**:
`gen_fixedPoint` has NO reduction rule in the canonical table (the
kernel never promises an unfolding step for it — Omega stays
unconstructible through the table). -/
theorem hasReductionRule_fixedPoint :
    Generator.hasReductionRule .gen_fixedPoint = false := rfl

/-! ## Root-firing honesty -/

/-- A successful table-walk firing names a member row whose
`fireAtRoot?` produced the reduct. -/
theorem fireTableRedexOver_someInversion {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope} :
    (rows : List IotaRuleDesc) →
    fireTableRedexOver rows generator payload children = some reduct →
    ∃ rule, rule ∈ rows
      ∧ rule.fireAtRoot? generator payload children = some reduct
  | [], walkEq => nomatch walkEq
  | headRule :: restRows, walkEq => by
      dsimp only [fireTableRedexOver] at walkEq
      match headFireEq : headRule.fireAtRoot? generator payload children with
      | some headReduct =>
          rw [headFireEq] at walkEq
          obtain rfl := Option.some.inj walkEq
          exact ⟨headRule, .head _, headFireEq⟩
      | none =>
          rw [headFireEq] at walkEq
          obtain ⟨rule, isInRest, ruleFires⟩ :=
            fireTableRedexOver_someInversion restRows walkEq
          exact ⟨rule, .tail _ isInRest, ruleFires⟩

/-- A row's root firing pins the cell's head as its eliminator. -/
theorem IotaRuleDesc.fireAtRoot?_pinsElimHead {rule : IotaRuleDesc}
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq : rule.fireAtRoot? generator payload children = some reduct) :
    rule.elimGenerator = generator := by
  dsimp only [IotaRuleDesc.fireAtRoot?] at fireEq
  by_cases isElimHead : generator = rule.elimGenerator
  · exact isElimHead.symm
  · rw [dif_neg isElimHead] at fireEq
    exact nomatch fireEq

/-- **Root-firing honesty**: a cell whose head has no reduction rule
NEVER root-fires through the canonical table. -/
theorem hasReductionRule_false_blocksRootFiring {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isRuleFree : Generator.hasReductionRule generator = false)
    {reduct : RawTerm scope}
    (walkEq : fireTableRedexOver iotaRuleTable generator payload children
      = some reduct) :
    False := by
  obtain ⟨rule, isRow, ruleFires⟩ :=
    fireTableRedexOver_someInversion iotaRuleTable walkEq
  have hasRule : Generator.hasReductionRule generator = true :=
    Generator.hasReductionRule_iff_existsRow.mpr
      ⟨rule, isRow, rule.fireAtRoot?_pinsElimHead ruleFires⟩
  exact Bool.noConfusion (isRuleFree.symm.trans hasRule)

end FX1Poly.Core
