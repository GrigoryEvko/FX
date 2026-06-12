import FX1Poly.Core.EtaRuleTable
import FX1Poly.Core.TableParallelStabilitySubstrate

/-! # EtaTableOrthogonality — ETA-T4: the WfEtaTable certificate +
the CROSS-table disjointness

The eta twin of the IOTA-T5 orthogonality certificate, with one
genuinely new ingredient: a check spanning BOTH rule tables.  Decidable
Bool checkers over the shipped `listForall` fold:

  * `allIntroRootsDistinct` — at most one eta row per former (the eta
    root key is just the intro generator);
  * `allRawRowsHaveObservation` — every raw-tier row observes
    SOMETHING (a zero-observation raw row would contract EVERY cell of
    its intro head);
  * `allObservationSlotsWithinArity` — every observation's slots exist
    in the generator table's binder-shift lists with the declared
    shifts (`introChildSlot` at the binder depth; `coreSlot` and the
    fresh slots at shift zero inside the observer);
  * ★ `etaIntroRootsAvoidIotaElimRoots` — the CROSS-table check: no
    eta intro root is any iota row's eliminator.  This classifies
    every eta/iota overlap as parent-child only (the ETA-T5 input).
    The canonical pin mentions BOTH tables in one `rfl`, so a new row
    in EITHER forces re-elaboration.

Bundled as `WfEtaTable`, pinned for the canonical 5-row eta table
against the canonical 18-row iota table.  Then root determinism via
the `contractAtRoot?` dispatcher (the eta analog of
`fireAtRoot?`/`rootFiringDeterministic`): two member rows of a wf
table contracting the same cell are the SAME row with the same core.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaTableOrthogonality.lean`. -/

namespace FX1Poly.Core

/-! ## The decidable well-formedness checkers -/

/-- Two eta rows have distinct intro roots. -/
def introRootsDiffer (firstRule secondRule : EtaRuleDesc) : Bool :=
  if firstRule.introGenerator = secondRule.introGenerator then false
  else true

/-- All intro roots in the table are pairwise distinct — at most one
eta rule per former. -/
def allIntroRootsDistinct : List EtaRuleDesc → Bool
  | [] => true
  | rule :: restRows =>
      listForall (introRootsDiffer rule) restRows
        && allIntroRootsDistinct restRows

/-- A raw-tier row observes something; typed-tier rows are exempt (they
never fire raw). -/
def rawRowHasObservation (rule : EtaRuleDesc) : Bool :=
  if rule.requiresTypedFiring = true then true
  else
    match rule.observations with
    | [] => false
    | _ :: _ => true

/-- Every raw-tier row has a non-empty observation list. -/
def allRawRowsHaveObservation (table : List EtaRuleDesc) : Bool :=
  listForall rawRowHasObservation table

/-- One observation's slots exist in the generator table's binder-shift
lists with the declared shifts: the intro child slot sits at the
observation's binder depth, and the core and fresh slots sit at shift
zero inside the observer head. -/
def observationSlotsWithinArity (introGenerator : Generator)
    (spec : EtaObservationSpec) : Bool :=
  (match listEntryAt? introGenerator.binderShifts spec.introChildSlot with
    | some declaredShift =>
        if declaredShift = spec.binderDepth then true else false
    | none => false)
  && (match listEntryAt? spec.observerHead.binderShifts spec.coreSlot with
    | some coreShift => if coreShift = 0 then true else false
    | none => false)
  && listForall
      (fun freshSlot =>
        match listEntryAt? spec.observerHead.binderShifts freshSlot with
        | some freshShift => if freshShift = 0 then true else false
        | none => false)
      spec.freshVarSlots

/-- Every observation of a row respects the arities. -/
def rowObservationSlotsWithinArity (rule : EtaRuleDesc) : Bool :=
  listForall (observationSlotsWithinArity rule.introGenerator)
    rule.observations

/-- Every row's observations respect the generator table's arities. -/
def allObservationSlotsWithinArity (table : List EtaRuleDesc) : Bool :=
  listForall rowObservationSlotsWithinArity table

/-- Two observations of one row watch distinct intro slots. -/
def observationSlotsDiffer (firstSpec secondSpec : EtaObservationSpec) :
    Bool :=
  if firstSpec.introChildSlot = secondSpec.introChildSlot then false
  else true

/-- A row's observations watch pairwise-distinct intro slots — the
core-replacement chain replaces one observation without disturbing its
siblings. -/
def rowObservationSlotsDistinct : List EtaObservationSpec → Bool
  | [] => true
  | spec :: restSpecs =>
      listForall (observationSlotsDiffer spec) restSpecs
        && rowObservationSlotsDistinct restSpecs

/-- Every row's observations watch pairwise-distinct intro slots. -/
def allObservationSlotsDistinct (table : List EtaRuleDesc) : Bool :=
  listForall (fun rule => rowObservationSlotsDistinct rule.observations)
    table

/-- ★ **The cross-table check**: no eta intro root is any iota row's
eliminator — decided against the iota table, so every eta/iota overlap
is parent-child only (never a root/root collision). -/
def etaIntroRootsAvoidIotaElimRoots (etaTable : List EtaRuleDesc)
    (someIotaTable : List IotaRuleDesc) : Bool :=
  listForall
    (fun etaRule =>
      listForall
        (fun iotaElimRoot =>
          if etaRule.introGenerator = iotaElimRoot then false else true)
        (tableElimRoots someIotaTable))
    etaTable

/-- ★ The well-formed eta table predicate, certified AGAINST an iota
table: distinct intro roots, observing raw rows, arity-respecting
observation slots, and the cross-table root disjointness.  Re-decides
on every new row in EITHER table. -/
structure WfEtaTable (etaTable : List EtaRuleDesc)
    (someIotaTable : List IotaRuleDesc) : Prop where
  introRootsAreDistinct : allIntroRootsDistinct etaTable = true
  rawRowsHaveObservations : allRawRowsHaveObservation etaTable = true
  observationSlotsRespectArity :
    allObservationSlotsWithinArity etaTable = true
  observationSlotsAreDistinct :
    allObservationSlotsDistinct etaTable = true
  introRootsAvoidIotaElimRoots :
    etaIntroRootsAvoidIotaElimRoots etaTable someIotaTable = true

/-! ## The canonical certificate (the audit guard spanning BOTH tables) -/

/-- ★ The canonical 5-row eta table is well-formed against the
canonical 18-row iota table — every check closes by `rfl`-decidable
enumeration.  This single theorem mentions BOTH canonical tables: a new
row in either forces this certificate to re-decide. -/
theorem etaRuleTable_isWf : WfEtaTable etaRuleTable iotaRuleTable :=
  { introRootsAreDistinct := rfl
    rawRowsHaveObservations := rfl
    observationSlotsRespectArity := rfl
    observationSlotsAreDistinct := rfl
    introRootsAvoidIotaElimRoots := rfl }

/-! ## Pairwise extraction -/

/-- Intro-root distinctness forces VALUE equality: two member rows with
the same intro root are the same row. -/
theorem allIntroRootsDistinct_memUnique :
    (table : List EtaRuleDesc) → allIntroRootsDistinct table = true →
    {firstRule secondRule : EtaRuleDesc} →
    firstRule ∈ table → secondRule ∈ table →
    firstRule.introGenerator = secondRule.introGenerator →
    firstRule = secondRule
  | [], _, _, _, firstIsRow, _, _ => by cases firstIsRow
  | headRule :: restRows, distinct, firstRule, secondRule,
      firstIsRow, secondIsRow, introsAgree => by
      dsimp only [allIntroRootsDistinct] at distinct
      obtain ⟨headDiffers, restDistinct⟩ := andEqTrueSplit distinct
      cases firstIsRow with
      | head =>
          cases secondIsRow with
          | head => rfl
          | tail _ secondInRest =>
              exfalso
              have differs :=
                listForall_mem restRows headDiffers secondInRest
              dsimp only [introRootsDiffer] at differs
              rw [if_pos introsAgree] at differs
              exact Bool.noConfusion differs
      | tail _ firstInRest =>
          cases secondIsRow with
          | head =>
              exfalso
              have differs :=
                listForall_mem restRows headDiffers firstInRest
              dsimp only [introRootsDiffer] at differs
              rw [if_pos introsAgree.symm] at differs
              exact Bool.noConfusion differs
          | tail _ secondInRest =>
              exact allIntroRootsDistinct_memUnique restRows restDistinct
                firstInRest secondInRest introsAgree

/-- ★ **Cross-table rigidity, pairwise**: in a well-formed eta table,
no member row's intro root is any iota member row's eliminator — THE
ETA-T5 input classifying every eta/iota overlap as parent-child. -/
theorem WfEtaTable.introRootsAreNotIotaElims
    {etaTable : List EtaRuleDesc} {someIotaTable : List IotaRuleDesc}
    (tableIsWf : WfEtaTable etaTable someIotaTable)
    {etaRule : EtaRuleDesc} (etaIsRow : etaRule ∈ etaTable)
    {iotaRule : IotaRuleDesc} (iotaIsRow : iotaRule ∈ someIotaTable) :
    etaRule.introGenerator ≠ iotaRule.elimGenerator := by
  intro rootsCollide
  have rowChecks :=
    listForall_mem etaTable tableIsWf.introRootsAvoidIotaElimRoots
      etaIsRow
  have verdict :=
    listForall_mem (tableElimRoots someIotaTable) rowChecks
      (tableElimRoots_memOfRow iotaIsRow)
  rw [if_pos rootsCollide] at verdict
  exact Bool.noConfusion verdict

/-! ## The root dispatcher -/

/-- Generator-dispatched root contraction — the eta analog of
`fireAtRoot?`: contract when the cell's head is this rule's intro
root. -/
def EtaRuleDesc.contractAtRoot? (rule : EtaRuleDesc) {scope : Nat}
    (generator : Generator)
    (children : RawTermChildren generator.binderShifts scope) :
    Option (RawTerm scope) :=
  if isIntroHead : generator = rule.introGenerator then
    rule.contractsOn? (isIntroHead ▸ children)
  else none

/-- A root contraction pins the intro head: the cell's generator IS the
rule's intro root. -/
theorem EtaRuleDesc.contractAtRoot?_pinsIntro {rule : EtaRuleDesc}
    {scope : Nat} {generator : Generator}
    {children : RawTermChildren generator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : rule.contractAtRoot? generator children = some core) :
    generator = rule.introGenerator := by
  dsimp only [EtaRuleDesc.contractAtRoot?] at contracts
  by_cases isIntroHead : generator = rule.introGenerator
  case pos => exact isIntroHead
  case neg =>
      rw [dif_neg isIntroHead] at contracts
      injection contracts

/-- A rule's `contractAtRoot?` at its OWN intro root is exactly its
`contractsOn?` (the generator-equality transport vanishes at `rfl`). -/
theorem EtaRuleDesc.contractAtRoot?_atOwnIntro (rule : EtaRuleDesc)
    {scope : Nat}
    (introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope) :
    rule.contractAtRoot? rule.introGenerator introChildren
      = rule.contractsOn? introChildren := by
  dsimp only [EtaRuleDesc.contractAtRoot?]
  rw [dif_pos rfl]

/-! ## Root determinism — the keystone -/

/-- ★ **Root-contraction determinism**: any two rows of a well-formed
eta table that both contract the same raw cell are the SAME row
(intro-root distinctness) producing the SAME core (`contractsOn?` is a
function) — the eta analog of `rootFiringDeterministic`. -/
theorem WfEtaTable.rootContractionDeterministic
    {etaTable : List EtaRuleDesc} {someIotaTable : List IotaRuleDesc}
    (tableIsWf : WfEtaTable etaTable someIotaTable)
    {firstRule secondRule : EtaRuleDesc}
    (firstIsRow : firstRule ∈ etaTable)
    (secondIsRow : secondRule ∈ etaTable)
    {scope : Nat} {generator : Generator}
    {children : RawTermChildren generator.binderShifts scope}
    {firstCore secondCore : RawTerm scope}
    (firstContracts :
      firstRule.contractAtRoot? generator children = some firstCore)
    (secondContracts :
      secondRule.contractAtRoot? generator children = some secondCore) :
    firstCore = secondCore := by
  have introsAgree :
      firstRule.introGenerator = secondRule.introGenerator :=
    (EtaRuleDesc.contractAtRoot?_pinsIntro firstContracts).symm.trans
      (EtaRuleDesc.contractAtRoot?_pinsIntro secondContracts)
  have rulesAgree : firstRule = secondRule :=
    allIntroRootsDistinct_memUnique etaTable
      tableIsWf.introRootsAreDistinct firstIsRow secondIsRow introsAgree
  subst rulesAgree
  exact Option.some.inj (firstContracts.symm.trans secondContracts)

end FX1Poly.Core
