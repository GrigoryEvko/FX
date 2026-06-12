import FX1Poly.Core.IotaTableOrthogonality
import FX1Poly.Core.EtaTableOrthogonality

/-! # FX1Poly/Core/RewriteRowOverlap — RW-3: the unified (iota × eta) row-pair overlap checker

The orthogonality of the kernel's β+ι+η presentation is, before this file, certified by THREE
SEPARATE notions of "two rows could rewrite the same root":

  * ι × ι — distinct `IotaRuleDesc.rootKey` (`IotaTableOrthogonality.allRootKeysDistinct`,
    IOTA-T5): same eliminator + slot + scrutinee head means the SAME row;
  * η × η — distinct `EtaRuleDesc.introGenerator` (`EtaTableOrthogonality.allIntroRootsDistinct`,
    ETA-T4): at most one η-rule per former;
  * ι × η — the cross-table `etaIntroRootsAvoidIotaElimRoots` (ETA-T4): no η-intro former is any
    ι-eliminator, so every η/ι overlap is parent-child, never root/root.

This file folds those three into ONE decidable predicate `RewriteRow.overlaps?` over a heterogeneous
row type `RewriteRow` (`.iotaRow` ‖ `.etaRow`), and ONE pairwise checker `allRewriteRowsDisjoint`
over the combined `rewriteBundle`.  The single canonical pin `fxRewriteBundle_rowsDisjoint` mentions
BOTH canonical tables, so a new row in EITHER re-elaborates it — the "re-decides on table growth"
guarantee.  It is the lightweight precursor to the RW-5 `RuleTableBundle`.

## Zero-axiom verification

`if _ = _ then false else true` over `DecidableEq` (Generator / the `rootKey` product), the shipped
`listForall` Bool fold (no `List.all` simp), and a single concrete `rfl` for the canonical pin — the
same idiom as `allRootKeysDistinct` / `etaRuleTable_isWf`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditRewriteRowOverlap.lean`.
-/

namespace FX1Poly.Core

/-! ## The heterogeneous rewrite row -/

/-- A row of the combined β+ι+η rewrite presentation: an ι-rule descriptor or an η-rule descriptor.
The lightweight precursor to the RW-5 `RuleTableBundle`. -/
inductive RewriteRow where
  | iotaRow : IotaRuleDesc → RewriteRow
  | etaRow : EtaRuleDesc → RewriteRow

/-- The generator at whose ROOT the row rewrites: an ι-row eliminates its `elimGenerator`, an η-row
contracts a cell headed by its `introGenerator`. -/
def RewriteRow.rootHead : RewriteRow → Generator
  | .iotaRow rule => rule.elimGenerator
  | .etaRow rule => rule.introGenerator

/-! ## The unified overlap test -/

/-- ★ **The generic decidable row-pair overlap test** — do two rows potentially rewrite at the SAME
root cell?  One predicate replacing the three bespoke notions:

  * ι × ι : identical `rootKey` (same eliminator + primary slot + primary head; distinct keys ⇒
    disjoint sources by IOTA-T5);
  * η × η : the same intro former (at most one η-rule per former by ETA-T4);
  * ι × η : the ι-eliminator IS the η-intro former — the only root/root collision a mixed pair can
    have (ETA-T4 forbids it, classifying every η/ι overlap as parent-child). -/
def RewriteRow.overlaps? : RewriteRow → RewriteRow → Bool
  | .iotaRow firstRule, .iotaRow secondRule =>
      if firstRule.rootKey = secondRule.rootKey then true else false
  | .etaRow firstRule, .etaRow secondRule =>
      if firstRule.introGenerator = secondRule.introGenerator then true else false
  | .iotaRow iotaRule, .etaRow etaRule =>
      if iotaRule.elimGenerator = etaRule.introGenerator then true else false
  | .etaRow etaRule, .iotaRow iotaRule =>
      if iotaRule.elimGenerator = etaRule.introGenerator then true else false

/-- Two rows are root-disjoint when they do not overlap. -/
def rewriteRowsDisjoint (firstRow secondRow : RewriteRow) : Bool :=
  if firstRow.overlaps? secondRow = true then false else true

/-- Every row is disjoint from every LATER row — the pairwise-over-tail fold, mirroring
`allRootKeysDistinct`.  A row is never compared with itself, so a single row needs no self-disjoint
side condition. -/
def allRewriteRowsDisjoint : List RewriteRow → Bool
  | [] => true
  | row :: restRows =>
      listForall (rewriteRowsDisjoint row) restRows && allRewriteRowsDisjoint restRows

/-! ## The combined bundle -/

/-- The combined β+ι+η presentation as one row list: the ι-rows then the η-rows. -/
def rewriteBundle (iotaTable : List IotaRuleDesc) (etaTable : List EtaRuleDesc) :
    List RewriteRow :=
  iotaTable.map RewriteRow.iotaRow ++ etaTable.map RewriteRow.etaRow

/-! ## The canonical certificate (the audit guard spanning BOTH tables) -/

/-- ★ The canonical bundle (18 ι-rows + 5 η-rows) is pairwise root-disjoint under the unified
checker — one `rfl` over BOTH canonical tables, so a new row in either re-decides it. -/
theorem fxRewriteBundle_rowsDisjoint :
    allRewriteRowsDisjoint (rewriteBundle iotaRuleTable etaRuleTable) = true := rfl

/-! ## Increment 2 — operational soundness: the disjoint bundle is root-deterministic

The overlap checker above is a STATIC certificate; this section discharges its OPERATIONAL meaning.
`RewriteRow.rewriteAtRoot?` dispatches a root rewrite — an ι-row FIRES (consuming payload +
children), an η-row CONTRACTS (consuming children, ignoring the payload) — and
`rewriteBundle_rootDeterministic` proves that ANY two bundle rows firing on the SAME cell agree on
the reduct.  The three shipped orthogonality theorems supply the cases: ι×ι via
`WfIotaTable.rootFiringDeterministic`, η×η via `WfEtaTable.rootContractionDeterministic`, and the
mixed ι×η case is VACUOUS — `fireAtRoot?` pins the head to an ι-eliminator while `contractAtRoot?`
pins it to an η-intro former, and `WfEtaTable.introRootsAreNotIotaElims` forbids those from
coinciding.  This is the local confluence (at the root) the disjointness certificate guarantees. -/

/-- Unified root rewrite over a heterogeneous bundle row: an ι-row fires (using the payload), an
η-row contracts (ignoring the payload). -/
def RewriteRow.rewriteAtRoot? (row : RewriteRow) {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) : Option (RawTerm scope) :=
  match row with
  | .iotaRow rule => rule.fireAtRoot? generator payload children
  | .etaRow rule => rule.contractAtRoot? generator children

/-- The ι-row dispatch is exactly the underlying `fireAtRoot?` — a definitional unfold. -/
theorem RewriteRow.rewriteAtRoot?_iotaRow (rule : IotaRuleDesc) {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    (RewriteRow.iotaRow rule).rewriteAtRoot? generator payload children
      = rule.fireAtRoot? generator payload children := rfl

/-- The η-row dispatch is exactly the underlying `contractAtRoot?` — a definitional unfold. -/
theorem RewriteRow.rewriteAtRoot?_etaRow (rule : EtaRuleDesc) {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    (RewriteRow.etaRow rule).rewriteAtRoot? generator payload children
      = rule.contractAtRoot? generator children := rfl

/-- Membership in an append splits to membership in one side — zero-axiom via the `List.Mem` ctors
(no `mem_append` iff lemma). -/
theorem mem_appendOr {elementType : Type} {firstList secondList : List elementType}
    {element : elementType} (isMember : element ∈ firstList ++ secondList) :
    element ∈ firstList ∨ element ∈ secondList := by
  induction firstList with
  | nil => exact Or.inr isMember
  | cons _ _ inductiveHypothesis =>
      cases isMember with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ restMembership =>
          cases inductiveHypothesis restMembership with
          | inl inFirst => exact Or.inl (List.Mem.tail _ inFirst)
          | inr inSecond => exact Or.inr inSecond

/-- A row in the ι-row image of a table came from an ι-table entry — zero-axiom via `List.Mem`. -/
theorem mem_mapIotaRow {iotaTable : List IotaRuleDesc} {row : RewriteRow}
    (isMember : row ∈ iotaTable.map RewriteRow.iotaRow) :
    ∃ rule, rule ∈ iotaTable ∧ row = RewriteRow.iotaRow rule := by
  induction iotaTable with
  | nil => cases isMember
  | cons headRule _ inductiveHypothesis =>
      cases isMember with
      | head => exact ⟨headRule, List.Mem.head _, rfl⟩
      | tail _ restMembership =>
          obtain ⟨rule, ruleMember, rowEquals⟩ := inductiveHypothesis restMembership
          exact ⟨rule, List.Mem.tail _ ruleMember, rowEquals⟩

/-- A row in the η-row image of a table came from an η-table entry — zero-axiom via `List.Mem`. -/
theorem mem_mapEtaRow {etaTable : List EtaRuleDesc} {row : RewriteRow}
    (isMember : row ∈ etaTable.map RewriteRow.etaRow) :
    ∃ rule, rule ∈ etaTable ∧ row = RewriteRow.etaRow rule := by
  induction etaTable with
  | nil => cases isMember
  | cons headRule _ inductiveHypothesis =>
      cases isMember with
      | head => exact ⟨headRule, List.Mem.head _, rfl⟩
      | tail _ restMembership =>
          obtain ⟨rule, ruleMember, rowEquals⟩ := inductiveHypothesis restMembership
          exact ⟨rule, List.Mem.tail _ ruleMember, rowEquals⟩

/-- Every bundle row is classified: an ι-row drawn from the ι-table, or an η-row from the η-table. -/
theorem mem_rewriteBundle {iotaTable : List IotaRuleDesc} {etaTable : List EtaRuleDesc}
    {row : RewriteRow} (rowIsMember : row ∈ rewriteBundle iotaTable etaTable) :
    (∃ rule, rule ∈ iotaTable ∧ row = RewriteRow.iotaRow rule) ∨
    (∃ rule, rule ∈ etaTable ∧ row = RewriteRow.etaRow rule) := by
  dsimp only [rewriteBundle] at rowIsMember
  cases mem_appendOr rowIsMember with
  | inl inIotaImage => exact Or.inl (mem_mapIotaRow inIotaImage)
  | inr inEtaImage => exact Or.inr (mem_mapEtaRow inEtaImage)

/-- ★ **Operational soundness of the disjoint bundle**: in a well-formed bundle (well-formed ι-table
+ well-formed η-table over that same ι-table), any two rows that both rewrite the SAME root cell
produce the SAME reduct.  ι×ι and η×η are the two shipped determinism theorems; the mixed ι×η case
is impossible because an ι-eliminator head is never an η-intro former. -/
theorem rewriteBundle_rootDeterministic {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc}
    (iotaTableIsWf : WfIotaTable iotaTable)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    {firstRow secondRow : RewriteRow}
    (firstIsRow : firstRow ∈ rewriteBundle iotaTable etaTable)
    (secondIsRow : secondRow ∈ rewriteBundle iotaTable etaTable)
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {firstReduct secondReduct : RawTerm scope}
    (firstRewrites : firstRow.rewriteAtRoot? generator payload children = some firstReduct)
    (secondRewrites : secondRow.rewriteAtRoot? generator payload children = some secondReduct) :
    firstReduct = secondReduct := by
  cases mem_rewriteBundle firstIsRow with
  | inl firstIota =>
      obtain ⟨firstRule, firstRuleMember, firstRowEquals⟩ := firstIota
      subst firstRowEquals
      rw [RewriteRow.rewriteAtRoot?_iotaRow] at firstRewrites
      cases mem_rewriteBundle secondIsRow with
      | inl secondIota =>
          obtain ⟨secondRule, secondRuleMember, secondRowEquals⟩ := secondIota
          subst secondRowEquals
          rw [RewriteRow.rewriteAtRoot?_iotaRow] at secondRewrites
          exact iotaTableIsWf.rootFiringDeterministic firstRuleMember secondRuleMember
            firstRewrites secondRewrites
      | inr secondEta =>
          obtain ⟨secondRule, secondRuleMember, secondRowEquals⟩ := secondEta
          subst secondRowEquals
          rw [RewriteRow.rewriteAtRoot?_etaRow] at secondRewrites
          have firstPinsElim : generator = firstRule.elimGenerator :=
            IotaRuleDesc.fireAtRoot?_pinsElim firstRewrites
          have secondPinsIntro : generator = secondRule.introGenerator :=
            EtaRuleDesc.contractAtRoot?_pinsIntro secondRewrites
          exact absurd (secondPinsIntro.symm.trans firstPinsElim)
            (etaTableIsWf.introRootsAreNotIotaElims secondRuleMember firstRuleMember)
  | inr firstEta =>
      obtain ⟨firstRule, firstRuleMember, firstRowEquals⟩ := firstEta
      subst firstRowEquals
      rw [RewriteRow.rewriteAtRoot?_etaRow] at firstRewrites
      cases mem_rewriteBundle secondIsRow with
      | inl secondIota =>
          obtain ⟨secondRule, secondRuleMember, secondRowEquals⟩ := secondIota
          subst secondRowEquals
          rw [RewriteRow.rewriteAtRoot?_iotaRow] at secondRewrites
          have firstPinsIntro : generator = firstRule.introGenerator :=
            EtaRuleDesc.contractAtRoot?_pinsIntro firstRewrites
          have secondPinsElim : generator = secondRule.elimGenerator :=
            IotaRuleDesc.fireAtRoot?_pinsElim secondRewrites
          exact absurd (firstPinsIntro.symm.trans secondPinsElim)
            (etaTableIsWf.introRootsAreNotIotaElims firstRuleMember secondRuleMember)
      | inr secondEta =>
          obtain ⟨secondRule, secondRuleMember, secondRowEquals⟩ := secondEta
          subst secondRowEquals
          rw [RewriteRow.rewriteAtRoot?_etaRow] at secondRewrites
          exact etaTableIsWf.rootContractionDeterministic firstRuleMember secondRuleMember
            firstRewrites secondRewrites

/-- ★ The canonical bundle is root-deterministic — the operational payoff of the disjointness pin,
instantiated at the kernel's own ι/η tables.  Mentions BOTH canonical well-formedness certificates,
so a new row in either table re-checks it. -/
theorem fxRewriteBundle_rootDeterministic
    {firstRow secondRow : RewriteRow}
    (firstIsRow : firstRow ∈ rewriteBundle iotaRuleTable etaRuleTable)
    (secondIsRow : secondRow ∈ rewriteBundle iotaRuleTable etaRuleTable)
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {firstReduct secondReduct : RawTerm scope}
    (firstRewrites : firstRow.rewriteAtRoot? generator payload children = some firstReduct)
    (secondRewrites : secondRow.rewriteAtRoot? generator payload children = some secondReduct) :
    firstReduct = secondReduct :=
  rewriteBundle_rootDeterministic iotaRuleTable_isWf etaRuleTable_isWf
    firstIsRow secondIsRow firstRewrites secondRewrites

end FX1Poly.Core
