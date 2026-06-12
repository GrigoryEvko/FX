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

end FX1Poly.Core
