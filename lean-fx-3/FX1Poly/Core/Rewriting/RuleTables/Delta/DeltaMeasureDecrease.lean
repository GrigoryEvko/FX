import FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaRuleTable
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationEta

/-! # DeltaMeasureDecrease — RW-4: δ-measure invariance under weakening + any-scope decrease

The δ-constant-occurrence measure `RawTerm.deltaConstantCount` (the honest
SN tier of `DeltaRuleTable.lean`) counts table-constant-headed leaves —
purely a function of the GENERATOR structure, blind to de Bruijn indices.
A δ-rule fires INSIDE a scope-`n` term and rewrites the constant leaf to
its definiens WEAKENED to scope `n` (`RawTerm.weakenClosed`).  To lift the
scope-0 measure decrease (`hyperrealDeltaStep_strictlyDecreasesCount`) to
ARBITRARY scope we need: weakening a closed term does not change its
constant count.

This module proves exactly that — `deltaConstantCount` is invariant under
`rename` (hence `weaken`, hence `weakenClosed`) — and harvests the
any-scope measure decrease.  The rename-invariance is the structural
substrate that makes δ-SN reasoning scope-uniform: it is the analogue of
`RawTerm.size_rename` (a renaming never duplicates or drops node structure,
so any generator-only measure is rename-stable), specialised to the δ
measure.

## Zero-axiom

The rename-invariance mirrors `RawTerm.size_rename` (same fold-dispatcher
case split, `propext`-clean); `weaken`/`weakenClosed` are the renaming
special case + a structural induction on the scope.  The any-scope decrease
closes by `Nat.succ_pos`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Core

open FX1Poly.Tier0.Syntax

/-! ## `deltaConstantCount` is invariant under renaming

Renaming rebuilds variables as variables and every other generator as the
SAME generator with renamed children — so the constant count, which reads
only the generators, is preserved.  Same proof shape as
`RawTerm.size_rename`. -/

mutual

/-- Renaming preserves the δ-constant count of a term. -/
theorem RawTerm.deltaConstantCount_rename {sourceScope targetScope : Nat}
    (constants : List Generator)
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.deltaConstantCount constants (RawTerm.rename someRenaming sourceTerm)
      = RawTerm.deltaConstantCount constants sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
      by_cases hVar : someGenerator = .gen_var
      · subst hVar
        cases someChildren
        rfl
      · dsimp only [RawTerm.rename, fold]
        simp only [dif_neg hVar]
        rw [GenAlgebra.canonical_algebra_eq_mkGen]
        dsimp only [RawTerm.deltaConstantCount]
        rw [← RawTermChildren.rename_eq_foldChildren someRenaming someChildren]
        rw [RawTermChildren.deltaConstantCount_rename constants someRenaming
          someChildren]

/-- Renaming preserves the δ-constant count of a child spine. -/
theorem RawTermChildren.deltaConstantCount_rename {sourceScope targetScope : Nat}
    {binderShifts : List Nat} (constants : List Generator)
    (someRenaming : RawRenaming sourceScope targetScope)
    (someChildren : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.deltaConstantCount constants
        (RawTermChildren.rename someRenaming someChildren)
      = RawTermChildren.deltaConstantCount constants someChildren := by
  match binderShifts, someChildren with
  | [], .childNil => rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTerm.deltaConstantCount constants
            (RawTerm.rename (iterateLiftRaw someRenaming headShift) childHead)
          + RawTermChildren.deltaConstantCount constants
            (RawTermChildren.rename someRenaming childTail)
        = RawTerm.deltaConstantCount constants childHead
          + RawTermChildren.deltaConstantCount constants childTail
      rw [RawTerm.deltaConstantCount_rename constants
        (iterateLiftRaw someRenaming headShift) childHead]
      rw [RawTermChildren.deltaConstantCount_rename constants someRenaming
        childTail]

end

/-! ## Weakening special cases -/

/-- Single-binder weakening preserves the δ-constant count. -/
theorem RawTerm.deltaConstantCount_weaken {scope : Nat} (constants : List Generator)
    (sourceTerm : RawTerm scope) :
    RawTerm.deltaConstantCount constants (RawTerm.weaken sourceTerm)
      = RawTerm.deltaConstantCount constants sourceTerm := by
  rw [RawTerm.weaken_eq_rename]
  exact RawTerm.deltaConstantCount_rename constants RawRenaming.weaken sourceTerm

/-- **Weakening a closed term to any scope preserves its δ-constant count.**
The scope-uniformity lemma: re-instantiating a closed definiens at firing
scope `scope` does not change how many table constants it carries. -/
theorem RawTerm.deltaConstantCount_weakenClosed (constants : List Generator)
    (scope : Nat) (closed : RawTerm 0) :
    RawTerm.deltaConstantCount constants (RawTerm.weakenClosed scope closed)
      = RawTerm.deltaConstantCount constants closed := by
  induction scope with
  | zero => rfl
  | succ predScope ih =>
      show RawTerm.deltaConstantCount constants
          (RawTerm.weaken (RawTerm.weakenClosed predScope closed)) = _
      rw [RawTerm.deltaConstantCount_weaken]
      exact ih

/-! ## The any-scope measure decrease

`hyperrealDeltaStep_strictlyDecreasesCount` (`DeltaRuleTable.lean`) is the
scope-0 instance; the `weakenClosed` invariance lifts it to ANY firing
scope, the form the δ-SN argument actually consumes (a δ-rule fires inside
a scope-`n` program). -/

/-- **★ The acyclic `gen_hyperreal ↝ unit` δ step strictly decreases the
constant count at EVERY scope.**  At firing scope `scope` the reduct is
`unit` weakened to `scope` (count 0, by the `weakenClosed` invariance) while
the redex cell carries one constant occurrence — the scope-uniform measure
decrease that powers δ-SN on the acyclic fragment. -/
theorem hyperrealDeltaStep_strictlyDecreasesCount_anyScope {scope : Nat} :
    RawTerm.deltaConstantCount hyperrealConstants
        (RawTerm.weakenClosed scope unitDefiniens)
      < RawTerm.deltaConstantCount hyperrealConstants
        (.mkGen .gen_hyperreal () .childNil : RawTerm scope) := by
  rw [RawTerm.deltaConstantCount_weakenClosed]
  exact Nat.succ_pos 0

end FX1Poly.Core
