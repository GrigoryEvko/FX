import FX1Poly.Typed.CellConstructors
import FX1Poly.Typed.CellRenaming
import FX1Poly.Core.RawTermRename
import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermStrengthen
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstRenameCommute

/-! # FX1Poly/Typed/CellSubstitution — how `RawTerm.subst` acts on the typing cells

The pure-`RawTerm` substitution substrate: the per-cell computation rules for how
a substitution acts on the kernel's typing cells (`variableCell`,
`universeCodeCell`, `emptyTypeCell`, `piTyCodeCell`, `sigmaTyCodeCell`), the
binder-crossing `subst_lift_weaken_commute` naturality square, and the singleton
cancellation `subst_singleton_renameWeaken_cancel`.  Like `CellRenaming`, these
mention NO typing judgement — they are statements about `RawTerm.subst` over the
cell constructors, consumed by every substitution arm in the typed metatheory
(the β-engine of formation/grown subject reduction, the BFT/denote reducibility
substrate).

The substitution substrate stands on the cell constructors alone, independent of
any typing engine.

## Zero-axiom verification

The leaf-cell computations reduce by `rfl`; `subst_lift_weaken_commute` is the
`rename_subst_commute` / `subst_rename_commute` pair + a pointwise agreement;
`subst_singleton_renameWeaken_cancel` rides `weaken_subst_singleton`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Substituting at a variable cell applies the substitution to the index —
the substituent REPLACES the variable (unlike renaming, which keeps it a
variable). -/
theorem subst_variableCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (index : Fin sourceScope) :
    RawTerm.subst substitution (variableCell index) = substitution index :=
  rfl

/-- Substituting at a universe-code cell leaves it unchanged — universe
codes are closed. -/
theorem subst_universeCodeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.subst substitution (universeCodeCell levelExpr flag)
      = universeCodeCell levelExpr flag :=
  rfl

/-- Substituting at the empty-type code cell leaves it unchanged — `emptyTypeCell`
is a closed nullary leaf.  Holds by `rfl` for the same reason as
`subst_universeCodeCell`: `RawTerm.subst` is `fold GenAlgebra.canonical`, which
over the literal `childNil` rebuilds the same cell.  The substrate of CON-A2
route E's `emptyFormation` substitution arm. -/
theorem subst_emptyTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (emptyTypeCell (scope := sourceScope))
      = emptyTypeCell :=
  rfl

/-- Substituting at a Π-type code cell distributes over the two children: the
domain (child shift `0`) is substituted by the substitution itself, the codomain
(child shift `1`, under one fresh binder) by the substitution lifted once
(`iterateLiftRaw substitution 1`).  Holds by `rfl` for the same reason as
`subst_universeCodeCell` — `RawTerm.subst` is `fold GenAlgebra.canonical`, which
iotas over the literal `childCons … childNil` spine and threads the lift at the
shift-`1` child.

The substitution-side companion to `rename_piTyCodeCell`; the typed
Π-substitution case (the dependent-codomain β-engine for Π formers) consumes it,
chaining with the `RawTermSubst0Commute` `iterateLiftRaw` lemmas. -/
theorem subst_piTyCodeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)
      = piTyCodeCell (RawTerm.subst substitution domainCode)
          (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) :=
  rfl

/-- Substitution distributes over a `sigmaTyCodeCell` exactly as over a
`piTyCodeCell`: the domain (child shift `0`) by the substitution itself, the
codomain (child shift `1`, under one fresh binder) by the substitution lifted
once.  Holds by `rfl` — the dual of `subst_piTyCodeCell`, the binder-crossing
brick the Σ-formation case of `substRespectingContext` consumes. -/
theorem subst_sigmaTyCodeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.subst substitution (sigmaTyCodeCell domainCode codomainCode)
      = sigmaTyCodeCell (RawTerm.subst substitution domainCode)
          (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) :=
  rfl

/-- Lifting a substitution commutes with weakening: substituting under one fresh
binder (`RawTermSubst.lift`) after weakening equals weakening after the un-lifted
substitution.  The substitution analog of `rename_lift_weaken_commute` (the
naturality square at the substitution level).

This is the binder-crossing crux the `piFormation` case of
`substRespectingContext` needs — its codomain premise is checked under
`Γ.cons domain`, so the IH fires with the LIFTED substitution, and discharging
the lifted side condition reduces (at de Bruijn 0 and at successors) to exactly
this commutation on the looked-up binding types.

Proof: `RawTerm.rename_subst_commute` rewrites the LHS to `subst (thenSubst
weaken (lift σ)) X`, `RawTerm.subst_rename_commute` rewrites the RHS to `subst
(postRename σ weaken) X`, and the two bridge substitutions agree pointwise (both
send `pos ↦ rename weaken (σ pos)` — the subst lift's successor branch is exactly
`postRename` at a weakened position), discharged by `RawTerm.subst_pointwise`. -/
theorem subst_lift_weaken_commute {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst (RawTermSubst.lift someSubstitution)
        (RawTerm.rename RawRenaming.weaken sourceTerm)
      = RawTerm.rename RawRenaming.weaken
          (RawTerm.subst someSubstitution sourceTerm) := by
  rw [RawTerm.rename_subst_commute, RawTerm.subst_rename_commute]
  exact RawTerm.subst_pointwise (fun _position => rfl) sourceTerm

/-- The cancellation the subst0 corollary's side condition needs:
substituting a singleton through a weakened (rename-by-`weaken`) term cancels
the weakening and returns the original term.  Bridges the substrate's
`weaken_subst_singleton` (stated on `RawTerm.weaken`) to the `rename
RawRenaming.weaken` form that `TypingContext.lookup` produces. -/
theorem subst_singleton_renameWeaken_cancel {scope : Nat}
    (sourceTerm rawArg : RawTerm scope) :
    RawTerm.subst (RawTermSubst.singleton rawArg)
        (RawTerm.rename RawRenaming.weaken sourceTerm) = sourceTerm := by
  rw [← RawTerm.weaken_eq_rename]
  exact RawTerm.weaken_subst_singleton sourceTerm rawArg


end FX1Poly.Typed
