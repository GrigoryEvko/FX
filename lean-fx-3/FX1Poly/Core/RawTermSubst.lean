import FX1Poly.Core.Fold
import FX1Poly.Core.RawTermSubstDefs
import FX1Poly.Core.RawTermWeaken

/-! # Foundation/PolyCell/Core/RawTermSubst — subst via fold

This file ships `RawTerm.subst` — the THIRD one-line fold
instantiation, completing the rename/weaken/subst trio that
demonstrates the L2 architectural payoff.

Direct v2 counterpart to v1's `RawTerm.subst` (a 74-arm pattern match
in the dim-indexed era).  In v2, subst is one fold call with the
`RawTermSubst` Container.

## What makes subst different from rename

`RawRenaming`'s variable bridge (per #175) wraps the renamed Fin in
`.mkGen .gen_var pos .childNil` — the position is renamed but stays
a variable.

`RawTermSubst`'s variable bridge (per #175) returns the substituent
DIRECTLY — the position is REPLACED by an arbitrary term.

Despite this semantic difference, the fold engine is the SAME for
both.  The Container's `ActsOnRawTermVar` instance picks the
variable semantics; fold dispatches via that instance at every
variable position.  No new engine code needed for subst.

## The LiftsRaw bootstrap

This file ships `RawTermSubst.lift` (the binder-lift operation for
substitutions) and `instance : LiftsRaw RawTermSubst`.  These ARE
the substitution-side equivalents of `RawRenaming.lift`.

Standard de Bruijn discipline: when lifting through a binder:
* Variable 0 in the new scope maps to a fresh variable 0 (the bound
  one).
* Variable k+1 in the new scope maps to the WEAKENED substituent
  that was at position k in the old scope.

The lift uses `RawTerm.weaken` (from #179) for the weakening step.

The Action instance for `RawTermSubst` (with `compose` using
`RawTerm.subst`) ships LATER at V2-L2.7 (#181), once `subst`
exists.  This file only ships the minimal `LiftsRaw` instance
sufficient for fold to traverse.

## The one-line definitions

```
def RawTerm.subst sigma term :=
  fold GenAlgebra.canonical sigma term
```

Same shape as `RawTerm.rename` (#178) — different Container, same
engine.  The L2 cascade-tax killer at work: rename and subst share
ONE recursion.

## Zero-axiom verification

All declarations propext-free:
* `RawTermSubst.lift` — small Fin-case pattern match
* `LiftsRaw RawTermSubst` instance — projection through lift
* `RawTerm.subst` / `RawTermChildren.subst` — fold delegation
* Smoke theorems close by `rfl` IF the fold dispatch chain reduces
  on concrete inputs (which it did for #178 rename and #179 weaken)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Lift a substitution under one binder.

Standard de Bruijn lift: variable 0 in the new (lifted) scope maps
to a fresh variable 0 (the bound variable), and variable k+1 maps to
the weakened substituent that was at position k in the old scope.

This is the substitution-side analog of `RawRenaming.lift` (which
shifts each position up via Fin.succ in the codomain).  Substitutions
must additionally WEAKEN the existing substituents to account for the
new bound variable. -/
def RawTermSubst.lift {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope) :
    RawTermSubst (sourceScope + 1) (targetScope + 1) :=
  fun newPosition =>
    match newPosition with
    | ⟨0, _hBound⟩ =>
        -- Fresh variable 0: the new bound variable in the lifted scope.
        .mkGen .gen_var ⟨0, Nat.zero_lt_succ targetScope⟩ .childNil
    | ⟨priorPositionValue + 1, hBound⟩ =>
        -- Position k+1: weaken the substituent that was at position k.
        RawTerm.weaken
          (someSubstitution ⟨priorPositionValue,
                              Nat.lt_of_succ_lt_succ hBound⟩)

/-- `RawTermSubst` lifts through binders via `RawTermSubst.lift`.

This is the minimal typeclass instance fold needs to traverse a
RawTerm using a substitution.  The full `Action` instance (with
`compose` defined via `RawTerm.subst`) ships at V2-L2.7 (#181)
once `subst` exists. -/
instance instLiftsRawRawTermSubst : LiftsRaw RawTermSubst where
  liftForRaw := RawTermSubst.lift

/-- Substitute into a `RawTerm`: replace each variable with the
corresponding substituent, threading through binders by lifting the
substitution at each crossing.

**ONE LINE via fold**.  Same engine as `rename` (#178), different
Container.  The L2 cascade-tax killer at work: rename and subst share
the fold recursion. -/
def RawTerm.subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm targetScope :=
  fold GenAlgebra.canonical someSubstitution sourceTerm

/-- Substitute into a `RawTermChildren` spine. -/
def RawTermChildren.subst {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someSubstitution : RawTermSubst parentSourceScope parentTargetScope)
    (children : RawTermChildren binderShifts parentSourceScope) :
    RawTermChildren binderShifts parentTargetScope :=
  foldChildren GenAlgebra.canonical someSubstitution children

/-- Definitional unfolding: `RawTerm.subst` is `fold` with
canonical algebra and `RawTermSubst` Container. -/
theorem RawTerm.subst_eq_fold {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst someSubstitution sourceTerm =
      fold GenAlgebra.canonical someSubstitution sourceTerm := rfl

/-- Definitional unfolding for the children-spine variant. -/
theorem RawTermChildren.subst_eq_foldChildren
    {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someSubstitution : RawTermSubst parentSourceScope parentTargetScope)
    (children : RawTermChildren binderShifts parentSourceScope) :
    RawTermChildren.subst someSubstitution children =
      foldChildren GenAlgebra.canonical someSubstitution children := rfl

/-- Smoke test: substituting `.gen_unit` by ANY substitution returns
`.gen_unit` (the term has no variables).

Closes by `rfl`: fold hits the NON-VARIABLE arm at `.gen_unit`,
recursively folds the empty children spine (`.childNil → .childNil`),
casts the `()` payload via scope-invariance, and applies the
canonical algebra to rebuild `.mkGen .gen_unit () .childNil`.  The
substitution is never consulted because no variable is encountered. -/
theorem RawTerm.subst_identity_unit_smoke :
    RawTerm.subst
        (RawTermSubst.identity (scope := 0))
        (.mkGen .gen_unit () .childNil) =
      (.mkGen .gen_unit () .childNil : RawTerm 0) := rfl

/-- Smoke test: substituting variable 0 by the identity substitution
returns the same variable.

Closes by `rfl`: fold hits the VARIABLE arm at `.gen_var`, casts
payload to `Fin 1`, invokes `ActsOnRawTermVar.varToRawTerm
identity ⟨0,_⟩` which (for `RawTermSubst.identity`) returns
`.mkGen .gen_var ⟨0,_⟩ .childNil` directly.

This empirically confirms that the VARIABLE bridge for
`RawTermSubst` is correctly wired: identity-substituent at
position 0 returns a fresh `gen_var` at position 0. -/
theorem RawTerm.subst_identity_var_zero_smoke :
    RawTerm.subst
        (RawTermSubst.identity (scope := 1))
        (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil) =
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil := rfl

end FX1Poly.Core
