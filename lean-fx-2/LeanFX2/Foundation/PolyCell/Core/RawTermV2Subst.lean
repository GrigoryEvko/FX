import LeanFX2.Foundation.PolyCell.Core.FoldV2
import LeanFX2.Foundation.PolyCell.Core.RawTermV2Weaken

/-! # Foundation/PolyCell/Core/RawTermV2Subst — subst via foldV2

This file ships `RawTermV2.subst` — the THIRD one-line foldV2
instantiation, completing the rename/weaken/subst trio that
demonstrates the L2 architectural payoff.

Direct v2 counterpart to v1's `RawTerm.subst` (a 74-arm pattern match
in the dim-indexed era).  In v2, subst is one foldV2 call with the
`RawTermSubstV2` Container.

## What makes subst different from rename

`RawRenaming`'s variable bridge (per #175) wraps the renamed Fin in
`.mkGen .gen_var pos .childNil` — the position is renamed but stays
a variable.

`RawTermSubstV2`'s variable bridge (per #175) returns the substituent
DIRECTLY — the position is REPLACED by an arbitrary term.

Despite this semantic difference, the foldV2 engine is the SAME for
both.  The Container's `ActsOnRawTermV2Var` instance picks the
variable semantics; foldV2 dispatches via that instance at every
variable position.  No new engine code needed for subst.

## The LiftsRaw bootstrap

This file ships `RawTermSubstV2.lift` (the binder-lift operation for
substitutions) and `instance : LiftsRaw RawTermSubstV2`.  These ARE
the substitution-side equivalents of `RawRenaming.lift`.

Standard de Bruijn discipline: when lifting through a binder:
* Variable 0 in the new scope maps to a fresh variable 0 (the bound
  one).
* Variable k+1 in the new scope maps to the WEAKENED substituent
  that was at position k in the old scope.

The lift uses `RawTermV2.weaken` (from #179) for the weakening step.

The Action instance for `RawTermSubstV2` (with `compose` using
`RawTermV2.subst`) ships LATER at V2-L2.7 (#181), once `subst`
exists.  This file only ships the minimal `LiftsRaw` instance
sufficient for foldV2 to traverse.

## The one-line definitions

```
def RawTermV2.subst sigma term :=
  foldV2 GenAlgebraV2.canonical sigma term
```

Same shape as `RawTermV2.rename` (#178) — different Container, same
engine.  The L2 cascade-tax killer at work: rename and subst share
ONE recursion.

## Zero-axiom verification

All declarations propext-free:
* `RawTermSubstV2.lift` — small Fin-case pattern match
* `LiftsRaw RawTermSubstV2` instance — projection through lift
* `RawTermV2.subst` / `RawTermChildrenV2.subst` — foldV2 delegation
* Smoke theorems close by `rfl` IF the foldV2 dispatch chain reduces
  on concrete inputs (which it did for #178 rename and #179 weaken)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Lift a substitution under one binder.

Standard de Bruijn lift: variable 0 in the new (lifted) scope maps
to a fresh variable 0 (the bound variable), and variable k+1 maps to
the weakened substituent that was at position k in the old scope.

This is the substitution-side analog of `RawRenaming.lift` (which
shifts each position up via Fin.succ in the codomain).  Substitutions
must additionally WEAKEN the existing substituents to account for the
new bound variable. -/
def RawTermSubstV2.lift {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope) :
    RawTermSubstV2 (sourceScope + 1) (targetScope + 1) :=
  fun newPosition =>
    match newPosition with
    | ⟨0, _hBound⟩ =>
        -- Fresh variable 0: the new bound variable in the lifted scope.
        .mkGen .gen_var ⟨0, Nat.zero_lt_succ targetScope⟩ .childNil
    | ⟨priorPositionValue + 1, hBound⟩ =>
        -- Position k+1: weaken the substituent that was at position k.
        RawTermV2.weaken
          (someSubstitution ⟨priorPositionValue,
                              Nat.lt_of_succ_lt_succ hBound⟩)

/-- `RawTermSubstV2` lifts through binders via `RawTermSubstV2.lift`.

This is the minimal typeclass instance foldV2 needs to traverse a
RawTermV2 using a substitution.  The full `Action` instance (with
`compose` defined via `RawTermV2.subst`) ships at V2-L2.7 (#181)
once `subst` exists. -/
instance instLiftsRawRawTermSubstV2 : LiftsRaw RawTermSubstV2 where
  liftForRaw := RawTermSubstV2.lift

/-- Substitute into a `RawTermV2`: replace each variable with the
corresponding substituent, threading through binders by lifting the
substitution at each crossing.

**ONE LINE via foldV2**.  Same engine as `rename` (#178), different
Container.  The L2 cascade-tax killer at work: rename and subst share
the foldV2 recursion. -/
def RawTermV2.subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2 targetScope :=
  foldV2 GenAlgebraV2.canonical someSubstitution sourceTerm

/-- Substitute into a `RawTermChildrenV2` spine. -/
def RawTermChildrenV2.subst {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someSubstitution : RawTermSubstV2 parentSourceScope parentTargetScope)
    (children : RawTermChildrenV2 binderShifts parentSourceScope) :
    RawTermChildrenV2 binderShifts parentTargetScope :=
  foldChildrenV2 GenAlgebraV2.canonical someSubstitution children

/-- Definitional unfolding: `RawTermV2.subst` is `foldV2` with
canonical algebra and `RawTermSubstV2` Container. -/
theorem RawTermV2.subst_eq_foldV2 {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2.subst someSubstitution sourceTerm =
      foldV2 GenAlgebraV2.canonical someSubstitution sourceTerm := rfl

/-- Definitional unfolding for the children-spine variant. -/
theorem RawTermChildrenV2.subst_eq_foldChildrenV2
    {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someSubstitution : RawTermSubstV2 parentSourceScope parentTargetScope)
    (children : RawTermChildrenV2 binderShifts parentSourceScope) :
    RawTermChildrenV2.subst someSubstitution children =
      foldChildrenV2 GenAlgebraV2.canonical someSubstitution children := rfl

/-- Smoke test: substituting `.gen_unit` by ANY substitution returns
`.gen_unit` (the term has no variables).

Closes by `rfl`: foldV2 hits the NON-VARIABLE arm at `.gen_unit`,
recursively folds the empty children spine (`.childNil → .childNil`),
casts the `()` payload via scope-invariance, and applies the
canonical algebra to rebuild `.mkGen .gen_unit () .childNil`.  The
substitution is never consulted because no variable is encountered. -/
theorem RawTermV2.subst_identity_unit_smoke :
    RawTermV2.subst
        (RawTermSubstV2.identity (scope := 0))
        (.mkGen .gen_unit () .childNil) =
      (.mkGen .gen_unit () .childNil : RawTermV2 0) := rfl

/-- Smoke test: substituting variable 0 by the identity substitution
returns the same variable.

Closes by `rfl`: foldV2 hits the VARIABLE arm at `.gen_var`, casts
payload to `Fin 1`, invokes `ActsOnRawTermV2Var.varToRawTermV2
identity ⟨0,_⟩` which (for `RawTermSubstV2.identity`) returns
`.mkGen .gen_var ⟨0,_⟩ .childNil` directly.

This empirically confirms that the VARIABLE bridge for
`RawTermSubstV2` is correctly wired: identity-substituent at
position 0 returns a fresh `gen_var` at position 0. -/
theorem RawTermV2.subst_identity_var_zero_smoke :
    RawTermV2.subst
        (RawTermSubstV2.identity (scope := 1))
        (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil) =
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil := rfl

end LeanFX2.Foundation.PolyCell.Core
