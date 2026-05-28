import LeanFX2.Foundation.PolyCell.Core.RawTermSubst

/-! # Foundation/PolyCell/Core/RawTermSubst0 — single-variable subst (β-substrate)

V2-L2.10 (2026-05-27).  Ships the **single-variable substitution
operation** that beta reduction (and every other dependent-type
elimination rule) cites.  Direct v2 counterpart to v1's
`RawTermSubst.singleton` + `RawTerm.subst0` (lives at
`Foundation/RawSubst/SubstDefs.lean:35,200`).

## What gets shipped

Two definitions and five smoke lemmas:

* `RawTermSubst.singleton rawArg : RawTermSubst (scope + 1) scope`
  — the substitution that maps position 0 to `rawArg` and position
  k+1 to variable k.  Same semantics as v1's `RawTermSubst.singleton`.

* `RawTerm.subst0 body rawArg : RawTerm scope` — convenience
  wrapper applying singleton.  Same semantics as v1's
  `RawTerm.subst0`.

Smoke lemmas:

* `singleton_var_zero` — position 0 returns rawArg.
* `singleton_var_succ` — position k+1 returns var k.
* `subst0_var_zero` — substituting var 0 returns rawArg.
* `subst0_var_succ_one_smoke` — substituting var 1 returns var 0
  (the shift-down).
* `subst0_unit_smoke` — substituting a closed term ignores rawArg.

## Why `@[reducible]` on the definitions

Both `RawTermSubst.singleton` and `RawTerm.subst0` are marked
`@[reducible]` so the smoke lemmas close by `rfl`.  Without it, the
Fin pattern match in singleton stays opaque and `rfl` cannot reduce
across it.

Reducibility cost: downstream proofs that don't want this unfolding
must `dsimp only` carefully — but this is the same discipline v1
already established (v1's `RawTermSubst.singleton` is also
`@[reducible]`).

## The β-reduct convention

The Step relation on V2 (Step.lean — M2/M3/M4 SR cascade
#251/#252/#253 SHIPPED) fires the canonical beta-reduction rule
as:

```
Step (.mkGen .gen_app payload₁ (.childCons (.mkGen .gen_lam payload₂
        (.childCons body .childNil)) (.childCons arg .childNil)))
     (RawTerm.subst0 body arg)
```

i.e., applying a lambda to its argument reduces to the body with
position 0 substituted by the argument.  This file ships `subst0`
as the SHAPE the Step relation will reference; the Step relation
itself ships at V2-L3.1 (subject reduction).

## What's NOT shipped here

* **`RawTermSubst.singleton_rename_commute_pointwise`** and other
  commute lemmas — these live with the v1 analogs in
  `Foundation/RawSubst/SubstIdentityAndBeta.lean`.  The v2 cascade
  laws file (`RawCellCascadeLaws.lean`) already covers the
  rename/subst commute at the FOLD level; the singleton-specific
  commute is a follow-up if/when the Step relation needs it.

* **A full Step relation with beta as a constructor** — V2-L3.1
  task.  This file just ships the substitution OPERATION; the
  judgement that fires it lives at L3.

* **Subject reduction theorems** — L3.

## Zero-axiom verification

All seven declarations pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

## Forward-compat: identity vs singleton

Note the relationship:
* `RawTermSubst.identity : RawTermSubst scope scope` — maps each
  position to a fresh `var` at the same position.
* `RawTermSubst.singleton rawArg : RawTermSubst (scope + 1) scope`
  — maps position 0 to rawArg, k+1 to var k.

Singleton can be VIEWED as identity with position 0 "consumed by
rawArg and everything shifted down by one".  But operationally they
are distinct definitions and the smoke lemmas pin behavior
specifically for singleton.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Single-position substitution: maps position 0 to `rawArg`, maps
position k+1 to variable k (shifting all higher variables down by one).

v2 analog of v1's `RawTermSubst.singleton`
(`Foundation/RawSubst/SubstDefs.lean:35`).  Same load-bearing role:
the substitution that the canonical beta-reduction rule references. -/
@[reducible] def RawTermSubst.singleton {scope : Nat}
    (rawArg : RawTerm scope) :
    RawTermSubst (scope + 1) scope :=
  fun position =>
    match position with
    | ⟨0, _⟩      => rawArg
    | ⟨k + 1, h⟩  =>
        .mkGen .gen_var ⟨k, Nat.lt_of_succ_lt_succ h⟩ .childNil

/-- Single-variable substitution at position 0: substitutes `rawArg`
for `var 0` in `body`, shifting all higher variables down by one.

v2 analog of v1's `RawTerm.subst0`
(`Foundation/RawSubst/SubstDefs.lean:200`).  In the future V2 Step
relation, the canonical beta-reduction rule will reduce
`app (lam body) arg` to `subst0 body arg`. -/
@[reducible] def RawTerm.subst0 {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst (RawTermSubst.singleton rawArg) body

/-- Behavior pin: singleton's position-0 entry returns the substituent. -/
theorem RawTermSubst.singleton_var_zero {scope : Nat}
    (rawArg : RawTerm scope) :
    RawTermSubst.singleton rawArg ⟨0, Nat.zero_lt_succ scope⟩ = rawArg := rfl

/-- Behavior pin: singleton's position-(k+1) entry returns variable k
(the shift-down). -/
theorem RawTermSubst.singleton_var_succ {scope : Nat}
    (rawArg : RawTerm scope) (k : Nat) (hBound : k + 1 < scope + 1) :
    RawTermSubst.singleton rawArg ⟨k + 1, hBound⟩ =
      .mkGen .gen_var ⟨k, Nat.lt_of_succ_lt_succ hBound⟩ .childNil := rfl

/-- Beta-shape smoke: substituting `var 0` returns the substituent.

This is the structural backbone of beta reduction: when the lambda's
body is exactly `var 0` (i.e., the identity lambda `λ x. x`), applying
it to an argument reduces to that argument. -/
theorem RawTerm.subst0_var_zero {scope : Nat} (rawArg : RawTerm scope) :
    RawTerm.subst0
        (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) rawArg =
      rawArg := rfl

/-- Beta-shape smoke: substituting `var 1` at scope 1 returns `var 0`
(the de Bruijn shift-down on substitution).

Demonstrates the singleton substitution's de Bruijn discipline:
positions other than 0 are shifted down to make room for the
substituent at position 0. -/
theorem RawTerm.subst0_var_succ_one_smoke (rawArg : RawTerm 1) :
    RawTerm.subst0
        (.mkGen .gen_var (⟨1, by decide⟩ : Fin 2) .childNil) rawArg =
      .mkGen .gen_var (⟨0, by decide⟩ : Fin 1) .childNil := rfl

/-- Beta-shape smoke: substituting into a closed term (`gen_unit`, no
variables) ignores the argument.

Witnesses that variable-free terms pass through substitution
unchanged.  Same discipline as v1's `RawTerm.subst_unit` family of
smoke lemmas. -/
theorem RawTerm.subst0_unit_smoke {scope : Nat} (rawArg : RawTerm scope) :
    RawTerm.subst0 (.mkGen .gen_unit () .childNil) rawArg =
      (.mkGen .gen_unit () .childNil : RawTerm scope) := rfl

end LeanFX2.Foundation.PolyCell.Core
