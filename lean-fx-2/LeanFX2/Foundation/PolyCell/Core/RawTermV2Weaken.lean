import LeanFX2.Foundation.PolyCell.Core.RawTermV2Rename

/-! # Foundation/PolyCell/Core/RawTermV2Weaken — weaken via foldV2

This file ships `RawTermV2.weaken` and `RawTermChildrenV2.weaken`,
the SECOND one-line foldV2 instantiation pair.  Weakening is the
canonical single-binder shift: every variable bumps up by one (via
`Fin.succ`), and the term's scope index increases from `scope` to
`scope + 1`.

Direct v2 counterpart to v1's `RawTerm.weaken` (a 74-arm pattern
match in the dim-indexed era).  In v2, weakening factors through
rename: `weaken := rename RawRenaming.weaken`.

## The one-line definitions

```
def RawTermV2.weaken term :=
  RawTermV2.rename RawRenaming.weaken term
```

Two delegations deep:
1. `weaken := rename RawRenaming.weaken term`
2. `rename rho t := foldV2 GenAlgebraV2.canonical rho t` (#178)

The composition shows that weaken is a SPECIAL CASE of rename, which
is a special case of foldV2.  Each derivation costs ONE LINE; the
74-arm cascade lives in neither — it has been completely eliminated.

## Why factor through rename rather than foldV2 directly

Both work:
* Direct: `weaken term := foldV2 GenAlgebraV2.canonical RawRenaming.weaken term`
* Via rename: `weaken term := rename RawRenaming.weaken term`

The via-rename form is more compositional — it explicitly names the
relationship "weaken is rename specialized to RawRenaming.weaken".
Downstream proofs of weaken's properties (e.g., commute lemmas at
#181) can lift directly from rename's corresponding properties via
this delegation.

The direct form would bypass rename and lose this connection.

## Zero-axiom verification

All declarations propext-free:
* `weaken` — definitional delegation to `rename` (zero-axiom from #178)
* Unfolding theorems close by `rfl`
* Smoke theorems close by `rfl` IF the rename → foldV2 chain reduces
  on concrete inputs (which #178's smoke tests confirmed)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Weaken a `RawTermV2`: shift every variable up by one, raising the
term's scope from `scope` to `scope + 1`.  Effectively introduces a
fresh binder ABOVE the term (the new variable at index 0 is unused).

**ONE LINE** as `rename` applied to the canonical weakening renaming
`RawRenaming.weaken : Fin scope → Fin (scope + 1)` defined as
`Fin.succ`. -/
def RawTermV2.weaken {scope : Nat} (sourceTerm : RawTermV2 scope) :
    RawTermV2 (scope + 1) :=
  RawTermV2.rename RawRenaming.weaken sourceTerm

/-- Weaken a `RawTermChildrenV2` spine: shift every variable in every
child up by one, raising the parent scope from `parentScope` to
`parentScope + 1`.

**ONE LINE** as `rename` applied to `RawRenaming.weaken`.  Sibling to
`RawTermV2.weaken` for the children-spine layer. -/
def RawTermChildrenV2.weaken {parentScope : Nat} {binderShifts : List Nat}
    (children : RawTermChildrenV2 binderShifts parentScope) :
    RawTermChildrenV2 binderShifts (parentScope + 1) :=
  RawTermChildrenV2.rename RawRenaming.weaken children

/-- Definitional unfolding: `weaken` is `rename` with the canonical
weakening renaming.  Useful for downstream proofs that want to
reduce weaken-specific reasoning to rename-specific reasoning. -/
theorem RawTermV2.weaken_eq_rename {scope : Nat}
    (sourceTerm : RawTermV2 scope) :
    RawTermV2.weaken sourceTerm =
      RawTermV2.rename RawRenaming.weaken sourceTerm := rfl

/-- Definitional unfolding for the children-spine variant. -/
theorem RawTermChildrenV2.weaken_eq_rename {parentScope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildrenV2 binderShifts parentScope) :
    RawTermChildrenV2.weaken children =
      RawTermChildrenV2.rename RawRenaming.weaken children := rfl

/-- Smoke test: weakening a `gen_unit` term produces the same shape
of term at the next scope.

Closes by `rfl`: weaken → rename → foldV2 reduces through the
non-variable arm.  Demonstrates that scope-bumping works correctly
for term-formers with no variable payload. -/
theorem RawTermV2.weaken_unit_smoke :
    RawTermV2.weaken (.mkGen .gen_unit () .childNil : RawTermV2 0) =
      (.mkGen .gen_unit () .childNil : RawTermV2 1) := rfl

/-- Smoke test: weakening the variable `var 0` at scope 1 produces
`var 1` at scope 2 (the position is shifted by `Fin.succ`).

Closes by `rfl`: weaken → rename → foldV2 → variable case →
`ActsOnRawTermV2Var.varToRawTermV2 RawRenaming.weaken ⟨0, _⟩` →
wrap `Fin.succ ⟨0, _⟩ = ⟨1, _⟩` back in `.mkGen .gen_var`.

This empirically confirms that the variable case of weaken correctly
applies `Fin.succ` to the position via the `RawRenaming.weaken =
fun pos => Fin.succ pos` body. -/
theorem RawTermV2.weaken_var_zero_smoke :
    RawTermV2.weaken
        (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil) =
      .mkGen .gen_var
        (Fin.succ (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)) .childNil := rfl

end LeanFX2.Foundation.PolyCell.Core
