import FX1Poly.Core.RawTermRename

/-! # Foundation/PolyCell/Core/RawTermWeaken — weaken via fold

This file ships `RawTerm.weaken` and `RawTermChildren.weaken`,
the SECOND one-line fold instantiation pair.  Weakening is the
canonical single-binder shift: every variable bumps up by one (via
`Fin.succ`), and the term's scope index increases from `scope` to
`scope + 1`.

Direct v2 counterpart to v1's `RawTerm.weaken` (a 74-arm pattern
match in the dim-indexed era).  In v2, weakening factors through
rename: `weaken := rename RawRenaming.weaken`.

## The one-line definitions

```
def RawTerm.weaken term :=
  RawTerm.rename RawRenaming.weaken term
```

Two delegations deep:
1. `weaken := rename RawRenaming.weaken term`
2. `rename rho t := fold GenAlgebra.canonical rho t` (#178)

The composition shows that weaken is a SPECIAL CASE of rename, which
is a special case of fold.  Each derivation costs ONE LINE; the
74-arm cascade lives in neither — it has been completely eliminated.

## Why factor through rename rather than fold directly

Both work:
* Direct: `weaken term := fold GenAlgebra.canonical RawRenaming.weaken term`
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
* Smoke theorems close by `rfl` IF the rename → fold chain reduces
  on concrete inputs (which #178's smoke tests confirmed)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- Weaken a `RawTerm`: shift every variable up by one, raising the
term's scope from `scope` to `scope + 1`.  Effectively introduces a
fresh binder ABOVE the term (the new variable at index 0 is unused).

**ONE LINE** as `rename` applied to the canonical weakening renaming
`RawRenaming.weaken : Fin scope → Fin (scope + 1)` defined as
`Fin.succ`. -/
def RawTerm.weaken {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm (scope + 1) :=
  RawTerm.rename RawRenaming.weaken sourceTerm

/-- Weaken a `RawTermChildren` spine: shift every variable in every
child up by one, raising the parent scope from `parentScope` to
`parentScope + 1`.

**ONE LINE** as `rename` applied to `RawRenaming.weaken`.  Sibling to
`RawTerm.weaken` for the children-spine layer. -/
def RawTermChildren.weaken {parentScope : Nat} {binderShifts : List Nat}
    (children : RawTermChildren binderShifts parentScope) :
    RawTermChildren binderShifts (parentScope + 1) :=
  RawTermChildren.rename RawRenaming.weaken children

/-- Definitional unfolding: `weaken` is `rename` with the canonical
weakening renaming.  Useful for downstream proofs that want to
reduce weaken-specific reasoning to rename-specific reasoning. -/
theorem RawTerm.weaken_eq_rename {scope : Nat}
    (sourceTerm : RawTerm scope) :
    RawTerm.weaken sourceTerm =
      RawTerm.rename RawRenaming.weaken sourceTerm := rfl

/-- Definitional unfolding for the children-spine variant. -/
theorem RawTermChildren.weaken_eq_rename {parentScope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts parentScope) :
    RawTermChildren.weaken children =
      RawTermChildren.rename RawRenaming.weaken children := rfl

/-- Smoke test: weakening a `gen_unit` term produces the same shape
of term at the next scope.

Closes by `rfl`: weaken → rename → fold reduces through the
non-variable arm.  Demonstrates that scope-bumping works correctly
for term-formers with no variable payload. -/
theorem RawTerm.weaken_unit_smoke :
    RawTerm.weaken (.mkGen .gen_unit () .childNil : RawTerm 0) =
      (.mkGen .gen_unit () .childNil : RawTerm 1) := rfl

/-- Smoke test: weakening the variable `var 0` at scope 1 produces
`var 1` at scope 2 (the position is shifted by `Fin.succ`).

Closes by `rfl`: weaken → rename → fold → variable case →
`ActsOnRawTermVar.varToRawTerm RawRenaming.weaken ⟨0, _⟩` →
wrap `Fin.succ ⟨0, _⟩ = ⟨1, _⟩` back in `.mkGen .gen_var`.

This empirically confirms that the variable case of weaken correctly
applies `Fin.succ` to the position via the `RawRenaming.weaken =
fun pos => Fin.succ pos` body. -/
theorem RawTerm.weaken_var_zero_smoke :
    RawTerm.weaken
        (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil) =
      .mkGen .gen_var
        (Fin.succ (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)) .childNil := rfl

end FX1Poly.Core
