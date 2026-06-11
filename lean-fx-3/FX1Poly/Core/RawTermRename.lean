import FX1Poly.Core.Fold
import FX1Poly.Foundation.RawSubst.ActionInstances

/-! # Foundation/PolyCell/Core/RawTermRename — rename via fold

`RawTerm.rename` and `RawTermChildren.rename`, one-line fold
instantiations: each definition is **one line** because fold
handles all 203 generators uniformly via the GenAlgebra canonical
algebra and the ActsOnRawTermVar bridge.

## The one-line definitions

```
def RawTerm.rename rho term :=
  fold GenAlgebra.canonical rho term
```

That's the entire body.  Every traversal (rename, subst, weaken,
...) reuses the same fold rather than duplicating a per-constructor
cascade.

This one line composes:
* `RawRenaming` Action instance (from `RawSubst/ActionInstances`,
  reusable verbatim since `RawRenaming := Fin src → Fin tgt` is
  profile-agnostic)
* `ActsOnRawTermVar RawRenaming` instance (variable bridge wrapping
  renamed Fin in `.mkGen .gen_var pos .childNil`)
* `GenAlgebra.canonical` (uniform rebuild algebra)
* `fold` engine (mutual structural recursion)

## Smoke tests demonstrate the architecture composes correctly

The smoke theorems reduce THROUGH fold's full dispatch chain:

1. Match on term → destructure into generator + payload + children
2. Decidable dispatch on `generator = .gen_var`
3. Variable arm: cast payload via `Eq.rec` motive trick + invoke
   `ActsOnRawTermVar.varToRawTerm` + wrap result
4. Non-variable arm: recursively fold children, cast payload via
   `Generator.payload_scope_invariant_of_not_var`, invoke algebra

If `rfl` closes the smoke tests, the entire pipeline reduces
definitionally on concrete inputs — proof that the un-indexed
substrate + Allais factoring composes cleanly.

## Zero-axiom verification

All declarations propext-free:
* `RawTerm.rename` / `RawTermChildren.rename` — definitional
  delegation to fold / foldChildren (already zero-axiom)
* Unfolding theorems close by `rfl`
* Smoke theorems close by `rfl` IF the fold dispatch chain reduces
  on concrete inputs

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- Rename a `RawTerm`: apply a positional renaming to every
variable in the term, threading through binders.

**ONE LINE via fold**: a single fold instantiation with the
`RawRenaming` Container and the canonical algebra. -/
def RawTerm.rename {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm targetScope :=
  fold GenAlgebra.canonical someRenaming sourceTerm

/-- Rename a `RawTermChildren` spine: apply a positional renaming
to every variable in each child, lifting under binder shifts.

**ONE LINE via foldChildren**.  Sibling operation to
`RawTerm.rename` — same algebra, same Container, just routed
through the children-spine engine. -/
def RawTermChildren.rename {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : RawRenaming parentSourceScope parentTargetScope)
    (children : RawTermChildren binderShifts parentSourceScope) :
    RawTermChildren binderShifts parentTargetScope :=
  foldChildren GenAlgebra.canonical someRenaming children

/-- Definitional unfolding: `RawTerm.rename` is `fold` with
canonical algebra and `RawRenaming` Container.

Closes by `rfl` — `RawTerm.rename` is literally the fold
application.  Useful for downstream proofs that need to unfold
rename into its fold form to reason about the recursion. -/
theorem RawTerm.rename_eq_fold {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename someRenaming sourceTerm =
      fold GenAlgebra.canonical someRenaming sourceTerm := rfl

/-- Definitional unfolding for the children spine: same delegation
pattern as `RawTerm.rename_eq_fold`. -/
theorem RawTermChildren.rename_eq_foldChildren
    {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : RawRenaming parentSourceScope parentTargetScope)
    (children : RawTermChildren binderShifts parentSourceScope) :
    RawTermChildren.rename someRenaming children =
      foldChildren GenAlgebra.canonical someRenaming children := rfl

/-- Smoke test: renaming a `gen_unit` term by the identity renaming
returns the same term.

Closes by `rfl` if fold's dispatch chain reduces on concrete
inputs.  This exercises the NON-VARIABLE path: fold hits
`generator = .gen_unit` (not `.gen_var`), invokes the canonical
algebra to rebuild `.mkGen .gen_unit () .childNil`.

If this `rfl` succeeds, it empirically confirms:
* fold's `if hVar : generator = .gen_var` dispatch reduces for
  closed inputs via DecidableEq Generator
* `Generator.payload_scope_invariant_of_not_var` casts payload
  cleanly through the Eq.rec motive
* `foldChildren` reduces on `.childNil`
* `GenAlgebra.canonical.algebra` rebuilds via `.mkGen` -/
theorem RawTerm.rename_identity_unit_smoke :
    RawTerm.rename
        (RawRenaming.identity (scope := 0))
        (.mkGen .gen_unit () .childNil) =
      .mkGen .gen_unit () .childNil := rfl

/-- Smoke test: renaming a variable by the identity renaming returns
the same variable.

Closes by `rfl` if the VARIABLE path of fold reduces: dispatch on
`generator = .gen_var`, `Eq.rec` cast of payload to `Fin scope`,
invocation of `ActsOnRawTermVar.varToRawTerm`, identity renaming
applied to the Fin position, re-wrap in `.mkGen .gen_var`.

If this `rfl` succeeds, it empirically confirms:
* fold's variable arm reduces for closed inputs
* The `Eq.rec` motive trick (memory `feedback_lean_eq_rec_motive`)
  reduces cleanly for `rfl`-shaped equalities
* `RawRenaming.identity` is `@[reducible]` and applies as the
  identity function on Fin -/
theorem RawTerm.rename_identity_var_smoke (varIndex : Fin 1) :
    RawTerm.rename
        (RawRenaming.identity (scope := 1))
        (.mkGen .gen_var varIndex .childNil) =
      .mkGen .gen_var varIndex .childNil := rfl

end FX1Poly.Core
