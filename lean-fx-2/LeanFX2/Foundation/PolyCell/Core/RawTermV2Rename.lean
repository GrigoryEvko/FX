import LeanFX2.Foundation.PolyCell.Core.FoldV2
import LeanFX2.Foundation.RawSubst.ActionInstances

/-! # Foundation/PolyCell/Core/RawTermV2Rename — rename via foldV2

This file ships `RawTermV2.rename` and `RawTermChildrenV2.rename`,
the FIRST one-line foldV2 instantiations.  The L2 cascade-tax killer
made concrete: each definition is **one line** because foldV2 (#177)
already handles all 194 generators uniformly via the GenAlgebraV2
canonical algebra (#176) and the ActsOnRawTermV2Var bridge (#175).

Direct v2 counterpart to v1's `RawTerm.rename` (in
`Foundation/RawTerm.lean`'s 74-arm pattern match) and the
corresponding children-spine renamer.

## The one-line definitions

```
def RawTermV2.rename rho term :=
  foldV2 GenAlgebraV2.canonical rho term
```

That's the entire body.  In v1's era, the equivalent would be a
74-arm pattern match enumerating every Term constructor — and EACH
new traversal (subst, weaken, ...) duplicated the same 74-arm
cascade.

This one line composes:
* `RawRenaming` Action instance (from v1's `RawSubst/ActionInstances`,
  reusable verbatim since `RawRenaming := Fin src → Fin tgt` is
  profile-agnostic)
* `ActsOnRawTermV2Var RawRenaming` instance (from #175 — variable
  bridge wrapping renamed Fin in `.mkGen .gen_var pos .childNil`)
* `GenAlgebraV2.canonical` (from #176 — uniform rebuild algebra)
* `foldV2` engine (from #177 — mutual structural recursion)

Each prior commit's investment makes THIS commit a single line.

## Smoke tests demonstrate the architecture composes correctly

The smoke theorems reduce THROUGH foldV2's full dispatch chain:

1. Match on term → destructure into generator + payload + children
2. Decidable dispatch on `generator = .gen_var`
3. Variable arm: cast payload via `Eq.rec` motive trick + invoke
   `ActsOnRawTermV2Var.varToRawTermV2` + wrap result
4. Non-variable arm: recursively fold children, cast payload via
   `Generator.payload_scope_invariant_of_not_var`, invoke algebra

If `rfl` closes the smoke tests, the entire pipeline reduces
definitionally on concrete inputs — empirical proof that v2's
un-indexed substrate + Allais factoring composes cleanly.

## Zero-axiom verification

All declarations propext-free:
* `RawTermV2.rename` / `RawTermChildrenV2.rename` — definitional
  delegation to foldV2 / foldChildrenV2 (already zero-axiom)
* Unfolding theorems close by `rfl`
* Smoke theorems close by `rfl` IF the foldV2 dispatch chain reduces
  on concrete inputs

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Rename a `RawTermV2`: apply a positional renaming to every
variable in the term, threading through binders.

**ONE LINE via foldV2**.  In v1's era this would be a 74-arm
pattern match; in v2 it's a single foldV2 instantiation with the
`RawRenaming` Container and the canonical algebra.  The cascade-tax
killer made concrete. -/
def RawTermV2.rename {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2 targetScope :=
  foldV2 GenAlgebraV2.canonical someRenaming sourceTerm

/-- Rename a `RawTermChildrenV2` spine: apply a positional renaming
to every variable in each child, lifting under binder shifts.

**ONE LINE via foldChildrenV2**.  Sibling operation to
`RawTermV2.rename` — same algebra, same Container, just routed
through the children-spine engine. -/
def RawTermChildrenV2.rename {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : RawRenaming parentSourceScope parentTargetScope)
    (children : RawTermChildrenV2 binderShifts parentSourceScope) :
    RawTermChildrenV2 binderShifts parentTargetScope :=
  foldChildrenV2 GenAlgebraV2.canonical someRenaming children

/-- Definitional unfolding: `RawTermV2.rename` is `foldV2` with
canonical algebra and `RawRenaming` Container.

Closes by `rfl` — `RawTermV2.rename` is literally the foldV2
application.  Useful for downstream proofs that need to unfold
rename into its foldV2 form to reason about the recursion. -/
theorem RawTermV2.rename_eq_foldV2 {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2.rename someRenaming sourceTerm =
      foldV2 GenAlgebraV2.canonical someRenaming sourceTerm := rfl

/-- Definitional unfolding for the children spine: same delegation
pattern as `RawTermV2.rename_eq_foldV2`. -/
theorem RawTermChildrenV2.rename_eq_foldChildrenV2
    {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : RawRenaming parentSourceScope parentTargetScope)
    (children : RawTermChildrenV2 binderShifts parentSourceScope) :
    RawTermChildrenV2.rename someRenaming children =
      foldChildrenV2 GenAlgebraV2.canonical someRenaming children := rfl

/-- Smoke test: renaming a `gen_unit` term by the identity renaming
returns the same term.

Closes by `rfl` if foldV2's dispatch chain reduces on concrete
inputs.  This exercises the NON-VARIABLE path: foldV2 hits
`generator = .gen_unit` (not `.gen_var`), invokes the canonical
algebra to rebuild `.mkGen .gen_unit () .childNil`.

If this `rfl` succeeds, it empirically confirms:
* foldV2's `if hVar : generator = .gen_var` dispatch reduces for
  closed inputs via DecidableEq Generator
* `Generator.payload_scope_invariant_of_not_var` casts payload
  cleanly through the Eq.rec motive
* `foldChildrenV2` reduces on `.childNil`
* `GenAlgebraV2.canonical.algebra` rebuilds via `.mkGen` -/
theorem RawTermV2.rename_identity_unit_smoke :
    RawTermV2.rename
        (RawRenaming.identity (scope := 0))
        (.mkGen .gen_unit () .childNil) =
      .mkGen .gen_unit () .childNil := rfl

/-- Smoke test: renaming a variable by the identity renaming returns
the same variable.

Closes by `rfl` if the VARIABLE path of foldV2 reduces: dispatch on
`generator = .gen_var`, `Eq.rec` cast of payload to `Fin scope`,
invocation of `ActsOnRawTermV2Var.varToRawTermV2`, identity renaming
applied to the Fin position, re-wrap in `.mkGen .gen_var`.

If this `rfl` succeeds, it empirically confirms:
* foldV2's variable arm reduces for closed inputs
* The `Eq.rec` motive trick (memory `feedback_lean_eq_rec_motive`)
  reduces cleanly for `rfl`-shaped equalities
* `RawRenaming.identity` is `@[reducible]` and applies as the
  identity function on Fin -/
theorem RawTermV2.rename_identity_var_smoke (varIndex : Fin 1) :
    RawTermV2.rename
        (RawRenaming.identity (scope := 1))
        (.mkGen .gen_var varIndex .childNil) =
      .mkGen .gen_var varIndex .childNil := rfl

end LeanFX2.Foundation.PolyCell.Core
