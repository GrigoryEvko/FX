import LeanFX2.Foundation.PolyCell.Core.RawTermV2
import LeanFX2.Foundation.RawSubst.RenameDefs

/-! # Foundation/PolyCell/Core/RawTermSubstV2 — L2 substitution Container + variable-bridge typeclass

This file opens L2 (the Allais ops layer).  It ships:

1. **`RawTermSubstV2 src tgt`** — the v2 substitution Container type
   (`Fin src → RawTermV2 tgt`), analog of v1's `RawTermSubst`.
2. **`RawTermSubstV2.identity`** — the trivial substitution mapping
   each variable to itself.
3. **`ActsOnRawTermV2Var`** — typeclass capturing "Container `C`
   produces a `RawTermV2` from a Fin position."  Allais bridge from
   the Action typeclass's `headIndex : Fin → ActionTarget` to the
   concrete target type `RawTermV2`.
4. Two instances of `ActsOnRawTermV2Var`:
   * `RawRenaming` — wraps the renamed Fin in `.mkGen .gen_var _ .childNil`.
   * `RawTermSubstV2` — direct lookup (returns the substituent).

## What's deferred to later L2 sub-tasks

This file is the L2 KICKOFF — minimum infrastructure to unblock the
Allais fold (foldV2 in #177).  Three things explicitly NOT shipped here:

* **Full `Action` instance for `RawTermSubstV2`**: requires `compose`,
  which requires `RawTermV2.subst`, which is downstream of foldV2.
  Ships at V2-L2.7 (#181 — Action laws for RawTermV2) once foldV2
  exists.

* **`RawTermSubstV2.lift` (lift through a binder)**: also requires
  `RawTermV2`-level operations (specifically a weakening-renaming on
  RawTermV2) that come from foldV2.  Ships at V2-L2.5/2.6 (#179, #180
  — weaken/subst via foldV2).

* **The recursion engine itself (`RawTermV2.act` / `foldV2`)**: that's
  V2-L2.3 (#177).  This file's typeclass instances are its INPUT
  shape, not the engine itself.

## Why two typeclasses (Action + ActsOnRawTermV2Var) rather than one

`Foundation/Action.lean`'s `Action` class abstracts over Containers
generically.  Its `headIndex` returns `ActionTarget targetScope` —
parameterised, NOT pinned to `RawTermV2`:

* For `RawRenaming`: `ActionTarget = Fin` (a positional renaming).
* For a v2-substitution Container: `ActionTarget = RawTermV2` (a
  full term).

A recursion engine traversing `RawTermV2` needs to know how to insert
the variable case, which means it needs a Container `C` plus a
function `C src tgt → Fin src → RawTermV2 tgt`.  The dedicated
`ActsOnRawTermV2Var` typeclass captures exactly that — separately
from the Action typeclass's binder-lift / compose / identity
machinery.

The split is INDEPENDENT OF v2 vs v1: v1 ships the same split as
`Action` (Foundation/Action.lean) + `ActsOnRawTermVar` (in
Foundation/RawTerm.lean) + `ActsOnRawTermVarLifts` (in
Foundation/RawSubst/ActionInstances.lean).  v2 inherits the same
architecture with the term-target swapped.

## Why `RawRenaming` is reused (not redefined)

`RawRenaming src tgt := Fin src → Fin tgt` (in `RawSubst/RenameDefs.lean`)
is purely positional — it does not carry any term-shape information.
The Container is reusable verbatim across v1's `RawTerm` and v2's
`RawTermV2`.  What differs is the variable bridge:

* v1: `instance : ActsOnRawTermVar RawRenaming` — wrap Fin in `RawTerm.var`
* v2: `instance : ActsOnRawTermV2Var RawRenaming` (this file) — wrap
  Fin in `.mkGen .gen_var pos .childNil`

Same Container, two distinct bridges to two distinct target types.
The shared Container is what lets a single `foldV2` engine cover
both rename (`RawRenaming` Container) and subst (`RawTermSubstV2`
Container).

## Zero-axiom verification

All declarations propext-free:
* `RawTermSubstV2` is a function-typed reducible def
* `RawTermSubstV2.identity` is a closed lambda + `.mkGen` data ctor
* `ActsOnRawTermV2Var` is a single-field class (no equation lemmas)
* Both instances ship by data definition (no propositional content)
* Smoke theorem closes by `rfl` (definitional reduction)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- v2 substitution Container: maps every position in the source
scope to a v2 raw term in the target scope.  Function-typed
(reducible) so downstream code can apply a `RawTermSubstV2` directly
as a function without method calls.

Direct v2 counterpart to v1's `RawTermSubst` (in
`Foundation/RawSubst/SubstDefs.lean`).  Same shape, different target
term type. -/
@[reducible] def RawTermSubstV2 (sourceScope targetScope : Nat) : Type :=
  Fin sourceScope → RawTermV2 targetScope

/-- The identity substitution: every variable maps to itself (wrapped
as a v2 raw term via the `gen_var` generator's single-arity arm with
empty children spine).

Closed form: `fun varIndex => .mkGen .gen_var varIndex .childNil`.
The generator metadata pins payload to `Fin scope` and children to
`RawTermChildrenV2 [] scope`, both of which are satisfied by the
literal `varIndex : Fin scope` and `.childNil : RawTermChildrenV2 []
scope`.

This is the substitution-side analog of `RawRenaming.identity`. -/
@[reducible] def RawTermSubstV2.identity {scope : Nat} :
    RawTermSubstV2 scope scope :=
  fun varIndex => .mkGen .gen_var varIndex .childNil

/-- A Container `C` that knows how to produce a `RawTermV2 targetScope`
from a `Fin sourceScope` position.

This is the Allais-style bridge from the Action typeclass's generic
`headIndex` to the concrete `RawTermV2` target.  A recursion engine
traversing `RawTermV2` (like `foldV2` in #177) requires both:
* `[Action C]` — for lift / compose / identity / generic structure
* `[ActsOnRawTermV2Var C]` — for the variable case in the recursion

Both instances are typically shipped at the same time for a given
Container (e.g. `RawRenaming`).  Splitting them keeps the
abstractions cleanly separated: `Action` is about Container
self-structure, `ActsOnRawTermV2Var` is about the bridge to a
specific target. -/
class ActsOnRawTermV2Var (Container : Nat → Nat → Type) where
  /-- Variable lookup: produce the `RawTermV2` value the Container
  associates with a given source position. -/
  varToRawTermV2 : ∀ {sourceScope targetScope : Nat},
      Container sourceScope targetScope →
      Fin sourceScope → RawTermV2 targetScope

/-- `RawRenaming` acts on `RawTermV2` variables by wrapping the
renamed Fin position in `.mkGen .gen_var ... .childNil`.

This is the variable bridge for rename-style traversals over v2:
when the foldV2 engine hits a `.mkGen .gen_var sourcePos .childNil`
node, it applies the renaming to `sourcePos` and re-wraps as a fresh
variable cell at the target scope.

Direct v2 counterpart to v1's `instance : ActsOnRawTermVar
RawRenaming` (in `Foundation/RawTerm.lean`). -/
instance : ActsOnRawTermV2Var RawRenaming where
  varToRawTermV2 someRenaming sourcePosition :=
    .mkGen .gen_var (someRenaming sourcePosition) .childNil

/-- `RawTermSubstV2` acts on `RawTermV2` variables by direct lookup:
the substitution map IS the variable-to-term function, so the bridge
is just function application.

This is the variable bridge for subst-style traversals over v2:
when foldV2 hits a `.mkGen .gen_var sourcePos .childNil` node, it
returns the substituent `someSubstitution sourcePos` directly. -/
instance : ActsOnRawTermV2Var RawTermSubstV2 where
  varToRawTermV2 someSubstitution sourcePosition :=
    someSubstitution sourcePosition

/-- Smoke check: the identity substitution applied to any position
returns a `gen_var` variable cell at that same position.

Closes by `rfl` since both sides reduce to the same `.mkGen .gen_var
pos .childNil` literal under `RawTermSubstV2.identity`'s reducible
definition. -/
theorem RawTermSubstV2.identity_lookup_eq_genVar
    {scope : Nat} (sourcePosition : Fin scope) :
    (RawTermSubstV2.identity : RawTermSubstV2 scope scope) sourcePosition =
      .mkGen .gen_var sourcePosition .childNil := rfl

/-- Equivalence theorem: the `ActsOnRawTermV2Var` bridge for `RawRenaming`
agrees with the explicit `.mkGen .gen_var` wrapper at every position.

Closes by `rfl` after typeclass-instance unfolding.  Demonstrates that
the bridge is the canonical re-wrap, NOT some derived/computed
embedding. -/
theorem ActsOnRawTermV2Var.rawRenaming_varToRawTermV2_eq
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourcePosition : Fin sourceScope) :
    ActsOnRawTermV2Var.varToRawTermV2 someRenaming sourcePosition =
      .mkGen .gen_var (someRenaming sourcePosition) .childNil := rfl

/-- Equivalence theorem: the `ActsOnRawTermV2Var` bridge for
`RawTermSubstV2` agrees with direct function application.

Closes by `rfl`.  Demonstrates that the bridge for substitutions is
the literal lookup operation — no extra wrapping or computation. -/
theorem ActsOnRawTermV2Var.rawTermSubstV2_varToRawTermV2_eq
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope)
    (sourcePosition : Fin sourceScope) :
    ActsOnRawTermV2Var.varToRawTermV2 someSubstitution sourcePosition =
      someSubstitution sourcePosition := rfl

end LeanFX2.Foundation.PolyCell.Core
