import FX.Kernel.Term

/-!
# Elaboration scope

De Bruijn-index bookkeeping for the surface-to-kernel
elaborator.  A `Scope` tracks the names of in-scope binders in
most-recently-bound-first order, so resolution by name returns
the de Bruijn index the kernel expects (0 = nearest binder).

## What it carries

Primary role is *name resolution* — the typing context
(`FX.Kernel.TypingContext`) is what the kernel checks against.
Scope does NOT replace the kernel's context.

Secondary role added in Q76: an optional per-binder *type hint*
used by elab-side inference.  The binder's type at declaration
site is often known (fn parameter, typed let, match arm ctor
arg after `substParams`); when it is, Scope records it so
elaboration passes can look up a scrutinee's type without
threading a full typing context.  The match-on-parameterized-
inductive case (Q76 vs Q75 gap) needs this to recover
`Option(Nat)` → `[Nat]` for the motive.

Type hints are optional: sites that don't have the type at push
time still call plain `push` (name only), getting `none`; sites
that do have the type call `pushWithType`.  Consumers tolerate
`none` by falling back to older inference paths.
-/

namespace FX.Elab

open FX.Kernel

/-- A scope is a stack of binder names paired with optional
    type hints.  Head = most-recent binder.  `types` is parallel
    to `binders`: `types[i]` is `binders[i]`'s hint (or `none`
    when unknown). -/
structure Scope where
  binders : List String
  types   : List (Option Term)
  deriving Inhabited

namespace Scope

/-- The empty scope — no binders. -/
def empty : Scope := { binders := [], types := [] }

/-- Push a new binder onto the scope with no type hint.  The
    new binder gets de Bruijn index 0, all older binders shift
    up by one.  Use `pushWithType` instead when the binder's
    type is known at push time (fn parameter, typed let, etc.). -/
def push (name : String) (scope : Scope) : Scope :=
  { binders := name :: scope.binders
  , types   := none :: scope.types }

/-- Push a new binder onto the scope with a known type.  The
    type is used by elaboration passes that need to recover a
    scope variable's type without a full typing context — the
    primary use is Q76's `match m` where `m: Option(Nat)` needs
    `[Nat]` threaded into the motive. -/
def pushWithType (name : String) (binderType : Term) (scope : Scope)
    : Scope :=
  { binders := name :: scope.binders
  , types   := some binderType :: scope.types }

/-- Push many binders left-to-right (the last listed has the
    smallest de Bruijn index).  Types are left as `none` — use
    `pushAllWithTypes` for typed binder batches. -/
def pushAll (names : List String) (scope : Scope) : Scope :=
  names.foldl (fun scopeSoFar name => scopeSoFar.push name) scope

/-- Push many binders with parallel type hints.  `names` and
    `binderTypes` must have the same length; any length
    mismatch silently zips to the shorter list (caller invariant). -/
def pushAllWithTypes (names : List String) (binderTypes : List Term)
    (scope : Scope) : Scope :=
  (names.zip binderTypes).foldl
    (fun scopeSoFar (name, binderType) =>
      scopeSoFar.pushWithType name binderType)
    scope

/-- Resolve a name to its de Bruijn index.  Returns `none` if
    the name isn't in scope. -/
def resolve? (name : String) (scope : Scope) : Option Nat :=
  scope.binders.findIdx? (· = name)

/-- Look up the type hint for a binder by name.  Returns `none`
    when the name isn't in scope OR when the binder was pushed
    with `push` (no type info) rather than `pushWithType`.
    Q76 elabMatch uses this to recover a scope variable's
    parameterized-spec type args. -/
def typeOf? (name : String) (scope : Scope) : Option Term := do
  let deBruijnIndex ← scope.binders.findIdx? (· = name)
  let typeHint? ← scope.types[deBruijnIndex]?
  typeHint?

/-- Size of the scope — number of in-scope binders. -/
def size (scope : Scope) : Nat := scope.binders.length

end Scope

end FX.Elab
