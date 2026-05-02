import LeanFX2.Surface.AST
import LeanFX2.Surface.KernelBridge

/-! # Surface/KernelEnv — global environment for free-name resolution

The "fully kernel-backed AST" mission has four genuine kernel
gaps (per `Surface/KernelBridge.lean`'s docstring):

1. `RawTerm.const` / global env — for free names
2. Primitive operators
3. First-class records
4. N-literal primitives

This module addresses gap #1 from the surface side: an `Env`
type that maps qualified names to their kernel forms, enabling
the bridge to resolve free names without extending the kernel.

## Architecture

```lean
structure Env where
  -- Map from QualifiedName to its kernel-form definition
  lookup : QualifiedName → Option ResolvedDef
  -- Module-level scope (always 0 for top-level defs)
  --   Resolved values are weakened to caller's scope on lookup.
```

A `ResolvedDef` carries the kernel `RawTerm` representing the
definition.  Module-level definitions live at scope 0 (no
enclosing binders); the env provides a `liftToScope` operation
that weakens the RawTerm into the caller's binder scope.

## Bridge integration

The env-aware bridge:

```lean
def RawExpr.toRawTermWithEnv? (env : Env) :
    RawExpr scope → Option (RawTerm scope)
```

resolves `rawFree qname` via `env.lookup` and lifts to scope.
Other cases match the env-free `toRawTerm?` shipped in
`KernelBridge.lean`.

## Operator desugaring (gap #2)

Once Env is in place, the bridge can also desugar binops:

```lean
| .rawBinop op lhs rhs =>
    -- Operators are just stdlib free names: + ↦ Std.Int.add etc.
    let opName := BinaryOp.toQualifiedName op  -- from Std.Ops
    match env.lookup opName with
    | none => none
    | some opDef =>
        -- Build: app (app opDef lhsRaw) rhsRaw
        ...
```

A `BinaryOp.toQualifiedName : BinaryOp → QualifiedName` mapping
table provides the canonical stdlib names for each operator.

## Status

This file is currently a STUB providing the interface +
documentation.  Implementation requires:
1. Kernel weakening function `RawTerm.weakenAtScope :
   RawTerm 0 → ∀ s, RawTerm s` (or similar — exists in
   `Foundation/RawSubst.lean` as `RawTermSubst.shift`).
2. Decidable equality on QualifiedName (needs LowerIdent /
   UpperIdent DecidableEq, which currently aren't derived).
3. A concrete env type (List of (QualifiedName, ResolvedDef) is
   the simplest; performance later via Trie).

Phase 10.C will land these.

## Why not just extend `RawTerm` with `const`?

Extending the kernel ADDS cases to every reduction proof
(Step, Step.par, confluence, ...).  These cases are inert (const
doesn't reduce), so they're mechanical, but the work is real:
~50 cases × ~10 ctor additions = ~500 lines of mechanical proof
amendments.

Per `AXIOMS.md` Layer K policy: kernel extensions are
HIGH-COST.  Better to handle free names at the surface layer
via an Env, leaving the kernel pristine.
-/

namespace LeanFX2.Surface

/-- A resolved kernel-side definition for a qualified name.
The RawTerm is at module scope (`scope = 0`); the env's
`liftToScope` operation weakens it to the caller's scope.

Future extension: also carry a `Ty 0 0` (the def's kernel type)
and a typed `Term` value, for full elaboration support. -/
structure ResolvedDef where
  /-- The definition's kernel RawTerm at module scope (0). -/
  rawTerm : RawTerm 0

/-- The global environment.  Maps qualified names to their
kernel-form definitions.  Total function (returns `none` for
unknown names). -/
structure Env where
  lookup : QualifiedName → Option ResolvedDef

/-- The empty environment — every lookup returns `none`. -/
def Env.empty : Env := { lookup := fun _ => none }

/-- Iterated weakening: `RawTerm sourceScope` lifted to
`RawTerm (sourceScope + n)` by applying `RawTerm.weaken` n
times.  Structural recursion on the iteration count. -/
def RawTerm.weakenIter {sourceScope : Nat}
    (term : RawTerm sourceScope) : ∀ (n : Nat), RawTerm (sourceScope + n)
  | 0 => term
  | n + 1 => (RawTerm.weakenIter term n).weaken

/-- Lift a module-scope (`RawTerm 0`) definition to the caller's
scope.  Implementation: iterate kernel `RawTerm.weaken`
(`Foundation/RawSubst.lean`) `scope` times.

`Nat.zero_add` reconciles the result type — `RawTerm (0 + scope)`
is definitionally `RawTerm scope`. -/
def ResolvedDef.liftToScope {scope : Nat} (rd : ResolvedDef) :
    Option (RawTerm scope) :=
  some (Nat.zero_add scope ▸ RawTerm.weakenIter rd.rawTerm scope)

/-- Sketch: resolve an `RawExpr` to a kernel `RawTerm` using an
environment.  Currently calls `RawExpr.toRawTerm?` (env-free)
for non-free-name cases and uses `env.lookup` + `liftToScope`
for free names.

Note: this is currently INCOMPLETE — the env-aware path only
handles free names at scope 0.  Lifting at higher scopes is
gated on `RawTermSubst.shift` integration. -/
def RawExpr.toRawTermWithEnv? {scope : Nat} (env : Env) :
    RawExpr scope → Option (RawTerm scope)
  | .rawFree qname =>
    match env.lookup qname with
    | none => none
    | some rd => rd.liftToScope
  -- All other cases delegate to the env-free bridge.  Recursion
  -- through compound forms (rawApp, rawLam, etc.) currently
  -- doesn't pass the env through subterms — env-aware recursion
  -- requires reproducing the bridge's structure here.  Phase
  -- 10.C work item.
  --
  -- Full enumeration (rather than `| other => ...`) keeps this
  -- propext-clean per Rule 2 of the match recipe.
  | r@(.rawBound _) => RawExpr.toRawTerm? r
  | r@(.rawLit _) => RawExpr.toRawTerm? r
  | r@.rawUnit => RawExpr.toRawTerm? r
  | r@(.rawParen _) => RawExpr.toRawTerm? r
  | r@(.rawDot _ _) => RawExpr.toRawTerm? r
  | r@(.rawApp _ _) => RawExpr.toRawTerm? r
  | r@(.rawBinop _ _ _) => RawExpr.toRawTerm? r
  | r@(.rawUnop _ _) => RawExpr.toRawTerm? r
  | r@(.rawLam _ _ _) => RawExpr.toRawTerm? r
  | r@(.rawBlock _ _) => RawExpr.toRawTerm? r
  | r@(.rawIf _ _ _) => RawExpr.toRawTerm? r

end LeanFX2.Surface
