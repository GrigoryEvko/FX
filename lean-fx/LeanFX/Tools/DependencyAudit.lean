import Lean

/-! # Dependency-audit tool — full trust footprint of a theorem.

`#print axioms FOO` reports only `axiom` declarations in `FOO`'s
transitive dependency.  This file extends the audit to every kind of
constant the proof reaches: definitions, theorems, inductives,
constructors, recursors, quotients, opaque declarations.

## Why count more than axioms

A theorem's trust budget has multiple components:

  * **Axioms** — the strongest commitment.  Each adds logical content
    that CIC alone cannot derive.  `propext`, `ua_wire`, etc.
  * **Definitions** — conservative extensions, but each one is a name
    the Lean kernel must typecheck correctly.  A buggy kernel handling
    a definition is just as unsound as accepting a bogus axiom.
  * **Inductives** — strict-positivity-checked types whose recursors
    are auto-generated.  Trust the inductive scheme + the recursor.
  * **Theorems** — proven facts.  Trust the proof body's typecheck.

The Metamath-Zero ethos: definitions don't add logical power, but
they expand the surface the verifier must implement correctly.
Tracking them gives a complete picture of the trust footprint.

## Usage

```
import LeanFX.Tools.DependencyAudit

-- For an individual constant:
#audit_dependencies LeanFX.Syntax.Ty.subst_id

-- Output:
--   Dependency audit for 'LeanFX.Syntax.Ty.subst_id':
--     axioms:       0
--     theorems:     N
--     definitions:  M
--     inductives:   K
--     constructors: ...
--     recursors:    ...
--     quotients:    ...
--     opaques:      ...
--     TOTAL:        sum
```

The command ignores constants in the `Lean.*` and `Init.*` namespaces
by default — those are stdlib plumbing that lives below the lean-fx
trust boundary.  Pass `(includeStdlib := true)` to include them.

## Scope of the tool

This file lives outside the `LeanFX/Foundation/` tree and outside
`LeanFX/Syntax/`.  It is a metaprogram, not part of the kernel's
trust base — bugs in this tool would cause incorrect *audit reports*,
never incorrect *proofs*.  The discipline against `partial def`
applies to foundation/syntax; this tool may use whatever Lean
metaprogramming machinery is convenient.

## What the audit cannot tell you

  * Whether a definition is sneakily nontrivial (e.g., uses `Decidable`
    machinery that pulls `propext` via auto-deriving).  The axiom
    count catches that.
  * Whether the kernel itself has a bug.  The kernel is the bottom
    of the trust base; nothing in lean-fx audits it.
  * Whether a definition's proof obligations are satisfied (that's
    what `#print` and elaboration time-checking do).

Combined with `#print axioms`, this gives a complete picture for
the human-checkable layer. -/

namespace LeanFX.Tools.DependencyAudit

open Lean

/-- Dependency-count statistics for one constant's transitive
dependency graph.  Each field is a count; `axiomNames` carries the
actual names of the axioms encountered for inspection. -/
structure Stats where
  axioms       : Nat := 0
  theorems     : Nat := 0
  definitions  : Nat := 0
  inductives   : Nat := 0
  constructors : Nat := 0
  recursors    : Nat := 0
  quotients    : Nat := 0
  opaques      : Nat := 0
  axiomNames   : Array Name := #[]
  deriving Inhabited, Repr

/-- Pretty-printed audit output. -/
def Stats.format (s : Stats) (target : Name) : String :=
  let total := s.axioms + s.theorems + s.definitions + s.inductives
             + s.constructors + s.recursors + s.quotients + s.opaques
  let axiomLine :=
    if s.axiomNames.isEmpty then s!"axioms:       {s.axioms}"
    else
      let nameList := s.axiomNames.toList.map toString |>.intersperse ", "
      s!"axioms:       {s.axioms}  [{String.join nameList}]"
  s!"Dependency audit for '{target}':\n" ++
  s!"  {axiomLine}\n" ++
  s!"  theorems:     {s.theorems}\n" ++
  s!"  definitions:  {s.definitions}\n" ++
  s!"  inductives:   {s.inductives}\n" ++
  s!"  constructors: {s.constructors}\n" ++
  s!"  recursors:    {s.recursors}\n" ++
  s!"  quotients:    {s.quotients}\n" ++
  s!"  opaques:      {s.opaques}\n" ++
  s!"  TOTAL:        {total}"

/-- Heuristic for "is this name part of stdlib plumbing".  Used to
filter audit output by default; the trust below this boundary is
Lean-the-system, not lean-fx. -/
def isStdlibPlumbing (n : Name) : Bool :=
  n.isInternal || n.getRoot == `Lean ||
  n.getRoot == `Init || n.getRoot == `Std || n.getRoot == `IO

/-- Get the body and type expressions of a constant.  Returns
`(type, value?)` — the type is always present, the value only for
non-axiom non-inductive declarations. -/
private def constExprs (info : ConstantInfo) : Expr × Option Expr :=
  (info.type, info.value?)

/-- Walk the dependency graph from a starting name, accumulating
all transitively-referenced constants.  Bounded by the finite
environment size; uses `partial def` because Lean cannot derive
termination automatically through the worklist. -/
private partial def collectAllDeps
    (env : Environment) (includeStdlib : Bool) (start : Name) :
    NameSet :=
  go (NameSet.empty.insert start) #[start]
where
  go (visited : NameSet) (queue : Array Name) : NameSet :=
    if queue.isEmpty then visited
    else
      let current := queue.back!
      let queue := queue.pop
      match env.find? current with
      | none => go visited queue
      | some info =>
        let typeRefs := info.type.foldConsts NameSet.empty (fun n s => s.insert n)
        let valueRefs := match info.value? with
          | some v => v.foldConsts NameSet.empty (fun n s => s.insert n)
          | none => NameSet.empty
        let allRefsList := typeRefs.toList ++ valueRefs.toList
        let newVisited := allRefsList.foldl (init := visited) fun acc n =>
          if !includeStdlib && isStdlibPlumbing n then acc
          else if acc.contains n then acc
          else acc.insert n
        let newQueue := allRefsList.foldl (init := queue) fun acc n =>
          if !includeStdlib && isStdlibPlumbing n then acc
          else if visited.contains n then acc
          else acc.push n
        go newVisited newQueue

/-- Compute the audit statistics for a constant, walking the
dependency graph and classifying each visited name. -/
def computeStats (env : Environment) (target : Name)
    (includeStdlib : Bool := false) : Stats :=
  let deps := collectAllDeps env includeStdlib target
  deps.toList.foldl (init := ({} : Stats)) fun s name =>
    match env.find? name with
    | none => s
    | some info =>
      match info with
      | .axiomInfo _ =>
        { s with
            axioms := s.axioms + 1,
            axiomNames := s.axiomNames.push name }
      | .thmInfo _ => { s with theorems := s.theorems + 1 }
      | .defnInfo _ => { s with definitions := s.definitions + 1 }
      | .inductInfo _ => { s with inductives := s.inductives + 1 }
      | .ctorInfo _ => { s with constructors := s.constructors + 1 }
      | .recInfo _ => { s with recursors := s.recursors + 1 }
      | .quotInfo _ => { s with quotients := s.quotients + 1 }
      | .opaqueInfo _ => { s with opaques := s.opaques + 1 }

/-- Command syntax — emits the audit report for a single constant.

  `#audit_dependencies FOO` — count constants in lean-fx scope only
  `#audit_dependencies_full FOO` — include Lean stdlib plumbing
-/
elab "#audit_dependencies" name:ident : command => do
  let env ← getEnv
  let target := name.getId
  if !env.contains target then
    throwError s!"unknown constant: {target}"
  let stats := computeStats env target (includeStdlib := false)
  logInfo (stats.format target)

elab "#audit_dependencies_full" name:ident : command => do
  let env ← getEnv
  let target := name.getId
  if !env.contains target then
    throwError s!"unknown constant: {target}"
  let stats := computeStats env target (includeStdlib := true)
  logInfo (stats.format target)

end LeanFX.Tools.DependencyAudit
