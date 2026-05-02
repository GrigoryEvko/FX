/-! # Tools/DependencyAudit — per-decl axiom + dependency inspector

The load-bearing audit infrastructure: inspect any declaration's
transitive axiom + definition footprint.  Used by `Tools/AuditAll.lean`
to enforce zero-axiom across the kernel.

## API

```lean
def computeStats (env : Environment) (target : Name)
    (includeStdlib : Bool := true) :
    DependencyStats
```

`DependencyStats` records:
* axiom names (transitive)
* theorem count
* definition count
* inductive count
* constructor count
* recursor count
* quotient count
* opaque count

## Two important commands

```lean
#audit_dependencies SomeTheorem
-- prints the full DependencyStats — useful during development
```

```lean
#assert_no_axioms SomeTheorem
-- typecheck-time check that no axioms are in the dependency tree;
-- compiler error if any (including stdlib propext / Quot.sound /
-- Classical.choice).  This is the canonical Layer K/M/E gate.
```

## Why include stdlib

The audit *must* count stdlib axioms (propext, Quot.sound,
Classical.choice).  Excluding them hides the real trust footprint.
Per `AXIOMS.md` policy, Layers K/M/E are strict about NO stdlib
axiom dependencies.

## Per-axiom catastrophe analysis

When `#assert_no_axioms` fails, the error message points at the
specific axiom + the chain of definitions that pulled it in.  See
`AXIOMS.md` for the per-axiom catastrophe analysis (P-1/P-2/P-3 for
propext, Q-1..3 for Quot.sound, C-1..3 for Classical.choice).

## Dependencies

* Lean.Elab.Command, Lean.Environment

## Downstream

* `Tools/AuditAll.lean` — invokes `#assert_no_axioms` per kernel decl
* CI scripts — gate builds on zero-axiom invariant

## Implementation plan (Layer 12)

1. Port from lean-fx's `LeanFX/Tools/DependencyAudit.lean` (~150 lines)
2. Adapt namespace + `LeanFX2.Tools` location

Target: ~150 lines.
-/

namespace LeanFX2.Tools

-- TODO Layer 12: DependencyStats structure
-- TODO Layer 12: computeStats traversal
-- TODO Layer 12: #audit_dependencies command
-- TODO Layer 12: #assert_no_axioms command (the core gate)

end LeanFX2.Tools
