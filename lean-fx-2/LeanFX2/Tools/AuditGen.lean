import LeanFX2.Tools.DependencyAudit

/-! # Tools/AuditGen — auto-generation of AuditAll gates

Crawls the project's namespace for theorems/defs/inductives and
emits `#assert_no_axioms <name>` for each.  Output goes to
`Tools/AuditAll.lean`.

## Tactic interface

```lean
#auditgen LeanFX2 -- emit gates for everything under LeanFX2 namespace
```

Walks the environment, filters to user-declared (not stdlib)
declarations, and emits the gate file.

## Why auto-generate

lean-fx's `AuditAll.lean` was manually maintained — 660 lines of
hand-written `#assert_no_axioms` lines that drift as the kernel
evolves.  Auto-generation eliminates the drift.

## Workflow

1. Develop kernel changes
2. Run `#auditgen LeanFX2` to regenerate `AuditAll.lean`
3. `lake build` re-checks all gates
4. Commit the regenerated `AuditAll.lean` alongside the change

## Dependencies

* `Tools/DependencyAudit.lean`

## Downstream

* `Tools/AuditAll.lean` — generated output

## Implementation plan (Layer 12)

1. Tactic that crawls `Environment.constants`
2. Filter to project namespace (exclude `Init.*`, `Std.*`, `Lean.*`)
3. Emit `#assert_no_axioms` lines
4. Optionally annotate each with the file/line of the declaration

Target: ~150 lines.
-/

namespace LeanFX2.Tools

-- TODO Layer 12: #auditgen command

end LeanFX2.Tools
