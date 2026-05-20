import LeanFX2.Tools.DependencyAudit

/-! # Tools/Tactics/AuditBatch — batched zero-axiom gate emitter

`#assert_no_axioms_batch [decl1, decl2, decl3]` expands to one
`#assert_no_axioms` command per name in the list, in declaration
order.  Per-decl elaboration semantics is unchanged: each child
still elaborates separately and reports its own axiom-set against
`Tools/DependencyAudit.lean`'s sweep.

The batch command saves only source LoC in audit gate files where
dozens of named decls are audited back-to-back (e.g.
`Tools/AuditAll/AuditTerm.lean` has ~1088 individual gates,
`AuditReduction.lean` has ~380).  Build-time elaboration tax of
N batched gates equals the tax of N individual gates — no
performance regression, no aggregation, no cross-decl diagnostic.

Deliberately thin: no search beyond the explicit name list.  An
empty list `[]` is a no-op.  A list with one name behaves exactly
like the single gate.

## Dependency footprint

Imports only `LeanFX2.Tools.DependencyAudit` (which defines the
underlying `#assert_no_axioms` command).  No production-layer
imports — this file is cache-immortal under kernel changes.
-/

open Lean Elab Command

namespace LeanFX2.Tools.Tactics

/-- Syntax: `#assert_no_axioms_batch [name1, name2, name3]`.

Emits one `#assert_no_axioms <name>` command per identifier in the
bracketed list.  Each emitted command elaborates independently;
batch failure on one name does not skip subsequent gates. -/
syntax (name := assertNoAxiomsBatchCmd)
  "#assert_no_axioms_batch" "[" ident,* "]" : command

@[command_elab assertNoAxiomsBatchCmd]
def elabAssertNoAxiomsBatch : CommandElab := fun cmdSyntax => do
  match cmdSyntax with
  | `(#assert_no_axioms_batch [$names,*]) =>
      for nameSyntax in names.getElems do
        let singleGate ← `(#assert_no_axioms $nameSyntax)
        elabCommand singleGate
  | _ => throwUnsupportedSyntax

end LeanFX2.Tools.Tactics
