import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen

namespace LeanFX2.Tools

open Lean Elab Command

open Lean Elab Command

/-! ## Audit count cache (env extension)

Each `#assert_*_dependent_budget` and similar budget gate writes the
count of violations it finds into a persistent env extension keyed
by gate name.  The aggregate dashboard reads from this cache instead
of recomputing the counts, which would otherwise take ~90 seconds
for ~22 redundant transitive-dependency walks per LeanFX2 decl.

Workflow:

1. Each budget-gate `elab` calls `recordAuditCount gateName count`
   after computing its violations array size.
2. The olean for that gate file persists the entry.
3. When `Tools/AuditAll/SummaryDebtDashboard.lean` imports the gate
   files (transitively via the umbrella prelude), Lean merges all
   env extension states.
4. The dashboard's `#audit_debt_dashboard` calls
   `lookupAuditCount environment gateName` instead of recomputing.

Persistence is per-gate-name: writing the same gate name twice
appends a new entry; the lookup returns the most recently-written
count. -/

/-- One cached audit-gate count. -/
structure AuditCountEntry where
  /-- Identifier for the gate, e.g. ``inhabited_dependent``. -/
  gateName : Name
  /-- Count of violations the gate found.  Renders directly in the
  debt dashboard. -/
  count : Nat
  deriving Inhabited

initialize auditCountExt :
    SimplePersistentEnvExtension AuditCountEntry (Array AuditCountEntry) ←
  registerSimplePersistentEnvExtension {
    name := `LeanFX2.Tools.auditCountExt
    addEntryFn := fun pendingEntries newEntry => pendingEntries.push newEntry
    addImportedFn := fun perFileEntryArrays =>
      perFileEntryArrays.foldl Array.append (#[] : Array AuditCountEntry)
  }

/-- Record one audit-gate count to the env extension.  Called by each
budget-gate `elab` after its violations array has been computed. -/
def recordAuditCount (gateName : Name) (count : Nat) :
    CommandElabM Unit := do
  modifyEnv fun environmentToUpdate =>
    auditCountExt.addEntry
      environmentToUpdate
      { gateName := gateName, count := count }

/-- Look up the most-recently-recorded count for a named gate.  Used
by the aggregate debt dashboard to avoid recomputing per-gate counts.
Returns `none` when no gate has recorded a count under that name yet
(typically only on the first build before all gates have fired).  The
fold scans entries left-to-right; if a gate writes multiple times
during one build, the rightmost write wins. -/
def lookupAuditCount (environment : Environment) (gateName : Name) :
    Option Nat :=
  let entries := auditCountExt.getState environment
  entries.foldl
    (init := (none : Option Nat))
    (fun latestSoFar entry =>
      if entry.gateName == gateName then some entry.count else latestSoFar)

/-- Look up an audit count, defaulting to zero when no entry exists.
Convenience for the dashboard, which prefers a numeric default to
an `Option`-shaped renderer. -/
def lookupAuditCountOrZero (environment : Environment) (gateName : Name) :
    Nat :=
  (lookupAuditCount environment gateName).getD 0

end LeanFX2.Tools
