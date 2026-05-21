import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.StrengtheningImage.AggregatorTotalCore

/-! # AuditTerm.AggregatorTotal

Residual arbitrary-strengthening predicate gate.
-/

namespace LeanFX2.Tools

-- Keep the arbitrary-strengthening predicate audited.  The obsolete
-- per-constructor and binder compatibility wrappers have been removed; actual
-- weakening-image consumers use `AuditTerm.TotalOnWeaken`.
#assert_no_axioms LeanFX2.Term.IsAggregatorTotal

end LeanFX2.Tools
