import LeanFX2.Term.Subst0RenameCommute

/-! # AuditStrengthT8 — strength-T8 subst/rename fusion reviewer log.

Reviewer-facing axiom-cleanliness log for the strength-T8 chain.  Every shipped
declaration here must report "does not depend on any axioms" — the canonical
machine-enforced gates are the `#assert_no_axioms` directives in
`Tools/AuditAll/AuditTerm/StrengthT8.lean`; this file is the supplementary
regression record (`#print axioms`).

## What landed

* Substrate: typed-Term rename functoriality `Term.rename_rename` (78-arm,
  HEq-valued), the rename-pointwise heterogeneous bridge
  `Term.rename_pointwise_HEq`, and the corollary `Term.rename_weaken_commute`
  (rename commutes with single-binder weakening).
* The ScR engine `Term.subst_rename_commute` (78-arm) and its three binder arms,
  closing the engine via `TermSubst.renameOutput_lift_entry_HEq` (whose var(k+1)
  case discharges a rename-of-weaken through `Term.rename_weaken_commute`).
* T8 headline `Term.subst0_rename_commute` (#1964): the two-engine corollary
  joining ScR (LHS) and RcS (RHS) by the singleton pointwise bridge. -/

namespace LeanFX2.Smoke

#print axioms LeanFX2.Term.rename_rename
#print axioms LeanFX2.Term.rename_pointwise_HEq
#print axioms LeanFX2.Term.rename_weaken_commute
#print axioms LeanFX2.TermSubst.renameOutput_lift_entry_HEq
#print axioms LeanFX2.Term.subst_rename_commute
#print axioms LeanFX2.Term.subst0_rename_commute

end LeanFX2.Smoke
