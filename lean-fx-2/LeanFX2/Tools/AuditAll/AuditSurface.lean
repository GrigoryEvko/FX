import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2

namespace LeanFX2.Tools

/-! ## AuditSurface — surface-layer per-decl axiom gates.

Tracker #1241 (B01 — denotational semantics) and #1531
(SURFACE-AUDIT-GATES — broader surface coverage).  This file
hosts the strict per-decl `#assert_no_axioms` checks for the
surface layer's load-bearing definitions and theorems.  The
namespace sweep `#audit_namespace LeanFX2` already covers
everything in `LeanFX2.Surface.*` automatically; the explicit
gates below ensure load-bearing names appear in the curated
ledger so a regression cannot slip through silently.
-/

/-! ### Surface.Semantics — denotational ⟦·⟧ for `Expr scope` -/

#assert_no_axioms LeanFX2.Surface.RawExpr.denote
#assert_no_axioms LeanFX2.Surface.Expr.denote
#assert_no_axioms LeanFX2.Surface.RawExpr.denote_eq_toRawTerm?
#assert_no_axioms LeanFX2.Surface.Expr.denote_eq_toRawTerm?
#assert_no_axioms LeanFX2.Surface.Expr.denote_eq_RawExpr_denote

end LeanFX2.Tools
