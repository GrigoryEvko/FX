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

/-! ### Per-ctor denotation corollaries (B02-B07 collapse) -/

#assert_no_axioms LeanFX2.Surface.Expr.denote_boundExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_freeNameExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_unitExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_litExpr_unitLit
#assert_no_axioms LeanFX2.Surface.Expr.denote_litExpr_boolTrue
#assert_no_axioms LeanFX2.Surface.Expr.denote_litExpr_boolFalse
#assert_no_axioms LeanFX2.Surface.Expr.denote_litExpr_intLit_zero
#assert_no_axioms LeanFX2.Surface.Expr.denote_litExpr_strLit
#assert_no_axioms LeanFX2.Surface.Expr.denote_appExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_lamExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_ifExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_blockExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_parenExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_dotExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_binopExpr
#assert_no_axioms LeanFX2.Surface.Expr.denote_unopExpr

/-! ### B12 partial: gap-free fragment totality (atomic + compositional) -/

#assert_no_axioms LeanFX2.Surface.Literal.isGapFree
#assert_no_axioms LeanFX2.Surface.RawExpr.isGapFree
#assert_no_axioms LeanFX2.Surface.OptRawExpr.isGapFree
#assert_no_axioms LeanFX2.Surface.RawArgList.isGapFree
#assert_no_axioms LeanFX2.Surface.RawCallArg.isGapFree
#assert_no_axioms LeanFX2.Surface.RawStmtList.isGapFree
#assert_no_axioms LeanFX2.Surface.Literal.bridgeIsTotalOnGapFree
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawBound
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawUnit
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawLit
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawParen
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawLam
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawApp
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnBoundExpr
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnUnitExpr
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnLitExpr

end LeanFX2.Tools
