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

/-! ### B12 compositional: helper-family + remaining ctors (#1252) -/

#assert_no_axioms LeanFX2.Surface.OptRawExpr.bridgeIsTotalOnRawNone
#assert_no_axioms LeanFX2.Surface.OptRawExpr.bridgeIsTotalOnRawSome
#assert_no_axioms LeanFX2.Surface.RawArgList.bridgeIsTotalOnRawNilArg
#assert_no_axioms LeanFX2.Surface.RawArgList.bridgeIsTotalOnRawConsArg
#assert_no_axioms LeanFX2.Surface.RawCallArg.bridgeIsTotalOnRawPositional
#assert_no_axioms LeanFX2.Surface.RawCallArg.bridgeIsTotalOnRawNamed
#assert_no_axioms LeanFX2.Surface.RawCallArg.bridgeIsTotalOnRawImplicit
#assert_no_axioms LeanFX2.Surface.RawStmtList.bridgeIsTotalOnRawNilStmt
#assert_no_axioms LeanFX2.Surface.RawStmtList.bridgeIsTotalOnRawLetCons
#assert_no_axioms LeanFX2.Surface.RawStmtList.bridgeIsTotalOnRawExprCons
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawIf
#assert_no_axioms LeanFX2.Surface.RawExpr.bridgeIsTotalOnRawBlock
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnParenExpr
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnLamExpr
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnAppExpr
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnIfExpr
#assert_no_axioms LeanFX2.Surface.Expr.denoteIsTotalOnBlockExpr

/-! ### Surface.KernelBridge — env-free bridge core (#1531) -/

#assert_no_axioms LeanFX2.Surface.RawTerm.natOfNat
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?
#assert_no_axioms LeanFX2.Surface.RawArgList.foldApps?
#assert_no_axioms LeanFX2.Surface.RawCallArg.toRawTerm?
#assert_no_axioms LeanFX2.Surface.OptRawExpr.toRawTermOrUnit?
#assert_no_axioms LeanFX2.Surface.RawStmtList.foldBlock?
#assert_no_axioms LeanFX2.Surface.Expr.toRawTerm?

/-! ### Surface.KernelEnv — env-aware bridge core (#1531) -/

#assert_no_axioms LeanFX2.Surface.KernelEnv.empty
#assert_no_axioms LeanFX2.Surface.RawTerm.weakenIter
#assert_no_axioms LeanFX2.Surface.ResolvedDef.liftToScope
#assert_no_axioms LeanFX2.Surface.Literal.toRawTermWithEnv?
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?
#assert_no_axioms LeanFX2.Surface.RawArgList.foldAppsEnv?
#assert_no_axioms LeanFX2.Surface.RawCallArg.toRawTermWithEnv?
#assert_no_axioms LeanFX2.Surface.OptRawExpr.toRawTermOrUnitEnv?
#assert_no_axioms LeanFX2.Surface.RawStmtList.foldBlockEnv?
#assert_no_axioms LeanFX2.Surface.Expr.toRawTermWithEnv?

/-! ### Surface.KernelEnvCorrespondence — env-empty equivalence (#1531) -/

#assert_no_axioms LeanFX2.Surface.KernelEnv.empty_lookup_eq
#assert_no_axioms LeanFX2.Surface.Literal.bridge_inclusion

/-! ### Surface.KernelEnvCorrespondence — B10 atomic + vacuous inclusion (#1250) -/

#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_inclusion_rawBound
#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_inclusion_rawUnit
#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_inclusion_rawLit
#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_inclusion_rawFree
#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_inclusion_rawDot
#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_inclusion_rawBinop
#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_inclusion_rawUnop

/-! ### Surface.KernelBridgeReduction — R-series per-ctor reduction lemmas (#1531) -/

#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_unitLit
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_boolLit_true
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_boolLit_false
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_intLit_zero
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_decLit
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_floatLit
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_strLit
#assert_no_axioms LeanFX2.Surface.Literal.toRawTerm?_intLit_neg
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawBound
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawFree
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawLit
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawUnit
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawParen
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawDot
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawApp
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawBinop
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawUnop
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawLam
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawBlock
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTerm?_rawIf
#assert_no_axioms LeanFX2.Surface.RawArgList.foldApps?_rawNilArg
#assert_no_axioms LeanFX2.Surface.RawArgList.foldApps?_rawConsArg
#assert_no_axioms LeanFX2.Surface.RawCallArg.toRawTerm?_rawPositional
#assert_no_axioms LeanFX2.Surface.RawCallArg.toRawTerm?_rawNamed
#assert_no_axioms LeanFX2.Surface.RawCallArg.toRawTerm?_rawImplicit
#assert_no_axioms LeanFX2.Surface.OptRawExpr.toRawTermOrUnit?_rawNone
#assert_no_axioms LeanFX2.Surface.OptRawExpr.toRawTermOrUnit?_rawSome
#assert_no_axioms LeanFX2.Surface.RawStmtList.foldBlock?_rawNilStmt
#assert_no_axioms LeanFX2.Surface.RawStmtList.foldBlock?_rawLetCons
#assert_no_axioms LeanFX2.Surface.RawStmtList.foldBlock?_rawExprCons

/-! ### Surface.GrammarToken — C09 reserved-non-token catalogue (#1225) -/

#assert_no_axioms LeanFX2.Surface.Token.spellingsOfReservedNonTokens
#assert_no_axioms LeanFX2.Surface.Token.spellingsOfReservedNonTokens_catalogue
#assert_no_axioms LeanFX2.Surface.Token.spellingsOfReservedNonTokens_length

/-! ### Surface.KernelEnv — S01/S02/S03 binop syntactic-role smoke (#1285-#1287) -/

#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawBinop_pipe
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawBinop_arrow
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawBinop_isCtor

/-! ### Surface.KernelEnv — B08 env-aware binopExpr correctness (#1248) -/

#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawBinop_plus
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawBinop_eqEq
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawBinop_logicalAnd
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawBinop_bitAnd

/-! ### Surface.KernelEnv — B09 env-aware freeNameExpr correctness (#1249) -/

#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawFree
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawFree_lookupNone
#assert_no_axioms LeanFX2.Surface.RawExpr.toRawTermWithEnv?_rawFree_lookupSome

/-! ### Surface.Semantics — S04 bridge invariant theorems (#1288) -/

#assert_no_axioms LeanFX2.Surface.Expr.bridge_invariant
#assert_no_axioms LeanFX2.Surface.RawExpr.bridge_invariant

/-! ### Surface.Lex — L02 classifyIdent reversal correctness (#1200) -/

#assert_no_axioms LeanFX2.Surface.Lex.classifyIdent_kwTrue
#assert_no_axioms LeanFX2.Surface.Lex.classifyIdent_kwFalse
#assert_no_axioms LeanFX2.Surface.Lex.classifyIdent_keyword_toToken

/-! ### Surface.Lex — L07 LexError offset projection (#1205) -/

#assert_no_axioms LeanFX2.Surface.LexError.offset
#assert_no_axioms LeanFX2.Surface.LexError.offset_unexpectedChar
#assert_no_axioms LeanFX2.Surface.LexError.offset_unterminatedString
#assert_no_axioms LeanFX2.Surface.LexError.offset_invalidEscape
#assert_no_axioms LeanFX2.Surface.LexError.offset_total

/-! ### Surface.Lex — L07 per-step preservation theorems (#1205)

Branch-helper preservation: `lexStringBranch`, `lexOpOrPunct`,
`lexIdentBranch`, `lexDigitBranch` all preserve the `offset`
parameter through any emitted `LexError`.  Composed via
`lexOne_error_offset_eq`. -/

#assert_no_axioms LeanFX2.Surface.lexTwoCharOp
#assert_no_axioms LeanFX2.Surface.lexTwoCharPeek
#assert_no_axioms LeanFX2.Surface.lexSingleCharPunct
#assert_no_axioms LeanFX2.Surface.lexOpOrPunct
#assert_no_axioms LeanFX2.Surface.lexStringBranch
#assert_no_axioms LeanFX2.Surface.lexIdentBranch
#assert_no_axioms LeanFX2.Surface.lexDigitBranch
#assert_no_axioms LeanFX2.Surface.Lex.lexStringBranch_error_offset_eq
#assert_no_axioms LeanFX2.Surface.Lex.lexOpOrPunct_error_offset_eq
#assert_no_axioms LeanFX2.Surface.Lex.lexIdentBranch_no_error
#assert_no_axioms LeanFX2.Surface.Lex.lexDigitBranch_no_error
#assert_no_axioms LeanFX2.Surface.Lex.lexOne_error_offset_eq

/-! ### Surface.StdNames — G05/G06 propositional + range desugaring (#1257, #1258) -/

#assert_no_axioms LeanFX2.Surface.BinaryOp.toQualifiedName_iff
#assert_no_axioms LeanFX2.Surface.BinaryOp.toQualifiedName_implies
#assert_no_axioms LeanFX2.Surface.BinaryOp.toQualifiedName_rangeExcl
#assert_no_axioms LeanFX2.Surface.BinaryOp.toQualifiedName_rangeIncl

end LeanFX2.Tools
