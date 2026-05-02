import LeanFX2.Surface.Token

/-! # Surface/AST — surface abstract syntax tree

Pre-elaboration AST.  Each node carries source position for error
reporting.  Strict 1:1 with `fx_grammar.md` §3-§9 EBNF productions.

## Node categories (per fx_grammar.md)

```lean
inductive Expr        -- expression nodes
  | identExpr (name : String) (pos : Pos)
  | litExpr (lit : Literal) (pos : Pos)
  | appExpr (fn : Expr) (args : Array (Option String × Expr))
  | lamExpr (params : Array Param) (body : Expr)
  | letExpr (binding : LetBinding) (body : Expr)
  | ifExpr (cond : Expr) (thenBr : Expr) (elseBr : Option Expr)
  | matchExpr (scrut : Expr) (arms : Array MatchArm)
  | beginExpr (stmts : Array Stmt)
  | piTyExpr (params : Array Param) (codomain : Expr)
  | sigmaTyExpr (firstType : Expr) (secondType : Expr)
  | dotExpr (obj : Expr) (field : String)
  | binopExpr (op : Op) (lhs : Expr) (rhs : Expr)
  -- ... more
```

```lean
inductive Decl       -- top-level declarations
  | fnDecl (...)
  | typeDecl (...)
  | machineDecl (...)
  | contractDecl (...)
  | classDecl (...)
  | instanceDecl (...)
  -- ... more

inductive Pattern    -- match patterns
  | wildcardPat
  | identPat (name : String)
  | ctorPat (ctor : String) (subpats : Array Pattern)
  | litPat (lit : Literal)
  | orPat (alts : Array Pattern)
  -- ... more
```

## Position tracking

Every node carries `Pos { file, line, col, length }` for diagnostics.
Pretty printer (`Surface/Print.lean`) preserves source spans.

## Dependencies

* `Surface/Token.lean` — for `Pos` definitions

## Downstream

* `Surface/Parse.lean` — produces ASTs
* `Surface/Print.lean` — consumes them
* `Surface/Elab.lean` — elaborates AST → kernel Term

## Implementation plan (Layer 10)

1. Define `Expr`, `Decl`, `Pattern` mutually
2. Position tracking utilities
3. DecidableEq (manual to avoid propext)

Target: ~800 lines.
-/

namespace LeanFX2.Surface

-- TODO Layer 10: AST inductives (Expr / Decl / Pattern / Stmt)
-- TODO Layer 10: position tracking
-- TODO Layer 10: DecidableEq

end LeanFX2.Surface
