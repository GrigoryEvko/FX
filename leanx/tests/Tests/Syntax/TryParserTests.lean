import FX.Syntax.Lexer
import FX.Syntax.Parser
import Tests.Framework

/-!
# `try EXPR` prefix parser tests (task E-3, parser half)

Per `fx_design.md` §4.9 control-flow vs enabling-effect split.
`try` is a prefix keyword that marks a call whose callee has
`Fail(E)` / `Exn(E)` in its effect row; the failure propagates
to the nearest enclosing `try-catch` handler.  The elaborator
currently passes `try EXPR` through to `EXPR` — full E042
emission lands once the `Fail` effect is wired in
`FX.Kernel.Effect` (follow-on).  These tests pin the parser
shape only.

Split into its own file from `ParserTests.lean` because the
`run` do-block in `ParserTests.lean` already hits Lean 4's
elaboration-depth ceiling.  Each new scenario there risks a
`maximum recursion depth has been reached` error — one more
reason the file split pattern matters.
-/

namespace Tests.Syntax.TryParserTests

open Tests FX.Syntax FX.Syntax.Ast

/-- Lex + parse; return decls plus any parse errors.  Mirrors
    `ParserTests.parse`. -/
def parse (sourceText : String) : Array Decl × Array FX.Util.Error :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (fileResult, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  (fileResult.decls, lexOut.errors ++ parseErrs)

/-- Extract a function body's expression (one-liner only). -/
def fnOneLiner? : Decl → Option Expr
  | .fnDecl _ _ _ _ _ _ _ (FnBody.oneLiner e) _ => some e
  | _                                           => none

/-- True iff the expression is a `try`-prefix wrapper. -/
def isTryPrefix : Expr → Bool
  | .tryPrefix _ _ => true
  | _              => false

/-- True iff the expression is a binop. -/
def isBinop : Expr → Bool
  | .binop _ _ _ _ => true
  | _              => false

def run : IO Unit := do
  /- ## 1. `try` wraps a function call — the canonical use. -/
  let (decls, errs) := parse "fn f() : i64 = try g();"
  check "1. try g(): no parse errors" 0 errs.size
  let bodyIsTry : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some expr => isTryPrefix expr
    | none      => false
  check "1. try g(): fn body is tryPrefix" true bodyIsTry

  /- ## 2. `try EXPR + 1` parses as `(try EXPR) + 1` — `try`
     binds at the prefix level, tighter than additive. -/
  let (decls, errs) := parse "fn f() : i64 = try g() + 1;"
  check "2. try g() + 1: no parse errors" 0 errs.size
  let bodyIsBinop : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some expr => isBinop expr
    | none      => false
  check "2. try g() + 1: top is binop, not tryPrefix" true bodyIsBinop

  /- ## 3. `try try f()` parses as `try (try f())` —
     right-associative.  Semantically redundant but legal
     grammar. -/
  let (decls, errs) := parse "fn f() : i64 = try try g();"
  check "3. try try g(): no parse errors" 0 errs.size
  let nestedTry : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some (.tryPrefix inner _) => isTryPrefix inner
    | _                          => false
  check "3. try try g(): nests as try (try g())" true nestedTry

  /- ## 4. `try -x` parses as `try (-x)` — prefix operators
     right-chain. -/
  let (decls, errs) := parse "fn f() : i64 = try -g();"
  check "4. try -g(): no parse errors" 0 errs.size
  let tryOverNeg : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some (.tryPrefix (.prefix_ _ _ _) _) => true
    | _                                     => false
  check "4. try -g(): tryPrefix wrapping prefix_" true tryOverNeg

  /- ## 5. Parenthesized: `(try g()) + 1` is equivalent shape
     to the unparenthesized form (tryPrefix at the LHS of
     binop).  Sanity-check parser doesn't collapse the paren. -/
  let (_decls, errs) := parse "fn f() : i64 = (try g()) + 1;"
  check "5. (try g()) + 1: no parse errors" 0 errs.size

  IO.println "Tests/Syntax/TryParserTests: all checks run."

end Tests.Syntax.TryParserTests
