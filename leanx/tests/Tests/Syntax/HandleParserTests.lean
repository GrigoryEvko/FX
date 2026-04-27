import FX.Syntax.Lexer
import FX.Syntax.Parser
import Tests.Framework

/-!
# Handle expression parser tests (task E-5, parser half)

Per `fx_grammar.md §6.5` / `fx_design.md §9.6`.  Exercises the
`handle EXPR (return NAME => EXPR ;)? OP_ARM+ end handle`
surface form.

Scope (parser half):

  * Body expression in handle position.
  * Optional `return` clause.
  * One or more operation arms `OP_NAME(params) => body ;`.
  * `end handle` closer.

Deferred to the elaborator half:

  * Handler typing rule per §9.6 — removing the handled effect
    from the body's effect row.
  * Continuation `k` binding semantics (one-shot vs multi-shot,
    §9.7).
  * Desugaring to kernel delimited-continuation operations.

Split into its own file from `ParserTests.lean` to avoid the
elab-depth ceiling there (same rationale as TryParserTests /
EffectParserTests).
-/

namespace Tests.Syntax.HandleParserTests

open Tests FX.Syntax FX.Syntax.Ast

/-- Lex + parse; return decls plus any parse errors. -/
def parse (sourceText : String) : Array Decl × Array FX.Util.Error :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (fileResult, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  (fileResult.decls, lexOut.errors ++ parseErrs)

/-- Project a one-liner fn body's expression, or `none`. -/
def fnOneLiner? : Decl → Option Expr
  | .fnDecl _ _ _ _ _ _ _ (FnBody.oneLiner e) _ => some e
  | _                                           => none

/-- True iff expression is a `handleExpr`. -/
def isHandleExpr : Expr → Bool
  | .handleExpr _ _ _ _ => true
  | _                   => false

/-- Extract handle-arm count from a `handleExpr`. -/
def handleArmCount? : Expr → Nat
  | .handleExpr _ _ arms _ => arms.size
  | _                      => 0

/-- True iff the `handleExpr` has a return clause. -/
def handleHasReturn? : Expr → Bool
  | .handleExpr _ returnClause _ _ => returnClause.isSome
  | _                              => false

/-- Project the i-th arm's op name, or `"<oob>"`. -/
def handleArmName? (expr : Expr) (index : Nat) : String :=
  match expr with
  | .handleExpr _ _ arms _ =>
    match arms[index]? with
    | some (HandleOpArm.mk opName _ _ _) => opName
    | none                                => "<oob>"
  | _ => "<not-handle>"

/-- Project the i-th arm's param count. -/
def handleArmParamCount? (expr : Expr) (index : Nat) : Nat :=
  match expr with
  | .handleExpr _ _ arms _ =>
    match arms[index]? with
    | some (HandleOpArm.mk _ params _ _) => params.size
    | none                                => 0
  | _ => 0

def run : IO Unit := do
  /- ## 1. Minimal single-op handler — the canonical
     identity-return shape when the handler does nothing but
     intercept one operation.  `handle body() op(k) => k(unit); end handle` -/
  let src := "fn example() : unit = handle body() op(k) => k(unit); end handle;"
  let (decls, errs) := parse src
  check "1. minimal handle: no parse errors" 0 errs.size
  let handleOk : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => isHandleExpr e
    | none   => false
  check "1. fn body is a handleExpr" true handleOk
  let armsOne : Nat :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmCount? e
    | none   => 0
  check "1. arm count == 1" 1 armsOne
  let hasRetClauseOne : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleHasReturn? e
    | none   => false
  check "1. no return clause" false hasRetClauseOne

  /- ## 2. With explicit return clause.  §9.6 example. -/
  let src2 :=
    "fn example() : unit = handle body() return x => x; op(k) => k(unit); end handle;"
  let (decls, errs) := parse src2
  check "2. with return clause: no parse errors" 0 errs.size
  let hasRet : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleHasReturn? e
    | none   => false
  check "2. has return clause" true hasRet
  let armsTwo : Nat :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmCount? e
    | none   => 0
  check "2. arm count == 1 (return doesn't count as arm)" 1 armsTwo

  /- ## 3. Multiple op arms — `State<s>` pattern from §9.6 with
     get/put handlers. -/
  let src3 :=
    "fn example() : unit = handle body() return x => x; get(k) => k(init); put(new_s, k) => k(unit); end handle;"
  let (decls, errs) := parse src3
  check "3. State handler: no parse errors" 0 errs.size
  let armsThree : Nat :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmCount? e
    | none   => 0
  check "3. two arms" 2 armsThree
  let firstArmName : String :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmName? e 0
    | none   => "<none>"
  check "3. first arm name: get" "get" firstArmName
  let secondArmName : String :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmName? e 1
    | none   => "<none>"
  check "3. second arm name: put" "put" secondArmName
  -- get(k) has 1 param; put(new_s, k) has 2 params.
  let getParams : Nat :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmParamCount? e 0
    | none   => 0
  check "3. get has 1 param (k)" 1 getParams
  let putParams : Nat :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmParamCount? e 1
    | none   => 0
  check "3. put has 2 params (new_s, k)" 2 putParams

  /- ## 4. Three-arm handler.  Verifies the accumulating loop
     doesn't miss arms in the middle of a sequence. -/
  let src4 :=
    "fn example() : unit = handle body() a(k) => k(unit); b(k) => k(unit); c(k) => k(unit); end handle;"
  let (decls, errs) := parse src4
  check "4. three arms: no parse errors" 0 errs.size
  let armsFour : Nat :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmCount? e
    | none   => 0
  check "4. three arms counted" 3 armsFour
  let thirdArmName : String :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmName? e 2
    | none   => "<none>"
  check "4. third arm name: c" "c" thirdArmName

  /- ## 5. Missing `end handle` closer — error recorded,
     parser stays productive. -/
  let src5 := "fn example() : unit = handle body() op(k) => k(unit);"
  let (_, errs) := parse src5
  check "5. missing end handle: error recorded" true (errs.size > 0)

  /- ## 6. Handle with only a return clause and no op arms —
     the parser accepts (arms can be empty); the elaborator
     would reject (a handler must cover at least one op).
     Pin the parser behavior: zero arms parse cleanly. -/
  let src6 := "fn example() : unit = handle body() return x => x; end handle;"
  let (decls, errs) := parse src6
  check "6. handle with only return: no parse errors" 0 errs.size
  let zeroArms : Nat :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleArmCount? e
    | none   => 0
  check "6. zero arms" 0 zeroArms
  let hasRetSix : Bool :=
    match (decls[0]? >>= fnOneLiner?) with
    | some e => handleHasReturn? e
    | none   => false
  check "6. return clause present" true hasRetSix

  IO.println "Tests/Syntax/HandleParserTests: all checks run."

end Tests.Syntax.HandleParserTests
