import FX.Elab.Elaborate
import FX.Kernel.Inductive
import Tests.ElabSupport
import Tests.Framework

/-!
# If/else elaboration tests (B6)

Exercises the Phase-2.2 `if`-expression desugaring:

  * `if cond; a else b end if` → `indRec "Bool" motive [b, a] cond`
  * `else if` chains fold into nested indRec forms
  * Missing `else` is E010 (exhaustiveness)
  * No `expected` in context (bare if-expression) is E010

The expected-type thread runs from `elabFnDecl`'s declared return
type, through `elabStmtChain`'s tail, and into the innermost
`.ifExpr` case.  Tests here cover all three reach paths.

`Term` has no `DecidableEq`; comparisons use `BEq Term` from
`structEq` via the `termEq` helper below.
-/

namespace Tests.Elab.IfExprTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests.ElabSupport

/-- Compare elab result to an expected Term via `BEq Term`. -/
private def elabEq (elabResult : Except ElabError Term) (expected : Term) : Bool :=
  match elabResult with
  | .ok resultTerm => resultTerm == expected
  | _              => false

/-- Run elab against an empty env with a declared expected type. -/
private def runWith (expected : Option Term) (expr : Expr)
    : Except ElabError Term :=
  elabExpr GlobalEnv.empty Scope.empty expected expr

/-! ## Direct desugaring -/

/-- Naked if-expression without context yields E010. -/
example :
  elabErrCode (runWith none
    (.ifExpr (.literal (.kw .trueKw) zeroSpan)
             (.literal (.kw .falseKw) zeroSpan)
             #[] (some (.literal (.kw .trueKw) zeroSpan)) zeroSpan)) "E010" := by
  native_decide

/-- With a Nat expected type, `if true; 1 else 0 end if` desugars
    to `indRec "Bool" (lambda_. Nat) [natLit 0, natLit 1] True`. -/
example :
  elabEq (runWith (some (.ind "Nat" []))
    (.ifExpr (.literal (.kw .trueKw) zeroSpan)
             (.literal (.intLit "1" .dec) zeroSpan)
             #[] (some (.literal (.intLit "0" .dec) zeroSpan)) zeroSpan))
    (Term.indRec "Bool"
       (.lam Grade.default (.ind "Bool" [])
             (Term.shift 0 1 (.ind "Nat" [])))
       [.ctor "Nat" 0 [] [], .ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]]
       (.ctor "Bool" 1 [] [])) := by
  native_decide

/-- Missing `else` → E010. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (.ifExpr (.literal (.kw .trueKw) zeroSpan)
             (.literal (.intLit "1" .dec) zeroSpan)
             #[] none zeroSpan)) "E010" := by
  native_decide

/-- Else-if chain: `if F; 10 else if T; 20 else 30 end if` with
    expected Nat → two nested indRecs. -/
example :
  let inner : Term :=
    Term.indRec "Bool"
       (.lam Grade.default (.ind "Bool" []) (Term.shift 0 1 (.ind "Nat" [])))
       [-- Bool.False method:
        .ctor "Nat" 1 [] [.ctor "Nat" 1 [] [.ctor "Nat" 1 [] [
          .ctor "Nat" 0 [] []]]],
        -- Bool.True method:
        .ctor "Nat" 1 [] [.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]]]
       (.ctor "Bool" 1 [] [])
  let outer : Term :=
    Term.indRec "Bool"
       (.lam Grade.default (.ind "Bool" []) (Term.shift 0 1 (.ind "Nat" [])))
       [-- Bool.False method (falls through to inner):
        inner,
        -- Bool.True method (the first `then`, but condition is false):
        .ctor "Nat" 0 [] []]
       (.ctor "Bool" 0 [] [])
  elabEq (runWith (some (.ind "Nat" []))
    (.ifExpr (.literal (.kw .falseKw) zeroSpan)
             (.literal (.intLit "0" .dec) zeroSpan)   -- misleading name; it's "big" - used only on F path
             #[(.literal (.kw .trueKw) zeroSpan, .literal (.intLit "2" .dec) zeroSpan)]
             (some (.literal (.intLit "3" .dec) zeroSpan)) zeroSpan)) outer := by
  native_decide

/-! ## Integration via fnDecl -/

/-- `fn flip(b: Bool) : Bool = if b; false else true end if;` -/
private def flipDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "flip")
    (params := #[.mk .default_ "b" boolTy zeroSpan])
    (retType := boolTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.ifExpr (.var (qualOf "b"))
               (.literal (.kw .falseKw) zeroSpan) #[]
               (some (.literal (.kw .trueKw) zeroSpan)) zeroSpan))
    (span := zeroSpan)

example : decl_ok flipDecl := by native_decide

/-- `fn ite(b: Bool) : Nat = if b; 42 else 7 end if;` -/
private def iteDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "ite")
    (params := #[.mk .default_ "b" boolTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.ifExpr (.var (qualOf "b"))
               (.literal (.intLit "42" .dec) zeroSpan) #[]
               (some (.literal (.intLit "7" .dec) zeroSpan)) zeroSpan))
    (span := zeroSpan)

example : decl_ok iteDecl := by native_decide

/-- `fn nested(a: Bool, b: Bool) : Nat =
     if a; (if b; 1 else 2 end if) else 3 end if;` -/
private def nestedDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "nested")
    (params := #[.mk .default_ "a" boolTy zeroSpan, .mk .default_ "b" boolTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.ifExpr (.var (qualOf "a"))
               (.ifExpr (.var (qualOf "b"))
                        (.literal (.intLit "1" .dec) zeroSpan) #[]
                        (some (.literal (.intLit "2" .dec) zeroSpan)) zeroSpan) #[]
               (some (.literal (.intLit "3" .dec) zeroSpan)) zeroSpan))
    (span := zeroSpan)

example : decl_ok nestedDecl := by native_decide

/-- `fn chain(b: Bool) : Nat =
     if b; 10 else if true; 20 else 30 end if;`

    The inner `if`'s condition is the literal `true` (not `b`
    again) because a linear binder (`b` has default mode = grade
    `one`) cannot be consumed twice in the body — M001 would
    fire.  The chained-if structure is still exercised; using a
    literal in the inner condition is a common idiom when the
    surface code needs a guaranteed-true path.  Once `ref`-mode
    elaboration maps to `omega` grade (out-of-scope task), this
    can return to `if b; ... else if b; ...` style. -/
private def chainDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "chain")
    (params := #[.mk .default_ "b" boolTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.ifExpr (.var (qualOf "b"))
               (.literal (.intLit "10" .dec) zeroSpan)
               #[(.literal (.kw .trueKw) zeroSpan,
                  .literal (.intLit "20" .dec) zeroSpan)]
               (some (.literal (.intLit "30" .dec) zeroSpan)) zeroSpan))
    (span := zeroSpan)

example : decl_ok chainDecl := by native_decide

/-- If in block-body return position: `fn f() : Nat = begin fn
     return if true; 5 else 6 end if; end fn;` -/
private def blockIfDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "blockIf") (params := #[])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.block #[]
      (.ifExpr (.literal (.kw .trueKw) zeroSpan)
               (.literal (.intLit "5" .dec) zeroSpan) #[]
               (some (.literal (.intLit "6" .dec) zeroSpan)) zeroSpan))
    (span := zeroSpan)

example : decl_ok blockIfDecl := by native_decide

/-- If after a let-stmt: `fn f() : Nat = begin fn let x : Bool =
     true; return if x; 1 else 0 end if; end fn;`  Verifies expected
     type propagates through `elabStmtChain` + shift-on-bind. -/
private def letThenIfDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "letThenIf") (params := #[])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.block
      #[.letStmt (.var "x" zeroSpan) (some boolTy)
         (.literal (.kw .trueKw) zeroSpan) zeroSpan]
      (.ifExpr (.var (qualOf "x"))
               (.literal (.intLit "1" .dec) zeroSpan) #[]
               (some (.literal (.intLit "0" .dec) zeroSpan)) zeroSpan))
    (span := zeroSpan)

example : decl_ok letThenIfDecl := by native_decide

/-! ## Runtime suite -/

def run : IO Unit := Tests.suite "Tests.Elab.IfExprTests" do
  Tests.check "bare if → E010 no expected type" true
    (elabErrCode (runWith none
      (.ifExpr (.literal (.kw .trueKw) zeroSpan)
               (.literal (.kw .falseKw) zeroSpan) #[]
               (some (.literal (.kw .trueKw) zeroSpan)) zeroSpan)) "E010")
  Tests.check "missing else → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (.ifExpr (.literal (.kw .trueKw) zeroSpan)
               (.literal (.intLit "1" .dec) zeroSpan) #[] none zeroSpan)) "E010")
  Tests.check "fn flip elab+check" true (decl_ok flipDecl)
  Tests.check "fn ite elab+check" true (decl_ok iteDecl)
  Tests.check "fn nested elab+check" true (decl_ok nestedDecl)
  Tests.check "fn chain elab+check" true (decl_ok chainDecl)
  Tests.check "fn blockIf elab+check" true (decl_ok blockIfDecl)
  Tests.check "fn letThenIf elab+check" true (decl_ok letThenIfDecl)

end Tests.Elab.IfExprTests
