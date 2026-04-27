import FX.Elab.Elaborate
import FX.Kernel.Inductive
import Tests.ElabSupport
import Tests.Framework

/-!
# Prelude surface-access tests (D1, D2)

Exercises the Phase-2.2 prelude resolution cascade:

  * Qualified ctor references (`Nat.Zero`, `Bool.True`) — §4.1 §4.10
  * Boolean keyword literals (`true`, `false`) — §2.4
  * Unsuffixed integer literals (`42`, `0xFF`, `0b1010`, `1_000`)
    as unary `Nat` — §3.1 (M1 unary encoding; fixed-width later)
  * Unqualified type names (`Nat`, `Bool`, `Unit`, `Empty`) — §3.1
  * Error shapes for malformed qualified names, arity mismatch

Every registered `IndSpec` in `Inductive.preludeSpecs` should have at
least one coverage point in this file.

`Term` does not derive `DecidableEq` (the `Grade.provenance` field
blocks auto-derive on nested `List Provenance`).  All term comparisons
go through the `BEq Term` instance from `Term.structEq` via the
`termOptEq` helper below, which returns `Bool`.
-/

namespace Tests.Elab.PreludeTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests.ElabSupport

/-- Alias for `varName` kept under the old name so the many
    test sites using `fxVar` elsewhere in this file keep parsing. -/
private def fxVar (name : String) : Expr := varName name

/-- Compare an `Except ElabError Term` result against an expected
    success Term using the `BEq Term` instance (structEq).  Any error
    yields `false`; the comparison is total and safe for
    `native_decide`. -/
private def elabEq (elabResult : Except ElabError Term)
    (expected : Term) : Bool :=
  match elabResult with
  | .ok resultTerm => resultTerm == expected
  | _              => false

/-- Run a fresh elab against the empty env and scope, with no
    expected-type hint (explicit `none` so Lean doesn't try to
    unify `e` against the `Option Term` expected param). -/
private def run1 (expr : Expr) : Except ElabError Term :=
  elabExpr GlobalEnv.empty Scope.empty none expr

/-! ## Qualified ctor references -/

example : elabEq (run1 (.var (qualPath ["Nat"] "Zero"))) (.ctor "Nat" 0 [] []) := by
  native_decide
example : elabEq (run1 (.var (qualPath ["Bool"] "True"))) (.ctor "Bool" 1 [] []) := by
  native_decide
example : elabEq (run1 (.var (qualPath ["Bool"] "False"))) (.ctor "Bool" 0 [] []) := by
  native_decide
example : elabEq (run1 (.var (qualPath ["Unit"] "tt"))) (.ctor "Unit" 0 [] []) := by
  native_decide
example : elabErrCode (run1 (.var (qualPath ["Nat"] "Succ"))) "E010" := by
  native_decide
example : elabErrCode (run1 (.var (qualPath ["Bool"] "Nonsense"))) "E001" := by
  native_decide
example : elabErrCode (run1 (.var (qualPath ["NotAType"] "Zero"))) "E001" := by
  native_decide

/-! ## Ctor application -/

example :
  elabEq (run1 (.app (.var (qualPath ["Nat"] "Succ"))
                     #[.pos (.var (qualPath ["Nat"] "Zero"))] zeroSpan))
         (.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]) := by
  native_decide

example :
  elabErrCode (run1 (.app (.var (qualPath ["Nat"] "Zero"))
                          #[.pos (.var (qualPath ["Nat"] "Zero"))] zeroSpan)) "E010" := by
  native_decide

example :
  elabErrCode (run1 (.app (.var (qualPath ["Nat"] "Succ")) #[] zeroSpan)) "E010" := by
  native_decide

example :
  elabErrCode
    (run1 (.app (.var (qualPath ["Nat"] "Succ"))
                #[.pos (.var (qualPath ["Nat"] "Zero")),
                  .pos (.var (qualPath ["Nat"] "Zero"))] zeroSpan)) "E010" := by
  native_decide

/-! ## Unqualified type names -/

example : elabEq (run1 (fxVar "Nat"))   (.ind "Nat" [])   := by native_decide
example : elabEq (run1 (fxVar "Bool"))  (.ind "Bool" [])  := by native_decide
example : elabEq (run1 (fxVar "Unit"))  (.ind "Unit" [])  := by native_decide
example : elabEq (run1 (fxVar "Empty")) (.ind "Empty" []) := by native_decide
example : elabErrCode (run1 (fxVar "NotAType")) "E001" := by native_decide

/-! ## Boolean keyword literals -/

private def litTrue  : Expr := .literal (.kw .trueKw) zeroSpan
private def litFalse : Expr := .literal (.kw .falseKw) zeroSpan

example : elabEq (run1 litTrue)  (.ctor "Bool" 1 [] []) := by native_decide
example : elabEq (run1 litFalse) (.ctor "Bool" 0 [] []) := by native_decide

/-! ## Numeric literals (D2) -/

example :
  elabEq (run1 (.literal (.intLit "0" .dec) zeroSpan))
         (.ctor "Nat" 0 [] []) := by native_decide

example :
  elabEq (run1 (.literal (.intLit "1" .dec) zeroSpan))
         (.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]) := by native_decide

example :
  elabEq (run1 (.literal (.intLit "2" .dec) zeroSpan))
         (.ctor "Nat" 1 [] [.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]]) := by
  native_decide

example :
  elabEq (run1 (.literal (.intLit "FF" .hex) zeroSpan)) (buildNatLit 255) := by
  native_decide

example :
  elabEq (run1 (.literal (.intLit "1010" .bin) zeroSpan)) (buildNatLit 10) := by
  native_decide

example :
  elabEq (run1 (.literal (.intLit "777" .oct) zeroSpan)) (buildNatLit 511) := by
  native_decide

/-! ## Integration: doElab+ check rolls through -/

private def zeroDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "zero") (params := #[])
    (retType := fxVar "Nat")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (.var (qualPath ["Nat"] "Zero")))
    (span := zeroSpan)

example : decl_ok zeroDecl := by native_decide

private def oneDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "one") (params := #[])
    (retType := fxVar "Nat")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (.var (qualPath ["Nat"] "Succ"))
            #[.pos (.var (qualPath ["Nat"] "Zero"))] zeroSpan))
    (span := zeroSpan)

example : decl_ok oneDecl := by native_decide

private def threeDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "three") (params := #[])
    (retType := fxVar "Nat")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (.literal (.intLit "3" .dec) zeroSpan))
    (span := zeroSpan)

example : decl_ok threeDecl := by native_decide

private def yesDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "yes") (params := #[])
    (retType := fxVar "Bool")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner litTrue)
    (span := zeroSpan)

example : decl_ok yesDecl := by native_decide

private def ttDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "tt") (params := #[])
    (retType := fxVar "Unit")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (.var (qualPath ["Unit"] "tt")))
    (span := zeroSpan)

example : decl_ok ttDecl := by native_decide

private def natTypeDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "natT") (params := #[])
    (retType := .literal (.kw .typeKw) zeroSpan)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (fxVar "Nat"))
    (span := zeroSpan)

example : decl_ok natTypeDecl := by native_decide

/-! ## Helper round-trips -/

example : parseIntText? "42"   .dec = some 42  := by native_decide
example : parseIntText? "FF"   .hex = some 255 := by native_decide
example : parseIntText? "ff"   .hex = some 255 := by native_decide
example : parseIntText? "1010" .bin = some 10  := by native_decide
example : parseIntText? "777"  .oct = some 511 := by native_decide
example : parseIntText? ""     .dec = none     := by native_decide

/-! ## Runtime suite

Each check is a single-line predicate so Lean's `do`-notation parser
never sees multi-line-argument continuations — avoids the
"unexpected token ')'; expected ':'" parse trap that multi-line
`(run1 (.app (.var ...)))` chains sometimes trigger inside a `do`
block. -/

private def natZeroE   : Expr := .var (qualPath ["Nat"] "Zero")
private def natSuccE   : Expr := .var (qualPath ["Nat"] "Succ")
private def boolTrueE  : Expr := .var (qualPath ["Bool"] "True")
private def boolFalseE : Expr := .var (qualPath ["Bool"] "False")
private def unitTtE    : Expr := .var (qualPath ["Unit"] "tt")
private def natSucc1 : Expr := .app natSuccE #[.pos natZeroE] zeroSpan
private def natZero_bad : Expr := .app natZeroE #[.pos natZeroE] zeroSpan
private def natSucc_arity0 : Expr := .app natSuccE #[] zeroSpan
private def intLit (digitText : String) (base : IntBase) : Expr :=
  .literal (.intLit digitText base) zeroSpan

def run : IO Unit := Tests.suite "Tests.Elab.PreludeTests" do
  Tests.check "Nat.Zero → ctor 0" true    (elabEq (run1 natZeroE)   (.ctor "Nat" 0 [] []))
  Tests.check "Bool.True → ctor 1" true   (elabEq (run1 boolTrueE)  (.ctor "Bool" 1 [] []))
  Tests.check "Bool.False → ctor 0" true  (elabEq (run1 boolFalseE) (.ctor "Bool" 0 [] []))
  Tests.check "Unit.tt → ctor 0" true     (elabEq (run1 unitTtE)    (.ctor "Unit" 0 [] []))
  Tests.check "bare Nat.Succ → E010" true (elabErrCode (run1 natSuccE) "E010")
  Tests.check "Bool.Nonsense → E001" true (elabErrCode (run1 (.var (qualPath ["Bool"] "Nonsense"))) "E001")
  Tests.check "NotAType.Zero → E001" true (elabErrCode (run1 (.var (qualPath ["NotAType"] "Zero"))) "E001")
  Tests.check "Nat.Succ(Nat.Zero) = 1" true
    (elabEq (run1 natSucc1) (.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]))
  Tests.check "Nat.Zero(x) → E010" true        (elabErrCode (run1 natZero_bad) "E010")
  Tests.check "Nat.Succ() → E010 (arity)" true (elabErrCode (run1 natSucc_arity0) "E010")
  let tyNat   := Expr.var (qualOf "Nat")
  let tyBool  := Expr.var (qualOf "Bool")
  let tyUnit  := Expr.var (qualOf "Unit")
  let tyEmpty := Expr.var (qualOf "Empty")
  let tyUnknown := Expr.var (qualOf "NotAType")
  Tests.check "Nat as type" true (elabEq (run1 tyNat)   (.ind "Nat" []))
  Tests.check "Bool as type" true (elabEq (run1 tyBool)  (.ind "Bool" []))
  Tests.check "Unit as type" true (elabEq (run1 tyUnit)  (.ind "Unit" []))
  Tests.check "Empty as type" true (elabEq (run1 tyEmpty) (.ind "Empty" []))
  Tests.check "unknown var E001" true (elabErrCode (run1 tyUnknown) "E001")
  Tests.check "true → ctor Bool 1" true  (elabEq (run1 litTrue)  (.ctor "Bool" 1 [] []))
  Tests.check "false → ctor Bool 0" true (elabEq (run1 litFalse) (.ctor "Bool" 0 [] []))
  let lit0   := Expr.literal (.intLit "0" .dec) zeroSpan
  let lit5   := Expr.literal (.intLit "5" .dec) zeroSpan
  let litFF  := Expr.literal (.intLit "FF" .hex) zeroSpan
  let litBin := Expr.literal (.intLit "1010" .bin) zeroSpan
  let litOct := Expr.literal (.intLit "777" .oct) zeroSpan
  Tests.check "intLit 0 elab" true (elabEq (run1 lit0) (.ctor "Nat" 0 [] []))
  Tests.check "intLit 5 elab" true (elabEq (run1 lit5) (buildNatLit 5))
  Tests.check "hex FF elab" true  (elabEq (run1 litFF)  (buildNatLit 255))
  Tests.check "bin 1010 elab" true (elabEq (run1 litBin) (buildNatLit 10))
  Tests.check "oct 777 elab" true (elabEq (run1 litOct) (buildNatLit 511))
  Tests.check "fn zero() : Nat = Nat.Zero" true            (decl_ok zeroDecl)
  Tests.check "fn one() : Nat = Nat.Succ(Nat.Zero)" true   (decl_ok oneDecl)
  Tests.check "fn three() : Nat = 3" true                  (decl_ok threeDecl)
  Tests.check "fn yes() : Bool = true" true                (decl_ok yesDecl)
  Tests.check "fn tt() : Unit = Unit.tt" true              (decl_ok ttDecl)
  Tests.check "fn natT() : type = Nat" true                (decl_ok natTypeDecl)

end Tests.Elab.PreludeTests
