import FX.Elab.Elaborate
import FX.Eval.Interp
import FX.Kernel.Inductive
import FX.Kernel.Reduction
import Tests.ElabSupport
import Tests.Framework

/-!
# Type-parameter elaboration tests (B2)

Exercises `fn id<a: type>(x: a) : a = x;` surface form — type
parameters as ghost-moded `FnParam`s prepended to the regular
parameter list, compiling to ghost-graded `Pi`/`lam` binders.

Shapes covered:

  * AST: parser converts `<a: type>` into ghost-moded FnParams,
    ordered before regular params.
  * Elab term: declared type is `Pi<ghost>(a : Type<0>). Pi(x : a). a`,
    body is `\<ghost> a. \ x. x`.
  * `elabAndCheck` accepts polymorphic identity.
  * Application with `#T` implicit args elaborates to plain
    `Term.app`.
  * End-to-end: `identity(#Nat, 42)` normalizes to `42`.
-/

namespace Tests.Elab.TypeParamsTests

open FX.Elab
open FX.Eval
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests.ElabSupport

/-! ## Builders -/

/-- A ghost FnParam `a : type`. -/
private def typeParam (name : String) : FnParam :=
  .mk .ghost name typeKw zeroSpan

/-- A default FnParam `name : type`. -/
private def normalParam (name : String) (ty : Expr) : FnParam :=
  .mk .default_ name ty zeroSpan

/-- `fn id<a: type>(x: a) : a = x;` -/
private def identityDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "identity")
    (params := #[typeParam "a", normalParam "x" (varName "a")])
    (retType := varName "a")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (varName "x"))
    (span := zeroSpan)

/-- The expected kernel body for `identity`:
    `\<ghost>(a : Type<0>). \<default>(x : var 0). var 0`. -/
private def identityBodyExpected : Term :=
  .lam Grade.ghost (.type .zero)
    (.lam Grade.default (.var 0)
      (.var 0))

/-- The expected kernel type for `identity`:
    `Pi<ghost>(a : Type<0>). Pi<default>(x : var 0). var 1`. -/
private def identityTypeExpected : Term :=
  .piTot Grade.ghost (.type .zero)
    (.piTot Grade.default (.var 0)
      (.var 1))

example : decl_ok identityDecl := by native_decide

example : bodyMatches identityDecl identityBodyExpected := by native_decide

example : typeMatches identityDecl identityTypeExpected := by native_decide

/-- `fn constZero<a: type>(x: a) : Nat = Nat.Zero;` — type param
    carried but unused in the body; compiles cleanly. -/
private def constZeroDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "constZero")
    (params := #[typeParam "a", normalParam "x" (varName "a")])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (.var (qualPath ["Nat"] "Zero")))
    (span := zeroSpan)

example : decl_ok constZeroDecl := by native_decide

/-- `fn pair<a: type, b: type>(x: a, y: b) : a = x;` — two type
    params plus two regular params.  Type params occupy the
    outermost binders (var 1 == a, var 0 == b at the innermost
    type-param scope; both unused in this body but verified
    to compile). -/
private def pairSelectDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "pairSelect")
    (params := #[
      typeParam "a", typeParam "b",
      normalParam "x" (varName "a"),
      normalParam "y" (varName "b")])
    (retType := varName "a")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (varName "x"))
    (span := zeroSpan)

example : decl_ok pairSelectDecl := by native_decide

/-! ## Implicit-arg application at call sites -/

/-- `fn result() : Nat = identity(#Nat, 42);` — wrapper that calls
    the polymorphic identity with an implicit type arg and a
    positional value arg.  The generated kernel term is the body
    of identity beta-reducible to `42`. -/
private def identityAppDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "result")
    (params := #[])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (varName "identity")
        #[.implicit natTy,
          .pos (.literal (.intLit "42" .dec) zeroSpan)]
        zeroSpan))
    (span := zeroSpan)

private def identityAppReducesTo42 : Bool :=
  let file : File := { decls := #[identityDecl, identityAppDecl], span := zeroSpan }
  let results := checkFile file
  let allCheck := results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false
  if ¬ allCheck then false
  else
    match results[1]? with
    | some (DeclResult.okDecl elaboratedDecl) =>
      let evalEnv : EvalEnv := EvalEnv.ofGlobals (resultsToEnv results)
      match unaryNatCount? (evalZeroArgBody evalEnv elaboratedDecl.body) with
      | some 42 => true
      | _       => false
    | _ => false

example : identityAppReducesTo42 = true := by native_decide

/-! ## Ghost-grade distinctness -/

/-- A decl with no type params compiles with Grade.default on
    every binder — verifies we haven't accidentally made every
    param ghost-graded. -/
private def addNatsDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "firstNat")
    (params := #[normalParam "n" natTy])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (varName "n"))
    (span := zeroSpan)

-- Q55: prelude `Nat` is marked `isCopy := true`, so the
-- elaborator's `gradeForParam` upgrades the binder's grade
-- from `Grade.default` (usage = 1) to `Grade.shared` (usage
-- = ω).  Pre-Q55 this test expected `Grade.default`; the
-- update reflects the new grade-carrying shape of the lam.
example : bodyMatches addNatsDecl
    (.lam Grade.shared (.ind "Nat" []) (.var 0)) := by
  native_decide

/-! ## Runtime suite -/

def run : IO Unit := Tests.suite "Tests.Elab.TypeParamsTests" do
  Tests.check "identity elab+check" true (decl_ok identityDecl)
  Tests.check "identity body = ghost-lam(Type).default-lam(var 0). var 0" true
    (bodyMatches identityDecl identityBodyExpected)
  Tests.check "identity type = ghost-pi(Type).pi(var 0). var 1" true
    (typeMatches identityDecl identityTypeExpected)
  Tests.check "constZero (type param unused in body) elab+check" true
    (decl_ok constZeroDecl)
  Tests.check "pairSelect (two type params, two value params)" true
    (decl_ok pairSelectDecl)
  Tests.check "identity(#Nat, 42) normalizes to 42" true
    identityAppReducesTo42
  -- Q55: Nat is now a @[copy]-marked prelude spec, so the
  -- binder's grade is `Grade.shared` (usage = ω), not the
  -- plain `Grade.default` the pre-Q55 kernel produced.  What
  -- the test really pins is "not ghost" — a value-level Nat
  -- param must not accidentally get grade-0 / erased.
  Tests.check "non-poly fn Nat param is non-ghost (copy-upgraded)" true
    (bodyMatches addNatsDecl
      (.lam Grade.shared (.ind "Nat" []) (.var 0)))

end Tests.Elab.TypeParamsTests
