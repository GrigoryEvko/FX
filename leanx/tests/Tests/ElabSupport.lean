import FX.Elab.Elaborate
import FX.Elab.CheckFile
import FX.Eval.Interp
import FX.Syntax.Ast
import FX.Kernel.Term

/-!
# Shared helpers for elaboration + eval tests

AST builders, result predicates, and evaluator setup used by
multiple files under `Tests/Elab/**`.  Extracting these removes
the copy-paste drift that accumulated across IfExprTests,
MatchExprTests, TypeParamsTests, RecursionTests, and
PreludeTests.

## Categories

  * **Spans + qualified identifiers** — `zeroSpan`, `qualOf`,
    `qualPath`.  Used everywhere.
  * **AST literals** — `trueLit`, `falseLit`, `typeKw`, `natLit`.
  * **Type / variable expressions** — `natTy`, `boolTy`,
    `varName`, `varQual`.
  * **Decl predicates** — `decl_ok`, `decl_body?`, `decl_type?`,
    `bodyMatches`, `typeMatches`, `elabErrCode`.
  * **End-to-end harness** — `resultsToEnv` (rebuild GlobalEnv
    from checkFile output), `unaryNatCount?` (inspect a Value
    as a unary-Nat count).

Helpers are non-`private` so test files can import them.  Every
helper is side-effect free.
-/

namespace Tests.ElabSupport

open FX.Elab
open FX.Eval
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast

/-! ## Spans and qualified identifiers -/

/-- A zero-origin Span for synthetic AST nodes. -/
def zeroSpan : Span := Span.zero

/-- Build an unqualified identifier (`parts := #[]`). -/
def qualOf (name : String) : QualIdent :=
  { parts := #[], final := name, span := zeroSpan }

/-- Build a qualified identifier with a `Module.Sub.final` path. -/
def qualPath (parts : List String) (final : String) : QualIdent :=
  { parts := parts.toArray, final := final, span := zeroSpan }

/-! ## AST literals -/

/-- `true` keyword literal as an Ast.Expr. -/
def trueLit : Ast.Expr := .literal (.kw .trueKw) zeroSpan

/-- `false` keyword literal as an Ast.Expr. -/
def falseLit : Ast.Expr := .literal (.kw .falseKw) zeroSpan

/-- `type` keyword literal (universe-zero atom) as an Ast.Expr. -/
def typeKw : Ast.Expr := .literal (.kw .typeKw) zeroSpan

/-- An unsuffixed decimal integer literal as an Ast.Expr.  The
    elaborator desugars it to a unary-Nat chain (§3.1 / D2). -/
def natLit (value : Nat) : Ast.Expr :=
  .literal (.intLit (toString value) .dec) zeroSpan

/-! ## Type / variable expressions -/

/-- Variable reference by unqualified name. -/
def varName (name : String) : Ast.Expr := .var (qualOf name)

/-- Variable reference by qualified path (`Module.Sub.name`). -/
def varQual (path : List String) (name : String) : Ast.Expr :=
  .var (qualPath path name)

/-- The `Nat` type as a surface Ast.Expr. -/
def natTy : Ast.Expr := varName "Nat"

/-- The `Bool` type as a surface Ast.Expr. -/
def boolTy : Ast.Expr := varName "Bool"

/-! ## Decl predicates — success / failure shape -/

/-- True iff `elabAndCheck decl` produced `okDecl _`. -/
def decl_ok (decl : Decl) : Bool :=
  match elabAndCheck decl with
  | .okDecl _ => true
  | _         => false

/-- Extract the elaborated body term from a successful decl; `none`
    if elab or type-check failed. -/
def decl_body? (decl : Decl) : Option Term :=
  match elabAndCheck decl with
  | .okDecl elaboratedDecl => some elaboratedDecl.body
  | _                      => none

/-- Extract the elaborated type term from a successful decl; `none`
    if elab or type-check failed. -/
def decl_type? (decl : Decl) : Option Term :=
  match elabAndCheck decl with
  | .okDecl elaboratedDecl => some elaboratedDecl.type
  | _                      => none

/-- True iff the elaborated decl's body structurally equals the
    given expected term.  Uses `BEq Term` from `structEq` because
    `Term` has no `DecidableEq` (Grade field blocks derivation). -/
def bodyMatches (decl : Decl) (expected : Term) : Bool :=
  match decl_body? decl with
  | some body => body == expected
  | none      => false

/-- True iff the elaborated decl's declared type structurally
    equals the given expected term. -/
def typeMatches (decl : Decl) (expected : Term) : Bool :=
  match decl_type? decl with
  | some typ => typ == expected
  | none     => false

/-- True iff an elaboration result is an error with the given
    `code`.  Used by rejection tests that want to verify not just
    "this failed" but "this failed with E010 specifically." -/
def elabErrCode (elabResult : Except ElabError Term) (expectedCode : String) : Bool :=
  match elabResult with
  | .error elabError => elabError.code == expectedCode
  | _                => false

/-! ## Zero-arg fn helpers (§31.7 Unit-Pi desugaring)

Every `fn f() : T with E = body` elaborates uniformly to
`λ (_ :_ghost Unit). body : Π (_ :_ghost Unit) → T @ E`, so
evaluating the decl's body directly returns a closure, not a
`T` value.  Tests that want the closed-over value must apply
the kernel's `Unit.tt` first; these helpers hide that step. -/

/-- The kernel `Unit.tt` ctor value. -/
def unitTt : Term := .ctor "Unit" 0 [] []

/-- Apply a zero-arg fn's body to `Unit.tt` and evaluate.  Use in
    place of `eval evalEnv elaboratedDecl.body` whenever the decl
    was elaborated from a `fn name() : T = ...` declaration —
    post §31.7 zero-arg uniform translation, the body is a lambda
    `λ (_ : Unit). inner` and calling it means applying `Unit.tt`. -/
def evalZeroArgBody (evalEnv : EvalEnv) (body : Term) : Value :=
  eval evalEnv (Term.app body unitTt)

/-! ## End-to-end harness (checkFile + eval) -/

/-- Rebuild a `GlobalEnv` from a `checkFile` result list so the
    evaluator can resolve `Term.const` refs.  Only successfully-
    checked decls contribute (mirrors the CLI's `fxi run` loop). -/
def resultsToEnv (results : Array DeclResult) : GlobalEnv :=
  results.foldl (init := GlobalEnv.empty) fun envSoFar declResult =>
    match declResult with
    | DeclResult.okDecl d =>
      envSoFar.addDecl d.name d.type d.body (transparent := false)
    | _ => envSoFar

/-- Rebuild a `GlobalEnv` that includes user-declared ADT specs
    AND successfully-elaborated decls.  Type decls from the parsed
    file are pre-registered on `userSpecs` before fn/const entries
    are added — matching `FX.Cli.Main.runFileCmd`'s ordering so
    eval of matches on user ADTs finds the spec at `iotaValue`. -/
def resultsToEnvWithAdts (parsedFile : File) (results : Array DeclResult)
    : GlobalEnv := Id.run do
  let mut env : GlobalEnv := GlobalEnv.empty
  for decl in parsedFile.decls do
    match decl with
    | .typeDecl attrs declName typeParams ctors span =>
      match elabTypeDeclSpec env attrs declName typeParams ctors span with
      | .ok fullSpec => env := env.addUserSpec fullSpec
      | .error _     => pure ()
    | _ => pure ()
  for declResult in results do
    match declResult with
    | DeclResult.okDecl d =>
      env := env.addDecl d.name d.type d.body (transparent := false)
    | _ => pure ()
  return env

/-- Walk a `Value` counting `Nat.Succ` constructors applied to
    `Nat.Zero` — the unary-encoding's integer value.  Returns
    `none` if the value isn't a well-formed unary Nat. -/
partial def unaryNatCount? : Value → Option Nat
  | .ctor "Nat" 0 _ _          => some 0
  | .ctor "Nat" 1 _ [inner]    => (unaryNatCount? inner).map (· + 1)
  | _                          => none

/-- Extract a Bool payload from a `Value` — `.ctor "Bool" 0 _ _`
    is `false`, `.ctor "Bool" 1 _ _` is `true`, anything else is
    `none` (stuck neutral, wrong type, etc.).  Used by recursion
    tests that want to distinguish "the function computed `true`"
    from "the function failed to normalize at all". -/
def boolFromValue? : Value → Option Bool
  | .ctor "Bool" 0 _ _ => some false
  | .ctor "Bool" 1 _ _ => some true
  | _                  => none

/-! ## Convenience constructors for Bool / Nat kernel values -/

/-- The kernel `Bool.False` ctor value. -/
def boolFalse : Term := .ctor "Bool" 0 [] []

/-- The kernel `Bool.True` ctor value. -/
def boolTrue : Term := .ctor "Bool" 1 [] []

/-- The kernel `Nat.Zero` term. -/
def natZero : Term := .ctor "Nat" 0 [] []

/-- Unary-Nat: n applications of Succ over Zero. -/
def natUnary : Nat → Term
  | 0     => natZero
  | n + 1 => .ctor "Nat" 1 [] [natUnary n]

end Tests.ElabSupport
