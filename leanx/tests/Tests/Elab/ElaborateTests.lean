import FX.Elab.Elaborate
import FX.Eval.Interp
import Tests.Framework
import Tests.ElabSupport

/-!
# Elaborate tests — surface AST → kernel Term

Covers the Phase-2.1 elaboration surface per `FX/Elab/Elaborate.lean`:

  * Expressions (`elabExpr`): var, type-literal, arrow, application
    (positional args), lambda (typed params), plus negative cases
    for every currently-unsupported form (E010).
  * Lambda-param chain (`elabLamChain`): typed, plain (rejected),
    wildcard (rejected), destructure (rejected).
  * Declarations (`elabDecl`): fnDecl with oneLiner body (positive)
    and block body (E030), plus non-fn decls (E020).
  * End-to-end (`elabAndCheck`): the identity function
    `fn id(a: type, x: a) : a = x` elaborates AND type-checks; an
    ill-typed `fn wrong(a: type, x: a) : type = x` elaborates but
    the kernel rejects.

Bool-helper pattern mirrors `Tests/Kernel/TypingTests.lean`
because `ElabError` doesn't derive `DecidableEq` and direct
equality on `Except` is awkward.

## Falsifiability notes

Tests here emphasize Term-shape equality over `.isOk` / `.elabFail`
flags so a broken elaborator returning a placeholder (e.g.
`Term.type .zero` for every input) cannot pass.  Rejection tests
additionally assert the `ElabError.span` round-trips from the
offending AST node where relevant — a broken elaborator that
smashes every error span to `Span.zero` would fail those
assertions while still emitting the correct code.
-/

namespace Tests.Elab.ElaborateTests

open FX.Elab
open FX.Eval
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests
open Tests.ElabSupport

/-! ## Test helpers -/

/-- Span placeholder used throughout the tests; we don't check
    spans, only shapes. -/
def zeroSpan : Span := Span.zero

/-- A distinctive non-zero Span used by rejection tests that
    assert the elaborator's `ElabError` carries the offending
    AST node's span (not `Span.zero`).  A broken elaborator that
    smashes every error span to `Span.zero` will fail span-
    equality checks against this. -/
def markerSpan : Span :=
  { start := { line := 7, column := 3, offset := 42 }
  , stop  := { line := 7, column := 9, offset := 48 } }

/-- Unqualified name in the default span. -/
def qualOf (name : String) : QualIdent :=
  { parts := #[], final := name, span := zeroSpan }

/-- Build an `Expr.var` from an unqualified name. -/
def var (name : String) : Ast.Expr := .var (qualOf name)

/-- The `type` keyword used as an expression atom.  This is the
    one-line Parser tweak from Phase 2.1. -/
def typeKw : Ast.Expr := .literal (.kw .typeKw) zeroSpan

/-- True iff `elabExpr scope expr = .ok expected`. -/
def elabExprIs (scope : Scope) (expr : Ast.Expr) (expected : Term) : Bool :=
  match elabExpr GlobalEnv.empty scope none expr with
  | .ok resultTerm => resultTerm == expected
  | .error _       => false

/-- True iff `elabExpr scope expr` errored with a specific `code`. -/
def elabExprFailsWith (scope : Scope) (expr : Ast.Expr)
    (expectedCode : String) : Bool :=
  match elabExpr GlobalEnv.empty scope none expr with
  | .error elabError => elabError.code == expectedCode
  | .ok _            => false

/-- True iff `elabExpr scope expr` errored with a specific `code`
    AND the error's span equals `expectedSpan`.  Distinguishes a
    correct elaborator (span of the offending AST node) from one
    that merely emits the right code with a lost span. -/
def elabExprFailsAtSpan (scope : Scope) (expr : Ast.Expr)
    (expectedCode : String) (expectedSpan : Span) : Bool :=
  match elabExpr GlobalEnv.empty scope none expr with
  | .error elabError =>
    elabError.code == expectedCode && elabError.span == expectedSpan
  | .ok _            => false

/-- True iff `elabDecl decl` errored with the given code. -/
def elabDeclFailsWith (decl : Decl) (expectedCode : String) : Bool :=
  match elabDecl decl with
  | .error elabError => elabError.code == expectedCode
  | .ok _            => false

/-- True iff `elabAndCheck decl` ended in `okDecl _`. -/
def elabAndChecksOk (decl : Decl) : Bool :=
  match elabAndCheck decl with
  | .okDecl _ => true
  | _         => false

/-- True iff `elabAndCheck decl` ended in `typeFail _ _`. -/
def elabAndCheckTypeFails (decl : Decl) : Bool :=
  match elabAndCheck decl with
  | .typeFail _ _ => true
  | _             => false

/-- True iff `elabAndCheck decl` ended in `elabFail _`. -/
def elabAndCheckElabFails (decl : Decl) : Bool :=
  match elabAndCheck decl with
  | .elabFail _ => true
  | _           => false

/-- True iff `elabAndCheck decl` ended in `elabFail` with the given
    `ElabError.code`.  Strictly stronger than
    `elabAndCheckElabFails`: a broken `elabDecl` that surfaced E999
    would still satisfy the latter. -/
def elabAndCheckElabFailsWith (decl : Decl) (expectedCode : String) : Bool :=
  match elabAndCheck decl with
  | .elabFail elabError => elabError.code == expectedCode
  | _                   => false

/-- Extract the elaborated body term from a successful `okDecl`;
    `none` otherwise.  Used by tests that verify a declaration
    not only type-checks but its elaborated body has a specific
    kernel shape. -/
def declBody? (decl : Decl) : Option Term :=
  match elabAndCheck decl with
  | .okDecl elaboratedDecl => some elaboratedDecl.body
  | _                      => none

/-- Extract the elaborated declared type from a successful
    `okDecl`; `none` otherwise. -/
def declType? (decl : Decl) : Option Term :=
  match elabAndCheck decl with
  | .okDecl elaboratedDecl => some elaboratedDecl.type
  | _                      => none

/-- True iff `elabAndCheck decl` succeeds and the body kernel
    term equals `expectedBody`.  Catches "elab is trivially
    OK but its output is nonsense" bugs. -/
def declBodyEq (decl : Decl) (expectedBody : Term) : Bool :=
  match declBody? decl with
  | some bodyTerm => bodyTerm == expectedBody
  | none          => false

/-- True iff `elabAndCheck decl` succeeds and the declared type
    kernel term equals `expectedType`. -/
def declTypeEq (decl : Decl) (expectedType : Term) : Bool :=
  match declType? decl with
  | some typeTerm => typeTerm == expectedType
  | none          => false

/-! ## Expression elaboration — positive cases -/

-- `type` keyword → Term.type Level.zero
example : elabExprIs Scope.empty typeKw (.type .zero) = true := by native_decide

-- Known variable resolves to its de Bruijn index.
example :
  elabExprIs (Scope.empty.push "x") (var "x") (.var 0) = true := by
  native_decide

example :
  elabExprIs (Scope.empty.push "y" |>.push "x") (var "y") (.var 1) = true := by
  native_decide

-- Arrow `A -> B` becomes `pi g A (shift 0 1 B)`.
-- When B is a closed term (like `type`), shifting by 1 is a no-op.
example :
  elabExprIs Scope.empty (.arrow typeKw typeKw zeroSpan)
    (.piTot Grade.default (.type .zero) (.type .zero)) = true := by
  native_decide

-- Positional application: f(x) with both in scope.
-- We set up a scope with `f` at 0 and `x` at 1 (outer), then
-- `f(x)` elaborates to `app (var 0) (var 1)`.  Wait — when we
-- push `f` first and `x` second, `x` is at 0 and `f` at 1.
example :
  let scopeWithFAndX := Scope.empty.push "f" |>.push "x"
  elabExprIs scopeWithFAndX (.app (var "f") #[.pos (var "x")] zeroSpan)
    (.app (.var 1) (.var 0)) = true := by
  native_decide

-- Lambda with typed parameter.
example :
  elabExprIs Scope.empty
    (.lam #[.typed "x" typeKw] (var "x") zeroSpan)
    (.lam Grade.default (.type .zero) (.var 0)) = true := by
  native_decide

/-! ## Expression elaboration — negative cases -/

-- Unknown variable → E001.
example :
  elabExprFailsWith Scope.empty (var "missing") "E001" = true := by
  native_decide

-- Unit → E010 (no unit type in kernel yet).  Assert the error's
-- span matches the offending AST node — a broken elaborator that
-- resets every span to `Span.zero` would fail this.
example :
  elabExprFailsAtSpan Scope.empty (.unit markerSpan) "E010" markerSpan
    = true := by
  native_decide

-- sorry → E010.  Span must propagate from the `sorryExpr` node.
example :
  elabExprFailsAtSpan Scope.empty (.sorryExpr markerSpan) "E010" markerSpan
    = true := by
  native_decide

-- Integer literal `42` → unary-Nat ctor chain (D2).  We compare
-- structurally against `FX.Elab.buildNatLit 42` (the authoritative
-- builder the elaborator itself uses), so a broken literal path
-- that returns `Term.type .zero`, a zero Nat, or a 43-deep chain
-- is distinguishable from a correct 42-deep Succ chain.
example :
  elabExprIs Scope.empty
    (.literal (.intLit "42" .dec) zeroSpan)
    (buildNatLit 42) = true := by
  native_decide

-- Also check the boundary literal `0` — a broken elaborator that
-- always returned the same Nat regardless of `text` would fail to
-- distinguish `0` from `42`.
example :
  elabExprIs Scope.empty
    (.literal (.intLit "0" .dec) zeroSpan)
    (buildNatLit 0) = true := by
  native_decide

-- Non-decimal literals route through `parseIntText?` — check hex.
-- `0xFF = 255` ⇒ a 255-deep Succ chain.  Round-trip verifies the
-- whole literal pipeline, not just the decimal fast path.
example :
  elabExprIs Scope.empty
    (.literal (.intLit "FF" .hex) zeroSpan)
    (buildNatLit 255) = true := by
  native_decide

-- Named argument at a call site where `f` is a local binding
-- (not a registered global decl): E012 per B12 — named args
-- require a direct reference to a registered fn decl with
-- known param names.  A local scope push doesn't register the
-- param names anywhere, so the call can't route.
example :
  elabExprFailsWith (Scope.empty.push "f")
    (.app (var "f") #[.named "x" typeKw] zeroSpan) "E012" = true := by
  native_decide

-- if-expression without an expected type → E010.  Span must
-- propagate from the surface `ifExpr` node.
example :
  elabExprFailsAtSpan Scope.empty
    (.ifExpr typeKw typeKw #[] (some typeKw) markerSpan) "E010" markerSpan
    = true := by
  native_decide

-- Untyped let-binding with `type` keyword as RHS now succeeds:
-- synthesis-mode inference (§4.6) picks `Type<succ 0>` as the
-- let-binding's declared type (since `type` elaborates to
-- `Type<0>` which has type `Type<succ 0>`).  The elab returns
-- a kernel term `(λ _. body) value`.
example :
  (elabExpr GlobalEnv.empty Scope.empty none
    (.letBind (.wildcard zeroSpan) none typeKw typeKw markerSpan)).isOk = true := by
  native_decide

-- Untyped let-binding with a non-synthesis-mode RHS (empty app
-- of an unregistered name) → T045.  Pins the fallback path of
-- the inference helper so `inferLetRhsType? = none` still
-- surfaces an error to the user.
example :
  elabExprFailsAtSpan Scope.empty
    (.letBind (.wildcard zeroSpan) none
      (Expr.var ⟨#[], "unregistered_xyz", zeroSpan⟩)
      typeKw markerSpan) "T045" markerSpan = true := by
  native_decide

/-! ## Lambda-param chain — untyped / wildcard / destructure

Rejection tests pin both the E-code AND the span.  The span
comes from the surrounding lambda's span argument, so a broken
`elabLamChain` that defaults the span to `Span.zero` fails
these assertions while still emitting the correct code. -/

-- Untyped parameter → E010.
example :
  elabExprFailsAtSpan Scope.empty
    (.lam #[.plain "x"] (var "x") markerSpan) "E010" markerSpan = true := by
  native_decide

-- Wildcard parameter → E010.
example :
  elabExprFailsAtSpan Scope.empty
    (.lam #[.wildcard] typeKw markerSpan) "E010" markerSpan = true := by
  native_decide

-- Destructuring parameter → E010.
example :
  elabExprFailsAtSpan Scope.empty
    (.lam #[.destructure (.wildcard zeroSpan)] typeKw markerSpan) "E010"
    markerSpan = true := by
  native_decide

-- Mixed chain: `fn(x: type, y) => x` — the untyped trailer must
-- still produce E010 even though the leading param is well-typed.
-- A broken elaborator that only checked the HEAD would pass here.
example :
  elabExprFailsWith Scope.empty
    (.lam #[.typed "x" typeKw, .plain "y"] (var "x") markerSpan) "E010"
    = true := by
  native_decide

/-! ## B11 partial — untyped/wildcard lambda params with expected Pi

When `elabExpr` receives an `expected` type that's a `Π`-type,
the `.plain` and `.wildcard` lambda params inherit their types
from the Pi's domain, and the rest-of-chain recurses with the
Pi's codomain as the new expected.  Without an expected, those
shapes still reject (tests above).

A broken implementation that ignored `expected`, or one that
matched on the wrong Pi position, would fail these assertions. -/

-- `fn(x) => x` against expected `Π(_: type<0>). type<0>` (identity
-- on Type<0>) should elaborate to `λ(x: type<0>). var 0`.
example :
  (match elabExpr GlobalEnv.empty Scope.empty
    (some (.piTot Grade.default (.type .zero) (.type .zero)))
    (.lam #[.plain "x"] (var "x") zeroSpan) with
   | .ok resultTerm =>
     resultTerm == .lam Grade.default (.type .zero) (.var 0)
   | .error _ => false) = true := by native_decide

-- `fn(_) => type<0>` against expected `Π(_: type<0>). type<1>`
-- — wildcard becomes an anonymous binder with domain type<0>.
example :
  (match elabExpr GlobalEnv.empty Scope.empty
    (some (.piTot Grade.default (.type .zero) (.type (.succ .zero))))
    (.lam #[.wildcard] typeKw zeroSpan) with
   | .ok resultTerm =>
     resultTerm == .lam Grade.default (.type .zero) (.type .zero)
   | .error _ => false) = true := by native_decide

-- Two-param chain `fn(x, y) => y` against `Π a. Π b. type<0>`:
-- the Pi chain's first domain fills x, second domain fills y,
-- the codomain (type<0>) is the body's expected.
example :
  (match elabExpr GlobalEnv.empty Scope.empty
    (some (.piTot Grade.default (.type .zero)
            (.piTot Grade.default (.type .zero) (.type .zero))))
    (.lam #[.plain "x", .plain "y"] (var "y") zeroSpan) with
   | .ok resultTerm =>
     resultTerm ==
       .lam Grade.default (.type .zero)
         (.lam Grade.default (.type .zero) (.var 0))
   | .error _ => false) = true := by native_decide

-- Non-Pi expected + untyped param still rejects (the expected-
-- Pi path is the ONLY escape from E010).
example :
  elabExprFailsWith Scope.empty
    (.lam #[.plain "x"] (var "x") markerSpan) "E010" = true := by
  native_decide

/-! ## Declaration elaboration -/

/-- A pure zero-arg fn: `fn tiny() : Nat = Nat.Zero;`.  Pinned
    by the Unit-Pi regression tests below — its elaborated body
    must be a ghost-graded Unit-parametered lambda and its type
    must be the matching Pi.  Regression target for the §31.7
    zero-arg kernel translation. -/
def tinyZeroArgDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "tiny")
    (params := #[])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body := .oneLiner (varQual ["Nat"] "Zero"))
    (span := zeroSpan)

/-- The identity function: `fn id(a: type, x: a) : a = x;` -/
def identityDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "id")
    (params := #[
      .mk .default_ "a" typeKw zeroSpan,
      .mk .default_ "x" (var "a") zeroSpan
    ])
    (retType := var "a")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (var "x"))
    (span := zeroSpan)

-- Identity elaborates AND type-checks.
example : elabAndChecksOk identityDecl = true := by native_decide

-- Also verify the ELABORATED BODY has the expected kernel shape
-- — two nested `lam`s over `type` and `var 0`, with `var 0` as
-- the inner body.  A broken elaborator that returned a constant
-- placeholder body could still `okDecl` if the kernel accepted
-- the placeholder at the declared type; this assertion prevents
-- that.  Body is `lam(type, lam(var 0, var 0))`.
example :
  declBodyEq identityDecl
    (.lam Grade.default (.type .zero)
      (.lam Grade.default (.var 0) (.var 0))) = true := by native_decide

-- And the DECLARED TYPE also round-trips as a Pi chain:
-- `(a: type) -> (x: a) -> a`  =  `pi(type, pi(var 0, var 1))`.
-- `var 1` on the inner codomain refers back to `a` through the
-- `x` binder.
example :
  declTypeEq identityDecl
    (.piTot Grade.default (.type .zero)
      (.piTot Grade.default (.var 0) (.var 1))) = true := by native_decide

/-- Well-typed `fst : (a: type, b: type, x: a, y: b) -> a`. -/
def fstDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "fst")
    (params := #[
      .mk .default_ "a" typeKw zeroSpan,
      .mk .default_ "b" typeKw zeroSpan,
      .mk .default_ "x" (var "a") zeroSpan,
      .mk .default_ "y" (var "b") zeroSpan
    ])
    (retType := var "a")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (var "x"))
    (span := zeroSpan)

example : elabAndChecksOk fstDecl = true := by native_decide

/-- Ill-typed: return type claims `type` but body is `x : a`. -/
def wrongDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "wrong")
    (params := #[
      .mk .default_ "a" typeKw zeroSpan,
      .mk .default_ "x" (var "a") zeroSpan
    ])
    (retType := typeKw)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (var "x"))
    (span := zeroSpan)

-- Elaboration succeeds (the surface is well-formed); kernel rejects.
example : elabAndCheckTypeFails wrongDecl = true := by native_decide

/-- A fn body referring to an unbound identifier — elaboration fails. -/
def unknownVarDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "bad")
    (params := #[.mk .default_ "a" typeKw zeroSpan])
    (retType := typeKw)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (var "nonexistent"))
    (span := zeroSpan)

-- Stronger form: ensure the underlying ElabError is E001 (unbound
-- identifier), not any other elabFail code.  A broken elaborator
-- that erroneously reported E999 for every unknown name would
-- satisfy the original `elabFail` predicate but fail here.
example :
  elabAndCheckElabFailsWith unknownVarDecl "E001" = true := by native_decide

/-- Block-form body with an empty stmt list + `type` tail —
    elaborates successfully after task B5.  The body here is `type`
    (= `Term.type zero`) whose kernel-inferred type is `Term.type
    (succ zero)`; the declared return type is `Term.type zero` so
    the kernel rejects with a universe mismatch.  This shows:
    block bodies now reach the checker (no more E030). -/
def blockBodyDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "blockBody")
    (params := #[])
    (retType := typeKw)
    (effects := #[])
    (specs := #[])
    (body :=.block #[] typeKw)
    (span := zeroSpan)

-- Block body elaborates (B5); the kernel rejects due to universe
-- mismatch (`type : type<1>` vs declared return `type<0>`).
example : elabAndCheckTypeFails blockBodyDecl = true := by native_decide

/-- A well-typed block body: `fn blockId(T: type, x: T) : T =
    begin fn return x; end fn;` — semantically identical to the
    one-liner `= x;` but via the block form. -/
def blockIdDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "blockId")
    (params := #[
      .mk .default_ "T" typeKw zeroSpan,
      .mk .default_ "x" (var "T") zeroSpan
    ])
    (retType := var "T")
    (effects := #[])
    (specs := #[])
    (body :=.block #[] (var "x"))
    (span := zeroSpan)

example : elabAndChecksOk blockIdDecl = true := by native_decide

-- Block-form body should elaborate to the same kernel shape as
-- the one-liner form — two `lam`s over `type` and `var 0`
-- wrapping `var 0`.  Ensures block desugaring is semantic no-op
-- when no statements are present.
example :
  declBodyEq blockIdDecl
    (.lam Grade.default (.type .zero)
      (.lam Grade.default (.var 0) (.var 0))) = true := by native_decide

/-- A let-binding via the block form:
    `fn letId(T: type, x: T) : T =
       begin fn let y : T = x; return y; end fn;` — introduces
    an intermediate binding and returns it. -/
def letIdDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "letId")
    (params := #[
      .mk .default_ "T" typeKw zeroSpan,
      .mk .default_ "x" (var "T") zeroSpan
    ])
    (retType := var "T")
    (effects := #[])
    (specs := #[])
    (body :=.block #[.letStmt (.var "y" zeroSpan) (some (var "T")) (var "x") zeroSpan]
                    (var "y"))
    (span := zeroSpan)

example : elabAndChecksOk letIdDecl = true := by native_decide

-- Also pin the elaborated body shape: let-binding desugars to
-- `app(lam Y_ty rhs_body, rhs_value)`, wrapping it in the
-- parameter lams.  If `elabStmtChain` silently dropped the
-- `letStmt` or failed to shift the expected return type, the
-- body would elaborate to `lam type (lam (var 0) (var 0))` —
-- same as `blockIdDecl` — which fails this structural check.
example :
  declBodyEq letIdDecl
    (.lam Grade.default (.type .zero)            -- T : type
      (.lam Grade.default (.var 0)                -- x : T
        (.app
          (.lam Grade.default (.var 1) (.var 0))  -- λ(y: T). y
          (.var 0)))) = true := by native_decide  -- applied to x

/-- Module decl — accepted as a no-op in Phase-2 (B13 partial).
    `module Foo;` at the top of a single-file program is
    benign; cross-file module-system semantics land with
    Phase-6.  The elaborator produces a placeholder ElabDecl
    with name `<module Foo>`. -/
def moduleDecl : Decl := .moduleDecl (qualOf "Foo") zeroSpan

example : (elabDecl moduleDecl).isOk = true := by native_decide

-- The elaborated module decl has a distinctive `<module ...>`
-- name prefix so the CLI can recognize it in output.
example :
  (match elabDecl moduleDecl with
   | .ok elaborated => elaborated.name == "<module Foo>"
   | .error _       => false) = true := by native_decide

/-- Const decl — elaborates as a zero-param alias (B13 partial).
    `const FOO : type = type` becomes a decl with type = `type 0`
    and body = `type 0`.  Distinguishing the elaborated body
    shape here also catches any regression where the elab
    swapped type and value positions. -/
def constDecl : Decl :=
  .constDecl "FOO" typeKw typeKw zeroSpan

example : (elabDecl constDecl).isOk = true := by native_decide

-- The elaborated decl has the right name, type, and body.
example :
  (match elabDecl constDecl with
   | .ok elaborated => elaborated.name == "FOO"
                       && (elaborated.type == .type .zero)
                       && (elaborated.body == .type .zero)
   | .error _ => false) = true := by native_decide

/-- `val NAME : TYPE ;` — forward declaration (B13 partial).
    Elaborates to an ElabDecl with the declared type and a
    placeholder `Term.const NAME` body.  Trust is external (set
    by checkFile pass 1), though at single-decl elabDecl level
    the ElabDecl doesn't carry trust. -/
def valDecl : Decl :=
  .valDecl "external_answer" typeKw zeroSpan

example : (elabDecl valDecl).isOk = true := by native_decide

-- The elaborated val decl body is `Term.const "external_answer"`
-- (self-ref placeholder).
example :
  (match elabDecl valDecl with
   | .ok elaborated =>
     elaborated.name == "external_answer"
       && (elaborated.body == Term.const "external_answer")
       && (elaborated.type == .type .zero)
   | .error _ => false) = true := by native_decide

/-! ## B4 — specification clauses (§5.1, §10.1-§10.2)

Pinning the parser→elab wiring for `where`, `pre`, `post`,
`decreases`.  Clauses elaborate under the fn's param scope
(plus the return-binder for `post`); §5.1 ordering is checked
at elab time; the resulting ElabSpecClause list rides on
ElabDecl.specs for Stream E to consume.  -/

/-- `fn specOk(n: Nat) : Nat
     pre true;
     post r => r;
     decreases n;
   = n;` — all three clauses in canonical §5.1 order. -/
def specOkDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "specOk")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[
      -- Predicates reference the fn's single param `n` via
      -- de Bruijn 0; `post` names the return binder `r`.
      .preCond    trueLit                      zeroSpan,
      .postCond   "r"  (varName "r")           zeroSpan,
      .decreases       (varName "n")           zeroSpan
    ])
    (body := .oneLiner (varName "n"))
    (span := zeroSpan)

/-- Spec count on ElabDecl — surface clauses should roundtrip
    1:1 to elaborated clauses. -/
def specCountOfDecl (d : Decl) : Option Nat :=
  match elabAndCheck d with
  | .okDecl elaborated => some elaborated.specs.size
  | _                  => none

/-- `fn badOrder(n: Nat) : Nat
     post r => r;
     pre true;                -- R007: pre after post
   = n;` -/
def specBadOrderDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "badOrder")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[
      .postCond "r" (varName "r") zeroSpan,
      .preCond       trueLit       zeroSpan   -- violation
    ])
    (body := .oneLiner (varName "n"))
    (span := zeroSpan)

/-- `fn whereAfterDecr(n: Nat) : Nat
     decreases n;
     where n;                  -- R007: where after decreases
   = n;` -/
def specWhereAfterDecrDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "whereAfterDecr")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[
      .decreases   (varName "n") zeroSpan,
      .whereCstr   (varName "n") zeroSpan    -- violation
    ])
    (body := .oneLiner (varName "n"))
    (span := zeroSpan)

/-- `fn postBinder(n: Nat) : Nat
     post r => r;
   = n;` — the post binder `r` must be in scope for the
   predicate.  Pins that elab extends the scope by one
   binder before elaborating the post predicate. -/
def postBinderDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "postBinder")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[
      .postCond "r" (varName "r") zeroSpan
    ])
    (body := .oneLiner (varName "n"))
    (span := zeroSpan)

/-- Check that the elaborated post binder really elaborated —
    the predicate Term should be `Term.var 0`, referencing the
    return binder at the innermost scope position. -/
def specPostBinderElabs (d : Decl) : Bool :=
  match elabAndCheck d with
  | .okDecl elaborated =>
    elaborated.specs.any fun specClause =>
      match specClause with
      | .postCond _ predicateTerm => predicateTerm == Term.var 0
      | _                          => false
  | _ => false

/-- Non-fn decl (sorry) → E020. -/
def sorryDecl : Decl := .sorryDecl zeroSpan

example : elabDeclFailsWith sorryDecl "E020" = true := by native_decide

/-! ## Decl.nameHint for diagnostics -/

example : Decl.nameHint identityDecl = "id" := by native_decide
example : Decl.nameHint fstDecl = "fst" := by native_decide
example : Decl.nameHint moduleDecl = "<module>" := by native_decide
example : Decl.nameHint constDecl = "FOO" := by native_decide
example : Decl.nameHint valDecl = "external_answer" := by native_decide
example : Decl.nameHint sorryDecl = "<sorry>" := by native_decide

/-! ## Runtime harness -/

def run : IO Unit := Tests.suite "Tests.Elab.ElaborateTests" do
  -- Positive elab cases.
  check "elab typeKw" true
    (elabExprIs Scope.empty typeKw (.type .zero))
  check "elab var (push x)" true
    (elabExprIs (Scope.empty.push "x") (var "x") (.var 0))
  check "elab var (push y,x → resolve y)" true
    (elabExprIs (Scope.empty.push "y" |>.push "x") (var "y") (.var 1))
  check "elab arrow" true
    (elabExprIs Scope.empty (.arrow typeKw typeKw zeroSpan)
      (.piTot Grade.default (.type .zero) (.type .zero)))
  check "elab lam(typed) x : type => x" true
    (elabExprIs Scope.empty
      (.lam #[.typed "x" typeKw] (var "x") zeroSpan)
      (.lam Grade.default (.type .zero) (.var 0)))
  -- Literal round-trips: the integer literal path must produce
  -- the right unary-Nat depth.  Compare structurally to distinguish
  -- 0 from 42 from 255 — a broken fast path that always returned
  -- zero would fail.
  check "int literal 42 → Succ^42 Zero" true
    (elabExprIs Scope.empty
      (.literal (.intLit "42" .dec) zeroSpan) (buildNatLit 42))
  check "int literal 0 → Zero" true
    (elabExprIs Scope.empty
      (.literal (.intLit "0" .dec) zeroSpan) (buildNatLit 0))
  check "hex literal 0xFF → Succ^255 Zero" true
    (elabExprIs Scope.empty
      (.literal (.intLit "FF" .hex) zeroSpan) (buildNatLit 255))

  -- Negative elab cases — code AND span asserted where the
  -- elaborator threads the AST node's span.
  check "unknown var → E001" true
    (elabExprFailsWith Scope.empty (var "missing") "E001")
  check "unit → E010 with propagated span" true
    (elabExprFailsAtSpan Scope.empty (.unit markerSpan) "E010" markerSpan)
  check "sorry → E010 with propagated span" true
    (elabExprFailsAtSpan Scope.empty (.sorryExpr markerSpan) "E010" markerSpan)
  check "if → E010 with propagated span" true
    (elabExprFailsAtSpan Scope.empty
      (.ifExpr typeKw typeKw #[] (some typeKw) markerSpan) "E010" markerSpan)
  check "let (no type ann, synthesis-mode typeKw RHS) → ok" true
    (elabExpr GlobalEnv.empty Scope.empty none
      (.letBind (.wildcard zeroSpan) none typeKw typeKw markerSpan)).isOk
  check "let (no type ann, non-synth RHS) → T045 with propagated span" true
    (elabExprFailsAtSpan Scope.empty
      (.letBind (.wildcard zeroSpan) none
        (Expr.var ⟨#[], "unregistered_xyz", zeroSpan⟩) typeKw markerSpan)
      "T045" markerSpan)
  check "named arg on local-scope callee → E012" true
    (elabExprFailsWith (Scope.empty.push "f")
      (.app (var "f") #[.named "x" typeKw] zeroSpan) "E012")
  check "untyped lam param → E010 with propagated span" true
    (elabExprFailsAtSpan Scope.empty
      (.lam #[.plain "x"] (var "x") markerSpan) "E010" markerSpan)
  check "wildcard lam param → E010 with propagated span" true
    (elabExprFailsAtSpan Scope.empty
      (.lam #[.wildcard] typeKw markerSpan) "E010" markerSpan)
  check "destructure lam param → E010 with propagated span" true
    (elabExprFailsAtSpan Scope.empty
      (.lam #[.destructure (.wildcard zeroSpan)] typeKw markerSpan) "E010"
      markerSpan)
  check "mixed typed + untyped lam chain → E010" true
    (elabExprFailsWith Scope.empty
      (.lam #[.typed "x" typeKw, .plain "y"] (var "x") zeroSpan) "E010")

  -- Declaration elab + check — go beyond `okDecl` to verify the
  -- elaborated Term shape matches the surface program's semantics.
  check "fn id elaborates + checks" true (elabAndChecksOk identityDecl)
  check "fn id body = λ(type).λ(var 0). var 0" true
    (declBodyEq identityDecl
      (.lam Grade.default (.type .zero)
        (.lam Grade.default (.var 0) (.var 0))))
  check "fn id type = Π(type). Π(var 0). var 1" true
    (declTypeEq identityDecl
      (.piTot Grade.default (.type .zero)
        (.piTot Grade.default (.var 0) (.var 1))))
  check "fn fst elaborates + checks" true (elabAndChecksOk fstDecl)
  check "fn wrong elab OK, kernel rejects" true (elabAndCheckTypeFails wrongDecl)
  check "fn with unknown var → elabFail (E001)" true
    (elabAndCheckElabFailsWith unknownVarDecl "E001")
  check "block body with universe mismatch → typeFail" true (elabAndCheckTypeFails blockBodyDecl)
  check "well-typed block body elaborates + checks" true (elabAndChecksOk blockIdDecl)
  check "block body body = id body (desugar no-op w/o stmts)" true
    (declBodyEq blockIdDecl
      (.lam Grade.default (.type .zero)
        (.lam Grade.default (.var 0) (.var 0))))
  check "block with let stmt elaborates + checks" true (elabAndChecksOk letIdDecl)
  check "block+let body uses let-redex (app(lam, var 0))" true
    (declBodyEq letIdDecl
      (.lam Grade.default (.type .zero)
        (.lam Grade.default (.var 0)
          (.app (.lam Grade.default (.var 1) (.var 0)) (.var 0)))))
  check "module decl accepted as no-op" true (elabDecl moduleDecl).isOk
  check "const decl elaborates" true (elabDecl constDecl).isOk
  check "sorry decl → E020" true (elabDeclFailsWith sorryDecl "E020")

  -- ## Zero-arg Unit-Pi (§31.7 kernel translation)
  -- Every `fn name() : T with eff = body` elaborates uniformly to
  -- `λ (_ :_ghost Unit). body : Π (_ :_ghost Unit) → T @ eff`.
  -- The ghost Unit binder gives the effect a home on the Pi's
  -- return-effect field; call sites `name()` are desugared to
  -- `name Unit.tt` at the App case.  Fires effects via the
  -- standard Pi-elim chain, eliminating the earlier special-case
  -- hack in `EffectInference.termEffect`'s `.const` arm.
  -- These tests pin the Term-level shape so a future refactor
  -- can't silently revert.
  check "zero-arg fn body = λ (_ :_ghost Unit). Nat.Zero" true
    (bodyMatches tinyZeroArgDecl
      (.lam Grade.ghost (.ind "Unit" []) (.ctor "Nat" 0 [] [])))
  check "zero-arg fn type = Π (_ :_ghost Unit) → Nat" true
    (typeMatches tinyZeroArgDecl
      (.pi Grade.ghost (.ind "Unit" []) (.ind "Nat" []) Effect.tot))

  -- ## B4 spec clauses (§5.1: where → pre → post → decreases)
  -- Parser attaches clauses; elab validates ordering and
  -- elaborates predicates under the fn's param scope (plus the
  -- return binder for post).  SMT discharge deferred to Stream E.
  -- Source-level elaboration ends-to-ends through the new
  -- `specs` field on ElabDecl.
  check "spec clauses — in-order: pre → post → decreases accepts" true
    (elabAndChecksOk specOkDecl)
  check "spec clauses — elaborated count matches surface count" (some 3)
    (specCountOfDecl specOkDecl)
  check "spec clauses — out-of-order pre after post → R007" true
    (elabDeclFailsWith specBadOrderDecl "R007")
  check "spec clauses — `where` after `decreases` → R007" true
    (elabDeclFailsWith specWhereAfterDecrDecl "R007")
  check "spec clauses — post binder scopes the predicate" true
    (specPostBinderElabs postBinderDecl)

  -- Decl.nameHint.
  check "nameHint(id)" "id" (Decl.nameHint identityDecl)
  check "nameHint(fst)" "fst" (Decl.nameHint fstDecl)
  check "nameHint(module)" "<module>" (Decl.nameHint moduleDecl)
  check "nameHint(const)" "FOO" (Decl.nameHint constDecl)
  check "nameHint(sorry)" "<sorry>" (Decl.nameHint sorryDecl)

end Tests.Elab.ElaborateTests
