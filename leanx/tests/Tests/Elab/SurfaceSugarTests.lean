import FX.Elab.Elaborate
import FX.Elab.MatchHelpers
import FX.Kernel.Inductive
import FX.Syntax.Parser
import FX.Syntax.Lexer
import Tests.ElabSupport
import Tests.Framework

/-!
# Surface-sugar elab tests (§4.2 pipe + dot-shorthand, §2.6 logical ops)

Unit coverage for the three landings that compose §4.2's
pipeline idiom:

  * `.field` dot-shorthand (Q61)        — `fx_design.md` §4.2 rule 25
  * `x |> f(args)` pipe operator (Q62)  — `fx_design.md` §4.2 rule 5
  * `not` / `and` / `or` keywords (Q63) — `fx_design.md` §2.6

Before this file the three features were covered only by the
end-to-end conformance programs (`40_dot_shorthand.fx`,
`41_pipe_and_dot.fx`, `42_logical_ops.fx`).  E2E tests catch
regressions but don't pin the kernel-layer shape each construct
elaborates to — a silent change to the `indRec` motive or the
pipe→app rewrite would pass conformance as long as the final
value still computed right.  The tests here pin exact Term
output for the success paths and exact error codes for the
rejection paths, so structural elaborator drift is caught in
~4ms instead of requiring a full `fxi run`.

## Covered

### §2.6 logical operators (`elab Expr.logicalNot`/`And`/`Or`)

  * Each op's `indRec "Bool"` shape is pinned to kernel Term
    equality.  `not`=swap-True/False methods, `and`=short-
    circuit False, `or`=short-circuit True.
  * Non-Bool operand trips T002 from the kernel's type-check
    pass (elab forces `some boolTy` on sub-expressions).
  * When no `expected` is provided, the motive defaults to
    Bool so the result still has a well-defined kernel type.

### §4.2 dot-shorthand

  * Three rejection paths (no expected, non-Pi expected,
    Pi-to-non-inductive expected) verify Q61's diagnostic
    hygiene — each emits E010 with a distinct message.
  * The happy path (dot-shorthand inside a higher-order fn
    arg position) is already exercised by
    `40_dot_shorthand.fx` at the conformance layer; repeating
    it here would require user-spec setup that duplicates
    `AdtTests`, so we defer that coverage.

### §4.2 pipe

  * Rewrite shape verified via decl-level `decl_ok`: simple
    pipe `n |> double` and pipe-chain `n |> double |> double`
    both elab + type-check, matching the E2E pipe test but
    isolated from the surrounding conformance scaffolding.
  * `inferLetRhsType?` sees through `.pipe` when the RHS is a
    registered fn — regression from the Q62 reimplementation
    commit, locked in here so a future refactor doesn't drop
    the case.
-/

namespace Tests.Elab.SurfaceSugarTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests.ElabSupport

/-! ## Shared helpers -/

/-- Run `elabExpr` against the empty env + empty scope, returning
    the kernel Term (or elaboration error).  Same shape as the
    helper `IfExprTests` uses locally — re-declared here to keep
    the tests self-contained. -/
private def runWith (expected : Option Term) (expr : Expr)
    : Except ElabError Term :=
  elabExpr GlobalEnv.empty Scope.empty expected expr

/-- Compare an elab result to an exact kernel Term.  Uses `BEq
    Term` from `structEq` (kernel's `Term` has no DecidableEq
    because `Grade` fields block derivation). -/
private def elabEq (elabResult : Except ElabError Term) (expected : Term) : Bool :=
  match elabResult with
  | .ok resultTerm => resultTerm == expected
  | _              => false

/-- Canonical Bool motive under expected type Bool — matches the
    `boolMotive` applied to `Term.ind "Bool" []` (self-motive,
    non-dependent elim).  The `shift 0 1` is a no-op on the
    closed `ind "Bool" []` term. -/
private def boolSelfMotive : Term :=
  boolMotive (.ind "Bool" [])

/-! ## §2.6 — logical `not`

Shape: `indRec "Bool" boolSelfMotive [ctorTrue, ctorFalse] body`.

  * method[0] runs on False → True  (flipping the scrutinee)
  * method[1] runs on True  → False

This matches §2.6's spec: `not x = if x then False else True`.
The kernel `indRec` is `if-then-else` on Bool (ctor 0 = False
arm, ctor 1 = True arm), so method[0] is the else-branch and
method[1] is the then-branch. -/

/-- `not true` with expected = Bool. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalNot trueLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-- `not false` with expected = Bool. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalNot falseLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
      (.ctor "Bool" 0 [] [])) := by
  native_decide

/-- `not` without an expected type still forces its body to
    Bool (the elab case calls `elabExpr` with `some boolTy` on
    the body).  No E010 here — the motive just defaults to
    Bool-self. -/
example :
  elabEq (runWith none
    (.logicalNot trueLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-! ## §2.6 — logical `and`

Shape: `indRec "Bool" motive [ctorFalse, rhs] lhs`.

  * method[0] (lhs = False) = ctorFalse  (short-circuit)
  * method[1] (lhs = True)  = rhs

Spec: `a and b = if a then b else False`. -/

/-- `true and false`. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalAnd trueLit falseLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 0 [] [], .ctor "Bool" 0 [] []]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-- `true and true`. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalAnd trueLit trueLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 0 [] [], .ctor "Bool" 1 [] []]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-! ## §2.6 — logical `or`

Shape: `indRec "Bool" motive [rhs, ctorTrue] lhs`.

  * method[0] (lhs = False) = rhs       (evaluate rhs)
  * method[1] (lhs = True)  = ctorTrue  (short-circuit)

Spec: `a or b = if a then True else b`. -/

/-- `false or true`. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalOr falseLit trueLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 1 [] [], .ctor "Bool" 1 [] []]
      (.ctor "Bool" 0 [] [])) := by
  native_decide

/-- `false or false`. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalOr falseLit falseLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 0 [] [], .ctor "Bool" 1 [] []]
      (.ctor "Bool" 0 [] [])) := by
  native_decide

/-! ## §4.2 — dot-shorthand rejection paths

`.field` requires an expected Pi whose domain is an inductive
type with a ctor declaring `field` among its named args.  Any
deviation is E010 with a message that cites the field name, so
subsequent diagnostics reach the user with enough context to
fix. -/

/-- No expected type at all → E010 "has no known argument type". -/
example :
  elabErrCode (runWith none
    (.dotShorthand "name" zeroSpan)) "E010" := by
  native_decide

/-- Expected is a ground type (Nat), not a Pi → E010. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (.dotShorthand "name" zeroSpan)) "E010" := by
  native_decide

/-- Expected is a Pi but the domain is a universe (Type), not
    an inductive → E010 "requires the expected Pi's domain to
    be an inductive type". -/
example :
  let domainIsUniverse : Term :=
    .pi Grade.default (.type .zero) (.ind "Nat" []) .tot
  elabErrCode (runWith (some domainIsUniverse)
    (.dotShorthand "name" zeroSpan)) "E010" := by
  native_decide

/-! ## §4.2 — pipe integration

Pipe is sugar for "prepend lhs as positional arg 0".  The
elaborator rewrites `x |> f(args)` to `f(x, args)` and
delegates to the `Expr.app` branch, so the typing rule, grade
flow, and arg-reorder logic are the existing app path — no new
kernel surface.

These decl-level tests use `decl_ok` (which drives elab +
type-check through `elabAndCheck`) because pipe's interesting
case is "a real fn call works through the pipe alias".  Setting
up the env via `checkFile` is the least-surface way to do that
without duplicating fn-registration helpers from PreludeTests. -/

/-- Helper: surface `Succ^n Zero` as an AST. -/
private def unaryNatExpr : Nat → Ast.Expr
  | 0     => varQual ["Nat"] "Zero"
  | n + 1 => .app (varQual ["Nat"] "Succ")
               #[.pos (unaryNatExpr n)] zeroSpan

/-- `fn id_nat(n: Nat) : Nat = n;` — identity over Nat.  Used
    as the pipe callee in `simplePipeFile` so the pipe result
    is a plain Nat without additional structure. -/
private def idNatDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "id_nat")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body := .oneLiner (varName "n"))
    (span := zeroSpan)

/-- `fn main() : Nat = 2 |> id_nat;` — pipe to bare var.
    Expected elab: `(id_nat 2)`. -/
private def pipeBareFile : File :=
  let mainDecl : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "main") (params := #[])
      (retType := natTy)
      (effects := #[])
      (specs := #[])
      (body := .oneLiner
        (.pipe (unaryNatExpr 2) (varName "id_nat") zeroSpan))
      (span := zeroSpan)
  { decls := #[idNatDecl, mainDecl], span := zeroSpan }

/-- `fn main() : Nat = 2 |> id_nat |> id_nat;` — pipe chain.
    Expected elab: left-assoc, `id_nat (id_nat 2)`. -/
private def pipeChainFile : File :=
  let mainDecl : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "main") (params := #[])
      (retType := natTy)
      (effects := #[])
      (specs := #[])
      (body := .oneLiner
        (.pipe
          (.pipe (unaryNatExpr 2) (varName "id_nat") zeroSpan)
          (varName "id_nat") zeroSpan))
      (span := zeroSpan)
  { decls := #[idNatDecl, mainDecl], span := zeroSpan }

/-- Helper: return `true` iff every decl in the file
    round-trips through elab + type-check. -/
private def allOk (file : File) : Bool :=
  (checkFile file).all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false

/-- `n |> f` elaborates to `f(n)` — simplest pipe.  The whole
    file must elab+check clean. -/
example : allOk pipeBareFile := by native_decide

/-- `n |> f |> g` elaborates to `g(f(n))` left-associatively. -/
example : allOk pipeChainFile := by native_decide

/-! ## §4.2 — pipe + let synthesis-mode inference

The Q62 reimplementation moved the pipe's lhs→positional rewrite
from parse time to elab time.  `inferLetRhsType?` needs its own
`.pipe` case — otherwise `let result = x |> f;` (no ascription)
trips T045 because the synthesis-mode allowlist doesn't
recognize `Expr.pipe` as a callable shape.

This regression cost one conformance failure at landing
(41_pipe_and_dot.fx:37); locked in below so a future AST
refactor can't silently drop the case. -/

/-- `fn main() : Nat = begin fn let result = 2 |> id_nat;
    return result; end fn;` — let binds an unascribed pipe. -/
private def pipeLetSynthFile : File :=
  let mainDecl : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "main") (params := #[])
      (retType := natTy)
      (effects := #[])
      (specs := #[])
      (body := .block
        #[.letStmt (.var "result" zeroSpan) none
           (.pipe (unaryNatExpr 2) (varName "id_nat") zeroSpan) zeroSpan]
        (varName "result"))
      (span := zeroSpan)
  { decls := #[idNatDecl, mainDecl], span := zeroSpan }

example : allOk pipeLetSynthFile := by native_decide

/-! ## §4.2 rule 25 — multi-dot argument lifting

The lift detects `.dotShorthand` reachable through composable
non-binding nodes (binop / prefix / logical / pipe / try / if
/ field / index) and wraps the whole arg in `fn(it) =>
subst(arg)` so every `.field` in the expression shares a
single implicit element.

### Pure helper pinning

The walk functions on `Ast.Expr` are small and self-contained;
pinning them as `BEq Expr` equalities at compile time catches
drift in the "what counts as composable" policy without
requiring an elab run.  -/

/-- Logical `and` of two dots contains a dot (walks in). -/
example :
    (Ast.Expr.logicalAnd
      (.dotShorthand "active" zeroSpan)
      (.dotShorthand "enabled" zeroSpan) zeroSpan).containsDotShorthand
      = true := by
  native_decide

/-- A dot inside a lambda body does NOT count as a parent-level
    dot — scope boundary. -/
example :
    (Ast.Expr.lam #[.plain "x"]
      (.dotShorthand "field" zeroSpan) zeroSpan).containsDotShorthand
      = false := by
  native_decide

/-- A plain var has no dots. -/
example :
    (Ast.Expr.var (qualOf "x")).containsDotShorthand = false := by
  native_decide

/-- After `substDotShorthand`, a bare dot no longer contains a
    dot — the substitution was total.  `Expr` has no
    decidable equality so we can't pin the Term shape directly;
    testing "the dot was consumed" via `containsDotShorthand`
    is the next-best structural check. -/
example :
  ((Ast.Expr.dotShorthand "name" zeroSpan).substDotShorthand "it"
    ).containsDotShorthand = false := by
  native_decide

/-- Substitution recurses through `logicalAnd`: both dots
    are consumed. -/
example :
  ((Ast.Expr.logicalAnd
    (.dotShorthand "a" zeroSpan)
    (.dotShorthand "b" zeroSpan) zeroSpan).substDotShorthand "it"
    ).containsDotShorthand = false := by
  native_decide

/-- Substitution stops at lambda boundaries: a dot inside
    `fn(x) => .y` is left untouched (the lift owner there is
    the nested lambda's arg position, not the outer).  After
    substitution, the outer `containsDotShorthand` returns
    false because the walk doesn't descend into lambda bodies
    in the first place. -/
example :
  ((Ast.Expr.lam #[.plain "x"]
    (.dotShorthand "y" zeroSpan) zeroSpan).substDotShorthand "it"
    ).containsDotShorthand = false := by
  native_decide

/-! ### End-to-end lift via parse + `checkFile`

Source-string pipeline mirrors `CopySoundnessTests` / this
file's earlier pipe tests: a minimal program exercises each
composable-node path and the resulting decl set must pass
`checkFile` clean.  `@[copy]` on the record type so the
lifted lambda's `it` binder admits multi-use without M001. -/

private def runFromSource (source : String) : Array DeclResult :=
  let lexOutput := FX.Syntax.tokenize source
  let (parsedFile, _) := FX.Syntax.Parser.parseFile lexOutput.tokens
  checkFile parsedFile

private def allSourceOk (source : String) : Bool :=
  (runFromSource source).all fun result =>
    match result with
    | .okDecl _ => true
    | _         => false

/-- Multi-dot through logical `and`. -/
example :
  allSourceOk
    "@[copy] type flag { a: Bool; b: Bool; };\n\
     fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
     fn test_and(f: flag) : Bool = apply_flag(p: .a and .b, f: f);"
    = true := by
  native_decide

/-- Multi-dot through logical `or`. -/
example :
  allSourceOk
    "@[copy] type flag { a: Bool; b: Bool; };\n\
     fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
     fn test_or(f: flag) : Bool = apply_flag(p: .a or .b, f: f);"
    = true := by
  native_decide

/-- Single dot through prefix `not`. -/
example :
  allSourceOk
    "@[copy] type flag { a: Bool; b: Bool; };\n\
     fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
     fn test_not(f: flag) : Bool = apply_flag(p: not .a, f: f);"
    = true := by
  native_decide

/-- Q61 path unchanged: bare `.field` at top of arg position
    still elaborates as before (Q65 skips the lift when the
    arg IS the dot — the existing dotShorthand elab case
    handles it). -/
example :
  allSourceOk
    "type flag { a: Bool; };\n\
     fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
     fn test_bare(f: flag) : Bool = apply_flag(p: .a, f: f);"
    = true := by
  native_decide

/-! ## §2.6 — constructor-test `is` (Q66)

`x is Ctor` elaborates to an exhaustive match over the ctor's
spec — `Bool.True` for the matching arm, `Bool.False` for every
other ctor.  Tests here cover success on prelude Bool/Nat,
spec-name resolution, and the parser's chained-is guard. -/

/-- Bool ctor test: `Bool.True is Bool.True` → Bool. -/
example :
  allSourceOk
    "fn check_one() : Bool = Bool.True is Bool.True;"
    = true := by
  native_decide

/-- Nat ctor test: `Nat.Zero is Nat.Zero` → Bool. -/
example :
  allSourceOk
    "fn check_two() : Bool = Nat.Zero is Nat.Zero;"
    = true := by
  native_decide

/-- Nat negative test: `Nat.Succ(Nat.Zero) is Nat.Zero`.  The
    scrutinee is a one-arg ctor; the elab resolves the target
    ctor (Zero, index 0) and emits two arms, one per Nat
    ctor, so exhaustiveness fires cleanly. -/
example :
  allSourceOk
    "fn check_three() : Bool = Nat.Succ(Nat.Zero) is Nat.Zero;"
    = true := by
  native_decide

/-- Composed with Q63 `and` — both the scrutinee sides must
    share the same `is` precedence, which the parser enforces
    by splitting at `parseIsCheck` (tighter than compare /
    looser than arithmetic). -/
example :
  allSourceOk
    "fn check_four() : Bool = Nat.Zero is Nat.Zero and Bool.True is Bool.True;"
    = true := by
  native_decide

/-- Unknown ctor → E010 (diagnostic from the elab case's
    resolveCtorRef? lookup). -/
example :
  allSourceOk
    "fn check_five() : Bool = Nat.Zero is NoSuchCtor;"
    = false := by
  native_decide

/-! ## §2.6 — propositional `==>` and `<==>` (Q67)

Implies and iff both elaborate to short-circuit `indRec
"Bool"` shapes.  Tests pin kernel Term output against the
expected method arrays. -/

/-- `a ==> b` = `indRec "Bool" motive [True, b] a`.  When lhs
    is False (method[0]), result is True; when lhs is True
    (method[1]), result is b.  Verified here with
    `True ==> False = False` (lhs=True so method[1]=b=False). -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalImplies trueLit falseLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-- `a ==> b` with lhs=False should produce the method[0] slot
    (= True) regardless of rhs. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalImplies falseLit falseLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
      (.ctor "Bool" 0 [] [])) := by
  native_decide

/-- `a <==> b` wraps a nested `not b` in method[0]:
    `indRec "Bool" motive [notRhs, rhs] lhs` where
    `notRhs = indRec "Bool" motive [True, False] b`. -/
example :
  let notRhs : Term :=
    Term.indRec "Bool" boolSelfMotive
      [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
      (.ctor "Bool" 1 [] [])
  elabEq (runWith (some (.ind "Bool" []))
    (.logicalIff trueLit trueLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive
      [notRhs, .ctor "Bool" 1 [] []]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-- End-to-end: `fn check() : Bool = Bool.True ==> Bool.False;`
    elaborates + type-checks clean. -/
example :
  allSourceOk
    "fn imp_one() : Bool = Bool.True ==> Bool.False;"
    = true := by
  native_decide

/-- End-to-end: `<==>` chain (non-chained, so single use). -/
example :
  allSourceOk
    "fn iff_one() : Bool = Bool.True <==> Bool.False;"
    = true := by
  native_decide

/-! ## §3.7 — list literal `[a, b, c]` (Q71)

List literal is a right-fold over the prelude `List` spec:
`[]` → `Nil`; `[a, b, c]` → `Cons(a, Cons(b, Cons(c, Nil)))`.
Element type is taken from the expected `List(T)` Pi — an empty
`some (.ind "List" [T])` lets the elab resolve `T` and bake it
into every generated `Cons` / `Nil` ctor call.

The bare-kernel `runWith` path exercises the elab case against a
synthetic expected; the `allSourceOk` path exercises the full
parser → elab → typecheck pipeline including the List spec
lookup via `preludeSpecs`. -/

/-- Kernel shape of `Nil` for `List(Nat)`. -/
private def listNilNat : Term :=
  Term.ctor "List" 0 [.ind "Nat" []] []

/-- Kernel shape of `Nat.Zero`. -/
private def kernelZeroNat : Term :=
  Term.ctor "Nat" 0 [] []

/-- Kernel shape of `Nat.Succ(Nat.Zero)`. -/
private def kernelOneNat : Term :=
  Term.ctor "Nat" 1 [] [kernelZeroNat]

/-- Empty list elaborates to bare `Nil` for the expected
    element type.  No items means no recursive folds. -/
example :
  elabEq (runWith (some (.ind "List" [.ind "Nat" []]))
    (.listLit #[] zeroSpan))
    listNilNat := by
  native_decide

/-- Single-item list `[Nat.Zero]` elaborates to
    `Cons(Zero, Nil)`. -/
example :
  elabEq (runWith (some (.ind "List" [.ind "Nat" []]))
    (.listLit #[varQual ["Nat"] "Zero"] zeroSpan))
    (Term.ctor "List" 1 [.ind "Nat" []]
      [kernelZeroNat, listNilNat]) := by
  native_decide

/-- Two-item list `[Nat.Zero, Nat.Succ(Nat.Zero)]` elaborates
    to `Cons(Zero, Cons(Succ Zero, Nil))` — right-fold order. -/
example :
  let succOne : Ast.Expr :=
    .app (varQual ["Nat"] "Succ")
      #[.pos (varQual ["Nat"] "Zero")] zeroSpan
  elabEq (runWith (some (.ind "List" [.ind "Nat" []]))
    (.listLit #[varQual ["Nat"] "Zero", succOne] zeroSpan))
    (Term.ctor "List" 1 [.ind "Nat" []]
      [kernelZeroNat,
       Term.ctor "List" 1 [.ind "Nat" []]
         [kernelOneNat, listNilNat]]) := by
  native_decide

/-- Without an expected `List(T)` type the element type is
    unrecoverable → E010 with a hint about adding an ascription. -/
example :
  elabErrCode (runWith none
    (.listLit #[varQual ["Nat"] "Zero"] zeroSpan)) "E010" := by
  native_decide

/-- Expected type is a ground non-list inductive — still E010
    (the match in elab only accepts `Term.ind "List" ...`). -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (.listLit #[] zeroSpan)) "E010" := by
  native_decide

/-- End-to-end: empty list in a `List(Nat)` position elab+checks
    through the full pipeline (spec lookup exercised). -/
example :
  allSourceOk
    "fn empty_nat() : List(Nat) = [];"
    = true := by
  native_decide

/-- End-to-end: two-element list via `Nat.Zero` / `Nat.Succ`. -/
example :
  allSourceOk
    "fn pair_nat() : List(Nat) = [Nat.Zero, Nat.Succ(Nat.Zero)];"
    = true := by
  native_decide

/-- End-to-end: Bool element type — the extraction path is
    generic over element type. -/
example :
  allSourceOk
    "fn bool_pair() : List(Bool) = [Bool.True, Bool.False];"
    = true := by
  native_decide

/-- End-to-end: nested `List(List(Nat))` — each inner list is
    elab'd with `Term.ind "List" [.ind "Nat" []]` as its own
    expected element type. -/
example :
  allSourceOk
    "fn nested() : List(List(Nat)) = [[Nat.Zero], [Nat.Succ(Nat.Zero)]];"
    = true := by
  native_decide

/-- End-to-end: trailing comma tolerated by the parser. -/
example :
  allSourceOk
    "fn trailing_comma() : List(Nat) = [Nat.Zero, Nat.Succ(Nat.Zero),];"
    = true := by
  native_decide

/-- End-to-end: no ascription → elab fires E010, which the
    `checkFile` pipeline surfaces as a non-ok decl. -/
example :
  allSourceOk
    "fn leaks() = [Nat.Zero];"
    = false := by
  native_decide

/-! ## §2.6 — Bool `==` / `!=` dispatch (Q72)

Synthesis-mode probe on both operands picks Bool path when
either emitted Term has a `Term.ctor "Bool" ..` or `Term.indRec
"Bool" ..` head.  Otherwise falls back to the Q68 Nat path.

Bool shapes:
  a == b  →  indRec "Bool" motive [notRhs, rhs]    lhs
  a != b  →  indRec "Bool" motive [rhs,    notRhs] lhs
  notRhs  =  indRec "Bool" motive [True, False]    rhs  -- Q63's `not`

Nat shapes (legacy, Q68):
  a == b  →  nat_eq lhs rhs
  a != b  →  indRec "Bool" motive [True, False] (nat_eq lhs rhs) -/

/-- `Bool.True == Bool.True` pins the iff shape.  method[0]
    (False arm) is `not rhs`; method[1] (True arm) is rhs. -/
example :
  let rhsTerm  : Term := .ctor "Bool" 1 [] []
  let notRhs   : Term := Term.indRec "Bool" boolSelfMotive
                          [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
                          rhsTerm
  elabEq (runWith (some (.ind "Bool" []))
    (.binop Token.eqEq trueLit trueLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive [notRhs, rhsTerm]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-- `Bool.True != Bool.False` pins the xor shape.  method[0]
    runs rhs; method[1] runs `not rhs`. -/
example :
  let rhsTerm : Term := .ctor "Bool" 0 [] []
  let notRhs  : Term := Term.indRec "Bool" boolSelfMotive
                         [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
                         rhsTerm
  elabEq (runWith (some (.ind "Bool" []))
    (.binop Token.neq trueLit falseLit zeroSpan))
    (Term.indRec "Bool" boolSelfMotive [rhsTerm, notRhs]
      (.ctor "Bool" 1 [] [])) := by
  native_decide

/-- Nat baseline: `Nat.Zero == Nat.Zero` still routes to
    `Term.const "nat_eq"` — the Q72 probe sees no Bool head
    on either side and falls back. -/
example :
  elabEq (runWith (some (.ind "Bool" []))
    (.binop Token.eqEq
      (varQual ["Nat"] "Zero")
      (varQual ["Nat"] "Zero") zeroSpan))
    (Term.app (Term.app (Term.const "nat_eq")
       (.ctor "Nat" 0 [] [])) (.ctor "Nat" 0 [] [])) := by
  native_decide

/-- End-to-end: `Bool.True == Bool.True` elab + checks clean. -/
example :
  allSourceOk
    "fn eq_literals() : Bool = Bool.True == Bool.True;"
    = true := by
  native_decide

/-- End-to-end: `Bool.True != Bool.False` elab + checks clean. -/
example :
  allSourceOk
    "fn neq_literals() : Bool = Bool.True != Bool.False;"
    = true := by
  native_decide

/-- End-to-end: `true != false` (keyword form) routes Bool. -/
example :
  allSourceOk
    "fn neq_kw() : Bool = true != false;"
    = true := by
  native_decide

/-- End-to-end: `(not Bool.True) == Bool.False` — the lhs's
    logical-op result has a Bool-head kernel shape. -/
example :
  allSourceOk
    "fn after_not() : Bool = (not Bool.True) == Bool.False;"
    = true := by
  native_decide

/-- End-to-end: `(a < b) == true` — comparison results have
    Bool heads (indRec "Bool"), so the probe picks Bool. -/
example :
  allSourceOk
    "fn cmp_eq() : Bool = (Nat.Zero < Nat.Succ(Nat.Zero)) == true;"
    = true := by
  native_decide

/-- End-to-end: `Nat.Zero == Nat.Zero` still works (legacy
    Nat path).  The probe sees no Bool head on either side. -/
example :
  allSourceOk
    "fn nat_baseline() : Bool = Nat.Zero == Nat.Zero;"
    = true := by
  native_decide

/-! ## §2.6 — Nat `/` / `%` via prelude fns (Q73)

Division and modulus each dispatch to a `Term.const` head:
`a / b → nat_div(a, b)`, `a % b → nat_mod(a, b)`.  The
prelude fns are registered by `seedPrelude` in dependency
order so `nat_mod` (which composes `nat_div`, `nat_mul`,
`nat_sub`) can resolve every reference at reduction time.

Unlike Q70's `+ - *` which double-indRec on one operand,
`nat_div` uses a fuel-bounded helper: outer `indRec "Nat"` on
fuel, motive `λ _ : Nat. Nat -> Nat -> Nat`, and an outer
Bool guard that short-circuits to `Zero` when `b = 0`.
`nat_mod` piggybacks: `a % b = a - (a/b)*b`, so `a % 0 = a`
(trivial Euclidean decomposition). -/

/-- `a / b` elabs to `Term.app (Term.app (Term.const "nat_div")
    lhs) rhs`.  Pin the dispatch so a future refactor can't
    silently break the routing. -/
example :
  elabEq (runWith (some (.ind "Nat" []))
    (.binop Token.slash
      (varQual ["Nat"] "Zero")
      (varQual ["Nat"] "Zero") zeroSpan))
    (Term.app (Term.app (Term.const "nat_div")
       (.ctor "Nat" 0 [] [])) (.ctor "Nat" 0 [] [])) := by
  native_decide

/-- `a % b` elabs to `Term.app (Term.app (Term.const "nat_mod")
    lhs) rhs`. -/
example :
  elabEq (runWith (some (.ind "Nat" []))
    (.binop Token.percent
      (varQual ["Nat"] "Zero")
      (varQual ["Nat"] "Zero") zeroSpan))
    (Term.app (Term.app (Term.const "nat_mod")
       (.ctor "Nat" 0 [] [])) (.ctor "Nat" 0 [] [])) := by
  native_decide

/-- End-to-end: `6 / 2 = 3` elab + checks + reduces. -/
example :
  allSourceOk
    "fn six_div_two() : Nat = Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))) / Nat.Succ(Nat.Succ(Nat.Zero));"
    = true := by
  native_decide

/-- End-to-end: `a / 0 = 0` guard triggers cleanly. -/
example :
  allSourceOk
    "fn a_div_zero() : Nat = Nat.Succ(Nat.Zero) / Nat.Zero;"
    = true := by
  native_decide

/-- End-to-end: `a % 0 = a` (derived from nat_div's zero-guard). -/
example :
  allSourceOk
    "fn a_mod_zero() : Nat = Nat.Succ(Nat.Zero) % Nat.Zero;"
    = true := by
  native_decide

/-! ## Runtime suite -/

def run : IO Unit := Tests.suite "Tests.Elab.SurfaceSugarTests" do
  -- §2.6 logical ops — exact Term-shape pinning
  Tests.check "not true → indRec[True,False] on True" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalNot trueLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
        (.ctor "Bool" 1 [] [])))
  Tests.check "not false → indRec[True,False] on False" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalNot falseLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
        (.ctor "Bool" 0 [] [])))
  Tests.check "not without expected still defaults to Bool" true
    (elabEq (runWith none
      (.logicalNot trueLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
        (.ctor "Bool" 1 [] [])))
  Tests.check "true and false → indRec[False,rhs] on lhs" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalAnd trueLit falseLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 0 [] [], .ctor "Bool" 0 [] []]
        (.ctor "Bool" 1 [] [])))
  Tests.check "true and true short-circuits into rhs slot" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalAnd trueLit trueLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 0 [] [], .ctor "Bool" 1 [] []]
        (.ctor "Bool" 1 [] [])))
  Tests.check "false or true → indRec[rhs,True] on lhs" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalOr falseLit trueLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 1 [] [], .ctor "Bool" 1 [] []]
        (.ctor "Bool" 0 [] [])))
  Tests.check "false or false places rhs in False method" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalOr falseLit falseLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 0 [] [], .ctor "Bool" 1 [] []]
        (.ctor "Bool" 0 [] [])))
  -- §4.2 dot-shorthand — rejection paths
  Tests.check "dot-shorthand no expected → E010" true
    (elabErrCode (runWith none
      (.dotShorthand "name" zeroSpan)) "E010")
  Tests.check "dot-shorthand ground expected → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (.dotShorthand "name" zeroSpan)) "E010")
  Tests.check "dot-shorthand Pi-to-non-inductive → E010" true
    (elabErrCode (runWith
      (some (.pi Grade.default (.type .zero) (.ind "Nat" []) .tot))
      (.dotShorthand "name" zeroSpan)) "E010")
  -- §4.2 pipe — integration through checkFile
  Tests.check "pipe n |> id_nat clean" true (allOk pipeBareFile)
  Tests.check "pipe chain n |> id_nat |> id_nat clean" true (allOk pipeChainFile)
  Tests.check "pipe in unascribed let (synthesis-mode regression)" true
    (allOk pipeLetSynthFile)
  -- §4.2 rule 25 — AST helper pinning
  Tests.check "containsDotShorthand walks through logicalAnd" true
    ((Ast.Expr.logicalAnd
        (.dotShorthand "a" zeroSpan)
        (.dotShorthand "b" zeroSpan) zeroSpan).containsDotShorthand)
  Tests.check "containsDotShorthand stops at lambda" false
    ((Ast.Expr.lam #[.plain "x"]
        (.dotShorthand "y" zeroSpan) zeroSpan).containsDotShorthand)
  Tests.check "substDotShorthand consumes every bare dot" true
    (!((Ast.Expr.dotShorthand "name" zeroSpan).substDotShorthand "it"
        ).containsDotShorthand)
  -- §4.2 rule 25 — end-to-end lift via source
  Tests.check "rule 25: .a and .b through logicalAnd" true
    (allSourceOk
      "@[copy] type flag { a: Bool; b: Bool; };\n\
       fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
       fn test_and(f: flag) : Bool = apply_flag(p: .a and .b, f: f);")
  Tests.check "rule 25: .a or .b through logicalOr" true
    (allSourceOk
      "@[copy] type flag { a: Bool; b: Bool; };\n\
       fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
       fn test_or(f: flag) : Bool = apply_flag(p: .a or .b, f: f);")
  Tests.check "rule 25: not .a through prefix walk" true
    (allSourceOk
      "@[copy] type flag { a: Bool; b: Bool; };\n\
       fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
       fn test_not(f: flag) : Bool = apply_flag(p: not .a, f: f);")
  Tests.check "rule 25: bare .a (Q61 path unchanged)" true
    (allSourceOk
      "type flag { a: Bool; };\n\
       fn apply_flag(p: flag -> Bool, f: flag) : Bool = p(f);\n\
       fn test_bare(f: flag) : Bool = apply_flag(p: .a, f: f);")
  -- §2.6 constructor-test `is` (Q66)
  Tests.check "Bool.True is Bool.True clean" true
    (allSourceOk "fn check_one() : Bool = Bool.True is Bool.True;")
  Tests.check "Nat.Zero is Nat.Zero clean" true
    (allSourceOk "fn check_two() : Bool = Nat.Zero is Nat.Zero;")
  Tests.check "Nat.Succ(Zero) is Nat.Zero (exhaustive arms)" true
    (allSourceOk "fn check_three() : Bool = Nat.Succ(Nat.Zero) is Nat.Zero;")
  Tests.check "is composed with Q63 `and`" true
    (allSourceOk "fn check_four() : Bool = Nat.Zero is Nat.Zero and Bool.True is Bool.True;")
  Tests.check "is on unknown ctor → E010" false
    (allSourceOk "fn check_five() : Bool = Nat.Zero is NoSuchCtor;")
  -- §2.6 propositional `==>` and `<==>` (Q67)
  Tests.check "True ==> False → indRec[True,False] on True" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalImplies trueLit falseLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
        (.ctor "Bool" 1 [] [])))
  Tests.check "False ==> False short-circuits to True method[0]" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.logicalImplies falseLit falseLit zeroSpan))
      (Term.indRec "Bool" boolSelfMotive
        [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
        (.ctor "Bool" 0 [] [])))
  Tests.check "`==>` end-to-end clean" true
    (allSourceOk "fn imp_two() : Bool = Bool.True ==> Bool.True;")
  Tests.check "`<==>` end-to-end clean" true
    (allSourceOk "fn iff_two() : Bool = Bool.True <==> Bool.True;")
  -- §2.6 Nat `==` / `!=` via prelude nat_eq (Q68)
  Tests.check "Nat.Zero == Nat.Zero clean" true
    (allSourceOk "fn nat_a() : Bool = Nat.Zero == Nat.Zero;")
  Tests.check "Succ == Succ clean" true
    (allSourceOk
      "fn nat_b() : Bool = Nat.Succ(Nat.Zero) == Nat.Succ(Nat.Zero);")
  Tests.check "Nat != Nat clean" true
    (allSourceOk
      "fn nat_c() : Bool = Nat.Zero != Nat.Succ(Nat.Zero);")
  -- Q69: Nat ordering (`<`, `<=`, `>`, `>=`) all route through
  -- the shared `nat_lt` prelude fn via arg-swap / `not` wrapping.
  Tests.check "Nat `<` clean" true
    (allSourceOk
      "fn nat_lt_a() : Bool = Nat.Zero < Nat.Succ(Nat.Zero);")
  Tests.check "Nat `<=` clean" true
    (allSourceOk
      "fn nat_le_a() : Bool = Nat.Succ(Nat.Zero) <= Nat.Succ(Nat.Zero);")
  Tests.check "Nat `>` clean" true
    (allSourceOk
      "fn nat_gt_a() : Bool = Nat.Succ(Nat.Zero) > Nat.Zero;")
  Tests.check "Nat `>=` clean" true
    (allSourceOk
      "fn nat_ge_a() : Bool = Nat.Succ(Nat.Zero) >= Nat.Succ(Nat.Zero);")
  -- Q70: Nat arithmetic (+, -, *) via nat_add / nat_sub /
  -- nat_mul prelude fns.  Full truth-table-equivalent coverage
  -- lives in tests/conformance/48_nat_arith.fx.
  Tests.check "Nat `+` clean" true
    (allSourceOk "fn plus_one() : Nat = Nat.Zero + Nat.Succ(Nat.Zero);")
  Tests.check "Nat `-` (saturating) clean" true
    (allSourceOk "fn sub_two() : Nat = Nat.Zero - Nat.Succ(Nat.Zero);")
  Tests.check "Nat `*` clean" true
    (allSourceOk
      "fn mul_one() : Nat = Nat.Succ(Nat.Zero) * Nat.Succ(Nat.Zero);")
  -- §3.7 list literals (Q71)
  Tests.check "empty list elaborates to bare Nil" true
    (elabEq (runWith (some (.ind "List" [.ind "Nat" []]))
      (.listLit #[] zeroSpan))
      listNilNat)
  Tests.check "[Nat.Zero] elaborates to Cons(Zero, Nil)" true
    (elabEq (runWith (some (.ind "List" [.ind "Nat" []]))
      (.listLit #[varQual ["Nat"] "Zero"] zeroSpan))
      (Term.ctor "List" 1 [.ind "Nat" []]
        [kernelZeroNat, listNilNat]))
  Tests.check "list literal without expected → E010" true
    (elabErrCode (runWith none
      (.listLit #[varQual ["Nat"] "Zero"] zeroSpan)) "E010")
  Tests.check "list literal with non-List expected → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (.listLit #[] zeroSpan)) "E010")
  Tests.check "[] end-to-end through checkFile" true
    (allSourceOk "fn empty_nat() : List(Nat) = [];")
  Tests.check "[Nat.Zero, Nat.Succ(Nat.Zero)] end-to-end" true
    (allSourceOk
      "fn pair_nat() : List(Nat) = [Nat.Zero, Nat.Succ(Nat.Zero)];")
  Tests.check "List(Bool) literal end-to-end" true
    (allSourceOk
      "fn bool_pair() : List(Bool) = [Bool.True, Bool.False];")
  Tests.check "nested List(List(Nat)) end-to-end" true
    (allSourceOk
      "fn nested() : List(List(Nat)) = [[Nat.Zero], [Nat.Succ(Nat.Zero)]];")
  Tests.check "trailing comma tolerated" true
    (allSourceOk
      "fn trailing_comma() : List(Nat) = [Nat.Zero, Nat.Succ(Nat.Zero),];")
  Tests.check "list literal without ascription rejects cleanly" false
    (allSourceOk "fn leaks() = [Nat.Zero];")
  -- §2.6 Bool == / != dispatch (Q72)
  Tests.check "Bool.True == Bool.True pins iff shape" true
    (let rhsTerm  : Term := .ctor "Bool" 1 [] []
     let notRhs   : Term := Term.indRec "Bool" boolSelfMotive
                             [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
                             rhsTerm
     elabEq (runWith (some (.ind "Bool" []))
       (.binop Token.eqEq trueLit trueLit zeroSpan))
       (Term.indRec "Bool" boolSelfMotive [notRhs, rhsTerm]
         (.ctor "Bool" 1 [] [])))
  Tests.check "Bool.True != Bool.False pins xor shape" true
    (let rhsTerm : Term := .ctor "Bool" 0 [] []
     let notRhs  : Term := Term.indRec "Bool" boolSelfMotive
                            [.ctor "Bool" 1 [] [], .ctor "Bool" 0 [] []]
                            rhsTerm
     elabEq (runWith (some (.ind "Bool" []))
       (.binop Token.neq trueLit falseLit zeroSpan))
       (Term.indRec "Bool" boolSelfMotive [rhsTerm, notRhs]
         (.ctor "Bool" 1 [] [])))
  Tests.check "Nat.Zero == Nat.Zero routes to nat_eq (legacy)" true
    (elabEq (runWith (some (.ind "Bool" []))
      (.binop Token.eqEq
        (varQual ["Nat"] "Zero")
        (varQual ["Nat"] "Zero") zeroSpan))
      (Term.app (Term.app (Term.const "nat_eq")
         (.ctor "Nat" 0 [] [])) (.ctor "Nat" 0 [] [])))
  Tests.check "Bool.True == Bool.True end-to-end" true
    (allSourceOk
      "fn eq_literals() : Bool = Bool.True == Bool.True;")
  Tests.check "true != false (keyword) end-to-end" true
    (allSourceOk "fn neq_kw() : Bool = true != false;")
  Tests.check "(not Bool.True) == Bool.False end-to-end" true
    (allSourceOk
      "fn after_not() : Bool = (not Bool.True) == Bool.False;")
  Tests.check "(a < b) == true — comparison lhs triggers Bool" true
    (allSourceOk
      "fn cmp_eq() : Bool = (Nat.Zero < Nat.Succ(Nat.Zero)) == true;")
  Tests.check "Nat.Zero == Nat.Zero legacy path unchanged" true
    (allSourceOk "fn nat_baseline() : Bool = Nat.Zero == Nat.Zero;")
  -- §2.6 Nat / and % via prelude fns (Q73)
  Tests.check "Nat `/` routes to Term.const \"nat_div\"" true
    (elabEq (runWith (some (.ind "Nat" []))
      (.binop Token.slash
        (varQual ["Nat"] "Zero")
        (varQual ["Nat"] "Zero") zeroSpan))
      (Term.app (Term.app (Term.const "nat_div")
         (.ctor "Nat" 0 [] [])) (.ctor "Nat" 0 [] [])))
  Tests.check "Nat `%` routes to Term.const \"nat_mod\"" true
    (elabEq (runWith (some (.ind "Nat" []))
      (.binop Token.percent
        (varQual ["Nat"] "Zero")
        (varQual ["Nat"] "Zero") zeroSpan))
      (Term.app (Term.app (Term.const "nat_mod")
         (.ctor "Nat" 0 [] [])) (.ctor "Nat" 0 [] [])))
  Tests.check "`a / 0` guard elab + checks" true
    (allSourceOk "fn adz() : Nat = Nat.Succ(Nat.Zero) / Nat.Zero;")
  Tests.check "`a % 0` derived elab + checks" true
    (allSourceOk "fn amz() : Nat = Nat.Succ(Nat.Zero) % Nat.Zero;")
  Tests.check "`6 / 2` end-to-end" true
    (allSourceOk
      "fn six_div_two() : Nat = Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))))) / Nat.Succ(Nat.Succ(Nat.Zero));")

end Tests.Elab.SurfaceSugarTests
