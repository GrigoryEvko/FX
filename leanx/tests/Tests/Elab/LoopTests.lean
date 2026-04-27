import FX.Elab.Elaborate
import FX.Kernel.Inductive
import Tests.ElabSupport
import Tests.Framework

/-!
# Loop elaboration tests (B10)

Exercises the Phase-2.2 for-loop desugaring and the
intentional rejection of while-loops:

  * `for LOOPVAR in 0..HI; BODY end for` →
    `indRec "Nat" motive_unit [Unit.tt, λ i. λ _rec. BODY] HI`
  * Non-zero `lo` → E013 (v1 restriction)
  * `while cond; body end while` → E013 (pending Div effect)

Paired with the end-to-end conformance coverage at
`tests/conformance/32_for_loop.fx`.
-/

namespace Tests.Elab.LoopTests

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

/-! ## Positive case — exact desugar shape

`for i in 0..3; Unit.tt end for` with expected `Unit` should
produce:

  indRec "Nat"
    (λ _ : Nat. Unit)                   -- motive
    [ Unit.tt,                           -- zero method
      λ i : Nat. λ _rec : Unit. Unit.tt  -- Succ method
    ]
    (Nat.Succ (Nat.Succ (Nat.Succ Nat.Zero)))
-/

/-- Constructor reference for `Unit.tt` as an AST Expr.  The
    parser produces this shape when the user writes `Unit.tt`
    as a qualified ctor reference. -/
private def astUnitTt : Expr :=
  .var (qualPath ["Unit"] "tt")

/-- AST literal for an integer.  Uses the intLit token form
    matching what the lexer emits. -/
private def astIntLit (literalValue : Nat) : Expr :=
  .literal (.intLit (toString literalValue) .dec) zeroSpan

/-- Canonical `for i in 0..count; body end for` AST. -/
private def astForLoop (count : Nat) (body : Expr) : Expr :=
  .forRange "i" (astIntLit 0) (astIntLit count) body zeroSpan

/-- Nat.Succ^n Nat.Zero as a kernel Term — mirror of
    `Elaborate.buildNatLit`. -/
private def buildNatLit : Nat → Term
  | 0     => .ctor "Nat" 0 [] []
  | n + 1 => .ctor "Nat" 1 [] [buildNatLit n]

/-- Expected shape of `for i in 0..count; Unit.tt end for` at the
    kernel layer. -/
private def expectedForLoopTerm (count : Nat) : Term :=
  let natInd  : Term := .ind "Nat" []
  let unitInd : Term := .ind "Unit" []
  let unitTt  : Term := .ctor "Unit" 0 [] []
  let succMethod : Term :=
    .lam Grade.default natInd
      (.lam Grade.default unitInd unitTt)
  let motive : Term :=
    .lam Grade.default natInd (Term.shift 0 1 unitInd)
  Term.indRec "Nat" motive [unitTt, succMethod] (buildNatLit count)

/-- `for i in 0..3; Unit.tt end for` with expected Unit produces
    exactly `indRec "Nat" motive [Unit.tt, λ i. λ _. Unit.tt]
    (Nat.Succ^3 Nat.Zero)`. -/
example :
  elabEq (runWith (some (.ind "Unit" []))
    (astForLoop 3 astUnitTt)) (expectedForLoopTerm 3) := by
  native_decide

/-- `for i in 0..0; Unit.tt end for` — empty iteration collapses
    to `indRec` with target `Nat.Zero`, yielding the zero
    method's value at runtime. -/
example :
  elabEq (runWith (some (.ind "Unit" []))
    (astForLoop 0 astUnitTt)) (expectedForLoopTerm 0) := by
  native_decide

/-! ## Rejection cases -/

/-- Non-zero `lo` triggers E013 — v1 only supports `lo = 0`. -/
example :
  elabErrCode (runWith (some (.ind "Unit" []))
    (.forRange "i" (astIntLit 2) (astIntLit 7)
      astUnitTt zeroSpan)) "E013" := by
  native_decide

/-- Any non-literal `lo` also triggers E013 (the elab check is
    a pattern-match on `.literal (.intLit "0")`). -/
example :
  elabErrCode (runWith (some (.ind "Unit" []))
    (.forRange "i" astUnitTt (astIntLit 5)
      astUnitTt zeroSpan)) "E013" := by
  native_decide

/-- While-loop elab rejects with E013 until the `Div` effect
    wiring lands (tasks E-3 / E-6). -/
example :
  elabErrCode (runWith (some (.ind "Unit" []))
    (.whileLoop (.literal (.kw .trueKw) zeroSpan)
      astUnitTt zeroSpan)) "E013" := by
  native_decide

end Tests.Elab.LoopTests
