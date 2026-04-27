-- FX.Smt.EncodeTests — runtime tests for the SMT-LIB2 encoder.
--
-- Covers `FX/Smt/Encode.lean`:
--
--   * Boolean / numeric literal encoding
--   * Built-in operator demangling (logical, comparison,
--     arithmetic, equality)
--   * Free symbol collection (Term.const + unbound Term.var
--     reach the FreeSym list)
--   * Forall encoding via `Term.pi` whose body is Bool-typed
--   * Full `encodeQuery` script assembly with declares + asserts
--   * Error cases: lambda outside quantifier, open de Bruijn,
--     non-Bool goal, non-Bool assumption, non-canonical Nat
--
-- Comparison strategy: all expected values are STRINGS.  Encode
-- results that succeed lower to the body string; results that
-- fail lower to a `ERROR: …` rendering of the structured
-- `EncodeError`.  This sidesteps the need for `DecidableEq` on
-- `EncodeError` (it derives `Repr` but not `BEq`) and gives
-- failure messages a stable shape for diffing.

import FX.Smt.Encode
import FX.Smt.Sort
import FX.Kernel.Term
import FX.Kernel.Grade
import Tests.Framework

namespace Tests.Smt.EncodeTests

open Tests FX.Smt FX.Kernel

/-! ## Term-construction helpers

    These build kernel `Term` values that surface code would
    otherwise produce after elaboration.  Kept tiny and local —
    the encoder doesn't need a full surface plumbing to test. -/

/-- The kernel `bool` type expression. -/
def boolType : Term := .ind "Bool" []

/-- The kernel `Nat` type expression. -/
def natType : Term := .ind "Nat" []

/-- Bool ctor 1 = true (matches `IndSpec` for "Bool" in
    `FX/Kernel/Inductive.lean`). -/
def trueLit : Term := .ctor "Bool" 1 [] []

/-- Bool ctor 0 = false. -/
def falseLit : Term := .ctor "Bool" 0 [] []

/-- Nat ctor 0 = zero (no value args). -/
def natZero : Term := .ctor "Nat" 0 [] []

/-- Nat ctor 1 = succ.  Wraps the predecessor as the single
    value arg per the canonical `Nat` `IndSpec`. -/
def natSucc (predecessor : Term) : Term :=
  .ctor "Nat" 1 [] [predecessor]

/-- Build a unary-Nat literal from a host `Nat`. -/
def natLit : Nat -> Term
  | 0     => natZero
  | n + 1 => natSucc (natLit n)

/-- Build `(op lhs rhs)`-style binary application as
    `app (app (const op) lhs) rhs`.  This is the surface shape
    the encoder pattern-matches in `encodeApp`. -/
def applyBinary (operatorName : String) (leftArg rightArg : Term) : Term :=
  .app (.app (.const operatorName) leftArg) rightArg

/-- Build `(op arg)`-style unary application. -/
def applyUnary (operatorName : String) (arg : Term) : Term :=
  .app (.const operatorName) arg

/-! ## Test-side rendering

    Convert encoder output to a stable string for comparison.
    Success goes to `OK <body>`; failure goes to
    `ERROR <error-toString>`.  Both shapes diff cleanly when
    a test fails — the failure message includes the rendered
    EncodeError. -/

/-- Render the body of a successful encode, or the structured
    error.  Returns just the body string on success. -/
def encodeBodyShow (term : Term) : String :=
  match encodeTerm term with
  | .ok encoded   => encoded.body
  | .error reason => s!"ERROR {reason}"

/-- Render the full encoded record, including the inferred
    sort and the free-symbol list.  Used when a test wants to
    assert all three fields at once. -/
def encodeFullShow (term : Term) : String :=
  match encodeTerm term with
  | .ok encoded   =>
      let symPart :=
        if encoded.freeSyms.isEmpty
        then ""
        else " | symbols=" ++ String.intercalate ", "
               (encoded.freeSyms.map fun sym =>
                 s!"{sym.name}:{sym.sort.toSmtLib}")
      s!"{encoded.body} : {encoded.sort.toSmtLib}{symPart}"
  | .error reason => s!"ERROR {reason}"

/-- Render the full SMT-LIB2 query string or error. -/
def queryShow (assumptions : List Term) (goal : Term) : String :=
  match encodeQuery assumptions goal with
  | .ok script    => script
  | .error reason => s!"ERROR {reason}"

/-! ## Test bodies -/

def run : IO Unit := Tests.suite "Tests.Smt.EncodeTests" do

  -----------------------------------------------------------
  -- Boolean and Nat literals
  -----------------------------------------------------------

  check "true literal"  "true"  (encodeBodyShow trueLit)
  check "false literal" "false" (encodeBodyShow falseLit)

  check "Nat 0"  "0"  (encodeBodyShow natZero)
  check "Nat 1"  "1"  (encodeBodyShow (natLit 1))
  check "Nat 5"  "5"  (encodeBodyShow (natLit 5))
  check "Nat 12" "12" (encodeBodyShow (natLit 12))

  -----------------------------------------------------------
  -- Boolean connectives
  -----------------------------------------------------------

  check "not true"
    "(not true)"
    (encodeBodyShow (applyUnary "not" trueLit))

  check "true and false"
    "(and true false)"
    (encodeBodyShow (applyBinary "and" trueLit falseLit))

  check "true or false"
    "(or true false)"
    (encodeBodyShow (applyBinary "or" trueLit falseLit))

  check "implies (==>)"
    "(=> true false)"
    (encodeBodyShow (applyBinary "==>" trueLit falseLit))

  check "iff (<=>)"
    "(= true false)"
    (encodeBodyShow (applyBinary "<=>" trueLit falseLit))

  -----------------------------------------------------------
  -- Equality / disequality / comparison
  -----------------------------------------------------------

  check "equality 1 == 2"
    "(= 1 2)"
    (encodeBodyShow (applyBinary "==" (natLit 1) (natLit 2)))

  check "disequality 1 != 2"
    "(distinct 1 2)"
    (encodeBodyShow (applyBinary "!=" (natLit 1) (natLit 2)))

  check "less-than 0 < 5"
    "(< 0 5)"
    (encodeBodyShow (applyBinary "<" (natLit 0) (natLit 5)))

  check "less-equal 1 <= 1"
    "(<= 1 1)"
    (encodeBodyShow (applyBinary "<=" (natLit 1) (natLit 1)))

  check "greater-than 7 > 3"
    "(> 7 3)"
    (encodeBodyShow (applyBinary ">" (natLit 7) (natLit 3)))

  check "greater-equal 4 >= 4"
    "(>= 4 4)"
    (encodeBodyShow (applyBinary ">=" (natLit 4) (natLit 4)))

  -----------------------------------------------------------
  -- Arithmetic
  -----------------------------------------------------------

  check "addition 2 + 3"
    "(+ 2 3)"
    (encodeBodyShow (applyBinary "+" (natLit 2) (natLit 3)))

  check "subtraction 5 - 2"
    "(- 5 2)"
    (encodeBodyShow (applyBinary "-" (natLit 5) (natLit 2)))

  check "multiplication 3 * 4"
    "(* 3 4)"
    (encodeBodyShow (applyBinary "*" (natLit 3) (natLit 4)))

  check "division 10 / 2"
    "(div 10 2)"
    (encodeBodyShow (applyBinary "/" (natLit 10) (natLit 2)))

  check "modulo 10 % 3"
    "(mod 10 3)"
    (encodeBodyShow (applyBinary "%" (natLit 10) (natLit 3)))

  -----------------------------------------------------------
  -- Free symbols (Term.const)
  -----------------------------------------------------------

  -- A const at non-application head becomes a free Int symbol.
  check "free const x"
    "x : Int | symbols=x:Int"
    (encodeFullShow (.const "x"))

  -- Two free consts; both registered as free symbols.
  check "free consts in addition"
    "(+ x y) : Int | symbols=x:Int, y:Int"
    (encodeFullShow (applyBinary "+" (.const "x") (.const "y")))

  -- An uninterpreted operator becomes a free Int symbol of
  -- function-shape (encoder defaults sort to Int; smarter sort
  -- inference is V8.4 typing-layer integration).
  check "uninterpreted operator"
    "(my_op x y)"
    (encodeBodyShow (applyBinary "my_op" (.const "x") (.const "y")))

  -----------------------------------------------------------
  -- Quantifier via Pi
  -----------------------------------------------------------

  -- forall(x: Nat), x == x  →  (forall ((x0 Int)) (= x0 x0))
  let forallEqRefl : Term :=
    .pi Grade.ghost natType
        (applyBinary "==" (.var 0) (.var 0))
        Effect.tot

  check "forall x: Nat, x == x"
    "(forall ((x0 Int)) (= x0 x0))"
    (encodeBodyShow forallEqRefl)

  -- forall(x: Nat), x >= 0
  let forallNonNeg : Term :=
    .pi Grade.ghost natType
        (applyBinary ">=" (.var 0) natZero)
        Effect.tot

  check "forall x: Nat, x >= 0"
    "(forall ((x0 Int)) (>= x0 0))"
    (encodeBodyShow forallNonNeg)

  -- Nested: forall(x: Nat), forall(y: Nat), x + y >= x
  let nestedForall : Term :=
    .pi Grade.ghost natType
      (.pi Grade.ghost natType
        (applyBinary ">=" (applyBinary "+" (.var 1) (.var 0)) (.var 1))
        Effect.tot)
      Effect.tot

  check "nested forall"
    "(forall ((x0 Int)) (forall ((x1 Int)) (>= (+ x0 x1) x0)))"
    (encodeBodyShow nestedForall)

  -----------------------------------------------------------
  -- Identity-type encoding (id A a b → equality)
  -----------------------------------------------------------

  -- id Nat 1 2  →  (= 1 2)
  let idEq : Term := .id natType (natLit 1) (natLit 2)
  check "id type as equality"
    "(= 1 2)"
    (encodeBodyShow idEq)

  -----------------------------------------------------------
  -- Full query assembly
  -----------------------------------------------------------

  -- Goal: forall(x: Nat), x >= 0
  -- No assumptions.  The encoder negates the goal so unsat
  -- proves validity.
  let basicQuery := queryShow [] forallNonNeg
  check "encodeQuery with no assumptions"
    "(set-logic AUFLIA)\n\
     (assert (not (forall ((x0 Int)) (>= x0 0))))\n\
     (check-sat)"
    basicQuery

  -- Goal with one assumption: assume `x > 0`, prove `x >= 0`.
  -- The free symbol `x` becomes a `(declare-const x Int)` in
  -- the preamble.
  let assumeXPos := applyBinary ">" (.const "x") natZero
  let goalXNonNeg := applyBinary ">=" (.const "x") natZero
  let queryWithAssumption := queryShow [assumeXPos] goalXNonNeg

  check "encodeQuery with one assumption"
    "(set-logic AUFLIA)\n\
     (declare-const x Int)\n\
     (assert (> x 0))\n\
     (assert (not (>= x 0)))\n\
     (check-sat)"
    queryWithAssumption

  -- Multiple assumptions sharing the same free symbol —
  -- declare-const should appear ONCE despite both assertions
  -- + the goal referencing `x`.
  let assumeXPos2 := applyBinary ">" (.const "x") natZero
  let assumeXLt100 := applyBinary "<" (.const "x") (natLit 100)
  let goalXNonNeg2 := applyBinary ">=" (.const "x") natZero
  let multiAssumeQuery := queryShow [assumeXPos2, assumeXLt100] goalXNonNeg2

  check "encodeQuery dedupes free symbols"
    "(set-logic AUFLIA)\n\
     (declare-const x Int)\n\
     (assert (> x 0))\n\
     (assert (< x 100))\n\
     (assert (not (>= x 0)))\n\
     (check-sat)"
    multiAssumeQuery

  -----------------------------------------------------------
  -- Error cases
  -----------------------------------------------------------

  -- Lambda outside quantifier position is unsupported.
  let bareLambda : Term := .lam Grade.ghost natType (.var 0)
  check "lam outside quantifier rejected"
    "ERROR E_smt_unsupported: lam (lambda outside quantifier position cannot encode in SMT-LIB)"
    (encodeBodyShow bareLambda)

  -- Open term (var 0 with no surrounding binder).
  let openVar : Term := .var 0
  check "open de Bruijn rejected"
    "ERROR E_smt_open_term: free de Bruijn index 0"
    (encodeBodyShow openVar)

  -- Open inside an arithmetic application — error propagates.
  let openInApp : Term := applyBinary "+" (.var 5) (natLit 3)
  check "open inside app rejected"
    "ERROR E_smt_open_term: free de Bruijn index 5"
    (encodeBodyShow openInApp)

  -- Inductive recursion (indRec) is unsupported in E1; full
  -- support is V8.4 typing-layer integration.
  let indRecTerm : Term :=
    .indRec "Nat" (.const "motive") [(.const "z"), (.const "s")] natZero
  match encodeTerm indRecTerm with
  | .error (.unsupported "indRec" _) =>
      check "indRec rejected (positive)" true true
  | other =>
      check "indRec must reject" "indRec error" s!"got {repr other}"

  -- Codata destruction is unsupported.
  let coindDest : Term := .coindDestruct "stream" 0 (.const "s")
  match encodeTerm coindDest with
  | .error (.unsupported "coinductive" _) =>
      check "coindDestruct rejected" true true
  | other =>
      check "coindDestruct must reject" "coind error" s!"got {repr other}"

  -- Goal whose sort is not Bool — encodeQuery refuses.
  let nonBoolGoal := natLit 5
  match encodeQuery [] nonBoolGoal with
  | .error (.sortMismatch "goal" gotSort .boolSort) =>
      check "non-Bool goal rejected" "Int" gotSort.toSmtLib
  | other =>
      check "non-Bool goal must reject" "sort error" s!"got {repr other}"

  -- Assumption whose sort is not Bool — encodeQuery refuses.
  let nonBoolAssumption := natLit 7
  match encodeQuery [nonBoolAssumption] forallNonNeg with
  | .error (.sortMismatch "assumption" gotSort .boolSort) =>
      check "non-Bool assumption rejected" "Int" gotSort.toSmtLib
  | other =>
      check "non-Bool assumption must reject" "sort error" s!"got {repr other}"

end Tests.Smt.EncodeTests
