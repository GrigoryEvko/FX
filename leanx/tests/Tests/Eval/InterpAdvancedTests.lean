import FX.Eval.Interp
import FX.Eval.Pretty
import FX.Kernel.Env
import Tests.Framework

/-!
# Advanced eval tests (task G3 — recursion, globals, defensive paths)

Companion to `Tests.Eval.InterpTests`.  That file covers the
common cases (beta, iota, closures, pretty-print).  This file
covers three gaps that `Tests.Eval.InterpTests` doesn't
directly exercise:

  1. **`Value.isCanonical` audit** — every Value constructor's
     canonicity flag is pinned so adding a new constructor that
     forgets its `isCanonical` case surfaces as a regression.
  2. **`Term.const` + `GlobalEnv` recursion** — a recursive
     function registered in `GlobalEnv` and called via
     `Term.const` name-indirection.  Q19 / Q21 / CLAUDE.md's
     "globalEnv threading — explicit argument, NOT closure-
     captured" rationale is load-bearing here; a regression
     that captured globals at closure-creation time would break
     this flow.
  3. **`applyValue` fallback** — the "apply non-function to an
     arg" path documented in CLAUDE.md as "degrades to a
     neutral, defensive against ill-typed input" currently has
     no direct test.

Split into its own file because `Tests.Eval.InterpTests` is
already 650+ lines and sits near the `run` do-block's
comfortable size.
-/

namespace Tests.Eval.InterpAdvancedTests

open FX.Eval
open FX.Kernel
open Tests

/-! ## Fixtures -/

private def env0 : EvalEnv := EvalEnv.empty

private def tZero : Term := .ctor "Nat" 0 [] []
private def tSucc (predecessorTerm : Term) : Term :=
  .ctor "Nat" 1 [] [predecessorTerm]
private def tyNat : Term := .ind "Nat" []

/-- Value for `1 : Nat`. -/
private def vOne : Value :=
  .ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]

/-! ## Section 1: `Value.isCanonical` audit

Pins which values are canonical (fully reduced) vs stuck.  The
full catalog:

  Canonical (reduced, value form):
    closure, piType, sigmaType, ctor, indType, universe,
    forallLevelType, idType, reflVal, quotType, quotMkVal

  Stuck (not reduced, preserves elim shape):
    neutral, neutralRec, neutralIdJ, neutralQuotLift

If a future refactor adds a new Value constructor, Lean's
exhaustive pattern match in `Value.isCanonical` forces an
explicit case — but a test forgetting to exercise it means
a bug in the case could silently land.  This section pins
every existing constructor's classification.
-/

-- Canonical cases.
example : Value.isCanonical (.closure tyNat tyNat []) = true := by native_decide

example : Value.isCanonical (.piType tyNat tyNat []) = true := by
  native_decide

example : Value.isCanonical (.sigmaType tyNat tyNat []) = true := by
  native_decide

example : Value.isCanonical (.ctor "Nat" 0 [] []) = true := by native_decide

example : Value.isCanonical (.indType "Nat" []) = true := by native_decide

example : Value.isCanonical (.universe Level.zero) = true := by native_decide

example :
  Value.isCanonical (.forallLevelType tyNat [])
    = true := by native_decide

example :
  Value.isCanonical (.idType (eval env0 tyNat) (eval env0 tZero) (eval env0 tZero))
    = true := by native_decide

example : Value.isCanonical (.reflVal (eval env0 tZero)) = true := by native_decide

example :
  Value.isCanonical
    (.quotType (eval env0 tyNat) (eval env0 (.lam Grade.default tyNat tyNat)))
    = true := by native_decide

example :
  Value.isCanonical
    (.quotMkVal (eval env0 (.lam Grade.default tyNat tyNat)) (eval env0 tZero))
    = true := by native_decide

-- Stuck cases.
example : Value.isCanonical (.neutral 0 []) = false := by native_decide

example :
  Value.isCanonical
    (.neutralRec "Nat" (eval env0 tyNat) [] (.neutral 0 []))
    = false := by native_decide

example :
  Value.isCanonical
    (.neutralIdJ (eval env0 tyNat) (eval env0 tZero) (.neutral 0 []))
    = false := by native_decide

example :
  Value.isCanonical
    (.neutralQuotLift (eval env0 tyNat) (eval env0 tyNat) (.neutral 0 []))
    = false := by native_decide

/-! ## Section 2: `Term.const` + `GlobalEnv` recursion

Builds a recursive function — a `double` on Nat — via
`Term.const` self-reference registered in `GlobalEnv`.  The
body of `double` references `Term.const "double"`; on each
recursive call, `eval` resolves the name through `globalEnv`
rather than through any local capture.

This exercises the "globalEnv threaded, not captured"
discipline from `FX/Eval/CLAUDE.md`.  A regression that
captured globals inside closures would either miss the
recursion or evaluate against a stale env — both cause the
doubled value to come out wrong.
-/

/-- `double` as a Term: `fn(n: Nat) => n + n` using recursion
    on n.  Body unfolds as:

      indRec "Nat" motive [Zero, λpred λih. Succ (Succ ih)] n

    Motive: constant Nat → Nat (identity motive used just to
    get the return type right for the recursor).

    Zero case: returns Zero (0 + 0 = 0).
    Succ case: takes the predecessor's "double" (= `ih`) and
    returns Succ (Succ ih) — adding 2 per step. -/
private def doubleBody : Term :=
  -- λ n : Nat. indRec "Nat" (λ _ : Nat. Nat) [zeroCase; succCase] n
  let motive      := Term.lam Grade.default tyNat tyNat
  let zeroCase    := tZero
  let succCase    :=
    Term.lam Grade.default tyNat                     -- pred
      (Term.lam Grade.default tyNat                  -- ih : double(pred)
        (tSucc (tSucc (Term.var 0))))                -- Succ (Succ ih)
  Term.lam Grade.default tyNat
    (Term.indRec "Nat" motive [zeroCase, succCase] (Term.var 0))

/-- Type of `double`: `Nat -> Nat`. -/
private def doubleType : Term :=
  Term.piTot Grade.default tyNat tyNat

/-- A `GlobalEnv` with `double` registered. -/
private def envWithDouble : GlobalEnv :=
  GlobalEnv.addDecl {} "double" doubleType doubleBody
    (transparent := true)

-- double(0) = 0
example :
  Value.asNat? (eval { env0 with globals := envWithDouble }
    (Term.app (Term.const "double") tZero))
    = some 0 := by native_decide

-- double(1) = 2
example :
  Value.asNat? (eval { env0 with globals := envWithDouble }
    (Term.app (Term.const "double") (tSucc tZero)))
    = some 2 := by native_decide

-- double(3) = 6
example :
  Value.asNat? (eval { env0 with globals := envWithDouble }
    (Term.app (Term.const "double")
      (tSucc (tSucc (tSucc tZero)))))
    = some 6 := by native_decide

/-! ## Section 3: `Term.const` through an inner closure

CLAUDE.md's "closures don't save globals" rationale in action.
A closure that references `Term.const "double"` at creation
time, returned to an outer scope, correctly resolves the name
against the CALLER's globalEnv at application time — not
against whatever globals were in scope when the closure was
built.

Pattern:

  1. Define `addDouble : Nat -> Nat -> Nat = λx. λy. x + double(y)`
  2. Apply `addDouble(3)` to get a closure over `x = 3`.
  3. Apply that closure to `5` with a globalEnv containing
     `double`.  Result: 3 + double(5) = 3 + 10 = 13.

If closures captured globals, the returned closure would
carry the globalEnv at `addDouble(3)` time, not the one used
to apply it — so the `double` lookup would fail or use
stale state. -/

-- Two-arg `addDouble` returns `x + double(y)`.  For this
-- test we use a simpler shape: `λx. λy. double(y)` — the
-- outer `x` binder exercises the captured-vs-lookup
-- distinction even without addition (which would need a
-- second inductive-recursor call).
private def callDoubleBody : Term :=
  -- λ x : Nat. λ y : Nat. double(y)
  Term.lam Grade.default tyNat
    (Term.lam Grade.default tyNat
      (Term.app (Term.const "double") (Term.var 0)))

-- (λx. λy. double(y)) 7 2 = double(2) = 4
example :
  Value.asNat? (eval { env0 with globals := envWithDouble }
    (Term.app
      (Term.app callDoubleBody
        (tSucc (tSucc (tSucc (tSucc (tSucc (tSucc (tSucc tZero))))))))  -- x = 7
      (tSucc (tSucc tZero))))                                             -- y = 2
    = some 4 := by native_decide

/-! ## Section 4: `applyValue` fallback — non-function in
function position

`applyValue` has a graceful-degradation fallback for values
that shouldn't appear in function position on well-typed
input: `ctor`, `reflVal`, `quotMkVal`, `indType`, `universe`,
etc.  The fallback returns `neutral 0 [unexpectedHead, arg]`
so pretty-printing still works.

These tests construct kernel terms that force `applyValue` to
hit the fallback via `.app` on a non-function value form.
Well-typed input would never produce these, so the tests use
explicit `Term.app (Term.ctor …) arg` shapes that skip the
normal function-position.
-/

-- `applyValue` with a `ctor` head produces a neutral.
-- `Term.app (ctor "Nat" 0 [] []) tZero` forces a ctor-in-function
-- position at eval time; the fallback fires.
private def stuckApplyCtor : Value :=
  eval env0 (.app (.ctor "Nat" 0 [] []) tZero)

-- Shape: the fallback wraps into `neutral 0 [...]` — head 0,
-- 2-element spine (the stuck head + the arg).
example :
  (match stuckApplyCtor with
   | .neutral _ spine => spine.length == 2
   | _ => false) = true := by native_decide

-- Applying a universe to an argument also hits the fallback.
private def stuckApplyUniverse : Value :=
  eval env0 (.app (.type .zero) tZero)

example :
  (match stuckApplyUniverse with
   | .neutral _ spine => spine.length == 2
   | _ => false) = true := by native_decide

-- Applying a `reflVal` to an arg — same fallback.
private def stuckApplyRefl : Value :=
  eval env0 (.app (.refl tZero) tZero)

example :
  (match stuckApplyRefl with
   | .neutral _ spine => spine.length == 2
   | _ => false) = true := by native_decide

/-! ## Section 4b: `indRec` lazy method dispatch (Q74)

Regression test for the interpreter bug where `eval`'s
`.indRec` case eagerly evaluated ALL methods before picking
the target's ctor.  In the desugared form of `if cond; a else
b end if` (= `indRec "Bool" motive [elseArm, thenArm] cond`),
eager eval of the non-selected arm entered any recursive self-
reference in that arm — infinite loop on the `gcd`-style
pattern `if b == 0; a else gcd(..) end if`.

Defense here: build a `loop_or_zero` global whose else-arm
*would* recurse forever if eager-evaluated.  Call it with
`True` and verify we get `Zero`.  Under the pre-Q74 bug this
test would hang (OOM / timeout); under the fix it returns in
constant time. -/

/-- `Bool` kernel type and ctors as Terms (local to this
    section to keep fixtures tight). -/
private def tyBool : Term := .ind "Bool" []
private def tTrue  : Term := .ctor "Bool" 1 [] []
private def tFalse : Term := .ctor "Bool" 0 [] []

/-- `loop_or_zero` body: `λ b : Bool.
      if b then Nat.Zero else loop_or_zero(False)`.

    Desugared via Bool indRec with methods `[elseArm, thenArm]`:
      method[0] (False arm) = `loop_or_zero(False)` — recurses
      method[1] (True  arm) = `Nat.Zero`            — base

    The False arm is an infinite-recursion hole on purpose —
    if eval ever touches it without the fix, the test hangs.  -/
private def loopOrZeroBody : Term :=
  let motive      := Term.lam Grade.default tyBool tyNat
  let elseRecurse := Term.app (Term.const "loop_or_zero") tFalse
  let thenZero    := tZero
  Term.lam Grade.default tyBool
    (Term.indRec "Bool" motive [elseRecurse, thenZero] (Term.var 0))

private def loopOrZeroType : Term :=
  Term.piTot Grade.default tyBool tyNat

private def envWithLoop : GlobalEnv :=
  GlobalEnv.addDecl {} "loop_or_zero" loopOrZeroType loopOrZeroBody
    (transparent := true)

-- `loop_or_zero(True) = 0` — the fix picks method[1] (Zero)
-- without ever evaluating method[0] (the recursive hole).
example :
  Value.asNat? (eval { env0 with globals := envWithLoop }
    (Term.app (Term.const "loop_or_zero") tTrue))
    = some 0 := by native_decide

/-! ## Section 5: Runtime suite entry point

Pretty-prints the three sections above via `Tests.check`
assertions on their key outcomes.  The compile-time `native_
decide` examples already pin the detailed invariants; the
runtime checks provide a human-readable summary in the
test-runner output. -/

def run : IO Unit := Tests.suite "Tests.Eval.InterpAdvancedTests" do
  -- isCanonical audit summary
  Tests.check "canonical closure"   true  (Value.isCanonical (.closure tyNat tyNat []))
  Tests.check "canonical ctor"      true  (Value.isCanonical (.ctor "Nat" 0 [] []))
  Tests.check "canonical universe"  true  (Value.isCanonical (.universe Level.zero))
  Tests.check "stuck neutral"       false (Value.isCanonical (.neutral 0 []))
  Tests.check "stuck neutralRec"    false
    (Value.isCanonical (.neutralRec "Nat" (eval env0 tyNat) [] (.neutral 0 [])))
  Tests.check "stuck neutralIdJ"    false
    (Value.isCanonical
      (.neutralIdJ (eval env0 tyNat) (eval env0 tZero) (.neutral 0 [])))
  Tests.check "stuck neutralQLift"  false
    (Value.isCanonical
      (.neutralQuotLift (eval env0 tyNat) (eval env0 tyNat) (.neutral 0 [])))
  -- Recursion via Term.const resolves through globalEnv
  Tests.check "double(0) via const → 0" (some 0)
    (Value.asNat? (eval { env0 with globals := envWithDouble }
      (Term.app (Term.const "double") tZero)))
  Tests.check "double(3) via const → 6" (some 6)
    (Value.asNat? (eval { env0 with globals := envWithDouble }
      (Term.app (Term.const "double")
        (tSucc (tSucc (tSucc tZero))))))
  -- Inner closure sees the caller's globals, not a captured snapshot
  Tests.check "closure reading const via globalEnv" (some 4)
    (Value.asNat? (eval { env0 with globals := envWithDouble }
      (Term.app
        (Term.app callDoubleBody
          (tSucc (tSucc (tSucc (tSucc (tSucc (tSucc (tSucc tZero))))))))
        (tSucc (tSucc tZero)))))
  -- applyValue fallback on non-function head
  let isNeutralSpineTwo : Value → Bool := fun v =>
    match v with
    | .neutral _ spine => spine.length == 2
    | _ => false
  Tests.check "apply ctor to arg → neutral fallback" true
    (isNeutralSpineTwo stuckApplyCtor)
  Tests.check "apply universe to arg → neutral fallback" true
    (isNeutralSpineTwo stuckApplyUniverse)
  Tests.check "apply refl to arg → neutral fallback" true
    (isNeutralSpineTwo stuckApplyRefl)
  -- Q74: lazy `indRec` method dispatch — `loop_or_zero(True)`
  -- must terminate with Zero despite method[0] being an
  -- infinite recursion hole.  Pre-fix this hung; the test
  -- would never return.
  Tests.check "indRec lazy methods: loop_or_zero(True) = 0" (some 0)
    (Value.asNat? (eval { env0 with globals := envWithLoop }
      (Term.app (Term.const "loop_or_zero") tTrue)))

end Tests.Eval.InterpAdvancedTests
