import FX.Eval.Interp
import FX.Eval.Pretty
import FX.Kernel.Inductive
import Tests.Framework

/-!
# Evaluator tests (Stream G3)

Covers `FX/Eval/Interp.lean`, `FX/Eval/Value.lean`, and
`FX/Eval/Pretty.lean` per `fx_design.md` §22 (sketch-mode VM
intent) and §31 (kernel reductions — beta, iota).

Scope:

  * **beta-reduction** — `(fn(x) => x) v` reduces to `v`; identity,
    constant-return, Church-style second-projection.
  * **Closure capture** — a lambda returned from under a let-like
    frame correctly captures outer bindings; nested closures
    retain their own environments independently.
  * **iota-reduction on Nat** — `indRec "Nat" motive [mZ, mS] n`
    reduces to `mZ` when `n = Zero`, and to `mS` applied to
    `pred` + recursive result when `n = Succ pred`.  Deep
    recursion (Succ^3 Zero) exercises the self-reference
    threading in `buildIotaSpine`.
  * **iota-reduction on Bool** — both arms fire; `neutralRec` is
    produced when the scrutinee is stuck.
  * **Pretty-printer** — `asNat?` collapses `Succ^k Zero` to
    the integer `k`; `asBool?` renders `True`/`False` as
    `"true"`/`"false"`; neutrals and stuck eliminators render
    with their shape intact.

Test strategy: every assertion is a `Tests.check` on a pure
expression — no IO side-effects.  The runtime `asNat?` /
`asBool?` / `pretty` helpers return `Option Nat` / `Option Bool`
/ `String` which all have `DecidableEq` + `Repr`, so `check`
gives structured failure output.

Note on Value comparison: `Value` does not derive `DecidableEq`
(closures carry `Term` which itself has no `DecidableEq` — the
`Grade` field in `lam`/`pi`/`sigma` blocks the auto-deriver).
Tests therefore project to inspectable simple types before
comparing.  For closure/neutral shape tests, we define a small
`Shape` tag in this file.
-/

namespace Tests.Eval.InterpTests

open FX.Eval
open FX.Kernel
open Tests

/-! ## Fixtures -/

/-- Empty runtime environment — no locals, no globals. -/
def env0 : EvalEnv := EvalEnv.empty

/-- A Nat term helper: `Zero`. -/
def tZero : Term := .ctor "Nat" 0 [] []

/-- A Nat term helper: `Succ n`. -/
def tSucc (predecessor : Term) : Term :=
  .ctor "Nat" 1 [] [predecessor]

/-- A Bool term helper: `False` (ctor idx 0). -/
def tFalse : Term := .ctor "Bool" 0 [] []

/-- A Bool term helper: `True` (ctor idx 1). -/
def tTrue : Term := .ctor "Bool" 1 [] []

/-- Nat type literal. -/
def tyNat : Term := .ind "Nat" []

/-- Bool type literal. -/
def tyBool : Term := .ind "Bool" []

/-- Identity motive over Nat: `lambda_. Nat`. -/
def motiveNat : Term :=
  .lam Grade.default tyNat tyNat

/-- Identity motive over Bool: `lambda_. Bool`. -/
def motiveBool : Term :=
  .lam Grade.default tyBool tyBool

/-! ## Value shape introspection

Because `Value` has no `DecidableEq`, tests project Values to
the smaller `Shape` enum before asserting.  Only the cases the
current tests exercise are enumerated — extend as needed. -/

/-- A rough shape tag on Values for test assertions. -/
inductive Shape where
  | ctor     (typeName : String) (ctorIdx : Nat) (argCount : Nat)
  | closure
  | neutral  (head : Nat) (spineLen : Nat)
  | nrec     (typeName : String)
  | other
  deriving DecidableEq, Repr

def shapeOf : Value → Shape
  | .ctor n i _ args  => .ctor n i args.length
  | .closure _ _ _    => .closure
  | .neutral h sp     => .neutral h sp.length
  | .neutralRec n _ _ _ => .nrec n
  | _                 => .other

/-! ## beta-reduction

Plain beta on a closed lambda.  The evaluator should pick up
`Value.closure` as the head of `app` and enter its captured
env with the argument pushed at de Bruijn 0. -/

/-- `(lambda x : Nat. x) Zero` — identity applied to Zero reduces to Zero. -/
def id_applied_zero : Value :=
  eval env0 (.app (.lam Grade.default tyNat (.var 0)) tZero)

example : Value.asNat? id_applied_zero = some 0 := by native_decide

/-- `(lambda x : Nat. Succ x) (Succ Zero)` — successor applied to 1 → 2. -/
def succ_of_one : Value :=
  eval env0 (.app (.lam Grade.default tyNat (tSucc (.var 0))) (tSucc tZero))

example : Value.asNat? succ_of_one = some 2 := by native_decide

/-- Shadowed de Bruijn: `(lambda x : Nat. (lambda y : Nat. x) Zero) (Succ Zero)`.
    Inner `x` is outer binder (index 1 under the inner lam).  The
    inner application discards its own bind (via the outer's index)
    and yields `x = Succ Zero`.  Exercises the `captured ::` push
    under a nested closure. -/
def shadowing_outer : Value :=
  eval env0
    (.app
      (.lam Grade.default tyNat
        (.app
          (.lam Grade.default tyNat (.var 1))
          tZero))
      (tSucc tZero))

example : Value.asNat? shadowing_outer = some 1 := by native_decide

/-- `(lambda x : Nat. lambda y : Nat. y) a b` — second-projection; discards
    the outer arg.  Tests that the inner closure's captured env
    contains the outer arg but the body references index 0 (the
    inner arg). -/
def snd_of_two : Value :=
  eval env0
    (.app
      (.app
        (.lam Grade.default tyNat
          (.lam Grade.default tyNat (.var 0)))
        (tSucc (tSucc tZero)))        -- outer arg = 2
      (tSucc tZero))                    -- inner arg = 1, this should win

example : Value.asNat? snd_of_two = some 1 := by native_decide

/-! ## Closure capture

A lambda that returns a lambda referencing an outer binding — the inner
closure must carry its captured env when the outer application
completes. -/

/-- `(lambda outer : Nat. lambda _dummy : Nat. outer) (Succ Zero) Zero`.
    The inner body references outer via index 1.  The outer beta
    step produces a Value.closure with `captured = [Succ Zero]`.
    Applying that closure to `Zero` then resolves `var 1` to the
    captured outer-value. -/
def returned_closure_reads_capture : Value :=
  eval env0
    (.app
      (.app
        (.lam Grade.default tyNat                -- outer
          (.lam Grade.default tyNat              -- _dummy
            (.var 1)))                           -- reads outer
        (tSucc tZero))                           -- outer = 1
      tZero)                                     -- _dummy = 0

example : Value.asNat? returned_closure_reads_capture = some 1 := by
  native_decide

/-- A curried closure only partly applied: `(lambda outer. lambda _. outer)
    (Succ (Succ Zero))` evaluates to a `Value.closure` — no beta
    on the inner layer yet.  This verifies the head remains a
    closure when the argument supply is exhausted. -/
def half_applied : Value :=
  eval env0
    (.app
      (.lam Grade.default tyNat
        (.lam Grade.default tyNat (.var 1)))
      (tSucc (tSucc tZero)))

example : shapeOf half_applied = .closure := by native_decide

/-! ## iota-reduction on Nat

Kernel spec: `indRec "Nat" P [mZ, mS] target` where target is a
canonical Nat value reduces by picking the method at the ctor
index and inserting recursive calls for self-referential args. -/

/-- `indRec "Nat" (lambda_. Nat) [Zero, lambda n rec. Succ(Succ rec)]
        Zero` → `Zero`.  Tests the base case: target is Zero, so
    the zero-method fires with no arg chain. -/
def iota_nat_zero : Value :=
  eval env0
    (.indRec "Nat" motiveNat
      [tZero,
       .lam Grade.default tyNat                -- n
         (.lam Grade.default tyNat              -- rec
           (tSucc (tSucc (.var 0))))]           -- doubles rec
      tZero)

example : Value.asNat? iota_nat_zero = some 0 := by native_decide

/-- Same recursor applied to `Succ Zero`: the succ-method fires
    with `n = Zero` and `rec = <iota on Zero> = Zero`.  Result =
    `Succ(Succ Zero) = 2`.  Tests that `buildIotaSpine` correctly
    threads the recursive call through and `applyAll` folds it. -/
def iota_nat_one : Value :=
  eval env0
    (.indRec "Nat" motiveNat
      [tZero,
       .lam Grade.default tyNat
         (.lam Grade.default tyNat
           (tSucc (tSucc (.var 0))))]
      (tSucc tZero))

example : Value.asNat? iota_nat_one = some 2 := by native_decide

/-- Deeper target `Succ^3 Zero`.  Each unfolding produces
    `Succ(Succ rec)`, so the final result is `2 * 3 = 6`.
    Exercises the recursive threading: three nested iota calls,
    each creating a new pair of (n, rec) args. -/
def iota_nat_three : Value :=
  eval env0
    (.indRec "Nat" motiveNat
      [tZero,
       .lam Grade.default tyNat
         (.lam Grade.default tyNat
           (tSucc (tSucc (.var 0))))]
      (tSucc (tSucc (tSucc tZero))))

example : Value.asNat? iota_nat_three = some 6 := by native_decide

/-- Predecessor via eliminator: `indRec "Nat" (lambda_. Nat) [Zero, lambda n
    rec. n] (Succ (Succ Zero))`.  The succ-method returns `n` —
    the predecessor of the current level.  Tests that the
    non-recursive arg (n) is distinct from the recursive arg
    (rec) and that argument ordering is correct. -/
def iota_nat_pred : Value :=
  eval env0
    (.indRec "Nat" motiveNat
      [tZero,
       .lam Grade.default tyNat              -- n
         (.lam Grade.default tyNat            -- rec (ignored)
           (.var 1))]                         -- return n
      (tSucc (tSucc tZero)))

example : Value.asNat? iota_nat_pred = some 1 := by native_decide

/-! ## iota-reduction on Bool

Bool is two nullary ctors: idx 0 = False, idx 1 = True.  Methods
list is `[falseMethod, trueMethod]` — method indexed by ctor.
No recursive arg so `buildIotaSpine` yields an empty spine. -/

/-- `if True then (Succ Zero) else Zero` via `indRec`.  The
    True-method (idx 1) fires. -/
def ite_on_true : Value :=
  eval env0
    (.indRec "Bool" motiveBool
      [tZero, tSucc tZero]    -- [False-arm, True-arm]
      tTrue)

example : Value.asNat? ite_on_true = some 1 := by native_decide

/-- Same on False. -/
def ite_on_false : Value :=
  eval env0
    (.indRec "Bool" motiveBool
      [tZero, tSucc tZero]
      tFalse)

example : Value.asNat? ite_on_false = some 0 := by native_decide

/-! ## Nested indRec

indRec inside indRec: `if b then (indRec Nat ... (Succ Zero))
else Zero`.  Verifies that iota on the outer doesn't short-
circuit inner elaboration. -/

/-- Outer Bool recursor; True-arm is an inner Nat recursor.
    When the outer fires on True, the inner runs on Succ Zero →
    Succ (Succ Zero) = 2 (using the double-rec method). -/
def nested_ite_then_iota : Value :=
  eval env0
    (.indRec "Bool" motiveBool
      [tZero,                             -- False-arm
       (.indRec "Nat" motiveNat           -- True-arm
         [tZero,
          .lam Grade.default tyNat
            (.lam Grade.default tyNat
              (tSucc (tSucc (.var 0))))]
         (tSucc tZero))]
      tTrue)

example : Value.asNat? nested_ite_then_iota = some 2 := by native_decide

/-! ## Stuck forms (neutral / neutralRec)

A free-variable target can't reduce; the eliminator stays
`neutralRec` and pretty-prints with its shape.  Tests this path
both as a head and inside an application. -/

/-- `indRec "Nat" ... (var 0)` — scrutinee is a free variable.
    Result should be a stuck `neutralRec`. -/
def stuck_iota : Value :=
  eval env0
    (.indRec "Nat" motiveNat
      [tZero,
       .lam Grade.default tyNat
         (.lam Grade.default tyNat (.var 0))]
      (.var 0))

example : shapeOf stuck_iota = .nrec "Nat" := by native_decide

/-- A bare free variable produces `Value.neutral 0 []`. -/
def stuck_var : Value := eval env0 (.var 0)

example : shapeOf stuck_var = .neutral 0 0 := by native_decide

/-- Applying a free variable to a value extends the spine. -/
def stuck_app : Value := eval env0 (.app (.var 3) tZero)

example : shapeOf stuck_app = .neutral 3 1 := by native_decide

/-! ## Pretty-printer -/

/-- Zero renders as `0`. -/
example : Value.pretty (.ctor "Nat" 0 [] []) = "0" := by native_decide

/-- Succ Zero renders as `1`. -/
example : Value.pretty (.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]) = "1" := by
  native_decide

/-- Deep Nat literal (5). -/
def v5 : Value :=
  .ctor "Nat" 1 [] [.ctor "Nat" 1 [] [.ctor "Nat" 1 [] [
    .ctor "Nat" 1 [] [.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]]]]]

example : Value.pretty v5 = "5" := by native_decide

/-- Bool pretty: False → `"false"`. -/
example : Value.pretty (.ctor "Bool" 0 [] []) = "false" := by native_decide

/-- Bool pretty: True → `"true"`. -/
example : Value.pretty (.ctor "Bool" 1 [] []) = "true" := by native_decide

/-- Unit pretty: falls back to named ctor form — spec registry
    knows Unit.tt. -/
example : Value.pretty (.ctor "Unit" 0 [] []) = "Unit.tt" := by native_decide

/-- Neutral pretty: bare free var. -/
example : Value.pretty (.neutral 2 []) = "?var2" := by native_decide

/-- Neutral with spine. -/
example : Value.pretty (.neutral 0 [.ctor "Nat" 0 [] []]) = "?var0[0]" := by
  native_decide

/-- Malformed Nat with two args falls back to ctor form. -/
example :
    Value.pretty (.ctor "Nat" 1 [] [.ctor "Nat" 0 [] [], .ctor "Nat" 0 [] []])
      = "Nat.Succ(0, 0)" := by native_decide

/-! ## evalClosed wrapper

Verifies that `evalClosed` drops outer locals — a fresh empty
locals stack regardless of what the input EvalEnv contained. -/

/-- A dirty-locals Value used to seed `evalClosed` so we can
    verify it's dropped.  Represents `Succ Zero` at the Value
    layer (not the Term layer — `EvalEnv.locals` is `List Value`). -/
def vOne : Value :=
  .ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]

/-- With stale locals present, `evalClosed` still treats the
    closed term as closed: `Zero` under empty locals → Zero. -/
def closed_ignores_dirty_locals : Value :=
  evalClosed { env0 with locals := [vOne] } tZero

example : Value.asNat? closed_ignores_dirty_locals = some 0 := by
  native_decide

/-- But a term with `var 0` inside, evaluated via `evalClosed`,
    sees empty locals — so it becomes a neutral head 0.  This
    documents the current behavior for future migration: if the
    elaborator ever emits a body with free variables, `evalClosed`
    produces a stuck form rather than reading stale outer locals. -/
def closed_free_var_stays_stuck : Value :=
  evalClosed { env0 with locals := [vOne] } (.var 0)

example : shapeOf closed_free_var_stays_stuck = .neutral 0 0 := by
  native_decide

/-! ## Runtime suite -/

def run : IO Unit := Tests.suite "Tests.Eval.InterpTests" do
  -- beta-reduction
  Tests.check "beta: id Zero → 0"               (some 0) (Value.asNat? id_applied_zero)
  Tests.check "beta: succ one → 2"              (some 2) (Value.asNat? succ_of_one)
  Tests.check "beta: shadow outer reads 1"      (some 1) (Value.asNat? shadowing_outer)
  Tests.check "beta: second-projection inner"   (some 1) (Value.asNat? snd_of_two)
  -- Closure capture
  Tests.check "capture: returned closure reads" (some 1)
    (Value.asNat? returned_closure_reads_capture)
  Tests.check "capture: half-applied is closure" Shape.closure (shapeOf half_applied)
  -- iota Nat
  Tests.check "iota Nat zero-arm → 0"     (some 0) (Value.asNat? iota_nat_zero)
  Tests.check "iota Nat succ 1 → 2"       (some 2) (Value.asNat? iota_nat_one)
  Tests.check "iota Nat succ^3 doubles → 6" (some 6) (Value.asNat? iota_nat_three)
  Tests.check "iota Nat predecessor → 1"  (some 1) (Value.asNat? iota_nat_pred)
  -- iota Bool
  Tests.check "iota Bool True-arm → 1"  (some 1) (Value.asNat? ite_on_true)
  Tests.check "iota Bool False-arm → 0" (some 0) (Value.asNat? ite_on_false)
  -- Nested
  Tests.check "nested: True → inner iota → 2" (some 2)
    (Value.asNat? nested_ite_then_iota)
  -- Stuck
  Tests.check "stuck: iota on free var → neutralRec"
    (Shape.nrec "Nat") (shapeOf stuck_iota)
  Tests.check "stuck: bare var → neutral 0 []"
    (Shape.neutral 0 0) (shapeOf stuck_var)
  Tests.check "stuck: app on free var extends spine"
    (Shape.neutral 3 1) (shapeOf stuck_app)
  -- Pretty
  Tests.check "pretty: Zero → \"0\"" "0"
    (Value.pretty (.ctor "Nat" 0 [] []))
  Tests.check "pretty: one → \"1\"" "1"
    (Value.pretty (.ctor "Nat" 1 [] [.ctor "Nat" 0 [] []]))
  Tests.check "pretty: 5 → \"5\"" "5" (Value.pretty v5)
  Tests.check "pretty: False → \"false\"" "false"
    (Value.pretty (.ctor "Bool" 0 [] []))
  Tests.check "pretty: True → \"true\"" "true"
    (Value.pretty (.ctor "Bool" 1 [] []))
  Tests.check "pretty: Unit.tt → \"Unit.tt\"" "Unit.tt"
    (Value.pretty (.ctor "Unit" 0 [] []))
  Tests.check "pretty: neutral bare → \"?var2\"" "?var2"
    (Value.pretty (.neutral 2 []))
  Tests.check "pretty: neutral spine" "?var0[0]"
    (Value.pretty (.neutral 0 [.ctor "Nat" 0 [] []]))
  Tests.check "pretty: malformed Nat falls back" "Nat.Succ(0, 0)"
    (Value.pretty
      (.ctor "Nat" 1 [] [.ctor "Nat" 0 [] [], .ctor "Nat" 0 [] []]))
  -- evalClosed
  Tests.check "evalClosed drops locals (Zero closed)" (some 0)
    (Value.asNat? closed_ignores_dirty_locals)
  Tests.check "evalClosed drops locals (var 0 stays stuck)"
    (Shape.neutral 0 0) (shapeOf closed_free_var_stays_stuck)

/-! ## Additional Value constructor coverage

`Value` has ~15 constructors.  The sections above exercise the
common ones (closure, ctor, neutral, neutralRec).  The rest —
`universe`, `piType`, `sigmaType`, `forallLevelType`, `idType`,
`reflVal`, `neutralIdJ`, `quotType`, `quotMkVal`,
`neutralQuotLift`, `indType` — need direct tests so a broken
evaluator that falls through to `.other` for any of them gets
caught. -/

/-- Shape tag for the additional Value constructors, extending
    `Shape` without changing existing consumers. -/
inductive ExtShape where
  | universe    (levelRepr : String)
  | piType
  | sigmaType
  | forallLevelType
  | idType
  | reflVal
  | nidJ
  | quotType
  | quotMkVal
  | nqLift
  | indType     (typeName : String) (paramCount : Nat)
  | other
  deriving DecidableEq, Repr

/-- Extended shape extraction — covers the Value constructors
    not addressed by `Shape`.  Renders each with a stable repr
    so `native_decide` can compare. -/
def extShapeOf : Value → ExtShape
  | .universe level           => .universe (reprStr level)
  | .piType _ _ _             => .piType
  | .sigmaType _ _ _          => .sigmaType
  | .forallLevelType _ _      => .forallLevelType
  | .idType _ _ _             => .idType
  | .reflVal _                => .reflVal
  | .neutralIdJ _ _ _         => .nidJ
  | .quotType _ _             => .quotType
  | .quotMkVal _ _            => .quotMkVal
  | .neutralQuotLift _ _ _    => .nqLift
  | .indType name args        => .indType name args.length
  | _                         => .other

-- `eval env (type u)` produces a `Value.universe u`.
example :
  extShapeOf (eval env0 (.type .zero))
    = .universe (reprStr Level.zero) := by native_decide

example :
  extShapeOf (eval env0 (.type (.succ .zero)))
    = .universe (reprStr (Level.succ .zero)) := by native_decide

-- Pi type evaluates to `.piType`.
example :
  extShapeOf (eval env0 (.piTot Grade.default tyNat tyNat)) = .piType := by
  native_decide

-- Sigma type evaluates to `.sigmaType`.
example :
  extShapeOf (eval env0 (.sigma Grade.default tyNat tyNat)) = .sigmaType := by
  native_decide

-- forallLevel (A10 U-poly).
example :
  extShapeOf (eval env0 (.forallLevel (.type (.var 0))))
    = .forallLevelType := by native_decide

-- Id type evaluates to `.idType`.
example :
  extShapeOf (eval env0 (.id tyNat tZero tZero)) = .idType := by native_decide

-- refl evaluates to `.reflVal`.
example :
  extShapeOf (eval env0 (.refl tZero)) = .reflVal := by native_decide

-- quot type evaluates to `.quotType`.
example :
  extShapeOf (eval env0 (.quot tyNat (.lam Grade.default tyNat tyNat)))
    = .quotType := by native_decide

-- quotMk evaluates to `.quotMkVal`.
example :
  extShapeOf
    (eval env0 (.quotMk (.lam Grade.default tyNat tyNat) tZero))
    = .quotMkVal := by native_decide

-- `ind "Nat" []` evaluates to `.indType "Nat" 0`.
example :
  extShapeOf (eval env0 (.ind "Nat" [])) = .indType "Nat" 0 := by
  native_decide

-- `ind "Option" [tyNat]` evaluates with paramCount = 1.
example :
  extShapeOf (eval env0 (.ind "Option" [tyNat])) = .indType "Option" 1 := by
  native_decide

/-! ## idJ iota — refl collapses to `app base witness`

`idJ motive base (refl w) → app base w`.  Eval should handle
this directly.  Using a non-identity base so the substitution
result is observable — an `asNat?` check on the resulting
Value distinguishes correct reduction from any bug that
returns the base unchanged.
-/

-- `idJ _ (λx. Succ x) (refl Zero)` → `(λx. Succ x) Zero` → `Succ Zero = 1`.
example :
  Value.asNat?
    (eval env0
      (.idJ
        (.lam Grade.default tyNat (.lam Grade.default tyNat (.lam Grade.default
          (.id tyNat (.var 1) (.var 0)) tyNat)))   -- motive (unused at runtime)
        (.lam Grade.default tyNat (tSucc (.var 0)))  -- base = λx. Succ x
        (.refl tZero)))                                -- refl Zero
    = some 1 := by native_decide

-- Non-refl eqProof → `neutralIdJ`.
example :
  extShapeOf
    (eval env0
      (.idJ
        (.lam Grade.default tyNat tyNat)
        (.lam Grade.default tyNat (.var 0))
        (.var 5)))                                   -- free var eqProof
    = .nidJ := by native_decide

/-! ## quotLift iota — quotMk collapses to `app lifted witness` -/

-- `quotLift (λx. Succ x) _ (quotMk _ Zero)` → `Succ Zero = 1`.
example :
  Value.asNat?
    (eval env0
      (.quotLift
        (.lam Grade.default tyNat (tSucc (.var 0)))
        (.lam Grade.default tyNat (.lam Grade.default tyNat tyNat))
        (.quotMk (.lam Grade.default tyNat tyNat) tZero)))
    = some 1 := by native_decide

-- Non-quotMk target → `neutralQuotLift`.
example :
  extShapeOf
    (eval env0
      (.quotLift
        (.lam Grade.default tyNat (.var 0))
        (.lam Grade.default tyNat tyNat)
        (.var 3)))
    = .nqLift := by native_decide

/-! ## Distinct-value evaluation — catches "returns zero" bugs

Many of the earlier tests evaluate to `Zero` (= 0).  A broken
evaluator that returns `Nat.Zero` for everything would pass
those.  These tests use distinct non-zero results so "always
returns 0" is visible. -/

example :
  Value.asNat?
    (eval env0 (.app (.lam Grade.default tyNat (tSucc (tSucc (.var 0)))) tZero))
    = some 2 := by native_decide

example :
  Value.asNat?
    (eval env0
      (.app (.lam Grade.default tyNat (tSucc (tSucc (tSucc (.var 0)))))
        (tSucc tZero)))
    = some 4 := by native_decide

-- Choose-first: `(λa. λb. a) 3 1 = 3` (distinct values guarantee
-- a broken "returns second arg" or "returns zero" evaluator is
-- caught).
example :
  Value.asNat?
    (eval env0
      (.app
        (.app
          (.lam Grade.default tyNat
            (.lam Grade.default tyNat (.var 1)))
          (tSucc (tSucc (tSucc tZero))))              -- 3
        (tSucc tZero)))                                -- 1
    = some 3 := by native_decide

-- Choose-second: dual of the above, ensures we can distinguish
-- "returns first" from "returns second".
example :
  Value.asNat?
    (eval env0
      (.app
        (.app
          (.lam Grade.default tyNat
            (.lam Grade.default tyNat (.var 0)))
          (tSucc (tSucc (tSucc tZero))))              -- 3 (discarded)
        (tSucc tZero)))                                -- 1 (returned)
    = some 1 := by native_decide

end Tests.Eval.InterpTests
