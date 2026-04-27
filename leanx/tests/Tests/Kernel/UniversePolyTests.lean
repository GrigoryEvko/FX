import FX.Kernel.Term
import FX.Kernel.Typing
import FX.Kernel.Context
import FX.Kernel.Substitution

/-!
# Universe polymorphism tests (A10, §31.4 U-poly)

Compile-time tests for the type-level universe-polymorphism
machinery:

  * `Term.forallLevel body` — the kernel form of `Π (k : level).
    body`.  Phase-2 scope: type-level only (no value
    abstraction/application).
  * `Level.varsInScope : Nat → Level → Bool` — predicate that
    every `Level.var n` in the level has `n < levelCount`.
  * `TypingContext.levelCount` — field tracking enclosing
    `forallLevel` scopes.
  * `TypingContext.extendLevel` — enters a new level scope.
  * Closed-level check in `.type` inference: out-of-scope
    `Level.var n` rejects with T060.

## Sections

 1. `Level.varsInScope` — the predicate.
 2. `structEq` / shift / subst traversal through forallLevel.
 3. `.type` inference closed-level check (Phase 1's silent
    acceptance upgraded to T060 rejection).
 4. `forallLevel` type inference — body checked under extended
    level scope.
 5. Nested `forallLevel` — levelCount scopes stack.
 6. Coe from `List TypingContextEntry` to `TypingContext` still
    resolves test fixtures unchanged.
-/

namespace Tests.Kernel.UniversePolyTests

open FX.Kernel
open FX.Kernel.Term

/-! ## Fixtures -/

def typeZero : Term := .type .zero
def typeOne  : Term := .type (.succ .zero)

/-! ## 1. Level.varsInScope -/

-- Closed levels: all vars in scope at any count (vacuously).
example : Level.varsInScope 0 Level.zero = true := by native_decide
example : Level.varsInScope 0 (Level.succ Level.zero) = true := by native_decide
example : Level.varsInScope 5 Level.zero = true := by native_decide

-- `var n` is in scope when n < levelCount.
example : Level.varsInScope 1 (Level.var 0) = true := by native_decide
example : Level.varsInScope 2 (Level.var 0) = true := by native_decide
example : Level.varsInScope 2 (Level.var 1) = true := by native_decide

-- `var n` is out of scope when n ≥ levelCount.
example : Level.varsInScope 0 (Level.var 0) = false := by native_decide
example : Level.varsInScope 1 (Level.var 1) = false := by native_decide
example : Level.varsInScope 2 (Level.var 2) = false := by native_decide

-- Compound levels: every constituent var must be in scope.
example :
  Level.varsInScope 1 (Level.max (Level.var 0) (Level.var 0)) = true := by
  native_decide
example :
  Level.varsInScope 1 (Level.max (Level.var 0) (Level.var 1)) = false := by
  native_decide
example :
  Level.varsInScope 2 (Level.succ (Level.var 1)) = true := by native_decide

/-! ## 2. structEq / shift / subst on forallLevel -/

example :
  (Term.forallLevel typeZero == Term.forallLevel typeZero) = true := by
  native_decide
example :
  (Term.forallLevel typeZero == Term.forallLevel typeOne) = false := by
  native_decide

-- Shift passes through forallLevel on term vars (level scope
-- is orthogonal to term de Bruijn).
example :
  shift 0 1 (Term.forallLevel (Term.var 0))
    = Term.forallLevel (Term.var 1) := rfl

example :
  subst 0 typeZero (Term.forallLevel (Term.var 0))
    = Term.forallLevel typeZero := rfl

-- shift_zero corollary.
example : shift 0 0 (Term.forallLevel typeZero)
            = Term.forallLevel typeZero :=
  shift_zero 0 (Term.forallLevel typeZero)

/-! ## 3. Closed-level check at `.type` inference

Phase-1 silently accepted `.type (Level.var 0)` at top level;
A10 upgrades to T060 rejection.  The kernel's invariant now:
every `Level.var n` at a `.type` node must have `n < context.
levelCount`, else the type is malformed.
-/

/-- True iff `infer` threw a `T060` (level variable out of scope). -/
def inferFailsT060 (context : TypingContext) (term : Term) : Bool :=
  match Term.infer context term with
  | .error e => e.code == "T060"
  | .ok _    => false

-- At levelCount = 0, `.type (Level.var 0)` is out of scope.
example : inferFailsT060 [] (.type (.var 0)) = true := by native_decide

-- At levelCount = 0, any `.type (var n)` fails.
example : inferFailsT060 [] (.type (.var 3)) = true := by native_decide

-- Compound levels containing an out-of-scope var also fail.
example :
  inferFailsT060 [] (.type (.max (.var 0) .zero)) = true := by native_decide

-- Closed levels still type-check at levelCount = 0.
example :
  (Term.infer [] (.type .zero)).isOk = true := by native_decide
example :
  (Term.infer [] (.type (.succ .zero))).isOk = true := by native_decide

/-! ## 4. forallLevel inference — body checked under extended scope

Inside a `forallLevel` body, `Level.var 0` is in scope.  The
typing rule extends `context.levelCount` by 1 before recursing. -/

/-- Check `infer context term` returned `.ok _`. -/
def inferOk (context : TypingContext) (term : Term) : Bool :=
  match Term.infer context term with
  | .ok _    => true
  | .error _ => false

-- `forallLevel (type (var 0))` — body mentions the freshly-bound
-- level variable, which IS in scope inside the body.
example : inferOk [] (Term.forallLevel (.type (.var 0))) = true := by
  native_decide

-- `forallLevel (type zero)` — body is closed, also fine.
example : inferOk [] (Term.forallLevel (.type .zero)) = true := by
  native_decide

-- `forallLevel (type (var 1))` — body references var 1 but only
-- one level binder is enclosing.  var 1 is out of scope → T060.
example :
  inferFailsT060 [] (Term.forallLevel (.type (.var 1))) = true := by
  native_decide

/-! ## 5. Nested forallLevel — levelCount scopes stack -/

-- Two-deep: `∀ k0. ∀ k1. type (var 0)` — innermost binder,
-- in scope.
example :
  inferOk []
    (Term.forallLevel (Term.forallLevel (.type (.var 0)))) = true := by
  native_decide

-- Two-deep: `∀ k0. ∀ k1. type (var 1)` — outer binder, in scope.
example :
  inferOk []
    (Term.forallLevel (Term.forallLevel (.type (.var 1)))) = true := by
  native_decide

-- Two-deep: `∀ k0. ∀ k1. type (var 2)` — out of scope.
example :
  inferFailsT060 []
    (Term.forallLevel (Term.forallLevel (.type (.var 2)))) = true := by
  native_decide

-- Three-deep: `∀ k0. ∀ k1. ∀ k2. type (max (var 0) (var 2))` —
-- compound level with two in-scope vars.
example :
  inferOk []
    (Term.forallLevel (Term.forallLevel (Term.forallLevel
      (.type (.max (.var 0) (.var 2)))))) = true := by native_decide

/-! ## 6. levelCount threaded as parameter

Architectural decision: `TypingContext` stays as
`abbrev List TypingContextEntry` (preserving ~40 test call
sites that use bare `[]` / `[{...}]` literals), and `levelCount`
threads through `infer`/`check`/`inferType` as an explicit
`(levelCount : Nat := 0)` parameter.  A struct refactor of
TypingContext with a `Coe` instance was attempted but reverted
because bare `[]` literals lack an element-type hint for Coe
elaboration, cascading errors into every bare-list test. -/

/-- Like `inferFailsT060` but takes an explicit levelCount. -/
def inferFailsT060At (context : TypingContext) (term : Term)
    (levelCount : Nat) : Bool :=
  match Term.infer context term (levelCount := levelCount) with
  | .error e => e.code == "T060"
  | .ok _    => false

/-- Like `inferOk` but takes an explicit levelCount. -/
def inferOkAt (context : TypingContext) (term : Term)
    (levelCount : Nat) : Bool :=
  match Term.infer context term (levelCount := levelCount) with
  | .ok _    => true
  | .error _ => false

-- Bare empty list fixture flows into TypingContext-typed args.
example : inferOk [] (.type .zero) = true := by native_decide

-- Singleton list fixture works unchanged.
example :
  inferOk [{ grade := Grade.default, typeTerm := typeZero }]
    (.var 0) = true := by native_decide

-- levelCount=1 — `.type (.var 0)` is in scope (one enclosing forallLevel).
example : inferOkAt [] (.type (.var 0)) 1 = true := by native_decide

-- levelCount=0 — `.type (.var 0)` is out of scope (T060).
example : inferFailsT060At [] (.type (.var 0)) 0 = true := by native_decide

-- levelCount=2 — both `.var 0` and `.var 1` are in scope.
example : inferOkAt [] (.type (.var 0)) 2 = true := by native_decide
example : inferOkAt [] (.type (.var 1)) 2 = true := by native_decide

-- levelCount=2 — `.var 2` is out of scope.
example : inferFailsT060At [] (.type (.var 2)) 2 = true := by native_decide

end Tests.Kernel.UniversePolyTests
