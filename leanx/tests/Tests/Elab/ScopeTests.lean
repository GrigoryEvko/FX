import FX.Elab.Scope
import Tests.Framework

/-!
# Scope tests — de Bruijn name resolution

`FX.Elab.Scope` is pure bookkeeping: a stack of binder names with
head = most-recent (de Bruijn index 0).  Every operation reduces
to list manipulation, so `by decide` proves shape identities at
compile time.

Coverage:
  * `empty` — zero binders
  * `push` — extending front; shifting older binders up
  * `pushAll` — left-to-right semantics matching typing rules
  * `resolve?` — `none` when unbound, correct index when bound,
    inner shadow wins over outer binding of same name
  * `size` — length of the stack
-/

namespace Tests.Elab.ScopeTests

open FX.Elab
open Tests

/-! ## Compile-time shape proofs -/

/-- Empty scope resolves nothing. -/
example : Scope.empty.resolve? "x" = none := by decide

/-- Size of empty scope is zero. -/
example : Scope.empty.size = 0 := by decide

/-- push adds one binder; new name lives at de Bruijn 0. -/
example : (Scope.empty.push "x").resolve? "x" = some 0 := by decide

/-- Size tracks push count. -/
example : (Scope.empty.push "x").size = 1 := by decide

/-- Two pushes: most-recent at 0, earlier at 1. -/
example : (Scope.empty.push "outer" |>.push "inner").resolve? "inner"
  = some 0 := by decide

example : (Scope.empty.push "outer" |>.push "inner").resolve? "outer"
  = some 1 := by decide

/-- Unknown name — even in a populated scope — returns `none`. -/
example : (Scope.empty.push "a" |>.push "b").resolve? "c" = none := by decide

/-- `pushAll` pushes left-to-right: the LAST name listed ends up
    at de Bruijn index 0 (it was pushed most recently). -/
example : (Scope.pushAll ["a", "b", "c"] Scope.empty).resolve? "c"
  = some 0 := by decide

example : (Scope.pushAll ["a", "b", "c"] Scope.empty).resolve? "b"
  = some 1 := by decide

example : (Scope.pushAll ["a", "b", "c"] Scope.empty).resolve? "a"
  = some 2 := by decide

/-- Inner shadow wins over outer same-named binding.  This is how
    `fn outer(x: T) = fn inner(x: U) => x` resolves: the inner `x`
    has index 0 and the outer `x` is unreachable by name. -/
example : (Scope.empty.push "x" |>.push "x").resolve? "x" = some 0 := by decide

/-- `size` after `pushAll` is the list length. -/
example : (Scope.pushAll ["a", "b", "c"] Scope.empty).size = 3 := by decide

/-! ## Runtime harness — same properties via `check` so the suite
    shows up in the aggregator totals.  Also covers a couple of
    cases that benefit from being expressed as values rather than
    proofs (printable diagnostics on failure). -/

def run : IO Unit := Tests.suite "Tests.Elab.ScopeTests" do
  -- Empty.
  check "empty.resolve?(\"x\")" (none : Option Nat) (Scope.empty.resolve? "x")
  check "empty.size" 0 Scope.empty.size

  -- Single binder.
  let s1 := Scope.empty.push "x"
  check "push x; resolve? x" (some 0) (s1.resolve? "x")
  check "push x; resolve? y" (none : Option Nat) (s1.resolve? "y")
  check "push x; size" 1 s1.size

  -- Two binders — order matters.
  let s2 := s1.push "y"
  check "push y; resolve? y = 0" (some 0) (s2.resolve? "y")
  check "push y; resolve? x = 1" (some 1) (s2.resolve? "x")
  check "push y; size" 2 s2.size

  -- Shadowing: inner `x` wins.
  let shadowedScope := Scope.empty.push "x" |>.push "x"
  check "shadow resolve? x = 0" (some 0) (shadowedScope.resolve? "x")
  check "shadow size" 2 shadowedScope.size

  -- pushAll: last-listed is index 0.
  let sAll := Scope.pushAll ["a", "b", "c"] Scope.empty
  check "pushAll resolve? c = 0" (some 0) (sAll.resolve? "c")
  check "pushAll resolve? b = 1" (some 1) (sAll.resolve? "b")
  check "pushAll resolve? a = 2" (some 2) (sAll.resolve? "a")
  check "pushAll size" 3 sAll.size

  -- pushAll into a non-empty scope composes correctly.
  let sComp := Scope.pushAll ["x", "y"] (Scope.empty.push "z")
  check "compose resolve? y = 0" (some 0) (sComp.resolve? "y")
  check "compose resolve? x = 1" (some 1) (sComp.resolve? "x")
  check "compose resolve? z = 2" (some 2) (sComp.resolve? "z")
  check "compose size" 3 sComp.size

end Tests.Elab.ScopeTests
