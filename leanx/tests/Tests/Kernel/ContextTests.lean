import FX.Kernel.Context

/-!
# Context tests

Compile-time tests for context construction and grade
operations.
-/

namespace Tests.Kernel.ContextTests

open FX.Kernel
open FX.Kernel.Term

def universeZero : Level := .zero
def typeZero : Term := .type universeZero

def linearGrade : Grade := Grade.default
def ghostGrade : Grade := Grade.ghost

/-! ## empty / extend / lookup -/

example : TypingContext.empty.size = 0 := rfl

example : (TypingContext.empty.extend linearGrade typeZero).size = 1 := rfl

example :
  (TypingContext.empty.extend linearGrade typeZero).lookup? 0
    = some { grade := linearGrade, typeTerm := typeZero } := rfl

-- lookup at out-of-range returns none
example : TypingContext.empty.lookup? 0 = none := rfl
example : (TypingContext.empty.extend linearGrade typeZero).lookup? 5 = none := rfl

-- Two-layer extend: index 0 is the latest binder
example :
  let context := (TypingContext.empty.extend ghostGrade typeZero).extend linearGrade typeZero
  (context.lookup? 0).map (·.grade.usage) = some Usage.one := rfl

example :
  let context := (TypingContext.empty.extend ghostGrade typeZero).extend linearGrade typeZero
  (context.lookup? 1).map (·.grade.usage) = some Usage.zero := rfl

/-! ## scale — pointwise usage multiplication -/

/-- Helper: head usage of a context via `lookup?`. -/
def headUsage (context : TypingContext) : Option Usage :=
  (context.lookup? 0).map (·.grade.usage)

-- scale by 0: every usage becomes 0
example : headUsage ((TypingContext.empty.extend linearGrade typeZero).scale Usage.zero)
    = some Usage.zero := rfl

-- scale by 1: unchanged
example : headUsage ((TypingContext.empty.extend linearGrade typeZero).scale Usage.one)
    = some Usage.one := rfl

-- scale by omega: linear becomes omega
example : headUsage ((TypingContext.empty.extend linearGrade typeZero).scale Usage.omega)
    = some Usage.omega := rfl

/-! ## divByUsage — Wood-Atkey context division -/

-- div by 1: unchanged
example : headUsage ((TypingContext.empty.extend linearGrade typeZero).divByUsage Usage.one)
    = some Usage.one := rfl

-- div by omega on linear (usage=1): becomes 0 — §27.1 Lam-bug witness
example : headUsage ((TypingContext.empty.extend linearGrade typeZero).divByUsage Usage.omega)
    = some Usage.zero := rfl

-- div by omega on ghost (usage=0): stays 0
example : headUsage ((TypingContext.empty.extend ghostGrade typeZero).divByUsage Usage.omega)
    = some Usage.zero := rfl

/-! ## add — pointwise grade addition, shape-checked

`TypingContext.add` is `partial def` (structural recursion through a
polymorphic list is not seen by Lean's termination checker), so
`rfl` cannot reduce it.  `native_decide` runs the compiled form.
-/

/-- Helper: check a TypingContext.add result against an expected option-of-
    head-usage pattern. -/
def addHeadUsage (context₁ context₂ : TypingContext) : Option Usage :=
  (TypingContext.add context₁ context₂).map (fun context' =>
    match context' with
    | e :: _ => e.grade.usage
    | [] => Usage.zero)  -- unreachable for non-empty add

def addFailed (context₁ context₂ : TypingContext) : Bool :=
  (TypingContext.add context₁ context₂).isNone

example : addFailed TypingContext.empty TypingContext.empty = false := by native_decide

example : addFailed (TypingContext.empty.extend linearGrade typeZero) TypingContext.empty = true := by
  native_decide

example : addHeadUsage (TypingContext.empty.extend linearGrade typeZero) (TypingContext.empty.extend linearGrade typeZero)
    = some Usage.omega := by native_decide

example :
  addFailed (TypingContext.empty.extend linearGrade typeZero) (TypingContext.empty.extend linearGrade (Term.var 0))
    = true := by native_decide

/-! ## Term.structEq — structural (not up-to-beta) equality -/

example : (Term.var 0 == Term.var 0 : Bool) = true := by native_decide
example : (Term.var 0 == Term.var 1 : Bool) = false := by native_decide
example : (typeZero == typeZero : Bool) = true := by native_decide

-- Structural vs convertible: (lambda x. x) T is NOT structurally equal to T.
example :
  (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero == typeZero : Bool)
    = false := by native_decide

end Tests.Kernel.ContextTests
