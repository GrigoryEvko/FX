import LeanFX2.Graded.GradeVector
import LeanFX2.Foundation.Context

/-! # Graded/Ctx — graded contexts

A graded context augments `Ctx` (the kernel's de-Bruijn-indexed
binder list) with one `GradeVector` per binding.  The grade vector
records, in each of FX's registered dimensions, how that variable
is consumed in the term being checked.

Per `fx_design.md` §6.2 (Wood-Atkey 2022 corrected Lam rule):
context division `Γ / p` divides every binding's grade vector by
the scaling vector `p`, where `pi/p = max { d : d * p ≤ pi }`.
For the Usage semiring, `1/ω = 0` — replicable closures cannot
capture linearly-used bindings.

## What ships (Phase 12.A.5)

* `GradedBinding` — one binding (carries grade vector)
* `GradedCtx` — recursively-built sequence of GradedBindings
  parameterized by Mode + level + scope + Dimension list
* Pointwise vector ops at the context level: `add`, `zero`,
  `pointwise sum across bindings`
* `lookup` retrieving the grade vector at a variable position

## What defers

* Wood-Atkey context division `Γ / p` — needs `Decidable` on
  `GradeVector.le`, deferred to Phase 12.A.6 alongside concrete
  semiring instances completing the `DecidableGradeSemiring`
  contract for the registered dimensions
* Sub-typing predicate `GradedCtx.le` — depends on division
* Integration with kernel's `Term` constructors — depends on
  the typing rules in `Graded/Rules.lean`

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded

/-- A single graded binding: a kernel `Ty` plus a grade vector
recording how the bound variable is used along each registered
dimension.  Lives at a specific universe `level` and scope
position, and carries grades over the registered `dimensions`. -/
structure GradedBinding
    (level scope : Nat)
    (dimensions : List Dimension)
    where
  /-- The bound variable's type. -/
  bindingTy : Ty level scope
  /-- The grade vector recording per-dimension usage. -/
  grade : GradeVector dimensions

/-- A graded context: a recursive list of graded bindings with
incrementing scope.  Empty context has scope 0; cons adds a binding
at the front with scope+1.

Note: scope grows in this representation because each new binding
extends the available variables.  Position 0 in the lookup refers
to the most-recently bound variable. -/
inductive GradedCtx
    (mode : Mode)
    (level : Nat)
    (dimensions : List Dimension) :
    Nat → Type
  | empty : GradedCtx mode level dimensions 0
  | cons {scope : Nat}
      (rest : GradedCtx mode level dimensions scope)
      (binding : GradedBinding level scope dimensions) :
      GradedCtx mode level dimensions (scope + 1)

/-! ## The all-zero graded context

An "empty-grade" context where every binding's grade vector is
`zero` (no usage).  Useful as the starting point for grade
accumulation: `Γ + (cost t)` when the entire usage comes from
checking `t`. -/

/-- Erase grades to all-zero, preserving binding types and structure.
The grades after erasure record "no usage" — the typing rules then
accumulate usage as the term is checked. -/
def GradedCtx.eraseGrades :
    ∀ {mode : Mode} {level : Nat} {dimensions : List Dimension} {scope : Nat},
      GradedCtx mode level dimensions scope →
      GradedCtx mode level dimensions scope
  | _, _, _, _, .empty => .empty
  | _, _, _, _, .cons rest binding =>
      .cons (GradedCtx.eraseGrades rest)
            { bindingTy := binding.bindingTy, grade := GradeVector.zero }

/-! ## Pointwise context addition

Sequential composition of operations accumulates grades: when
typing `e1 ; e2`, the resulting context grades are `(grades of
e1) + (grades of e2)` pointwise, both at the binding level
(per-binding grade vectors) and at the dimension level (per
dimension within each grade vector).

Note: addition only makes sense when both contexts have the same
SHAPE (same scope, same Ty per binding).  The graded difference
is in grades only. -/

/-- Project the head binding from a non-empty graded context
(scope > 0).  Implemented via `GradedCtx.casesOn` with an explicit
motive — direct partial pattern matching leaks propext through
the auto-generated equation lemma for the impossible `.empty`
case (scope 0 vs scope+1 mismatch). -/
def GradedCtx.headBinding {mode : Mode} {level : Nat}
    {dimensions : List Dimension} {scope : Nat}
    (someCtx : GradedCtx mode level dimensions (scope + 1)) :
    GradedBinding level scope dimensions :=
  GradedCtx.casesOn (motive := fun (someScope : Nat)
                                   (_ : GradedCtx mode level dimensions someScope) =>
                                  someScope = scope + 1 →
                                  GradedBinding level scope dimensions)
    someCtx
    (fun (impossibleEq : (0 : Nat) = scope + 1) =>
      Nat.noConfusion impossibleEq)
    (fun {someInner} _ binding (scopeEq : someInner + 1 = scope + 1) =>
      let innerEq : someInner = scope := Nat.succ.inj scopeEq
      innerEq ▸ binding)
    rfl

/-- Project the tail of a non-empty graded context.  Same
encoding as `headBinding` — uses `casesOn` with explicit motive
to avoid the propext leak from indexed-inductive partial match. -/
def GradedCtx.tailCtx {mode : Mode} {level : Nat}
    {dimensions : List Dimension} {scope : Nat}
    (someCtx : GradedCtx mode level dimensions (scope + 1)) :
    GradedCtx mode level dimensions scope :=
  GradedCtx.casesOn (motive := fun (someScope : Nat)
                                   (_ : GradedCtx mode level dimensions someScope) =>
                                  someScope = scope + 1 →
                                  GradedCtx mode level dimensions scope)
    someCtx
    (fun (impossibleEq : (0 : Nat) = scope + 1) =>
      Nat.noConfusion impossibleEq)
    (fun {someInner} rest _ (scopeEq : someInner + 1 = scope + 1) =>
      let innerEq : someInner = scope := Nat.succ.inj scopeEq
      innerEq ▸ rest)
    rfl

/-- Pointwise add: requires both contexts have matching binding
types.  Implementation uses `headBinding` and `tailCtx` projectors
on the second operand, avoiding cross-product matches that the
Lean 4 match compiler discharges via propext. -/
def GradedCtx.add :
    ∀ {mode : Mode} {level : Nat} {dimensions : List Dimension} {scope : Nat},
      GradedCtx mode level dimensions scope →
      GradedCtx mode level dimensions scope →
      GradedCtx mode level dimensions scope
  | _, _, _, _, .empty, _ => .empty
  | _, _, _, _, .cons restLeft bindingLeft, secondCtx =>
      let bindingRight := GradedCtx.headBinding secondCtx
      let restRight := GradedCtx.tailCtx secondCtx
      .cons (GradedCtx.add restLeft restRight)
            { bindingTy := bindingLeft.bindingTy,
              grade := GradeVector.add bindingLeft.grade bindingRight.grade }

/-! ## Lookup the grade at a position

Position 0 is the most recent (head) binding, position 1 is the
next, etc.  Returns the binding (type + grade vector) at that
position, with `Fin scope` ensuring the lookup is in-range. -/

/-- Project the binding at de Bruijn index `idx` in a graded context. -/
def GradedCtx.lookup :
    ∀ {mode : Mode} {level : Nat} {dimensions : List Dimension} {scope : Nat},
      GradedCtx mode level dimensions scope →
      Fin scope →
      Σ' (lookupScope : Nat), GradedBinding level lookupScope dimensions
  | _, _, _, _, .cons rest binding, ⟨0, _⟩ => ⟨_, binding⟩
  | _, _, _, _, .cons rest _, ⟨innerIdx + 1, lookupBound⟩ =>
      GradedCtx.lookup rest ⟨innerIdx, Nat.lt_of_succ_lt_succ lookupBound⟩

/-! ## Smoke -/

/-- Empty context lookup is impossible (Fin 0 has no inhabitants). -/
example {mode : Mode} {level : Nat} {dimensions : List Dimension}
    (impossible : Fin 0) :
    Σ' (lookupScope : Nat), GradedBinding level lookupScope dimensions :=
  GradedCtx.lookup (mode := mode) (.empty) impossible

/-- Adding a context to itself doubles the per-binding grade vector
componentwise.  Smoke check at the empty context (trivially equal). -/
example {mode : Mode} {level : Nat} {dimensions : List Dimension} :
    GradedCtx.add (GradedCtx.empty (mode := mode) (level := level) (dimensions := dimensions))
                  GradedCtx.empty
    = GradedCtx.empty := rfl

/-- Erasing grades on an empty context yields the empty context. -/
example {mode : Mode} {level : Nat} {dimensions : List Dimension} :
    GradedCtx.eraseGrades
        (GradedCtx.empty (mode := mode) (level := level) (dimensions := dimensions))
    = GradedCtx.empty := rfl

end LeanFX2.Graded
