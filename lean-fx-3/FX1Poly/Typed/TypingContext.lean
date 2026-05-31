import FX1Poly.Core.RawTermRename
import FX1Poly.Core.PolyProfile

/-! # FX1Poly/Typed/TypingContext — the native de Bruijn typing telescope

The `.context`-sort spine of the typed layer (polycell.md §11.8.5): the
`TypingContext` inductive + `lookup`, under the design described below.

## The design: a RAW de Bruijn telescope

A `TypingContext profile scope` is a de Bruijn sequence of exactly
`scope` binding-type cells.  Each binding's type is itself a `.type`-
sorted `RawTerm` cell (cells classify cells, §5), NOT a legacy
`Foundation.Ty` value.  The `cons` constructor stores the new binding's
type at the scope BEFORE the binding (`RawTerm scope`), so a binding may
mention only the variables introduced earlier — the standard well-scoped
Allais–McBride encoding.

This telescope is RAW: it carries NO typing well-formedness field.  The
`.type`-cell discipline ("each binding inhabits some universe", the
`∃ levelCode, HasType context bindingType (universeCell levelCode)`
side condition the §11.8.5 sketch imagines) is DELIBERATELY NOT a `cons`
field.

**Why no `IsType` field — the mutual-index wall.**  `IsType` is defined
in terms of `HasType`, and `HasType` is indexed by `TypingContext`.  A
`cons (_ : IsType context bindingType)` field would make the inductive's
INDEX signature reference a sibling (`HasType`/`IsType`) that itself
references `TypingContext` — exactly the sibling-index cycle Lean 4
rejects (it forbids mutual references in index signatures, not only
strict-positivity violations).  The resolution: `TypingContext` is the
RAW spine here; well-formedness is a SEPARATE `WfContext` predicate,
layered OVER this raw telescope rather than baked into it.  Do not
"helpfully" add an `IsType` field back — it will not build.

## What is delivered

* `TypingContext` — the `empty` / `cons` raw telescope.
* `length` + `length_eq_scope` — the recursive binding count agrees with
  the scope index (length/scope coherence).
* `lookup` — the de Bruijn variable lookup returning the bound type with
  the weakening shift applied (§11.6.3); `Fin` is destructured via the
  propext-free `⟨0, _⟩` / `⟨k + 1, _⟩` structure matching (NOT
  `Fin.cases`, which pulls `propext`).
* `lookup_cons_zero` / `lookup_cons_succ` — definitional unfolders.

**On context "weakening".**  A whole-context renaming action
`TypingContext profile source → TypingContext profile target` is
ILL-DEFINED: a telescope of `n` bindings IS scope `n`, so it cannot be
renamed to a different scope while keeping `n` bindings.  The genuine
weakening is (i) the per-binding `RawRenaming.weaken` shift that `lookup`
threads internally, here, and (ii) the JUDGMENT-level lemma `HasType`
under `RawRenaming.weaken` — which lives with the typed weakening lemma,
not as a context primitive.

## Zero-axiom verification

Structural recursion + `rfl`-closed unfolders + one `induction` with
`dsimp only` / `rw`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- A `TypingContext profile scope` is a de Bruijn telescope of exactly
`scope` binding-type cells.  `cons` stores the new binding's type at the
scope BEFORE the binding (`RawTerm scope`), so a binding mentions only
the variables introduced earlier.  RAW spine — no `IsType`
well-formedness field (see the file header on the mutual-index wall). -/
inductive TypingContext (profile : PolyProfile) : Nat → Type
  | empty : TypingContext profile 0
  | cons {scope : Nat} (restContext : TypingContext profile scope)
      (bindingType : RawTerm scope) : TypingContext profile (scope + 1)

namespace TypingContext

/-- The number of bindings in the telescope, by structural recursion.
Equals the scope index (`length_eq_scope`); kept as an explicit recursive
count so the coherence is a CHECKED fact rather than an unstated
invariant. -/
def length {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : Nat :=
  match context with
  | .empty => 0
  | .cons restContext _ => restContext.length + 1

/-- Coherence: the recursive binding count equals the scope index.  Every
`cons` adds exactly one binding and lifts the scope by one, so the count
the telescope reports never drifts from the index it is classified by. -/
theorem length_eq_scope {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : context.length = scope := by
  induction context with
  | empty => rfl
  | cons restContext bindingType lengthOfRestEqScope =>
      dsimp only [length]
      rw [lengthOfRestEqScope]

/-- Look up the de Bruijn variable `index` in `context`, returning the
bound type weakened into the full scope.  Index `0` selects the newest
(most-recently-bound) binding; `RawRenaming.weaken` shifts the stored
`RawTerm scope` up to `RawTerm (scope + 1)` to account for the binding
the variable refers through.  Index `k + 1` recurses into the rest of
the telescope and applies the same single weakening on the way out — one
shift per binder tunneled, accumulated by the recursion (§11.6.3).

The `.empty` arm is vacuous (`Fin 0` is uninhabited) and is discharged
explicitly via `Nat.not_lt_zero` rather than left to the match compiler,
which would synthesize the impossibility through `propext`. -/
def lookup {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    RawTerm scope :=
  match context, index with
  | .empty, emptyIndex =>
      absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | .cons _ bindingType, ⟨0, _⟩ =>
      RawTerm.rename RawRenaming.weaken bindingType
  | .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      RawTerm.rename RawRenaming.weaken
        (restContext.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩)

/-- Unfolder: looking up index `0` in a `cons` returns the newest
binding's type, weakened by one. -/
theorem lookup_cons_zero {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (TypingContext.cons restContext bindingType).lookup ⟨0, isLtZeroSucc⟩ =
      RawTerm.rename RawRenaming.weaken bindingType :=
  rfl

/-- Unfolder: looking up index `position + 1` in a `cons` recurses into
the rest of the telescope and weakens the result by one. -/
theorem lookup_cons_succ {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (position : Nat) (isLtSuccSucc : position + 1 < scope + 1) :
    (TypingContext.cons restContext bindingType).lookup
        ⟨position + 1, isLtSuccSucc⟩ =
      RawTerm.rename RawRenaming.weaken
        (restContext.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩) :=
  rfl

end TypingContext
end FX1Poly.Typed
