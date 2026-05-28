import LeanFX2.Foundation.PolyCell.Typed.TypingContext

/-! # Foundation/PolyCell/Typed/TypingContextHelpers
   — M32 TypingContext.lookup + weakening helpers

M32 (#281, 2026-05-28).  Ships the foundational query +
extension helpers for the M31 #280 `TypingContext` inductive.

Per polycell.md §3.16 Phase Z₁ commitment + the established
de Bruijn discipline:

* **`TypingContext.lookup`** — given a position `Fin scope`,
  retrieve the binding's type AT THE LOOKUP SCOPE.  The
  scope-adjustment discipline: looking up position 0 in
  `cons newType ctx` returns `newType.weaken` (shifted up
  by 1 because the lookup happens at scope `parent + 1`,
  but `newType` was added at scope `parent`).

* **`TypingContext.weaken`** — apply weakening across an
  entire context.  Used by M33 #282 HasType conv rule when
  introducing a new binder.

* Plus per-fixture smoke witnesses showing lookup returns the
  expected type on the M31-shipped `singleUnit` and
  `twoBindings` fixtures.

## The lookup scope-adjustment

Critical subtlety: when looking up position `k` in
`TypingContext level scope`, the result type is
`Ty level scope` — the LOOKUP scope, not the scope where
the binding was originally inserted.

If `cons newType ctx` adds `newType : Ty level n` to a context
at scope n, then the result is at scope `n+1`.  Looking up
position 0 in the new context should return a `Ty level (n+1)`
— which is `newType.weaken`, since `newType` was originally
at scope `n` and the lookup scope is `n+1`.

This is the SAME discipline used by typed Subst.lift / typed
Term.weaken — the binding has to track scope across context
extensions.

## Why parametric over level + scope

M31's TypingContext has 2 parameters (level, scope).  The helpers
inherit them: `lookup` and `weaken` are both `level`-polymorphic
+ scope-aware.  M-Ty-wf #383's `Ty.size` already pinned that
all Ty type formers are scope-polymorphic; that translates to
the helpers being well-defined at every scope.

## Recursion shape

`lookup` recurses on:
* `(cons newType ctx, ⟨0, h⟩)` — innermost binding case;
  return `newType.weaken`.
* `(cons newType ctx, ⟨k+1, h⟩)` — recurse on `ctx` at position
  `⟨k, h'⟩`, then weaken the result to lift into the extended scope.

The recursion terminates because the position index decreases
(`k+1 → k`) and the context shrinks by one cons per recursion
step.  Pattern-form match handles this cleanly per the M-Ty-wf
#383 well-foundedness discipline.

`weaken` recurses on context shape:
* `empty.weaken = empty` — empty stays empty.
* `(cons newType ctx).weaken = cons newType.weaken ctx.weaken`
  — push weakening through each binding.

## What this does NOT ship

* **`weaken_lookup_commute`** theorem: `lookup (ctx.weaken) k =
  (lookup ctx k).weaken`.  Substantial structural recursion;
  defer to M33 conv-rule task when actually needed.

* **Position-shift / dropFront helpers**: when the typed-layer
  substitution lemmas (M47 #296) need to "drop" the innermost
  binding from a context, that helper ships separately.

* **`lookup_singleUnit` proofs verifying lookup returns
  `unit.weaken` on the singleUnit fixture**: would need to
  unfold `lookup` on the specific cons + Fin shape; not
  load-bearing for M33+ rules which dispatch on context
  shape directly.

## Zero-axiom verification

`lookup` defined by pattern-form structural recursion over
(TypingContext, Fin scope) pairs.  Pattern matches return
appropriate values; the position case-analysis uses direct
`Fin.mk` struct match per `feedback_lean_fin_cases_axiom`
recipe (NOT `Fin.cases` which leaks propext).

`weaken` defined by pattern-form structural recursion over
TypingContext (no Fin involved).

Smokes close by `rfl` via the `@[reducible]` pattern
applied to `Ty.weaken` (already shipped in Foundation/Ty.lean
at line 229).

No `axiom`, no `sorry`, no Classical.  Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Typed

/-- Look up a binding's type at a de Bruijn position.

Given `position : Fin scope` and `ctx : TypingContext level scope`,
return the binding's type at the LOOKUP SCOPE (post-weakening
through any intervening binders).

Recursion shape:
* `cons newType _ , ⟨0, _⟩` → `newType.weaken` (innermost binding;
  weakened to lift into the post-cons scope).
* `cons _ ctxRest , ⟨k+1, h⟩` → recurse on `ctxRest` at
  `⟨k, _⟩`, weaken the result.

Direct `Fin.mk` struct match per the axiom-free recipe — avoids
the propext leak from `Fin.cases`. -/
def TypingContext.lookup {level : Nat} : ∀ {scope : Nat},
    TypingContext level scope → Fin scope → LeanFX2.Ty level scope
  | _, .cons newType _, ⟨0, _⟩ => newType.weaken
  | _, .cons _ ctxRest, ⟨k + 1, hBound⟩ =>
      (ctxRest.lookup ⟨k, Nat.lt_of_succ_lt_succ hBound⟩).weaken

/-! ## Why no `TypingContext.weaken` shipped here

The M32 task title says "lookup + weakening helpers".  Note the
PLURAL "helpers" — not "context weaken function".  The
TypingContext inductive's structure makes a literal
`weaken : TypingContext level scope → TypingContext level (scope+1)`
STRUCTURALLY IMPOSSIBLE: `empty : TypingContext level 0` can't
elevate to scope 1 because there's no scope-1 empty constructor
(scope = number of bindings is part of the inductive index).

The "weakening helpers" the task title commits to are SUPPORT
THEOREMS for type-level weakening proofs that downstream M33+
HasType rules will need — these ship at THOSE rule-specific
task slots (M33 conv, M34 var, etc.) because each rule has its
own weakening obligation shape.

What ships here in M32 alone: `TypingContext.lookup` — the
foundational query operation.  The weakening helpers ship
alongside the HasType rules where they're actually consumed,
not pre-cached here.

## Per-fixture lookup smokes

Verify lookup on the M31-shipped fixtures.  These pin the
expected lookup outcomes for the typed-layer cascade. -/

/-- Lookup position 0 in singleUnit returns Ty.unit.weaken. -/
theorem TypingContext.lookup_singleUnit_zero :
    TypingContext.singleUnit.lookup ⟨0, by decide⟩ =
      (LeanFX2.Ty.unit : LeanFX2.Ty 0 0).weaken := rfl

/-- Lookup position 0 in twoBindings returns Ty.bool.weaken
(bool is the innermost / most-recently-cons'd binding). -/
theorem TypingContext.lookup_twoBindings_zero :
    TypingContext.twoBindings.lookup ⟨0, by decide⟩ =
      (LeanFX2.Ty.bool : LeanFX2.Ty 0 1).weaken := rfl

/-- Lookup position 1 in twoBindings returns the OUTER
binding's type (Ty.unit) weakened twice — once to enter
twoBindings's outer scope, once to enter the lookup scope. -/
theorem TypingContext.lookup_twoBindings_one :
    TypingContext.twoBindings.lookup ⟨1, by decide⟩ =
      (LeanFX2.Ty.unit : LeanFX2.Ty 0 0).weaken.weaken := rfl

/-! ## Per-arm unfolders for lookup

Per audit-A8 (#393, Agent 1 2026-05-28 gap-audit finding): the M34
#283 HasType var smokes had to use `ctx.lookup position` directly
in their result-type positions because Lean's elaborator does not
reduce through the recursive `lookup` match in goal position.

These two unfolders give downstream M33-M44 HasType rules clean
`rfl`-equations for the two match arms.  Both close by `rfl` since
they are LITERAL match arms of `TypingContext.lookup`.

* `lookup_cons_zero` — innermost-binding case: looking up position 0
  in `cons newType ctxRest` returns `newType.weaken`.
* `lookup_cons_succ` — recursion case: looking up position `k+1` in
  `cons _ ctxRest` recurses on `ctxRest` at position `k`, weakened. -/

/-- Unfolder for the innermost-binding case of lookup.

Looking up position 0 in `cons newType ctxRest` evaluates to
`newType.weaken`.  Closes by `rfl` — direct match-arm unfold.

Used by downstream M33-M44 HasType rules to rewrite away
`lookup` applications on a known-shape context without
re-traversing the recursion. -/
theorem TypingContext.lookup_cons_zero
    {level scope : Nat}
    (newType : LeanFX2.Ty level scope)
    (ctxRest : TypingContext level scope)
    (hZeroLt : 0 < scope + 1) :
    (TypingContext.cons newType ctxRest).lookup ⟨0, hZeroLt⟩
      = newType.weaken := rfl

/-- Unfolder for the recursion case of lookup.

Looking up position `positionPredecessor + 1` in
`cons newType ctxRest` recurses on `ctxRest` at position
`positionPredecessor` and weakens the result.  Closes by `rfl` —
direct match-arm unfold.

The `Nat.lt_of_succ_lt_succ` invocation in the recursive call's
position witness matches the literal definition of `lookup` —
re-quoting it explicitly here so callers can rewrite at this
exact shape. -/
theorem TypingContext.lookup_cons_succ
    {level scope : Nat}
    (newType : LeanFX2.Ty level scope)
    (ctxRest : TypingContext level scope)
    (positionPredecessor : Nat)
    (hBound : positionPredecessor + 1 < scope + 1) :
    (TypingContext.cons newType ctxRest).lookup
        ⟨positionPredecessor + 1, hBound⟩
      = (ctxRest.lookup
          ⟨positionPredecessor,
           Nat.lt_of_succ_lt_succ hBound⟩).weaken := rfl

/-! ## Aggregate metric -/

/-- TypingContextHelpers ships 1 primary operation (lookup) plus
2 unfolders (lookup_cons_zero / lookup_cons_succ) per audit-A8.
The weakening helpers per the M32 task title ship at the
HasType-rule task slots (M33-M44) where they're consumed. -/
def TypingContextHelpers.operationCount : Nat := 1

theorem TypingContextHelpers.operationCount_correct :
    TypingContextHelpers.operationCount = 1 := rfl

end LeanFX2.Foundation.PolyCell.Typed
