import LeanFX2.Foundation.Subst

/-! # Foundation/IsClosedTyAtBinder — Prop-valued binder-Ty closure witness

A `Ty level (scope + 1)` is **closed at the var-0 binder** when it is
in the image of `Ty.weaken` — equivalently, when every type-variable
reference inside it sits at `succ _` so the Ty can be lowered across
one outer binder.

## Why this matters

The typed `Step.par.pair` cong rule (`ParRed/ParInductive/Inductive.lean
:94-107`) has source and target Term children at potentially DIFFERENT
secondType substitutions:

  * `secondValueSource : Term context (secondType.subst0 firstType firstRawSource) ...`
  * `secondValueTarget : Term context (secondType.subst0 firstType firstRawTarget) ...`

When `firstRawSource ↝ firstRawTarget` under `RawStep.par`, the
secondLift IH gives a Term at the **source's** subst — but constructing
`Term.pair firstValueTarget secondValueTarget` demands a Term at the
**target's** subst.  Bridging the two requires either:

  1. A Conv-cast across the subst0 difference (heavy machinery), or
  2. A witness that the subst0 difference is **definitionally trivial**.

Path 2 ships cleanly when `secondType` is in the image of `Ty.weaken`
— the var-0 binder reference is absent, so any singleton substitution
yields the same result.  That witness is this file's `IsClosedTyAtBinder`
predicate.

`IsClosedTy` (Foundation/IsClosedTy.lean:108-152) covers ground-scope
type closure (`Ty level scope`); this file covers the dual case of
binder-scope closure (`Ty level (scope + 1)`) — Σ secondType, Π
codomainType, and any other type that lives under an introduced binder.

## Definition shape — existential wrapper

Following the same architectural pattern as
`Foundation/IsClosedRawTerm.lean` (commit 57f92b28 + 623216ab),
the predicate is the existential

  `IsClosedTyAtBinder someType ↔ ∃ inner : Ty level scope, someType = inner.weaken`

This avoids declaring a 25-ctor inductive paralleling `Ty` (the
inductive form would parallel `IsClosedTy` but at scope+1 — ~150 LoC).
The existential is Prop-valued and supports witness extraction via
`obtain ⟨inner, weakenEq⟩ := closed`.

## Load-bearing corollary

`subst0_invariant` proves that when secondType is closed at the binder,
varying `argRaw` in `secondType.subst0 argType argRaw` does not change
the result.  Direct corollary of `Ty.weaken_subst_singleton` (which
shows `inner.weaken.subst (Subst.singleton argType argRaw) = inner` for
any singleton).

## Zero-axiom

Every declaration here is a `def` / `theorem` with `#print axioms`
clean.  The infrastructure leans entirely on `Ty.weaken_subst_singleton`,
itself zero-axiom (Foundation/Subst.lean:671).

## Downstream consumers

* `unblock-A.leaf.pair` (#2010) — `lift_full_pair` SR helper for the
  Σ-introduction takes an `IsClosedTyAtBinder secondType` hypothesis;
  the cong arm's secondLift result is realigned via `subst0_invariant`.
* `unblock-A.leaf.equivApply` (#2013) — equivalent infrastructure for
  the dependent equiv-codomain case.
* `D2.5.5/6/7 transp* cascade` — when secondType / codomainType is
  closed, the cubical-β cd-cascade collapses.
-/

namespace LeanFX2

/-- A binder-scope type is **closed at the binder** iff it is in the
image of `Ty.weaken`.  Equivalent to "no var-0 reference anywhere in the
type", stated as the existential `∃ inner, someType = inner.weaken` so
the inner can be extracted directly. -/
def IsClosedTyAtBinder {level scope : Nat}
    (someType : Ty level (scope + 1)) : Prop :=
  ∃ inner : Ty level scope, someType = inner.weaken

/-- From a syntactic weaken-equation, produce the `IsClosedTyAtBinder`
witness directly. -/
theorem IsClosedTyAtBinder.of_weaken_eq {level scope : Nat}
    {someType : Ty level (scope + 1)} {inner : Ty level scope}
    (weakenEq : someType = inner.weaken) :
    IsClosedTyAtBinder someType :=
  ⟨inner, weakenEq⟩

/-- The weakened form of any type is trivially closed at the
incremented scope — `inner.weaken = inner.weaken` is the witness. -/
theorem IsClosedTyAtBinder.weaken_self {level scope : Nat}
    (inner : Ty level scope) :
    IsClosedTyAtBinder (inner.weaken : Ty level (scope + 1)) :=
  ⟨inner, rfl⟩

/-- Convenience: extract the inner type and the witness equation
from a closed binder-Ty. -/
theorem IsClosedTyAtBinder.imp_weaken {level scope : Nat}
    {someType : Ty level (scope + 1)} (closed : IsClosedTyAtBinder someType) :
    ∃ inner : Ty level scope, someType = inner.weaken :=
  closed

/-- **Load-bearing subst0-invariance lemma.**  A binder-Ty closed at
the binder is invariant under singleton substitution — varying `argRaw`
yields the same result.  Direct corollary of `Ty.weaken_subst_singleton`:
substituting any singleton through a weakened Ty annihilates the
singleton, recovering the inner.

This is the typed-Ty counterpart to `IsClosedRawTerm.subst_singleton_invariant`
(Foundation/IsClosedRawTerm.lean:113) and underpins the SR cascade for
type-formers whose binder-scope payload depends on a singleton subst.
The downstream Σ-cong reconstruction discharges the source/target
subst0 mismatch by transporting `secondValueSource` directly. -/
theorem IsClosedTyAtBinder.subst0_invariant {level scope : Nat}
    {someType : Ty level (scope + 1)} (closed : IsClosedTyAtBinder someType)
    (argType : Ty level scope) (raw1 raw2 : RawTerm scope) :
    someType.subst0 argType raw1 = someType.subst0 argType raw2 := by
  obtain ⟨inner, weakenEq⟩ := closed
  subst weakenEq
  show inner.weaken.subst (Subst.singleton argType raw1) =
       inner.weaken.subst (Subst.singleton argType raw2)
  rw [Ty.weaken_subst_singleton, Ty.weaken_subst_singleton]

/-- Stronger form: substituting `someType.subst0 argType argRaw` yields
the **specific** `inner` named by the witness — useful when the
downstream SR proof needs to identify the result with a fixed term, not
merely compare two substitutions. -/
theorem IsClosedTyAtBinder.subst0_eq_inner {level scope : Nat}
    {someType : Ty level (scope + 1)} {inner : Ty level scope}
    (weakenEq : someType = inner.weaken)
    (argType : Ty level scope) (argRaw : RawTerm scope) :
    someType.subst0 argType argRaw = inner := by
  subst weakenEq
  exact Ty.weaken_subst_singleton inner argType argRaw

end LeanFX2
