import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.Mode

/-! # Ty — types indexed by `(level, scope)`.

`Ty level scope : Type` is the type-level syntax indexed by universe level
and de Bruijn scope size.

## Constructor list

Standard MLTT base + dependent + Identity + Modal + Refinement:

* `unit`, `bool`, `nat`
* `arrow (dom cod : Ty level scope)` — non-dependent function type
* `piTy (dom : Ty level scope) (cod : Ty level (scope+1))` — dependent Π
* `sigmaTy (first : Ty level scope) (second : Ty level (scope+1))` — dependent Σ
* `tyVar (position : Fin scope)` — type variable (for Π/Σ codomains referencing the binder)
* `id (carrier : Ty level scope) (left right : RawTerm scope)` — Identity type
* `universe (level : Nat) (boundOk : level < universeBound)` — universe type
* `list (element : Ty level scope)`, `option (element : Ty level scope)`
* `either (left right : Ty level scope)`
* `modal (modality : Modality m₁ m₂) (inner : Ty level scope)` — modally-decorated type
* `refine (base : Ty level scope) (predicate : RefinePredicate base)` — refinement type

## Cumulativity policy

**Cumulativity is a Conv rule, not a Ty constructor.**  lean-fx had `Ty.cumul`
constructor experimentally in v1.29 — it was reverted because cumulativity
between universe levels generates Subst incoherence (base's tyVars expect
Subst at levelLow but outer call passes Subst at levelHigh, per
`feedback_lean_cumul_subst_mismatch.md`).  lean-fx-2 puts cumulativity in
`Reduction/Conv.lean` as a definitional-conversion rule between universe
levels.  Subtype semantics, not constructor-level distinction.

## Identity types — endpoints as RawTerm

`id carrier left right` carries the endpoint terms as `RawTerm scope` values,
NOT as typed `Term` values.  This is the standard MLTT-formalisation pattern
(BiSikkel, lean4-tt-in-lean4, Coq HoTT).  Forcing endpoints to be typed Term
values would require Term to be defined before Ty — which would force a mutual
inductive definition that Lean 4's strict-positivity check rejects (per
`feedback_lean_mutual_index_rule.md`).

The trade-off: typed Term values' raw projections must align with their
identity-type endpoints.  In lean-fx-2 this is automatic because Term's
raw index IS the projection.

## Modal types

`modal modality inner` decorates `inner` with a 1-cell `modality : Modality m₁ m₂`.
The decoration carries the modal computation rules (modElim of modIntro reduces,
subsume composition, etc.) — these live in Layer 6.

## Refinement types

`refine base predicate` is a subtype: values of `refine base p` are values
of `base` satisfying `p`.  Predicate is decidable in the Lean-internal fragment;
SMT-cert-recheckable for the broader fragment.  Layer 8 details.

## Decidable equality

`deriving DecidableEq` — works for inductive families with finite indices,
provided the predicate fields are also DecidableEq.  Manual instance for
`refine` (since `RefinePredicate` carries a `Decidable` instance, not raw decision).

## Dependencies

* `Foundation/RawTerm.lean` — for Identity-type endpoints
* `Foundation/Mode.lean` — for Modality 1-cells

## Downstream

* `Foundation/Subst.lean` — `Ty.subst` operates structurally on Ty
* `Foundation/Context.lean` — Ctx stores `Ty` values
* `Term.lean` — Term's second index is `Ty`
-/

namespace LeanFX2

-- TODO: Ty inductive (per constructor list above)
-- TODO: deriving DecidableEq (with manual instance for `refine` ctor)
-- TODO: Ty.weaken via Renaming.weaken
-- TODO: Ty.rename via structural recursion
-- TODO: Ty.subst via structural recursion (consults Subst.forTy)

end LeanFX2
