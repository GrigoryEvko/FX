import LeanFX2.Foundation.IsClosedTy
import LeanFX2.Reduction.StepStar

/-! # Term/SubjectReductionGeneral — IsClosedTy-indexed subject reduction

Generalizes the per-type SR cascade (`Step.preserves_ty_unit / bool /
nat`) to arbitrary closed types via the `IsClosedTy` predicate.

## Architecture

This file is the *single source of truth* for closed-type subject
reduction.  `Term/SubjectReduction.lean` re-exports the per-type
specializations (`Step.preserves_ty_unit / bool / nat`) as one-line
corollaries via `IsClosedTy.{unit, bool, nat}` witnesses.

## Building blocks

* `Ty.subst0_raw_invariance_unit / bool / nat` — leaf-case lemmas
  proving `T.subst0 α raw₁ = leafType → T.subst0 α raw₂ = leafType`.
  These are needed in the `unit`/`bool`/`nat` cases of the general
  invariance theorem.

## Headline lemma

`Ty.subst0_raw_invariance_isClosedTy` says: if
`someType.subst0 argType raw1 = closedType` for some `IsClosedTy
closedType`, then `someType.subst0 argType raw2 = closedType` for any
other `raw2`.

Proof: induction on `resultIsClosed`, the `IsClosedTy` witness.

* `unit`/`bool`/`nat` cases dispatch to the per-type invariance
  lemmas defined above.
* `arrow`/`listType`/`optionType`/`eitherType` cases case on
  `someType` (single level), use injectivity to extract inner
  reductions, and recurse via the IH on inner closed witnesses.

## Why induct on `resultIsClosed`, not `someType`

`someType : Ty level (scope + 1)` has a non-variable index (`scope +
1`) which blocks Lean's `induction` tactic per pitfall P-2.
Inducting on `resultIsClosed : IsClosedTy closedType` instead places
the recursion at the closed-witness level — `closedType : Ty level
scope` has free variable indices, so induction works cleanly.  The
IH for inner closed witnesses (e.g., `closedDomain` inside
`IsClosedTy.arrow closedDomain closedCodomain`) is exactly the
inductive-hypothesis form we need for the recursive `Ty.arrow d c`
sub-case.

## Pitfalls + mitigations

* P-1 (match-compiler propext on big inductives): full enumeration
  of `Ty` ctors via `cases someType with | ctor1 => ... | ctor2 =>
  ...` (no wildcards).
* P-2 (multi-Nat-index propext): scope-shifted index sidestepped
  via induction on `resultIsClosed` rather than `someType`.

## Downstream consumers

* `Step.preserves_isClosedTy` (later in this file) — uses the
  invariance lemma in the β-rule case.
* `StepStar.preserves_isClosedTy` — chain extension.
* M06/M07 (#1275/#1276) — closed by `Step.preserves_ty_arrow /
  listType / optionType / eitherType` corollaries.
* `Term/SubjectReduction.lean` — re-exports per-type specializations.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Substitution invariance for closed-type leaves

These three theorems are the building blocks for the general
`Ty.subst0_raw_invariance_isClosedTy`.  Each handles one leaf
ctor (`unit`, `bool`, `nat`) by case analysis on `someType` — the
result type fixes the ctor uniquely except when `someType` is a
`tyVar 0` looking up to the leaf via the singleton substitution. -/

/-- Substitution-raw-invariance for `Ty.unit`.  If `someType`'s
single-variable substitution reduces to `Ty.unit`, the choice of
raw argument is irrelevant.  Discharged by case analysis on
`someType` — only `Ty.unit` and `Ty.tyVar ⟨0, _⟩` survive the
filter. -/
theorem Ty.subst0_raw_invariance_unit
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToUnit : someType.subst0 argType raw1 = Ty.unit) :
    someType.subst0 argType raw2 = Ty.unit := by
  cases someType with
  | unit => rfl
  | bool => nomatch someTypeReducesToUnit
  | nat => nomatch someTypeReducesToUnit
  | arrow _ _ => nomatch someTypeReducesToUnit
  | piTy _ _ => nomatch someTypeReducesToUnit
  | sigmaTy _ _ => nomatch someTypeReducesToUnit
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToUnit
      | succ k => nomatch someTypeReducesToUnit
  | id _ _ _ => nomatch someTypeReducesToUnit
  | listType _ => nomatch someTypeReducesToUnit
  | optionType _ => nomatch someTypeReducesToUnit
  | eitherType _ _ => nomatch someTypeReducesToUnit

/-- Substitution-raw-invariance for `Ty.bool`. -/
theorem Ty.subst0_raw_invariance_bool
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToBool : someType.subst0 argType raw1 = Ty.bool) :
    someType.subst0 argType raw2 = Ty.bool := by
  cases someType with
  | unit => nomatch someTypeReducesToBool
  | bool => rfl
  | nat => nomatch someTypeReducesToBool
  | arrow _ _ => nomatch someTypeReducesToBool
  | piTy _ _ => nomatch someTypeReducesToBool
  | sigmaTy _ _ => nomatch someTypeReducesToBool
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToBool
      | succ k => nomatch someTypeReducesToBool
  | id _ _ _ => nomatch someTypeReducesToBool
  | listType _ => nomatch someTypeReducesToBool
  | optionType _ => nomatch someTypeReducesToBool
  | eitherType _ _ => nomatch someTypeReducesToBool

/-- Substitution-raw-invariance for `Ty.nat`. -/
theorem Ty.subst0_raw_invariance_nat
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToNat : someType.subst0 argType raw1 = Ty.nat) :
    someType.subst0 argType raw2 = Ty.nat := by
  cases someType with
  | unit => nomatch someTypeReducesToNat
  | bool => nomatch someTypeReducesToNat
  | nat => rfl
  | arrow _ _ => nomatch someTypeReducesToNat
  | piTy _ _ => nomatch someTypeReducesToNat
  | sigmaTy _ _ => nomatch someTypeReducesToNat
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToNat
      | succ k => nomatch someTypeReducesToNat
  | id _ _ _ => nomatch someTypeReducesToNat
  | listType _ => nomatch someTypeReducesToNat
  | optionType _ => nomatch someTypeReducesToNat
  | eitherType _ _ => nomatch someTypeReducesToNat

/-- Generalized substitution-raw-invariance.  For any `someType : Ty
level (scope+1)`, if `someType.subst0 argType raw1` equals a closed
type, then `someType.subst0 argType raw2` equals the same closed
type — closed types contain no `Ty.id` endpoints, so the raw
substitution component is irrelevant.

Proof by induction on the closed witness (`resultIsClosed`); the
`someType`-shape cases dispatch via single-level `cases someType`. -/
theorem Ty.subst0_raw_invariance_isClosedTy {level scope : Nat}
    (someType : Ty level (scope + 1))
    (argType : Ty level scope)
    (raw1 raw2 : RawTerm scope)
    {closedType : Ty level scope}
    (resultIsClosed : IsClosedTy closedType)
    (someTypeReduces : someType.subst0 argType raw1 = closedType) :
    someType.subst0 argType raw2 = closedType := by
  induction resultIsClosed generalizing someType raw1 raw2 with
  | unit =>
      exact Ty.subst0_raw_invariance_unit someTypeReduces
  | bool =>
      exact Ty.subst0_raw_invariance_bool someTypeReduces
  | nat =>
      exact Ty.subst0_raw_invariance_nat someTypeReduces
  | arrow closedDomain closedCodomain ihDomain ihCodomain =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow domainSrc codomainSrc =>
          injection someTypeReduces with _ hDomain hCodomain
          have domainInv := ihDomain domainSrc raw1 raw2 hDomain
          have codomainInv := ihCodomain codomainSrc raw1 raw2 hCodomain
          show Ty.arrow (domainSrc.subst0 argType raw2)
                        (codomainSrc.subst0 argType raw2) = _
          rw [domainInv, codomainInv]
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
  | listType closedElement ihElement =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType elementSrc =>
          injection someTypeReduces with _ hElement
          have elementInv := ihElement elementSrc raw1 raw2 hElement
          show Ty.listType (elementSrc.subst0 argType raw2) = _
          rw [elementInv]
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
  | optionType closedElement ihElement =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType elementSrc =>
          injection someTypeReduces with _ hElement
          have elementInv := ihElement elementSrc raw1 raw2 hElement
          show Ty.optionType (elementSrc.subst0 argType raw2) = _
          rw [elementInv]
      | eitherType _ _ => nomatch someTypeReduces
  | eitherType closedLeft closedRight ihLeft ihRight =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType leftSrc rightSrc =>
          injection someTypeReduces with _ hLeft hRight
          have leftInv := ihLeft leftSrc raw1 raw2 hLeft
          have rightInv := ihRight rightSrc raw1 raw2 hRight
          show Ty.eitherType (leftSrc.subst0 argType raw2)
                              (rightSrc.subst0 argType raw2) = _
          rw [leftInv, rightInv]

/-! ## Generalized step-preservation theorem

`Step.preserves_isClosedTy` follows the established tactic-combo
pattern from `Step.preserves_ty_unit / bool / nat`: induction on
the Step, dispatch each constructor case via `first` over four
tactic fallbacks.  The 4th fallback uses the new general invariance
lemma. -/

/-- Generalized subject reduction: every `Step` from a closed-typed
source produces a target with the same closed type.  Replaces the
per-type `Step.preserves_ty_unit / bool / nat` cascade with a single
inductive proof parameterized by the closed witness. -/
theorem Step.preserves_isClosedTy
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {closedType : Ty level scope}
    (sourceClosed : IsClosedTy closedType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsClosed : sourceType = closedType) :
    targetType = closedType := by
  induction someStep
  all_goals
    first
      | exact sourceIsClosed
      | (subst sourceIsClosed; rfl)
      | rfl
      | exact Ty.subst0_raw_invariance_isClosedTy _ _ _ _
                sourceClosed sourceIsClosed
      | (subst sourceIsClosed; exact Ty.weaken_subst_singleton _ _ _)

/-- StepStar lift of `Step.preserves_isClosedTy`: closed-typed
StepStar chains preserve the closed target type.  Trivial chain
induction on the head + tail. -/
theorem StepStar.preserves_isClosedTy
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {closedType : Ty level scope}
    (sourceClosed : IsClosedTy closedType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsClosed : sourceType = closedType) :
    targetType = closedType := by
  induction chain with
  | refl _ => exact sourceIsClosed
  | step head _ tailIH =>
      exact tailIH (Step.preserves_isClosedTy sourceClosed head sourceIsClosed)

/-! ## Specialized SR for closed-type families

Closes kernel-sprint M06 (#1275 — SR at arrow types) and M07
(#1276 — SR at parametric types: listType, optionType,
eitherType).  Each is a one-line corollary of
`Step.preserves_isClosedTy` (and StepStar variant), instantiated
at the matching `IsClosedTy` ctor with closed-component
witnesses.

These lemmas only apply when the type's *components* are also
closed.  For `Ty.arrow Ty.nat Ty.bool` this is trivial; for
`Ty.arrow (Ty.tyVar 0) Ty.bool` it is not, and a deeper SR
(general open-types Phase 7.D) is needed.  Most user-visible
arrow types in compiled FX are concrete and fall in scope.
-/

/-- Subject reduction at `Ty.arrow domain codomain` when both
component types are closed.  Closes M06 (#1275). -/
theorem Step.preserves_ty_arrow
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsArrow : sourceType = Ty.arrow domainType codomainType) :
    targetType = Ty.arrow domainType codomainType :=
  Step.preserves_isClosedTy
    (IsClosedTy.arrow closedDomain closedCodomain) someStep sourceIsArrow

/-- StepStar lift of `Step.preserves_ty_arrow`. -/
theorem StepStar.preserves_ty_arrow
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsArrow : sourceType = Ty.arrow domainType codomainType) :
    targetType = Ty.arrow domainType codomainType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.arrow closedDomain closedCodomain) chain sourceIsArrow

/-- Subject reduction at `Ty.listType element` when element type
is closed.  First half of M07 (#1276). -/
theorem Step.preserves_ty_listType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsList : sourceType = Ty.listType elementType) :
    targetType = Ty.listType elementType :=
  Step.preserves_isClosedTy
    (IsClosedTy.listType closedElement) someStep sourceIsList

/-- StepStar lift of `Step.preserves_ty_listType`. -/
theorem StepStar.preserves_ty_listType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsList : sourceType = Ty.listType elementType) :
    targetType = Ty.listType elementType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.listType closedElement) chain sourceIsList

/-- Subject reduction at `Ty.optionType element` when element
type is closed.  Second half of M07 (#1276). -/
theorem Step.preserves_ty_optionType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsOption : sourceType = Ty.optionType elementType) :
    targetType = Ty.optionType elementType :=
  Step.preserves_isClosedTy
    (IsClosedTy.optionType closedElement) someStep sourceIsOption

/-- StepStar lift of `Step.preserves_ty_optionType`. -/
theorem StepStar.preserves_ty_optionType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsOption : sourceType = Ty.optionType elementType) :
    targetType = Ty.optionType elementType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.optionType closedElement) chain sourceIsOption

/-- Subject reduction at `Ty.eitherType left right` when both
component types are closed.  Third half of M07 (#1276). -/
theorem Step.preserves_ty_eitherType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {leftType rightType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsEither : sourceType = Ty.eitherType leftType rightType) :
    targetType = Ty.eitherType leftType rightType :=
  Step.preserves_isClosedTy
    (IsClosedTy.eitherType closedLeft closedRight) someStep sourceIsEither

/-- StepStar lift of `Step.preserves_ty_eitherType`. -/
theorem StepStar.preserves_ty_eitherType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {leftType rightType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsEither : sourceType = Ty.eitherType leftType rightType) :
    targetType = Ty.eitherType leftType rightType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.eitherType closedLeft closedRight) chain sourceIsEither

end LeanFX2
