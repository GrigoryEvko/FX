import LeanFX2.Term.SubjectReductionGeneral

/-! # Term/SubjectReductionUniverse — SR at `Ty.universe` types.

CUMUL-6.1 / CUMUL-6.2 / CUMUL-6.3 deliverable: ship subject
reduction at `Ty.universe` types via specialization of
`Step.preserves_isClosedTy` / `StepStar.preserves_isClosedTy`.

## Architecture

`Ty.universe` is a closed leaf in the `IsClosedTy` predicate (see
`Foundation/IsClosedTy.lean`).  Both Step and StepStar already
have generic preservation at any `IsClosedTy` source type
(`Step.preserves_isClosedTy`, `StepStar.preserves_isClosedTy` in
`SubjectReductionGeneral.lean`).  This file specializes them at
the universe leaf.

## What ships

* `Step.preserves_ty_universe` — reducing a Term at `Ty.universe lvl`
  preserves the universe type.  One-line corollary of
  `Step.preserves_isClosedTy` at the `IsClosedTy.universe` witness.

* `StepStar.preserves_ty_universe` — chain extension via
  `StepStar.preserves_isClosedTy` at the same witness.

## What does NOT ship (and why)

* `Step.preserves_ty_universe_via_cumulUpInner` — would address
  reductions INSIDE `Term.cumulUp`'s `lowerTerm` payload.  Blocked
  on CUMUL-3.1 (`Step.cumulUpInner` not yet shipped).  Currently
  no Step rule fires INSIDE a `cumulUp`-wrapped term, so universe
  type preservation holds vacuously for that shape — there are no
  reductions to preserve.

* `Conv.preserves_ty_universe` — needs reverse SR (deferred per
  `SubjectReductionGeneral.lean` line 875).

## CUMUL-6 task closure

* CUMUL-6.1 (#1423): closed by `Step.preserves_ty_universe`.
* CUMUL-6.2 (#1424): smoke audit demonstrates SR at universe.
* CUMUL-6.3 (#1425): closed by `StepStar.preserves_ty_universe`.

The `cumulUpInner` reduction shape — reductions INSIDE the
cumulUp's `lowerTerm` payload — awaits CUMUL-3.1.  Until that
ships, no Step reduces a `cumulUp`-wrapped Term, so there is no
test case to write for the inner-shape preservation.  This is
documented but not papered over with a fake `sorry`-blocked
theorem.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Subject reduction at `Ty.universe universeLevel`.  Reducing a
Term whose source type is `Ty.universe universeLevel ...` produces
a Term whose target type is also `Ty.universe universeLevel ...`.

One-line corollary of the generic `Step.preserves_isClosedTy` at
the closed-universe witness.

Closes CUMUL-6.1 (#1423). -/
theorem Step.preserves_ty_universe
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 ≤ level)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsUniverse :
      sourceType = Ty.universe (level := level) (scope := scope)
                               universeLevel levelLe) :
    targetType = Ty.universe (level := level) (scope := scope)
                             universeLevel levelLe :=
  Step.preserves_isClosedTy
    (IsClosedTy.universe (level := level) (scope := scope)
                         universeLevel levelLe)
    someStep sourceIsUniverse

/-- StepStar lift of `Step.preserves_ty_universe`: closed-universe
chains preserve the universe target type.

Closes CUMUL-6.3 (#1425). -/
theorem StepStar.preserves_ty_universe
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 ≤ level)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsUniverse :
      sourceType = Ty.universe (level := level) (scope := scope)
                               universeLevel levelLe) :
    targetType = Ty.universe (level := level) (scope := scope)
                             universeLevel levelLe :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.universe (level := level) (scope := scope)
                         universeLevel levelLe)
    chain sourceIsUniverse

end LeanFX2
