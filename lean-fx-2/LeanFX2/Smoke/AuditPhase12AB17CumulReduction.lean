import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Bridge
import LeanFX2.Term.SubjectReductionUniverse

/-! # Smoke/AuditPhase12AB17CumulReduction — Step.cumulUpInner audit.

Phase 12.A.B17 (CUMUL-3.1..3.5).  Audits the new `Step.cumulUpInner`
ctor and its parallel-reduction analog `Step.par.cumulUpInnerCong`,
plus their downstream cascades through:

* `Step.toPar` — single Step lifts to parallel
* `Step.toConvCumul` — single Step lifts to ConvCumul
* `Step.par.toRawBridge` — typed parallel projects to raw parallel
* `Step.preserves_isClosedTy` (general SR) — universe types
  preserved through cumulUpInner

## What ships

* `Step.cumulUpInner` (Reduction/Step.lean) — cong rule that
  reduces inside `Term.cumulUp`'s `lowerTerm` payload.  First Step
  ctor that bridges different scope/context parameterizations.
* `Step.par.cumulUpInnerCong` (Reduction/ParRed.lean) — parallel
  analog mirroring the same shape.
* `Step.toPar` extended with `cumulUpInner` arm — lifts a single
  inner Step to parallel via `Step.par.cumulUpInnerCong`.
* `Step.toConvCumul` extended with `cumulUpInner` arm — lifts to
  `ConvCumul.cumulUpCong` after IH.
* `Step.par.toRawBridge` extended with `cumulUpInnerCong` arm —
  the raw projection is reflexive (both source and target raw are
  the constant `RawTerm.universeCode innerLevel.toNat`).
* `Step.preserves_isClosedTy` extended (via existing `all_goals
  first` dispatcher) — handles the `cumulUpInner` case via
  `subst sourceIsClosed; rfl` since source and target Term both
  type at `Ty.universe higherLevel _`.

## Audit gates

Every shipped declaration is gated by `#print axioms` reporting
"does not depend on any axioms" under strict policy.

## Smoke examples

Each example demonstrates a `Step.cumulUpInner` lifting cleanly
through the existing infrastructure: parallel reduction, ConvCumul
bridge, raw projection, and subject reduction.
-/

namespace LeanFX2

#print axioms Step.toPar
#print axioms Step.toConvCumul
#print axioms Step.par.toRawBridge
#print axioms Step.preserves_isClosedTy
#print axioms StepStar.preserves_isClosedTy
#print axioms Step.preserves_ty_universe
#print axioms StepStar.preserves_ty_universe

/-! ## Smoke: Step.cumulUpInner lifts to parallel reduction. -/

/-- Step.cumulUpInner lifts to a parallel reduction inside cumulUp. -/
example
    {mode : Mode} {scopeLow scope : Nat}
    {innerLevel lowerLevel higherLevel : UniverseLevel}
    {cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat}
    {cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {lowerSource lowerTarget :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)}
    (innerStep : Step lowerSource lowerTarget) :
    Step.par
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerSource)
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerTarget) :=
  Step.toPar (Step.cumulUpInner innerLevel lowerLevel higherLevel
                                cumulOkLow cumulOkHigh cumulMonotone
                                innerStep)

/-! ## Smoke: Step.cumulUpInner lifts to ConvCumul. -/

/-- Step.cumulUpInner lifts to a ConvCumul.cumulUpCong witness. -/
example
    {mode : Mode} {scopeLow scope : Nat}
    {innerLevel lowerLevel higherLevel : UniverseLevel}
    {cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat}
    {cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {lowerSource lowerTarget :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)}
    (innerStep : Step lowerSource lowerTarget) :
    ConvCumul
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerSource)
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerTarget) :=
  Step.toConvCumul (Step.cumulUpInner innerLevel lowerLevel higherLevel
                                       cumulOkLow cumulOkHigh cumulMonotone
                                       innerStep)

/-! ## Smoke: Step.cumulUpInner subject reduction at universe types.

The cumulUp-wrapped Term inhabits `Ty.universe higherLevel ...`,
and reduction inside the lower payload preserves that universe
type.  This is the non-vacuous case of CUMUL-6.2 unlocked by
CUMUL-3.1's shipping. -/

/-- Step.cumulUpInner preserves the outer universe type. -/
example
    {mode : Mode} {scopeLow scope : Nat}
    {innerLevel lowerLevel higherLevel : UniverseLevel}
    {cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat}
    {cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {lowerSource lowerTarget :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)}
    (innerStep : Step lowerSource lowerTarget) :
    (Ty.universe (level := higherLevel.toNat + 1) (scope := scope)
                 higherLevel (Nat.le_refl _))
      = Ty.universe (level := higherLevel.toNat + 1) (scope := scope)
                    higherLevel (Nat.le_refl _) :=
  Step.preserves_ty_universe (level := higherLevel.toNat + 1)
                             (scope := scope) (context := ctxHigh)
    (sourceTerm :=
      Term.cumulUp (ctxHigh := ctxHigh)
                   innerLevel lowerLevel higherLevel
                   cumulOkLow cumulOkHigh cumulMonotone
                   (Nat.le_refl _) (Nat.le_refl _) lowerSource)
    (targetTerm :=
      Term.cumulUp (ctxHigh := ctxHigh)
                   innerLevel lowerLevel higherLevel
                   cumulOkLow cumulOkHigh cumulMonotone
                   (Nat.le_refl _) (Nat.le_refl _) lowerTarget)
    higherLevel (Nat.le_refl _)
    (Step.cumulUpInner innerLevel lowerLevel higherLevel
                       cumulOkLow cumulOkHigh cumulMonotone innerStep)
    rfl

end LeanFX2
