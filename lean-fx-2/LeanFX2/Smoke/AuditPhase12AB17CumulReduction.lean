import LeanFX2.Reduction.Step
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.Cumul

/-! # Smoke/AuditPhase12AB17CumulReduction — Step.cumulUpInner audit
(Phase CUMUL-2.6 Design D revision).

Phase 12.A.B17 (CUMUL-3.1..3.5).  Audits the new `Step.cumulUpInner`
ctor and its parallel-reduction analog `Step.par.cumulUpInnerCong`,
plus the `Step.toPar` and `Step.toConvCumul` extensions.

Phase CUMUL-2.6 revises the audit: cumulUp now uses Design D (single
context, schematic codeRaw, output wrapped in cumulUpMarker).

## Audit targets

* `Step.cumulUpInner` (Reduction/Step.lean) — cong rule that
  reduces inside `Term.cumulUp`'s `typeCode` payload (single context,
  schematic codeRaw).
* `Step.par.cumulUpInnerCong` (Reduction/ParRed.lean) — parallel
  analog of the above.
* `Step.toPar` extended with `cumulUpInner` arm — lifts a single
  inner Step to parallel via `Step.par.cumulUpInnerCong`.
* `Step.toConvCumul` extended with `cumulUpInner` arm — lifts to
  ConvCumul via cumulUpCong.
-/

namespace LeanFX2

/-! ## Smoke: Step.cumulUpInner lifts to Step.par via Step.toPar. -/

/-- Step.cumulUpInner lifts to a parallel reduction inside cumulUp. -/
example
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {lowerLevel higherLevel : UniverseLevel}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {levelLeLow : lowerLevel.toNat + 1 ≤ level}
    {levelLeHigh : higherLevel.toNat + 1 ≤ level}
    {codeSourceRaw codeTargetRaw : RawTerm scope}
    {typeCodeSource :
      Term context (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
    {typeCodeTarget :
      Term context (Ty.universe lowerLevel levelLeLow) codeTargetRaw}
    (innerStep : Step typeCodeSource typeCodeTarget) :
    Step.par
      (Term.cumulUp (context := context)
                    lowerLevel higherLevel cumulMonotone
                    levelLeLow levelLeHigh typeCodeSource)
      (Term.cumulUp (context := context)
                    lowerLevel higherLevel cumulMonotone
                    levelLeLow levelLeHigh typeCodeTarget) :=
  Step.toPar (Step.cumulUpInner lowerLevel higherLevel cumulMonotone
                                levelLeLow levelLeHigh innerStep)

/-! ## Audit declarations -/

#print axioms LeanFX2.Step.cumulUpInner
#print axioms LeanFX2.Step.par.cumulUpInnerCong

end LeanFX2
