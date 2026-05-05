import LeanFX2.Cubical.Path
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.ParRed

/-! # Cubical/PathLemmas

Day 0 scaffold for path algebra lemmas.

## Deliverable

Future work will collect path refl, inverse, composition, application, and
transport lemmas here when those definitions move into the cubical layer.
-/

namespace LeanFX2
namespace Cubical

/-- Raw constant-path application contracts to the endpoint.  This is a
derived theorem over the existing `betaPathApp` rule plus the established
`weaken_subst_singleton` cancellation; it does not add a new reduction rule. -/
theorem constantPath_rawBetaApp {scope : Nat}
    (pointRaw intervalRaw : RawTerm scope) :
    RawStep.par
      (RawTerm.pathApp (RawTerm.pathLam pointRaw.weaken) intervalRaw)
      pointRaw := by
  have betaStep :
      RawStep.par
        (RawTerm.pathApp (RawTerm.pathLam pointRaw.weaken) intervalRaw)
        (pointRaw.weaken.subst0 intervalRaw) :=
    RawStep.par.betaPathApp (RawStep.par.refl _) (RawStep.par.refl _)
  simpa [RawTerm.subst0, RawTerm.weaken_subst_singleton] using betaStep

/-- Typed constant-path application is an instance of the existing
`Step.par.betaPathApp` rule.  The target is the kernel's explicit
single-binder substitution form; `constantPath_rawBetaApp` records the
raw endpoint simplification separately. -/
theorem constantPath_betaPathApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw intervalRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    Step.par
      (Term.pathApp (constantPath pointTerm) intervalTerm)
      (Term.subst0 (Term.weaken Ty.interval pointTerm) intervalTerm) :=
  Step.par.betaPathApp (Step.par.refl _) (Step.par.refl _)

end Cubical
end LeanFX2
