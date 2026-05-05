import LeanFX2.Cubical.Path
import LeanFX2.Foundation.RawPartialRename
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

/-- The typed `constantPath` helper is recognized by the raw
constant-path detector.  This is a wiring guardrail between the typed
cubical helper, `Term.toRaw`, raw weakening, and `RawTerm.unweaken?`;
it deliberately does not add a transport computation rule. -/
theorem constantPath_rawRecognized {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    RawTerm.constantPathBody? (constantPath pointTerm).toRaw =
      some pointRaw := by
  rw [constantPath_toRaw]
  exact RawTerm.constantPathBody?_pathLam_weaken pointRaw

/-- Universe-code specialization of `constantPath_rawRecognized`.
Future constant-transport rules should consume this recognizer theorem
rather than assuming every `pathLam` is a constant type line. -/
theorem constantTypePath_rawRecognized {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw) :
    RawTerm.constantPathBody?
      (constantTypePath universeLevel universeLevelLt typeCode).toRaw =
      some typeRaw := by
  rw [constantTypePath_toRaw]
  exact RawTerm.constantPathBody?_pathLam_weaken typeRaw

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
