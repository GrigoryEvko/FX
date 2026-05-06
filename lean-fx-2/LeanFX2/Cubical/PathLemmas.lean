import LeanFX2.Cubical.Path
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Bridge
import LeanFX2.Term.Bridge

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
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    RawTerm.constantPathBody? (constantPath modeIsUnivalent pointTerm).toRaw =
      some pointRaw := by
  rw [constantPath_toRaw modeIsUnivalent]
  exact RawTerm.constantPathBody?_pathLam_weaken pointRaw

/-- Universe-code specialization of `constantPath_rawRecognized`.
Future constant-transport rules should consume this recognizer theorem
rather than assuming every `pathLam` is a constant type line. -/
theorem constantTypePath_rawRecognized {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw) :
    RawTerm.constantPathBody?
      (constantTypePath modeIsUnivalent universeLevel universeLevelLt typeCode).toRaw =
      some typeRaw := by
  rw [constantTypePath_toRaw modeIsUnivalent]
  exact RawTerm.constantPathBody?_pathLam_weaken typeRaw

/-- The interval identity path mentions the interval binder, so it is
not a constant path.  This typed term is the small counterexample that
blocks the unsound shortcut "every `pathLam` is transport-constant". -/
def intervalBinderPath {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent) :
    Term context (Ty.path Ty.interval RawTerm.interval0 RawTerm.interval1)
      (RawTerm.pathLam
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) :=
  Term.pathLam modeIsUnivalent Ty.interval RawTerm.interval0 RawTerm.interval1
    (Term.var (context := context.cons Ty.interval)
      ⟨0, Nat.zero_lt_succ scope⟩)

/-- The raw constant-path recognizer rejects `intervalBinderPath`.
This is the typed counterpart to
`RawTerm.constantPathBody?_pathLam_interval_var_none`. -/
theorem intervalBinderPath_rawRejected
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent) :
    RawTerm.constantPathBody?
      (intervalBinderPath (context := context) modeIsUnivalent).toRaw =
      none := by
  change RawTerm.constantPathBody?
    (RawTerm.pathLam
      (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) = none
  exact RawTerm.constantPathBody?_pathLam_interval_var_none

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
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw intervalRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    Step.par
      (Term.pathApp modeIsUnivalent
        (constantPath modeIsUnivalent pointTerm) intervalTerm)
      (Term.subst0 (Term.weaken Ty.interval pointTerm) intervalTerm) :=
  Step.par.betaPathApp modeIsUnivalent (Step.par.refl _) (Step.par.refl _)

/-- Typed constant-path β projects through the typed-to-raw bridge to
the endpoint-level raw β fact.  This is a load-bearing wiring smoke:
it uses the typed `constantPath`, typed `Step.par.betaPathApp`,
`Step.par.toRawBridge`, `Term.toRaw_weaken`, `Term.toRaw_subst0`, and
the raw weakening/substitution cancellation together. -/
theorem constantPath_betaPathApp_toRawEndpoint
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw intervalRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    RawStep.par
      (RawTerm.pathApp (RawTerm.pathLam pointRaw.weaken) intervalRaw)
      pointRaw := by
  have bridgeStep :
      RawStep.par
        (RawTerm.pathApp (RawTerm.pathLam pointRaw.weaken) intervalRaw)
        (pointRaw.weaken.subst0 intervalRaw) := by
    simpa [constantPath_toRaw, Term.toRaw_weaken, Term.toRaw_subst0]
      using Step.par.toRawBridge
        (constantPath_betaPathApp modeIsUnivalent pointTerm intervalTerm)
  simpa [RawTerm.subst0, RawTerm.weaken_subst_singleton] using bridgeStep

/-- Universe-code specialization of `constantPath_betaPathApp`.  This
is the typed redex shape future constant-transport computation will
consume: a path application over a constant type line. -/
theorem constantTypePath_betaPathApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {typeRaw intervalRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    Step.par
      (Term.pathApp modeIsUnivalent
        (constantTypePath modeIsUnivalent universeLevel universeLevelLt typeCode)
        intervalTerm)
      (Term.subst0 (Term.weaken Ty.interval typeCode) intervalTerm) :=
  Step.par.betaPathApp modeIsUnivalent (Step.par.refl _) (Step.par.refl _)

/-- Universe-code constant-path β projects through the typed-to-raw
bridge to the original universe code.  This is the load-bearing
type-line guardrail for future constant-transport rules. -/
theorem constantTypePath_betaPathApp_toRawEndpoint
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {typeRaw intervalRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    RawStep.par
      (RawTerm.pathApp (RawTerm.pathLam typeRaw.weaken) intervalRaw)
      typeRaw := by
  have bridgeStep :
      RawStep.par
        (RawTerm.pathApp (RawTerm.pathLam typeRaw.weaken) intervalRaw)
        (typeRaw.weaken.subst0 intervalRaw) := by
    simpa [constantTypePath_toRaw, Term.toRaw_weaken, Term.toRaw_subst0]
      using Step.par.toRawBridge
        (constantTypePath_betaPathApp
          modeIsUnivalent universeLevel universeLevelLt typeCode intervalTerm)
  simpa [RawTerm.subst0, RawTerm.weaken_subst_singleton] using bridgeStep

end Cubical
end LeanFX2
