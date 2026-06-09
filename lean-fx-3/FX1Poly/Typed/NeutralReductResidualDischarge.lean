import FX1Poly.Typed.PinnedReflectionPiElimDispatcher
import FX1Poly.Typed.PlateauPinnedReflection

/-! # FX1Poly/Typed/NeutralReductResidualDischarge — the neutral-reduct head residual HOLDS

One of the whnf dispatcher's two head residuals discharges unconditionally:

  * `IsNeutral.ne_lamCell` — a neutral is never a λ (12-arm head discrimination: every
    `IsNeutral` constructor's head generator differs from `gen_lam`, killed by
    `Generator.noConfusion` after mkGen injection).
  * `pinnedReflectionPiElimNeutralReductResidualHolds` — when the residual's function
    whnf-reduces to a normal NEUTRAL: the reduct is in-image (`StepStar.reflectRename` on the
    in-image function) and keeps the Π classifier (`subjectReductionStar` under the motive's
    target wf); the plateau pin-extraction (`normalNonLambdaClassifierPinned`) pins it — the
    ∀-bound guarded residual (`piElimResidualGuardedAtEveryBound`) makes the budget guard free —
    and `pinnedReflectionPiElimCore` finishes with the ORIGINAL premise reflections.

With this, the full piElim residual is one λ-reduct residual away
(`pinnedReflectionPiElimResidualOfHeadResiduals`).

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- A neutral term is never a λ: every `IsNeutral` head generator differs from `gen_lam`. -/
theorem IsNeutral.ne_lamCell {scope : Nat} {neutralTerm : RawTerm scope}
    (neutral : IsNeutral neutralTerm) :
    ∀ body : RawTerm (scope + 1), neutralTerm ≠ lamCell body := by
  cases neutral <;>
    exact fun body hEq => by
      injection hEq with hScope hGenerator hPayload hChildren
      exact Generator.noConfusion hGenerator

/-- **The neutral-reduct head residual HOLDS**: when the function whnf-reduces to a normal
neutral, the residual conclusion follows — the reduct is in-image and keeps the Π classifier by
subject reduction, the plateau pin-extraction pins it (the ∀-bound guarded residual supplies the
budget), and the pinned-function core finishes with the original premise reflections. -/
theorem pinnedReflectionPiElimNeutralReductResidualHolds (profile : PolyProfile) :
    PinnedReflectionPiElimNeutralReductResidual profile := by
  intro targetScope targetContext functionTerm argument domainCode reduct codomainCode
    functionTyped argumentTyped functionReduces reductNeutral reductNormal
    functionIH argumentIH
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage _pinned _pinBaseTyped
  obtain ⟨sourceFunction, sourceArgument, hSubject, hFunction, hArgument⟩ :=
    renameEqAppCellInversion rho subjectInImage.symm
  subst hSubject
  rw [hFunction] at functionReduces functionTyped
  obtain ⟨sourceReduct, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename rho functionReduces
  have reductTyped : HasTypeDescPi profile targetContext reduct
      (piTyCodeCell domainCode codomainCode) :=
    HasTypeDescPi.subjectReductionStar targetWellFormed functionTyped functionReduces
  obtain ⟨reflectedPiBase, piPinned, piBaseTyped⟩ :=
    normalNonLambdaClassifierPinned (budget := reduct.size)
      (fun {smallBound} _withinBudget =>
        piElimResidualGuardedAtEveryBound profile smallBound)
      reductTyped reductNormal (IsNeutral.ne_lamCell reductNeutral) (Nat.le_refl _)
      targetWellFormed rho sourceContext rhoInjective condition wellFormed imageEq.symm
  exact pinnedReflectionPiElimCore profile functionIH argumentIH rho sourceContext
    targetWellFormed rhoInjective condition wellFormed hFunction hArgument
    piPinned piBaseTyped

end FX1Poly.Typed
