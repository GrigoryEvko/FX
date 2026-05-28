import LeanFX2.Foundation.PolyCell.Core.HasCertifiedProjections
import LeanFX2.Foundation.PolyCell.Core.StepEta
import LeanFX2.Foundation.PolyCell.Core.SubstPreservationMutual

/-! # Foundation/PolyCell/Core/SubjectReductionEtaBinder

Subject-reduction arms for binder eta rules.

The current `Step.eta` relation has two binder-shaped eta sources:

* function eta: `lam (app (weaken f) newestVar) -> f`
* path eta: `pathLam (pathApp (weaken p) newestVar) -> p`

Both proofs first project the certified weakened head out of the eta
source, then drop the weakening by substituting any certified term for
the newest variable.  `RawTerm.weaken_subst_singleton` proves that this
singleton substitution cancels the weakening, so no inverse-cell-renamer
assumption or injectivity theorem is needed.

Clock and parametricity eta remain reserved until their generators are
present in the current `Generator` enum.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **Drop one syntactic weakening from a certified term.**

If `RawTerm.weaken sourceTerm` is certified at `scope + 1`, then
`sourceTerm` is certified at `scope`.  The proof substitutes the
canonical unit term for the newest variable and uses the existing
substitution-preservation theorem plus the computational
`weaken_subst_singleton` cancellation lemma. -/
theorem HasCertifiedCellDim0.certifiesBeforeWeakening
    {profile : PolyProfile} {scope : Nat}
    {sourceTerm : RawTerm scope}
    (weakenedCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.weaken sourceTerm)) :
    HasCertifiedCellDim0 (profile := profile) sourceTerm := by
  let unitTerm : RawTerm scope := .mkGen .gen_unit () .childNil
  have unitCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase unitTerm) :=
    PolyCell.gen
      SupportedGenerator.gen_unit
      (genPayloadEvidence (generator := .gen_unit)
        (scope := scope) ())
      CertifiedTermSpine.nil
  have substitutedCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.subst0 (RawTerm.weaken sourceTerm) unitTerm) :=
    HasCertifiedCellDim0.preservedBySubst0 weakenedCert unitCell
  rw [RawTerm.subst0,
    RawTerm.weaken_subst_singleton sourceTerm unitTerm] at substitutedCert
  exact substitutedCert

/-- **SR-eta arm: lambda eta preserves `HasCertifiedCellDim0`.**

Given a certificate for `lam (app (weaken f) newestVar)`, project the
lambda body, then project the application's function child
`weaken f`, then remove the weakening with
`certifiesBeforeWeakening`. -/
theorem HasCertifiedCellDim0.preservedByEtaLam
    {profile : PolyProfile} {scope : Nat}
    {innerFunction : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.etaLamSource innerFunction)) :
    HasCertifiedCellDim0 (profile := profile) innerFunction := by
  let etaBody : RawTerm (scope + 1) :=
    .mkGen .gen_app ()
      (.childCons
        (RawTerm.weaken innerFunction)
        (.childCons RawTerm.newestVar .childNil))
  have bodyCert :
      HasCertifiedCellDim0 (profile := profile) etaBody :=
    HasCertifiedCellDim0.lam_body_projection etaBody sourceCert
  have weakenedFunctionCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.weaken innerFunction) :=
    HasCertifiedCellDim0.app_function_projection
      (RawTerm.weaken innerFunction) RawTerm.newestVar bodyCert
  exact HasCertifiedCellDim0.certifiesBeforeWeakening
    weakenedFunctionCert

/-- **SR-eta arm: cubical path eta preserves `HasCertifiedCellDim0`.**

This is the path-shaped analogue of `preservedByEtaLam`.  The source
is `pathLam (pathApp (weaken p) newestVar)`; the certified path term
is recovered from the first child of the certified `pathApp` body and
then strengthened back to the parent scope. -/
theorem HasCertifiedCellDim0.preservedByEtaPathLam
    {profile : PolyProfile} {scope : Nat}
    {innerPath : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (RawTerm.etaPathLamSource innerPath)) :
    HasCertifiedCellDim0 (profile := profile) innerPath := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons pathAppCell _restSpine =>
        generalize hSort :
          (ChildSpec.termUnderBinder.cellSort) = bodySort
          at pathAppCell
        cases pathAppCell with
        | gen _ _ pathAppSpine =>
          have weakenedPathCert :
              HasCertifiedCellDim0 (profile := profile)
                (RawTerm.weaken innerPath) :=
            .intro .term (pathAppSpine.headAtDim0 rfl)
          exact HasCertifiedCellDim0.certifiesBeforeWeakening
            weakenedPathCert

end LeanFX2.Foundation.PolyCell.Core
