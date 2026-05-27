import LeanFX2.Foundation.PolyCell.Core.CongPreservationMutual
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaBoolTrue
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaBoolFalse
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionBaseIotas
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaProjections
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaEither
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaOption
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaIdRefl
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaNatRec

/-! # Foundation/PolyCell/Core/StepPreservesShape
    — subject-reduction umbrella dispatcher

Task #253 / M4.  This is the structural subject-reduction umbrella for
the v2 substrate: any one-step `Step source target` preserves
`HasCertifiedCellDim0`.

This is deliberately only structural shape preservation (certified
dim-0 cell at the same profile/scope), not typed `HasType` subject
reduction.  Typed subject reduction belongs to the later typed layer.
-/

namespace LeanFX2.Foundation.PolyCell.Core

namespace Step

/-- Structural subject reduction for one raw `Step`.

Dispatches across the 18 `Step` constructors: beta, uniform congruence,
and the 16 iota rules.  All substantive arms are already proved in the
specialized SR files; this theorem is the single entry point downstream
CR/SN/NbE code should consume. -/
theorem preservesShape
    {profile : PolyProfile} {scope : Nat}
    {source target : RawTerm scope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile) source)
    (stepRel : Step source target) :
    HasCertifiedCellDim0 (profile := profile) target := by
  cases stepRel with
  | beta =>
      exact HasCertifiedCellDim0.preservedByBeta sourceCert
  | cong generator payload childStep =>
      exact HasCertifiedCellDim0.preservedByCong childStep sourceCert
  | iotaBoolTrue =>
      exact HasCertifiedCellDim0.preservedByIotaBoolTrue sourceCert
  | iotaBoolFalse =>
      exact HasCertifiedCellDim0.preservedByIotaBoolFalse sourceCert
  | iotaFstPair =>
      exact HasCertifiedCellDim0.preservedByIotaFstPair sourceCert
  | iotaSndPair =>
      exact HasCertifiedCellDim0.preservedByIotaSndPair sourceCert
  | iotaNatElimZero =>
      exact HasCertifiedCellDim0.preservedByIotaNatElimZero sourceCert
  | iotaNatRecZero =>
      exact HasCertifiedCellDim0.preservedByIotaNatRecZero sourceCert
  | iotaListElimNil =>
      exact HasCertifiedCellDim0.preservedByIotaListElimNil sourceCert
  | iotaOptionMatchNone =>
      exact HasCertifiedCellDim0.preservedByIotaOptionMatchNone sourceCert
  | iotaOptionMatchSome =>
      exact HasCertifiedCellDim0.preservedByIotaOptionMatchSome sourceCert
  | iotaEitherMatchInl =>
      exact HasCertifiedCellDim0.preservedByIotaEitherMatchInl sourceCert
  | iotaEitherMatchInr =>
      exact HasCertifiedCellDim0.preservedByIotaEitherMatchInr sourceCert
  | iotaNatElimSucc =>
      exact HasCertifiedCellDim0.preservedByIotaNatElimSucc sourceCert
  | iotaNatRecSucc =>
      exact HasCertifiedCellDim0.preservedByIotaNatRecSucc sourceCert
  | iotaListElimCons =>
      exact HasCertifiedCellDim0.preservedByIotaListElimCons sourceCert
  | iotaIdJRefl =>
      exact HasCertifiedCellDim0.preservedByIotaIdJRefl sourceCert
  | iotaIdStrictRecRefl =>
      exact HasCertifiedCellDim0.preservedByIotaIdStrictRecRefl sourceCert

end Step

end LeanFX2.Foundation.PolyCell.Core
