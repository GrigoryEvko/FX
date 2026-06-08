import FX1Poly.Core.EtaPostponementOverBeta
import FX1Poly.Core.StrongNormalizationBetaEtaUnion

/-! Probe (NEVER committed): OSN-B6 — assemble EtaQuasiCommutesOverBeta by casing on the η-step.
    CRITICAL CHECK: is `cases etaStep` over the indexed Step.eta propext-clean? -/

namespace FX1Poly.Core.Spike

theorem etaQuasiCommutesOverBeta : EtaQuasiCommutesOverBeta := by
  intro scope a b c etaStep betaStep
  cases etaStep with
  | etaLam innerFunction => exact etaLamQuasiCommutesOverBeta betaStep
  | etaPair pairTerm => exact etaPairQuasiCommutesOverBeta betaStep
  | etaPathLam innerPath => exact etaPathLamQuasiCommutesOverBeta betaStep
  | etaModIntro modalTerm => exact etaModIntroQuasiCommutesOverBeta betaStep
  | etaGlueIntro gluedTerm => exact etaGlueIntroQuasiCommutesOverBeta betaStep

end FX1Poly.Core.Spike

#print axioms FX1Poly.Core.Spike.etaQuasiCommutesOverBeta
