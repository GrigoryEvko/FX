import LeanFX2.Foundation.PolyCell.Core.StepPreservesShape
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionEtaStructural
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionEtaBinder

/-! # Foundation/PolyCell/Core/StepBetaEtaPreservesShape

Subject-reduction umbrellas for the raw beta+iota/eta union.

The existing `Step.preservesShape` theorem stays beta+iota-only.  This
file adds the opt-in eta layer:

* `Step.eta.preservesShape` dispatches over the current eta constructors.
* `Step.betaEta.preservesShape` dispatches over the sum relation.
* closure/map helpers replay those one-step dispatchers over
  `etaStar` and `betaEtaStar`.

No reserved eta cases are faked here.  Clock, parametricity, and record
eta are added only when their generator families exist in the raw table.
-/

namespace LeanFX2.Foundation.PolyCell.Core

namespace Step

namespace eta

/-- Structural subject reduction for one raw eta step. -/
theorem preservesShape
    {profile : PolyProfile} {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile) sourceTerm)
    (etaStep : Step.eta sourceTerm targetTerm) :
    HasCertifiedCellDim0 (profile := profile) targetTerm := by
  cases etaStep with
  | etaLam innerFunction =>
      exact HasCertifiedCellDim0.preservedByEtaLam sourceCert
  | etaPair pairTerm =>
      exact HasCertifiedCellDim0.preservedByEtaPair sourceCert
  | etaPathLam innerPath =>
      exact HasCertifiedCellDim0.preservedByEtaPathLam sourceCert
  | etaModIntro modalTerm =>
      exact HasCertifiedCellDim0.preservedByEtaModIntro sourceCert
  | etaGlueIntro gluedTerm =>
      exact HasCertifiedCellDim0.preservedByEtaGlueIntro sourceCert

end eta

namespace betaEta

/-- Lift a beta+iota-or-eta step through a raw-term transformer, given
separate one-step lifters for the beta+iota and eta relations. -/
theorem mapStep {scope : Nat}
    (mapTerm : RawTerm scope → RawTerm scope)
    (mapBeta :
      ∀ {sourceTerm targetTerm : RawTerm scope},
        Step sourceTerm targetTerm →
          Step (mapTerm sourceTerm) (mapTerm targetTerm))
    (mapEta :
      ∀ {sourceTerm targetTerm : RawTerm scope},
        Step.eta sourceTerm targetTerm →
          Step.eta (mapTerm sourceTerm) (mapTerm targetTerm))
    {sourceTerm targetTerm : RawTerm scope}
    (singleStep : Step.betaEta sourceTerm targetTerm) :
    Step.betaEta (mapTerm sourceTerm) (mapTerm targetTerm) := by
  cases singleStep with
  | inl betaStep => exact Or.inl (mapBeta betaStep)
  | inr etaStep => exact Or.inr (mapEta etaStep)

/-- Structural subject reduction for one raw beta+iota-or-eta step. -/
theorem preservesShape
    {profile : PolyProfile} {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile) sourceTerm)
    (singleStep : Step.betaEta sourceTerm targetTerm) :
    HasCertifiedCellDim0 (profile := profile) targetTerm := by
  cases singleStep with
  | inl betaStep =>
      exact Step.preservesShape sourceCert betaStep
  | inr etaStep =>
      exact Step.eta.preservesShape sourceCert etaStep

end betaEta

namespace etaStar

/-- Replay eta shape preservation across an eta-star chain. -/
theorem preservesShape
    {profile : PolyProfile} {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile) sourceTerm)
    (chain : Step.etaStar sourceTerm targetTerm) :
    HasCertifiedCellDim0 (profile := profile) targetTerm := by
  induction chain with
  | refl term =>
      exact sourceCert
  | trans etaStep tailChain tailIH =>
      exact tailIH (Step.eta.preservesShape sourceCert etaStep)

end etaStar

namespace betaEtaStar

/-- Lift a beta+iota+eta-star chain through a raw-term transformer,
given separate one-step lifters for the beta+iota and eta relations. -/
theorem mapStep {scope : Nat}
    (mapTerm : RawTerm scope → RawTerm scope)
    (mapBeta :
      ∀ {sourceTerm targetTerm : RawTerm scope},
        Step sourceTerm targetTerm →
          Step (mapTerm sourceTerm) (mapTerm targetTerm))
    (mapEta :
      ∀ {sourceTerm targetTerm : RawTerm scope},
        Step.eta sourceTerm targetTerm →
          Step.eta (mapTerm sourceTerm) (mapTerm targetTerm))
    {sourceTerm targetTerm : RawTerm scope}
    (chain : Step.betaEtaStar sourceTerm targetTerm) :
    Step.betaEtaStar (mapTerm sourceTerm) (mapTerm targetTerm) := by
  induction chain with
  | refl term =>
      exact Step.betaEtaStar.refl (mapTerm term)
  | trans headStep tailChain tailIH =>
      exact Step.betaEtaStar.trans
        (Step.betaEta.mapStep mapTerm mapBeta mapEta headStep)
        tailIH

/-- Replay beta+iota+eta shape preservation across a betaEta-star
chain. -/
theorem preservesShape
    {profile : PolyProfile} {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile) sourceTerm)
    (chain : Step.betaEtaStar sourceTerm targetTerm) :
    HasCertifiedCellDim0 (profile := profile) targetTerm := by
  induction chain with
  | refl term =>
      exact sourceCert
  | trans headStep tailChain tailIH =>
      exact tailIH (Step.betaEta.preservesShape sourceCert headStep)

end betaEtaStar

end Step

end LeanFX2.Foundation.PolyCell.Core
