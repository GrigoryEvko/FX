import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StepBetaEtaConfluence
import FX1Poly.Core.StrongNormalizationEta
import FX1Poly.Core.StepStarConfluence

/-! Probe (NEVER committed): OSN-B1 — instantiate the abstract Geser SN-of-union (B2) at the concrete
    FX βη relations.  `reduceLeft := Step` (β/ι), `reduceRight := Step.eta` (η).  `Step.betaEtaSuccessor`
    is DEFINITIONALLY `UnionSuccessor Step Step.eta`, so `accUnion` instantiates by defeq — the only
    remaining ingredient is the η-postponement crux `EtaQuasiCommutesOverBeta` (B3..B6 discharge it). -/

namespace FX1Poly.Core.Spike

/-- η quasi-commutes over β at every scope — the βη-named crux (B3..B6 discharge it). -/
def EtaQuasiCommutesOverBeta : Prop :=
  ∀ {scope : Nat}, QuasiCommutesRightOverLeft (@Step scope) (@Step.eta scope)

/-- The βη successor relation IS the union successor (defeq bridge). -/
theorem betaEtaSuccessor_eq_unionSuccessor {scope : Nat} :
    @Step.betaEtaSuccessor scope = UnionSuccessor (@Step scope) (@Step.eta scope) := rfl

/-- Conditional βη-SN: β-SN (OB-5 later) + shipped η-SN + the η-postponement crux ⇒ βη-SN. -/
theorem accUnionBetaEta {scope : Nat}
    (etaQuasiCommutes : EtaQuasiCommutesOverBeta)
    {subject : RawTerm scope}
    (betaStronglyNormalizing : StepStar.IsStronglyNormalizing subject) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  accUnion
    (fun term => Step.etaStar.isStronglyNormalizing term)
    etaQuasiCommutes
    betaStronglyNormalizing

end FX1Poly.Core.Spike

#print axioms FX1Poly.Core.Spike.betaEtaSuccessor_eq_unionSuccessor
#print axioms FX1Poly.Core.Spike.accUnionBetaEta
