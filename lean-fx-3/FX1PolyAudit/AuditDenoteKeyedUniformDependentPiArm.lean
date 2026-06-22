import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Denote.Pi.DenoteKeyedUniformDependentPiArm

/-! # FX1PolyAudit/AuditDenoteKeyedUniformDependentPiArm
    — zero-axiom gate for the dependent composite piArm in the uniform motive (SN-043/#752)

The dependent generalization of the shipped constant-codomain `nonDependentArrow`: a dependent `Π domainCode
codomainCode` is `UniformlyReducibleAboveDenote` (uniformly reducible above the sum threshold) given the domain
reducible above one threshold and the codomain reducible above another UNIFORMLY in the argument, plus its
member-stability corollary.  Isolates the composite-domain threshold-swap as the sole explicit residual of the
`UniformlyReducibleAboveDenote.ofReducibleTypeStepDenote` backbone's `piType` arm.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.dependentPi_reducibleAboveSumThreshold
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.dependentPiArm
#assert_no_axioms FX1Poly.Typed.dependentPi_memberStableAboveSumThreshold
-- FTGEN-5.1: the uniform-motive product leaf — a productCode is uniformly reducible above the SUM of its
-- carriers' thresholds, with the carrier-aware pair candidate (axiom-free sum bounds, no Nat.max).
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.ofDataFlatProduct

end FX1PolyAudit
