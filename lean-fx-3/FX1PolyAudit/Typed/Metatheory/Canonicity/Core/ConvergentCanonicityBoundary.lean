import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Canonicity.Core.ConvergentCanonicityBoundary

/-! # FX1PolyAudit.Typed.Metatheory.Canonicity.Core.ConvergentCanonicityBoundary

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.Metatheory.Canonicity.Core.ConvergentCanonicityBoundary`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The honest convergence/canonicity boundary for the word/RPO leg: the convergent ι∪η presentation does NOT
-- yield canonicity, because its normal forms include non-canonical β-redexes.  appLamUnit = app(lam(unit))unit
-- is ι∪η-NORMAL (appLamUnit_iotaEtaNormal: no IotaEtaStep fires — root app matches no ι/η head-redex, the lam
-- and unit children are normal) yet β-reduces to the value unit (appLamUnit_betaStepsToUnit: Step.beta).  So
-- the convergent presentation halts on a non-value; canonicity requires β-normalization, and β is excluded
-- from the ι∪η word system (raw β is non-SN, Tait-imported).  convergentNormalFormNeedNotBeCanonical packages
-- the NO-GO; convergentNormalFormCanStillBeStronglyNormalizing notes the gap is ι∪η-normality vs canonicity,
-- not SN vs canonicity.  Inversions are direct propext-clean cases over a closed term whose root head matches
-- no redex arm.
#assert_no_axioms FX1Poly.Core.unit_iotaEtaNormal

#assert_no_axioms FX1Poly.Core.lamUnit_iotaEtaNormal

#assert_no_axioms FX1Poly.Core.appLamUnit_iotaEtaNormal

#assert_no_axioms FX1Poly.Core.appLamUnit_betaStepsToUnit

#assert_no_axioms FX1Poly.Core.convergentNormalFormNeedNotBeCanonical

#assert_no_axioms FX1Poly.Core.convergentNormalFormCanStillBeStronglyNormalizing

end FX1PolyAudit
