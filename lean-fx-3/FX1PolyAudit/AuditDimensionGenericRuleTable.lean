import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.DimensionGenericRuleTable

/-! # FX1PolyAudit/AuditDimensionGenericRuleTable — DIMN-TAB-1 audit shard

Per-declaration zero-axiom gate for the dimension-generic RuleTable spike:
the shared `RuleTableShape` interface, the two shipped dim-2 instantiations
(`dim2IotaShape`/`dim2EtaShape`) + their carrier/key pins, the
`RewriteDimension`/substrate enums, the `substrateOf` map, the
`fitsFlatOrthogonalTable` classifier, the three substrate-distinctness facts,
and the ★ verdict (`dimensionGenericRuleTable_verdict`).  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The shared shape + dim-2 instantiations -/

#assert_no_axioms FX1Poly.Core.dim2IotaShape
#assert_no_axioms FX1Poly.Core.dim2EtaShape
#assert_no_axioms FX1Poly.Core.dim2IotaShape_rowType_isIotaRuleDesc
#assert_no_axioms FX1Poly.Core.dim2EtaShape_rowType_isEtaRuleDesc
#assert_no_axioms FX1Poly.Core.dim2IotaShape_headKey_isElimGeneratorTag

/-! ## The substrate descriptor + classifiers -/

#assert_no_axioms FX1Poly.Core.substrateOf
#assert_no_axioms FX1Poly.Core.RewriteDimension.fitsFlatOrthogonalTable

/-! ## Substrate distinctness -/

#assert_no_axioms FX1Poly.Core.substrate_definitional_ne_extensional
#assert_no_axioms FX1Poly.Core.substrate_extensional_ne_coherence
#assert_no_axioms FX1Poly.Core.substrate_definitional_ne_coherence

/-! ## The ★ verdict -/

#assert_no_axioms FX1Poly.Core.dimensionGenericRuleTable_verdict

end FX1PolyAudit
