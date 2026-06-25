import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Tables.DimensionGenericRuleTable

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Tables.DimensionGenericRuleTable — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.dim2IotaShape
#assert_no_axioms FX1Poly.Core.dim2EtaShape
#assert_no_axioms FX1Poly.Core.dim2IotaShape_rowType_isIotaRuleDesc
#assert_no_axioms FX1Poly.Core.dim2EtaShape_rowType_isEtaRuleDesc
#assert_no_axioms FX1Poly.Core.dim2IotaShape_headKey_isElimGeneratorTag
#assert_no_axioms FX1Poly.Core.substrateOf
#assert_no_axioms FX1Poly.Core.RewriteDimension.fitsFlatOrthogonalTable
#assert_no_axioms FX1Poly.Core.substrate_definitional_ne_extensional
#assert_no_axioms FX1Poly.Core.substrate_extensional_ne_coherence
#assert_no_axioms FX1Poly.Core.substrate_definitional_ne_coherence
#assert_no_axioms FX1Poly.Core.dimensionGenericRuleTable_verdict

end FX1PolyAudit
