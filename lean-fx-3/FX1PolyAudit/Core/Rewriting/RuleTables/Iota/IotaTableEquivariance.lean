import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableEquivariance

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableEquivariance

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableEquivariance`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.optionSomeBindMonadic

#assert_no_axioms FX1Poly.Core.optionSomeBindExplicit

#assert_no_axioms FX1Poly.Core.optionSomeMap

#assert_no_axioms FX1Poly.Core.optionMapEqSome

#assert_no_axioms FX1Poly.Core.castCompose

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeChildLookup_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.elimPayloadAtDepth?_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_subst

end FX1PolyAudit
