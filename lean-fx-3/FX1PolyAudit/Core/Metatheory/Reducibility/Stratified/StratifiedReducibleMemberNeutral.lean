import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberNeutral

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberNeutral

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberNeutral`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Fuel-zero boundary witness: unlike universe-code domains, neutral classifiers can genuinely have
-- members at fuel zero, so the dependent-formation telescope's base-level branch cannot be discharged by
-- a generic contradiction.
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.variableClassifierHasVariableMemberAtZero

end FX1PolyAudit
