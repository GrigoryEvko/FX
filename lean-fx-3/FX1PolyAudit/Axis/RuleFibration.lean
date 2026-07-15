import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.RuleFibration

/-! # FX1PolyAudit.Axis.RuleFibration

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.RuleFibration`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Axis substrate: inhabitation is sound (the one generic theorem).
#assert_no_axioms FX1Poly.Axis.RuleFibration.inhabits_eq_true_iff

end FX1PolyAudit
