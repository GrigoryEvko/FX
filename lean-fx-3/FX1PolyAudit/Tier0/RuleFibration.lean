import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.RuleFibration

/-! # FX1PolyAudit.Tier0.RuleFibration

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.RuleFibration`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Tier0 substrate: inhabitation is sound (the one generic theorem).
#assert_no_axioms FX1Poly.Tier0.RuleFibration.inhabits_eq_true_iff

end FX1PolyAudit
