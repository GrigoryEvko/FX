import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Neutral.NeutralStepClosure

/-! # FX1PolyAudit.Core.Substrate.Neutral.NeutralStepClosure

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Substrate.Neutral.NeutralStepClosure`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- A neutral term's one-step reduct is again neutral: a neutral can only step by congruence (no root redex
-- fires, the principal child being neutral never a constructor), and congruence preserves the stuck shape.
-- Discharges the `neutralClosedUnderStep` hypothesis of `CanonicalFormsPredicate.closedUnderStep`.
#assert_no_axioms FX1Poly.Core.IsNeutral.closedUnderStep

end FX1PolyAudit
