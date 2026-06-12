import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaSpinePointwise

/-! # FX1PolyAudit/AuditEtaSpinePointwise — ETA-T5 inc-4.2 shard

Per-declaration zero-axiom gate for the pointwise refl-or-step spine
relation and its shift-0/1/2 lookup bricks.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.EtaChildrenPointwise.refl
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwise.ofChildrenStep
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwise.lookupAtShiftZeroRelated
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwise.lookupAtShiftOneRelated
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwise.lookupAtShiftTwoRelated

end FX1PolyAudit
