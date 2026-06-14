import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaMeasureDecrease

/-! # FX1PolyAudit/AuditDeltaMeasureDecrease — RW-4 δ-measure scope-uniformity audit shard

Per-declaration zero-axiom gate for the δ-constant-count rename-invariance
(`deltaConstantCount_rename` term + children), the weaken / weakenClosed
special cases, and the ★ any-scope measure decrease.  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.deltaConstantCount_rename
#assert_no_axioms FX1Poly.Core.RawTermChildren.deltaConstantCount_rename
#assert_no_axioms FX1Poly.Core.RawTerm.deltaConstantCount_weaken
#assert_no_axioms FX1Poly.Core.RawTerm.deltaConstantCount_weakenClosed
#assert_no_axioms FX1Poly.Core.hyperrealDeltaStep_strictlyDecreasesCount_anyScope

end FX1PolyAudit
