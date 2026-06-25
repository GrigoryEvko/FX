import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaMeasureDecrease

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Delta.DeltaMeasureDecrease

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaMeasureDecrease`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.deltaConstantCount_rename

#assert_no_axioms FX1Poly.Core.RawTermChildren.deltaConstantCount_rename

#assert_no_axioms FX1Poly.Core.RawTerm.deltaConstantCount_weaken

#assert_no_axioms FX1Poly.Core.RawTerm.deltaConstantCount_weakenClosed

#assert_no_axioms FX1Poly.Core.hyperrealDeltaStep_strictlyDecreasesCount_anyScope

end FX1PolyAudit
