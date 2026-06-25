import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Normalize.RawTermNF

/-! # FX1PolyAudit.Core.Rewriting.Normalize.RawTermNF

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Normalize.RawTermNF`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The table-firing root-redex-detector bridge (the per-row inversions pin the literal
-- redex shape, on which the boolean computes) feeding isStepNormalForm_blocks_step post-swap.
#assert_no_axioms FX1Poly.Core.RawTerm.hasRootStepSource_of_firing

end FX1PolyAudit
