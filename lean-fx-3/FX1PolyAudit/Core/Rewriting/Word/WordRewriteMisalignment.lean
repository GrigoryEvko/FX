import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Word.WordRewriteMisalignment

/-! # FX1PolyAudit.Core.Rewriting.Word.WordRewriteMisalignment

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Word.WordRewriteMisalignment`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.misalignmentRedex_steps

#assert_no_axioms FX1Poly.Core.misalignmentRule_mem_fxStepSystem

#assert_no_axioms FX1Poly.Core.misalignedPairHost_isNormal

#assert_no_axioms FX1Poly.Core.misalignedPairHost_code

#assert_no_axioms FX1Poly.Core.fxWordRewritesOneStep_firesOnNormalImage

#assert_no_axioms FX1Poly.Core.wordStepInversion_isFalse

end FX1PolyAudit
