import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Conversion.ConvRenameReflection

/-! # FX1PolyAudit.Core.Rewriting.Conversion.ConvRenameReflection

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Conversion.ConvRenameReflection`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepStar.reflectRename

#assert_no_axioms FX1Poly.Core.RawTerm.weaken_injective

#assert_no_axioms FX1Poly.Core.Conv.reflectRename

#assert_no_axioms FX1Poly.Core.Conv.reflectWeaken

#assert_no_axioms FX1Poly.Core.RawRenaming.lift_injective

end FX1PolyAudit
