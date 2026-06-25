import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Preservation.RawTermRenameInjective

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Preservation.RawTermRenameInjective

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Reduction.Preservation.RawTermRenameInjective`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.eqRecTypeCast_injective

#assert_no_axioms FX1Poly.Core.RawRenaming.iterateLiftRaw_injective

#assert_no_axioms FX1Poly.Core.RawTerm.rename_injective

#assert_no_axioms FX1Poly.Core.RawTermChildren.rename_injective

#assert_no_axioms FX1Poly.Core.Conv.reflectRenameOfFinInjective

#assert_no_axioms FX1Poly.Core.Conv.reflectLiftRename

end FX1PolyAudit
