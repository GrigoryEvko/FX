import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.DeltaTypedSubjectReduction

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.DeltaTypedSubjectReduction

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.Metatheory.SubjectReduction.DeltaTypedSubjectReduction`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.deltaConstantHead_reserved

#assert_no_axioms FX1Poly.Typed.deltaConstantCell_grownUntyped

#assert_no_axioms FX1Poly.Typed.deltaRootStep_typedSubjectReduction

end FX1PolyAudit
