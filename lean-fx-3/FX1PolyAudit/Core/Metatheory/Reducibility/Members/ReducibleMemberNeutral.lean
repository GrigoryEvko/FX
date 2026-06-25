import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Members.ReducibleMemberNeutral

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Members.ReducibleMemberNeutral

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Members.ReducibleMemberNeutral`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The type-code-former family inhabits its neutral universe as a reducible member (the conv-complete
-- IsReducibleMember layer the fundamental theorem assembles over).  atNeutralClassifier is the
-- characterization (membership at a neutral classifier = strong normalization); the seven formers
-- (dependent pi/sigma + non-dependent arrow/product/sum/either/equiv) discharge via their SN closures.
#assert_no_axioms FX1Poly.Core.IsReducibleMember.atNeutralClassifier

#assert_no_axioms FX1Poly.Core.IsReducibleMember.piFormerInNeutralUniverse

#assert_no_axioms FX1Poly.Core.IsReducibleMember.sigmaFormerInNeutralUniverse

#assert_no_axioms FX1Poly.Core.IsReducibleMember.arrowFormerInNeutralUniverse

#assert_no_axioms FX1Poly.Core.IsReducibleMember.productFormerInNeutralUniverse

#assert_no_axioms FX1Poly.Core.IsReducibleMember.sumFormerInNeutralUniverse

#assert_no_axioms FX1Poly.Core.IsReducibleMember.eitherFormerInNeutralUniverse

#assert_no_axioms FX1Poly.Core.IsReducibleMember.equivFormerInNeutralUniverse

end FX1PolyAudit
