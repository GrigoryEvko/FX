import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rename.RawTermRenameAsSubst

/-! # FX1PolyAudit.Tier0.Term.Rename.RawTermRenameAsSubst

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Term.Rename.RawTermRenameAsSubst`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTermSubst.ofRenaming

#assert_no_axioms FX1Poly.Core.RawTermSubst.ofRenaming_lift_pointwise

#assert_no_axioms FX1Poly.Core.RawTermSubst.ofRenaming_iterateLift_pointwise

#assert_no_axioms FX1Poly.Core.RawTerm.rename_eq_subst_ofRenaming

#assert_no_axioms FX1Poly.Core.RawTermChildren.rename_eq_subst_ofRenaming

end FX1PolyAudit
