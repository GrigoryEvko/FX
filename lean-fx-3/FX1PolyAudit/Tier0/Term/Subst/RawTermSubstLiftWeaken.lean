import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Subst.RawTermSubstLiftWeaken

/-! # FX1PolyAudit.Tier0.Term.Subst.RawTermSubstLiftWeaken

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Term.Subst.RawTermSubstLiftWeaken`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.subst_lift_weaken

#assert_no_axioms FX1Poly.Core.RawTerm.subst_lift_singleton_weaken_weaken

end FX1PolyAudit
