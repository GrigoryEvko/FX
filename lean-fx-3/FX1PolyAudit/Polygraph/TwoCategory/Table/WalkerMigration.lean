import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.WalkerMigration

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.WalkerMigration — zero-axiom gate for the smallest-walker migration
bridge (POLY-TAB r0, T4).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.FrobeniusSpecialLawRel
#assert_no_axioms FX1Poly.Polygraph.FrobeniusSpecialWalkerConv
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpecialWalker_to_generic
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpecialWalkerIsCongruence
#assert_no_axioms FX1Poly.Polygraph.generic_to_frobeniusSpecialWalker
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpecialWalker_iff_generic
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpecialWalker_special_transports
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasSmallestWalkerMigration
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasBornGenericWalker

end FX1PolyAudit
