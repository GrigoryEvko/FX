import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapCorePackage

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcSwapCorePackage — zero-axiom gate

Per-declaration zero-axiom gate for the peel-ready swap-core bundle: the four combo package
builders and the extract-equality consumer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_full_of_swapCorePackage
#assert_no_axioms FX1Poly.Polygraph.arcSwapCorePackage_cupCup
#assert_no_axioms FX1Poly.Polygraph.arcSwapCorePackage_cupCap
#assert_no_axioms FX1Poly.Polygraph.arcSwapCorePackage_capCup
#assert_no_axioms FX1Poly.Polygraph.arcSwapCorePackage_capCap

end FX1PolyAudit
