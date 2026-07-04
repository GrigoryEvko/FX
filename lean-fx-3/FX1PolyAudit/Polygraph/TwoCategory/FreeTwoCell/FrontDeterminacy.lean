import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FrontDeterminacy

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/FrontDeterminacy — zero-axiom gate

Per-declaration zero-axiom gate for the separating keying and the front-form determinacy
theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.GeneratorSeparatingKeying.generatorPackEqOfKeyEq
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.eqOfStageCompositeAndMeasureEq

end FX1PolyAudit
