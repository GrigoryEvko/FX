import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineListDecEq

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpineListDecEq — zero-axiom gate

Per-declaration zero-axiom gate for the generic spine-trace decidable equality (the
class-saturation search's membership layer).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineListDecEq

end FX1PolyAudit
