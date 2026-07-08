import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenAssembly

/-! # FX1PolyAudit/…/SpineValleyStraightenAssembly — zero-axiom gate

Per-declaration zero-axiom gate for THE STRAIGHTEN ASSEMBLY: the total closed per-step move
`straightenCellDescentStep` (dispatching both handednesses by the width dichotomy — no input, no `matchingOf`
read).  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.straightenCellDescentStep
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenAssembly

end FX1PolyAudit
