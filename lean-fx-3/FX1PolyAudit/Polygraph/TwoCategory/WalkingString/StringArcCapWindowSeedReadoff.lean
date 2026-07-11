import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowSeedReadoff

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapWindowSeedReadoff — zero-axiom gate
(FC-3 r22, B3)

Per-declaration zero-axiom gate for the located-cap read-off seat-bound substrate and its two honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcPairCapWindow_splitSeatBound
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapWindowSeatBound
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapWindowSeedReadoff

end FX1PolyAudit
