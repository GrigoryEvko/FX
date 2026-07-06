import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTailsCancelInterface

/-! # FX1PolyAudit/…/ArcCupTailsCancelInterface — zero-axiom gate

Per-declaration zero-axiom gate for the cup tails-cancel residual interface: the full cup tailsCancel
from the whole-spine arc equality + bubble trace equivalence + head-cup + the three orbit residuals
(diagram + two internal-count legs).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupTailsCancel_ofCupHead_diagramAndInternals
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupTailsCancelInterface

end FX1PolyAudit
