import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapTrichotomy

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SwapTrichotomy — zero-axiom gate

Per-declaration zero-axiom gate for the orientation-totality lemma: every adjacent atom swap
fires as an oriented step in exactly one direction, or relates two equal lists.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.orientOrEqual

end FX1PolyAudit
