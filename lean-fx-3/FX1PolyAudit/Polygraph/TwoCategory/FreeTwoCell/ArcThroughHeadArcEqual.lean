import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcThroughHeadArcEqual

/-! # FX1PolyAudit/…/ArcThroughHeadArcEqual — zero-axiom gate

Per-declaration zero-axiom gate for the through-head arc equality: the caller's whole-spine arc
equality plus the located bubble's trace equivalence yield that the head-fronted tail and the
head-fronted remainder share an arc structure at the seed boundary — the constraint the cup orbit's
re-selection must satisfy.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcStructureThroughHead_ofArcEqualAndAtomicEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcThroughHeadArcEqual

end FX1PolyAudit
