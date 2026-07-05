import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadDischarge

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapHeadDischarge — zero-axiom gate

Per-declaration zero-axiom gate for the cap-head discharge: the chained per-head extraction
obligation's full conclusion at a cap-arity head — locate, bubble, identify, realize,
cancel.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineArcHeadExtractionChained_ofCapArity
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCapHeadDischarge

end FX1PolyAudit
