import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapArcReconstruct

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringPureCapArcReconstruct — zero-axiom gate
(FC-3 r27 B2a)

Per-declaration zero-axiom gate for the string cap tails-cancel clone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

-- the cap-side internal CUP-count free legs (transitively cover the private range / replicate / reflect helpers)
#assert_no_axioms FX1Poly.Polygraph.stringPureCapSpine_internalCupCounts_eq_replicate
#assert_no_axioms FX1Poly.Polygraph.stringPureCapSpines_internalCupCountsAgree_ofDiagram

-- ★ the enabling clone: the cap tails-cancel from `diagram` + internal cap counts
#assert_no_axioms FX1Poly.Polygraph.stringPureCapTailsCancel_ofDiagramAndInternalCap

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringPureCapSpine_internalCupCounts_eq_replicate
#print axioms FX1Poly.Polygraph.stringPureCapSpines_internalCupCountsAgree_ofDiagram
#print axioms FX1Poly.Polygraph.stringPureCapTailsCancel_ofDiagramAndInternalCap

end FX1PolyAudit
