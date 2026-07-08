import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPeelLastAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupPeelLastAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the PEEL-LAST reconstruction assembly (route D): the walking-adjunction
cell reconstruction reduced to the peel-last per-atom obligation `SpineArcLastExtractionChained` by STRUCTURAL
`Nat.rec` on the width measure, with the last cup's short chord read off the shared arc (NO head windowPin).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_of_chainedLastExtraction
#assert_no_axioms FX1Poly.Polygraph.adjunctionArcCellReconstruction_of_chainedLastExtraction
#assert_no_axioms FX1Poly.Polygraph.lastCup_sharedShortChord_ofArcEqual
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPeelLastAssembly

end FX1PolyAudit
