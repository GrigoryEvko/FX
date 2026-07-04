import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadReindex

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcHeadReindex — zero-axiom gate

Per-declaration zero-axiom gate for the concrete head reindexing at the peel's seed pair
(peel campaign H, seed rung, positional leg): the above-width translation law, the generic
range image, the two boundary-width pins, the two seed shift discharges, and the two
positional seed simulations.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcHeadReindex_shiftsAboveLength
#assert_no_axioms FX1Poly.Polygraph.arcHeadReindex_mapRange
#assert_no_axioms FX1Poly.Polygraph.cupHeadOpenWires_length
#assert_no_axioms FX1Poly.Polygraph.capHeadOpenWires_length
#assert_no_axioms FX1Poly.Polygraph.arcHeadReindex_cupSeedShifts
#assert_no_axioms FX1Poly.Polygraph.arcHeadReindex_capSeedShifts
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_cupHeadSeed
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_capHeadSeed

end FX1PolyAudit
