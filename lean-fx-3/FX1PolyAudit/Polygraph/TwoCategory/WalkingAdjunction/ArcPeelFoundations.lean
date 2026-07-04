import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPeelFoundations — zero-axiom gate

Per-declaration zero-axiom gate for the cup/cap peel's ground facts: seed classification,
boundary-path pinning, and rigidity at equal boundary lengths.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtom_isCupOrCap
#assert_no_axioms FX1Poly.Polygraph.adjunctionAtoms_domBoundaryPathsEqual_of_lengthsEqual
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths

end FX1PolyAudit
