import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.PresentedKernelSeed

/-! # FX1PolyAudit.Polygraph.Omega.PresentedKernelSeedAudit — zero-axiom gate for the presented-kernel seed
(OMEGA-7 r1, B2).

Per-declaration `#assert_no_axioms` on the empty off-slot row, the `PresentedKernel` (signature, table2,
table3) tuple record, the per-dimension row family, the non-vacuous demo instance, the two row-inhabitation
witnesses, and the dim-3 generator's genuine 3-cell (OMEGA-4 `interchangeThreeCell` reseated as table3). -/

namespace FX1PolyAudit

-- PresentedKernelSeed.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.emptyCellRel
#assert_no_axioms FX1Poly.Polygraph.Omega.PresentedKernel
#assert_no_axioms FX1Poly.Polygraph.Omega.presentedKernelRow
#assert_no_axioms FX1Poly.Polygraph.Omega.demoPresentedKernel
#assert_no_axioms FX1Poly.Polygraph.Omega.demoPresentedKernel_table2_inhabited
#assert_no_axioms FX1Poly.Polygraph.Omega.demoPresentedKernel_table3_inhabited
#assert_no_axioms FX1Poly.Polygraph.Omega.demoPresentedKernel_table3_threeCell

end FX1PolyAudit
