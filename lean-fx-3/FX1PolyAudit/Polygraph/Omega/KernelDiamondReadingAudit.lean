import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.KernelDiamondReading

/-! # FX1PolyAudit.Polygraph.Omega.KernelDiamondReadingAudit — zero-axiom gate for the kernel confluence
certificate re-read as dim-3 content (OMEGA-4 r1, B3).

Per-declaration `#assert_no_axioms` on the diamond computad + four 2-generators, the label-distinctness
witness, the globular confluence-square row, the first dim-3 kernel 3-cell, the parallelism, the cited
abstract certificate (`= completeCoherentJoin`), and the honesty marker. -/

namespace FX1PolyAudit

-- KernelDiamondReading.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondTwoLabelCode
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondOneCell
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondLeftStep
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondJoinLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondRightStep
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondJoinRight
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondLeftRightSteps_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondCriticalRow
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.diamondCriticalRow_isParallelPair
#assert_no_axioms FX1Poly.Polygraph.Omega.kernelDiamondCoherence
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_kernelDiamondRereadingShipped

end FX1PolyAudit
