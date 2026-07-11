import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeTotalAssembly

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFactorizeTotalAssembly — zero-axiom gate for the total
(existence) factorization reader, the two-sided decision's both verdicts, and the purification adjudication
(WP-AMALG-2 r15, B4)

Per-declaration zero-axiom gate for the total 5-way-match reader, the gen / vcomp slot-count observability, the
two-sided decision's both verdicts, the purification-stays-open and top-induction-stays-walled adjudications, and the
honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeTotal
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeTotal_gen_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeTotal_vcomp_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutDecisionBothVerdicts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPurificationStaysOpenWithTotalReader
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutTopInductionStaysWalledWithTotalReader
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_totalFactorizeReaderShips

end FX1PolyAudit
