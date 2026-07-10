import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.AdmissionChainSeed

/-! # FX1PolyAudit.Polygraph.Omega.AdmissionChainSeedAudit — zero-axiom gate for the admission chain seed
(OMEGA-7 r1, B3).

Per-declaration `#assert_no_axioms` on the admitted-table record, the per-dimension admission family, the
admission-inheritance handoff shape, the chain induced by a presented kernel, the demo chain, and the three
non-vacuity witnesses (dim-3 admissible / dim-3 fires on the interchange legs / off-slot not-admissible). -/

namespace FX1PolyAudit

-- AdmissionChainSeed.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.AdmittedTableSeed
#assert_no_axioms FX1Poly.Polygraph.Omega.AdmissionChainSeed
#assert_no_axioms FX1Poly.Polygraph.Omega.AdmissionInheritanceShape
#assert_no_axioms FX1Poly.Polygraph.Omega.presentedKernelAdmissionChain
#assert_no_axioms FX1Poly.Polygraph.Omega.demoAdmissionChain
#assert_no_axioms FX1Poly.Polygraph.Omega.demoAdmissionChain_dim3_isAdmissible
#assert_no_axioms FX1Poly.Polygraph.Omega.demoAdmissionChain_dim3_fires
#assert_no_axioms FX1Poly.Polygraph.Omega.demoAdmissionChain_offSlot_notAdmissible

end FX1PolyAudit
