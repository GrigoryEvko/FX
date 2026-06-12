import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaIotaCrossPairCounterexample

/-! # FX1PolyAudit/AuditEtaIotaCrossPairCounterexample — ETA-T5
inc-4.5b shard

Per-declaration zero-axiom gate for the honest boundary: the cross-pair
fixture computations (contraction, firing, iota-irreducibility), the
concrete eta/iota steps and duality witness, and the ★★ refutations of
the duality oracle and the Geser hypothesis for the raw canonical
tables.  Must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Fixture computations -/

#assert_no_axioms FX1Poly.Core.betaIotaRow_memIotaTable
#assert_no_axioms FX1Poly.Core.etaPairRow_memEtaTable
#assert_no_axioms FX1Poly.Core.etaPairRow_contractsOnLamCore
#assert_no_axioms FX1Poly.Core.betaIotaRow_firesOnCrossPairMiddle
#assert_no_axioms FX1Poly.Core.crossPairSource_isIotaIrreducible

/-! ## The steps and the duality witness -/

#assert_no_axioms FX1Poly.Core.crossPairSpineStep
#assert_no_axioms FX1Poly.Core.crossPairEtaStep
#assert_no_axioms FX1Poly.Core.crossPairIotaStep
#assert_no_axioms FX1Poly.Core.crossPair_hasEtaDuality

/-! ## ★★ The refutations -/

#assert_no_axioms FX1Poly.Core.dualityReorders_canonicalRaw_refuted
#assert_no_axioms FX1Poly.Core.rawEtaIota_quasiCommutation_refuted

/-! ## The etaLam dual — not about pair eta -/

#assert_no_axioms FX1Poly.Core.fstPairIotaRow_memIotaTable
#assert_no_axioms FX1Poly.Core.etaLamRow_memEtaTable
#assert_no_axioms FX1Poly.Core.etaLamRow_contractsOnPairCore
#assert_no_axioms FX1Poly.Core.fstPairIotaRow_firesOnCrossLamMiddle
#assert_no_axioms FX1Poly.Core.crossLamSource_isIotaIrreducible
#assert_no_axioms FX1Poly.Core.etaLamRow_memEtaLamOnlyTable
#assert_no_axioms FX1Poly.Core.crossLamSpineStep
#assert_no_axioms FX1Poly.Core.crossLamEtaStep
#assert_no_axioms FX1Poly.Core.crossLamIotaStep
#assert_no_axioms FX1Poly.Core.rawEtaLamOnly_quasiCommutation_refuted

end FX1PolyAudit
