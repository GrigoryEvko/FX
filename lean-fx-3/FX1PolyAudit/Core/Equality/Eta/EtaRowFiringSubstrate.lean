import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Equality.Eta.EtaRowFiringSubstrate

/-! # FX1PolyAudit.Core.Equality.Eta.EtaRowFiringSubstrate

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Equality.Eta.EtaRowFiringSubstrate`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The bespoke-`Step.eta`-FREE weakening-shape + table-row firing lemmas relocated out of the
-- (now-being-deleted) StepEtaCriticalPairs cluster into the standalone EtaRowFiringSubstrate
-- home; consumed by the table-native childJoin path-lambda join + union subject reduction.
#assert_no_axioms FX1Poly.Core.RawTerm.weaken_lam

#assert_no_axioms FX1Poly.Core.RawTerm.weaken_eq_lam_implies_source_lam

#assert_no_axioms FX1Poly.Core.RawTerm.weaken_pathLam

#assert_no_axioms FX1Poly.Core.RawTerm.weaken_eq_pathLam_implies_source_pathLam

#assert_no_axioms FX1Poly.Core.pathBetaRowFiringDecompose

end FX1PolyAudit
