import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaBetaCommutation

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Delta.DeltaBetaCommutation

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaBetaCommutation`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Step.no_step_from_hyperreal

#assert_no_axioms FX1Poly.Core.Step.no_step_from_qubit

#assert_no_axioms FX1Poly.Core.deltaConstantHead_notRedexHead

#assert_no_axioms FX1Poly.Core.deltaConstantCell_noRootStepSource

#assert_no_axioms FX1Poly.Core.hyperrealDeltaRedex_canonicalNormal

#assert_no_axioms FX1Poly.Core.qubitDeltaRedex_canonicalNormal

#assert_no_axioms FX1Poly.Core.deltaRootRedex_noCanonicalStep

#assert_no_axioms FX1Poly.Core.hyperrealDeltaFiresAtCanonicalNormal

end FX1PolyAudit
