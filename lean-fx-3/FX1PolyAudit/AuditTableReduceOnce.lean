import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableReduceOnce

/-! # FX1PolyAudit/AuditTableReduceOnce — IOTA-T9 reducer-migration shard

Per-declaration zero-axiom gate for the table-driven leftmost-outermost
one-step reducer: the mutual reducer, soundness, blocking completeness,
the table normal-form characterization, the descent guarantee, the
canonical 18-row instantiations, and the endpoint-β operational
liveness smoke.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The reducer -/

#assert_no_axioms FX1Poly.Core.reduceOnceOverTable
#assert_no_axioms FX1Poly.Core.reduceOnceSpineOverTable

/-! ## Soundness -/

#assert_no_axioms FX1Poly.Core.reduceOnceOverTable_sound
#assert_no_axioms FX1Poly.Core.reduceOnceSpineOverTable_sound

/-! ## Blocking completeness -/

#assert_no_axioms FX1Poly.Core.reduceOnceOverTable_eq_none_blocks_step
#assert_no_axioms FX1Poly.Core.reduceOnceSpineOverTable_eq_none_blocks_step

/-! ## The halting characterization -/

#assert_no_axioms FX1Poly.Core.IsNormalFormOverTable
#assert_no_axioms FX1Poly.Core.reduceOnceOverTable_eq_none_iff_isNormalFormOverTable
#assert_no_axioms FX1Poly.Core.not_isNormalFormOverTable_imp_reduceOnceOverTable_isSome

/-! ## The canonical instantiation + endpoint-β liveness -/

#assert_no_axioms FX1Poly.Core.StepTable.reduceOnce
#assert_no_axioms FX1Poly.Core.StepTable.reduceOnce_sound
#assert_no_axioms FX1Poly.Core.StepTable.reduceOnce_eq_none_iff
#assert_no_axioms FX1Poly.Core.StepTable.reduceOnce_firesPathBeta

end FX1PolyAudit
