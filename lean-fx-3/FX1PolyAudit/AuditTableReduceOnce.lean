import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableReduceOnce

/-! # FX1PolyAudit/AuditTableReduceOnce — IOTA-T9 reducer-migration shard

Per-declaration zero-axiom gate for the table-driven leftmost-outermost
one-step reducer: the mutual reducer, soundness, blocking completeness,
the table normal-form characterization, and the descent guarantee.  The
canonical 21-row instantiation is `RawTerm.reduceOnce` (gated in
`AuditReduceOnce`), under which endpoint-β `pathBeta` is operationally
live.  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

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

end FX1PolyAudit
