import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Orders.RawIotaRpoBridge

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Orders.RawIotaRpoBridge

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Orders.RawIotaRpoBridge`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- RawTerm RPO bridge: the generic rose-tree RPO instantiated at the REAL kernel. eraseToRose
-- forgets RawTerm's scope/binder-shift structure to a RoseTerm Generator; realGenPrecedence ranks the
-- recursive eliminators above gen_app. Post Phase-Z re-scope: ONLY listElimCons remains a live RPO-oriented
-- recursive Step (listElimConsRaw_isStep confirms the redex/reduct pair really is the live constructor; its
-- app-chain reduct is RPO-dominated by the redex). The natElim/natRec succ-iotas now SUBSTITUTE and are
-- NOT erasure-orientable — their pre-migration arity-3 app-chain orientations survive only as ROSE-level
-- boundary records (rpo_orients_iotaNatElimSucc / iotaNatRecSucc over RoseTerm; the retired arity-3 shape
-- is no longer even RawTerm-expressible against the live arity-4 generator table). realGenRpoWellFounded
-- gives the order is well-founded. beta + the substituting succ-iotas stay Tait-imported.
#assert_no_axioms FX1Poly.Core.RawIotaRpo.listElimConsRaw_isStep

#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaNatElimSucc

#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaNatRecSucc

#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaListElimCons

#assert_no_axioms FX1Poly.Core.RawIotaRpo.realGenRpoWellFounded

end FX1PolyAudit
