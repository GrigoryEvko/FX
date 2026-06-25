import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Core.NeutralEliminatorMemberSmoke

/-! # FX1PolyAudit.Core.Eliminators.Core.NeutralEliminatorMemberSmoke

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Core.NeutralEliminatorMemberSmoke`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Non-vacuous regression corpus for the eliminator-neutral set: each neutral member, instantiated at the SN
-- candidate with `var index` as the genuinely-neutral principal child, gives a concrete strong-normalization
-- fact for the stuck eliminator.  Guards the set against silently regressing to vacuity or losing zero-axiom
-- status.  Parametric over an arbitrary Fin scope index.
#assert_no_axioms FX1Poly.Core.natElimNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.natRecNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.listElimNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.optionMatchNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.eitherMatchNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.boolElimNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.fstNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.sndNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.idJNeutralVarSmoke

#assert_no_axioms FX1Poly.Core.idStrictRecNeutralVarSmoke

end FX1PolyAudit
