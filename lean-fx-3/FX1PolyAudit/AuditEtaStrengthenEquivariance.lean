import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaStrengthenEquivariance

/-! # FX1PolyAudit/AuditEtaStrengthenEquivariance — ETA-T2 crux shard

Per-declaration zero-axiom gate for the strengthening equivariance
bricks: the single-depth substitution square, the multi-depth
substitution and renaming engines, and the fresh-block fixpoint of
lifted substitutions.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.strengthen_subst
#assert_no_axioms FX1Poly.Core.RawTerm.strengthenBy?_subst
#assert_no_axioms FX1Poly.Core.RawTerm.strengthenBy?_rename
#assert_no_axioms FX1Poly.Core.iterateLiftRaw_RawTermSubst_fixesFreshVar

end FX1PolyAudit
