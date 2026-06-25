import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Core.DirectIotaEliminatorNeutralScrutineeMember

/-! # FX1PolyAudit.Core.Eliminators.Core.DirectIotaEliminatorNeutralScrutineeMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Core.DirectIotaEliminatorNeutralScrutineeMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The neutral regime of the direct-iota eliminators (boolElim/fst/snd/idJ/idStrictRec): the non-recursive
-- companion to the natElim/listElim neutral regimes.  Each iota-reduct is a branch/component (not an
-- application), so the cell-SN-from-children needs no extra interface and each neutral member is a pure compose
-- with memberOfStronglyNormalizingNeutral + the IsNeutral.X arm.
#assert_no_axioms FX1Poly.Core.boolElimNeutralScrutineeMember

#assert_no_axioms FX1Poly.Core.fstNeutralArgumentMember

#assert_no_axioms FX1Poly.Core.sndNeutralArgumentMember

#assert_no_axioms FX1Poly.Core.idJNeutralWitnessMember

#assert_no_axioms FX1Poly.Core.idStrictRecNeutralWitnessMember

end FX1PolyAudit
