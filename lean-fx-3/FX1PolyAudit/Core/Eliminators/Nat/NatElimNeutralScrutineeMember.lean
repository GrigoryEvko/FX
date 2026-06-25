import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimNeutralScrutineeMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The neutral-scrutinee regime of the Nat recursor, the dual of the value case.  A neutral scrutinee is
-- never a numeral and stays neutral under Step, so natElim/natRec never iota-fires and the cell is a stuck
-- neutral, which inhabits every candidate by CR3.  memberOfStronglyNormalizingNeutral is the reusable bridge
-- (SN neutral implies member of any candidate, generalizing the CanonicalFormsPredicate-only version);
-- rootGenerator_ne_natZero/natSucc are the iota-vacuity discriminators; the cell-SN recursors are a triple Acc
-- induction with the two iota cases vacuous by neutrality (fixed result candidate, fuel-independent).
#assert_no_axioms FX1Poly.Core.IsReducibilityCandidate.memberOfStronglyNormalizingNeutral

#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_natZero

#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_natSucc

#assert_no_axioms FX1Poly.Core.natElim_neutralScrutinee_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.natRec_neutralScrutinee_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.natElimNeutralScrutineeMember

#assert_no_axioms FX1Poly.Core.natRecNeutralScrutineeMember

end FX1PolyAudit
