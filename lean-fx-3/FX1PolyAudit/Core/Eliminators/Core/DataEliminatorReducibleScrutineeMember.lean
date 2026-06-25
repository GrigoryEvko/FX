import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Core.DataEliminatorReducibleScrutineeMember

/-! # FX1PolyAudit.Core.Eliminators.Core.DataEliminatorReducibleScrutineeMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Core.DataEliminatorReducibleScrutineeMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The general-scrutinee regime of the non-recursive data eliminators (starting with boolElim): the
-- open-scope value regime + general dispatch alongside the closed membership and neutral regimes.
-- boolElimValueReducibility is the boolElim analogue of natElimValueReducibility (no IH, no successor
-- application); the dispatch mirrors the recursive case on the bool candidate's value-or-neutral disjunct.
-- rootGenerator_ne_boolTrue/False are the iota-vacuity discriminators.
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_boolTrue

#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_boolFalse

#assert_no_axioms FX1Poly.Core.boolElim_notNeutral_ofBoolValueScrutinee

#assert_no_axioms FX1Poly.Core.boolValue_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.boolElimValueReducibility

#assert_no_axioms FX1Poly.Core.boolElimReducibleScrutineeMember

end FX1PolyAudit
