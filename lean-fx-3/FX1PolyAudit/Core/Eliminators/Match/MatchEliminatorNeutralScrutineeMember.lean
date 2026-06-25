import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Match.MatchEliminatorNeutralScrutineeMember

/-! # FX1PolyAudit.Core.Eliminators.Match.MatchEliminatorNeutralScrutineeMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Match.MatchEliminatorNeutralScrutineeMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The neutral regime of the application-iota match eliminators (optionMatch/eitherMatch): the last 2 of 12
-- IsNeutral eliminators, completing the eliminator-neutral-coverage set.  Their iota is an application
-- (optionMatch (some v) ... to app s v), so cell-SN needs the bespoke triple-Acc (the natElim pattern, iota
-- cases vacuous by neutrality) + constructor discriminators
-- rootGenerator_ne_optionNone/optionSome/eitherInl/eitherInr, not a pure compose like the direct-iota five.
-- With these, all 12 IsNeutral eliminators are reducible over a neutral principal child.
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_optionNone

#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_optionSome

#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_eitherInl

#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_eitherInr

#assert_no_axioms FX1Poly.Core.optionMatch_neutralScrutinee_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.eitherMatch_neutralScrutinee_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.optionMatchNeutralScrutineeMember

#assert_no_axioms FX1Poly.Core.eitherMatchNeutralScrutineeMember

end FX1PolyAudit
