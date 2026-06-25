import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Instances.Renaming.FxBaseRenamingVecIsomorphism

/-! # FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecIsomorphism — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RenamingVec.isomorphismOfLookupInverse
#assert_no_axioms FX1Poly.Tier0.RenamingVec.swapTwo
#assert_no_axioms FX1Poly.Tier0.RenamingVec.swapTwo_involutive
#assert_no_axioms FX1Poly.Tier0.RenamingVec.swapTwoIsIsomorphism
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isCategoricalIsomorphism_identity
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isCategoricalIsomorphism_compose
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isCategoricalIsomorphism_pullback

end FX1PolyAudit
