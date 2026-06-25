import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Instances.Renaming.FxBaseRenamingVecTryTabulate

/-! # FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecTryTabulate — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate_succ_eq
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate_none

end FX1PolyAudit
