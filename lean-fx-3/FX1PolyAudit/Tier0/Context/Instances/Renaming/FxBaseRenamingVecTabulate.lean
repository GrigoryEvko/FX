import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Instances.Renaming.FxBaseRenamingVecTabulate

/-! # FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecTabulate — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RenamingVec.tabulate
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tabulate_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tabulate_lookup_self
#assert_no_axioms FX1Poly.Tier0.RenamingVec.decEq
#assert_no_axioms FX1Poly.Tier0.instDecidableEqRenamingVec

end FX1PolyAudit
