import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Instances.Renaming.FxBaseRenamingVecTabulate

/-! # FX1PolyAudit.Axis.Context.Instances.Renaming.FxBaseRenamingVecTabulate — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.RenamingVec.tabulate
#assert_no_axioms FX1Poly.Axis.RenamingVec.tabulate_lookup
#assert_no_axioms FX1Poly.Axis.RenamingVec.tabulate_lookup_self
#assert_no_axioms FX1Poly.Axis.RenamingVec.decEq
#assert_no_axioms FX1Poly.Axis.instDecidableEqRenamingVec

end FX1PolyAudit
