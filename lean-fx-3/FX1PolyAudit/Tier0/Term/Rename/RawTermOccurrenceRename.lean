import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rename.RawTermOccurrenceRename

/-! # FX1PolyAudit.Tier0.Term.Rename.RawTermOccurrenceRename — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawRenaming.liftAvoidsSucc
#assert_no_axioms FX1Poly.Core.RawVarSet.raiseParentPosition_zero
#assert_no_axioms FX1Poly.Core.RawVarSet.raiseParentPosition_succ
#assert_no_axioms FX1Poly.Core.iterateLiftRawAvoidsRaised
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_rename_avoided
#assert_no_axioms FX1Poly.Core.RawTermChildren.occurrenceCountAt_rename_avoided
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_weaken_zeroPosition

end FX1PolyAudit
