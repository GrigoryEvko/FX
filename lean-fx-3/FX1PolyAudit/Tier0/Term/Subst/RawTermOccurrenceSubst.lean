import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubst

/-! # FX1PolyAudit.Tier0.Term.Subst.RawTermOccurrenceSubst — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawRenaming.liftHitsSucc
#assert_no_axioms FX1Poly.Core.iterateLiftRawHitsRaised
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_rename_image
#assert_no_axioms FX1Poly.Core.RawTermChildren.occurrenceCountAt_rename_image
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_weaken_succ
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst0_weaken
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst0_of_strengthens
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst0_weaken_self

end FX1PolyAudit
