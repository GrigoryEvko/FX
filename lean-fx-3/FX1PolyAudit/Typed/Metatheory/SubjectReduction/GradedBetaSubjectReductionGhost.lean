import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.GradedBetaSubjectReductionGhost

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.GradedBetaSubjectReductionGhost — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.PartialRawRenaming.liftFailsOnlyAtSucc
#assert_no_axioms FX1Poly.Core.iterateLiftRawFailsOnlyAtRaised
#assert_no_axioms FX1Poly.Core.RawTerm.partialRenameSucceeds_of_occurrenceZero
#assert_no_axioms FX1Poly.Core.RawTermChildren.partialRenameSucceeds_of_occurrenceZero
#assert_no_axioms FX1Poly.Core.RawTerm.strengthen_eq_some_of_occurrenceZero
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst0_ghost
#assert_no_axioms FX1Poly.Typed.gradedGhostBetaErasesArgument
#assert_no_axioms FX1Poly.Typed.gradedGhostBetaErasesArgument_weakenWitness

end FX1PolyAudit
