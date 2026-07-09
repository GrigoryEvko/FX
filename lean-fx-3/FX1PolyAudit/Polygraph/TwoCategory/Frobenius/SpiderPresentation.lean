import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderPresentation

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderPresentation — zero-axiom gate (WP-FROB r2, FROB-1)

Per-declaration zero-axiom gate for the special / extraspecial commutative-Frobenius spider PRESENTATION: the
thirteen relation rows + the bone row (as `BrauerRelation` data), the two presentation lists, the top-boundary arity
reader, every per-row PARALLELISM witness and its conjunction, the seven STAGED process reductions feeding the
depth-2 four-port soundness rows, every per-row SOUNDNESS witness (special + extraspecial) and their conjunctions,
the both-directions non-vacuity witnesses, and the eight honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-1: the relation rows (as data)
#assert_no_axioms FX1Poly.Polygraph.frobAssoc
#assert_no_axioms FX1Poly.Polygraph.frobUnitLeft
#assert_no_axioms FX1Poly.Polygraph.frobUnitRight
#assert_no_axioms FX1Poly.Polygraph.frobCoassoc
#assert_no_axioms FX1Poly.Polygraph.frobCounitLeft
#assert_no_axioms FX1Poly.Polygraph.frobCounitRight
#assert_no_axioms FX1Poly.Polygraph.frobLeft
#assert_no_axioms FX1Poly.Polygraph.frobRight
#assert_no_axioms FX1Poly.Polygraph.frobCommMult
#assert_no_axioms FX1Poly.Polygraph.frobCommComult
#assert_no_axioms FX1Poly.Polygraph.frobCrossingInvolution
#assert_no_axioms FX1Poly.Polygraph.frobYangBaxter
#assert_no_axioms FX1Poly.Polygraph.frobSpecial
#assert_no_axioms FX1Poly.Polygraph.frobBone
#assert_no_axioms FX1Poly.Polygraph.specialFrobeniusPresentation
#assert_no_axioms FX1Poly.Polygraph.extraSpecialPresentation

-- FROB-1: the top-boundary arity reader
#assert_no_axioms FX1Poly.Polygraph.frobWordOutputCount

-- FROB-1: per-row PARALLELISM + the conjunction
#assert_no_axioms FX1Poly.Polygraph.frobAssoc_parallel
#assert_no_axioms FX1Poly.Polygraph.frobUnitLeft_parallel
#assert_no_axioms FX1Poly.Polygraph.frobUnitRight_parallel
#assert_no_axioms FX1Poly.Polygraph.frobCoassoc_parallel
#assert_no_axioms FX1Poly.Polygraph.frobCounitLeft_parallel
#assert_no_axioms FX1Poly.Polygraph.frobCounitRight_parallel
#assert_no_axioms FX1Poly.Polygraph.frobLeft_parallel
#assert_no_axioms FX1Poly.Polygraph.frobRight_parallel
#assert_no_axioms FX1Poly.Polygraph.frobCommMult_parallel
#assert_no_axioms FX1Poly.Polygraph.frobCommComult_parallel
#assert_no_axioms FX1Poly.Polygraph.frobCrossingInvolution_parallel
#assert_no_axioms FX1Poly.Polygraph.frobYangBaxter_parallel
#assert_no_axioms FX1Poly.Polygraph.frobSpecial_parallel
#assert_no_axioms FX1Poly.Polygraph.frobBone_parallel
#assert_no_axioms FX1Poly.Polygraph.specialFrobeniusPresentation_allParallel

-- FROB-1: the seven STAGED process reductions (the perf-critical depth-2 four-port reductions)
#assert_no_axioms FX1Poly.Polygraph.frobAssocLhsProcess
#assert_no_axioms FX1Poly.Polygraph.frobAssocRhsProcess
#assert_no_axioms FX1Poly.Polygraph.frobCoassocLhsProcess
#assert_no_axioms FX1Poly.Polygraph.frobCoassocRhsProcess
#assert_no_axioms FX1Poly.Polygraph.frobLeftLhsProcess
#assert_no_axioms FX1Poly.Polygraph.frobHElementProcess
#assert_no_axioms FX1Poly.Polygraph.frobRightLhsProcess

-- FROB-1: per-row SOUNDNESS under the special (Cospan) invariant + the conjunction
#assert_no_axioms FX1Poly.Polygraph.frobAssoc_sound
#assert_no_axioms FX1Poly.Polygraph.frobUnitLeft_sound
#assert_no_axioms FX1Poly.Polygraph.frobUnitRight_sound
#assert_no_axioms FX1Poly.Polygraph.frobCoassoc_sound
#assert_no_axioms FX1Poly.Polygraph.frobCounitLeft_sound
#assert_no_axioms FX1Poly.Polygraph.frobCounitRight_sound
#assert_no_axioms FX1Poly.Polygraph.frobLeft_sound
#assert_no_axioms FX1Poly.Polygraph.frobRight_sound
#assert_no_axioms FX1Poly.Polygraph.frobCommMult_sound
#assert_no_axioms FX1Poly.Polygraph.frobCommComult_sound
#assert_no_axioms FX1Poly.Polygraph.frobCrossingInvolution_sound
#assert_no_axioms FX1Poly.Polygraph.frobYangBaxter_sound
#assert_no_axioms FX1Poly.Polygraph.frobSpecial_sound
#assert_no_axioms FX1Poly.Polygraph.specialFrobeniusPresentation_allSound

-- FROB-1: the extraspecial (partition-only / corelation) soundness + the conjunction
#assert_no_axioms FX1Poly.Polygraph.frobBone_extraSound
#assert_no_axioms FX1Poly.Polygraph.extraSpecialPresentation_allSound

-- FROB-1: both-directions non-vacuity (identification / separation / the seed choice)
#assert_no_axioms FX1Poly.Polygraph.frobLeft_identifies_distinct_words
#assert_no_axioms FX1Poly.Polygraph.frobeniusH_ne_identity
#assert_no_axioms FX1Poly.Polygraph.special_separates_bone_extraspecial_identifies

-- FROB-1: the honesty markers (true = backed by green theorems; false = honest open work)
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderPresentation
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpecialFrobeniusPresentation
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasExtraSpecialBone
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasPerRelationSoundnessAtSeed
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasPartitionSoundness
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasContextualSpiderSoundness
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSymbolicSaturatedConvOver
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderCompleteness

end FX1PolyAudit
