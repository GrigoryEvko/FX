import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Canonicity.Consistency.EmptyTypeConsistencyNativeUnion

/-! # FX1PolyAudit/AuditEmptyTypeConsistencyNativeUnion — TYTAB-2-FT consistency-route audit shard

Per-declaration zero-axiom gate for the assembled NATIVE union consistency route (`HasTypeUnion`'s closed
empty-type uninhabitedness, gated on the three named FT-lane residuals — native SN, iterated union subject
reduction, closed-normal canonicity).  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.consistencyOfNativeSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.subjectReductionStarFromSingleStep
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.consistencyOfNativeSingleStepSubjectReduction

-- Gate 3 (closed-normal canonicity at the empty type) DISCHARGED — the empty-type twin of the lane master.
#assert_no_axioms FX1Poly.Typed.headReaches_emptyTypeCell
#assert_no_axioms FX1Poly.Typed.refuteConvToEmptyFromStableHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNormalNoInhabitantAtEmptyType
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNormalEmptyTypeHasNoInhabitant
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.coreFragmentConsistencyOfSnAndSingleStepSR

-- Gate 2 (single-step union SR) decomposed into two named closers — consistency now rests on SN + two closers.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.coreFragmentConsistencyFromClosers

-- Gate-2 redex half DISCHARGED — consistency now rests on SN + the congruence closer ONLY.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.coreFragmentConsistencyFromCongruenceCloser

-- Gate-2 congruence half REDUCED to one arm — consistency now rests on SN + the ELIMINATOR congruence closer.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.coreFragmentConsistencyFromElimCongruenceCloser

-- The ofGrown-FREE native kernel carries its OWN consistency statement (the #1698 RETIRE leg).
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.coreFragmentConsistencyFromElimCongruenceCloser

-- The ofGrown-FREE native kernel carries its OWN closed-normal canonicity (UNCONDITIONAL, the #1698 RETIRE leg).
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.closedNormalEmptyTypeHasNoInhabitant

end FX1PolyAudit
