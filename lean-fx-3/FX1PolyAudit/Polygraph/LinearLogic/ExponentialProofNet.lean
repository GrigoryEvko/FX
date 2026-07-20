import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.LinearLogic.ExponentialProofNet

/-! # FX1PolyAudit.Polygraph.LinearLogic.ExponentialProofNet — zero-axiom gate
    (linear-exponential `!`-comonad over the finite-multiset model)

Per-declaration zero-axiom gate for the exponential layer: the finite-multiset carrier and its decidable
equality / union; the resource-store `!` functor with the four exponential generators (dereliction,
digging, weakening, contraction); the comonad laws and the multiset commutative-comonoid laws; the
promotion-free exponential-fragment word decision; the honest MELL wall; and the ground fires.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (deliberately, per task constraint). -/

namespace FX1PolyAudit

-- T1: the finite-multiset carrier
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngNorm
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMultisetEq
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngEmpty
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMerge

-- T1: the ! functor + the four exponential generators
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.BngBang
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngBangMap
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngDereliction
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngDigging
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngWeakening
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngContraction

-- T2: the comonad laws (resource-store witness)
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngBangMap_id
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngDereliction_natural
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngDigging_natural
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngCounit_comult
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMap_counit_comult
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngComult_comult

-- T2: the comonoid laws (trivial store part)
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngWeakening_unit
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngContraction_cocomm

-- T2: the comonoid laws on the multiset (structural free-commutative-monoid content)
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngAppendNil
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngPushCons
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngAppendComm
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMergeEmptyLeft
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMergeEmptyRight
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMergeAssoc
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMergeComm
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngMergeComm_decides

-- T3: the promotion-free exponential-fragment word decision
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngDecideFragment
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngFragmentSound
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngFragmentDecisionCorrect

-- T3/T4: capability markers + the MELL wall
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngHasMultisetComonadModel
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngHasCommComonoidLaws
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngHasPromotionFreeFragmentDecision
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngHasMellWordProblem

-- T5: the ground fires
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngFireCounitComult
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngFireContractThenWeaken
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngFireFragmentEqual
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.bngFireFragmentControl

end FX1PolyAudit
