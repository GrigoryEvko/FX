import FX1Poly.Core.SigmaProjectionClosedMembership
import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.BoolCanonicalFormsCandidate

namespace FX1Poly.Core
open StepStar

-- generic route: no bespoke cases proof, reuse isStepNormalForm_blocks_step + by decide
theorem fstClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_fst () (.childCons (pairCell boolTrueCell boolFalseCell) .childNil)) :=
  fstClosedIsMember
    (pairValue_isMember (by decide) (by decide))
    (fun first second reaches => by
      have eq := StepStar.eq_of_noStep
        (fun reduct step =>
          RawTerm.isStepNormalForm_blocks_step (by decide) reduct step) reaches
      injection eq with _scopeEq _genEq _payloadEq childrenEq
      injection childrenEq with _scopeC _shiftC _restShiftsC firstEq _tailC
      subst firstEq
      exact boolTrueCell_isMember)

theorem sndClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_snd () (.childCons (pairCell boolTrueCell boolFalseCell) .childNil)) :=
  sndClosedIsMember
    (pairValue_isMember (by decide) (by decide))
    (fun first second reaches => by
      have eq := StepStar.eq_of_noStep
        (fun reduct step =>
          RawTerm.isStepNormalForm_blocks_step (by decide) reduct step) reaches
      injection eq with _scopeEq _genEq _payloadEq childrenEq
      injection childrenEq with _scopeC _shiftC _restShiftsC _firstEq tailEq
      injection tailEq with _scopeC2 _shiftC2 _restShiftsC2 secondEq _nilC
      subst secondEq
      exact boolFalseCell_isMember)

#print axioms fstClosedMembershipSmoke
#print axioms sndClosedMembershipSmoke

end FX1Poly.Core
