import FX1Poly.Core.SigmaProjectionClosedMembership
import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.BoolCanonicalFormsCandidate

namespace FX1Poly.Core
open StepStar

theorem pairCell_noStep :
    ∀ reduct : RawTerm 0,
      Step (pairCell boolTrueCell boolFalseCell) reduct → False := by
  intro reduct step
  cases step with
  | cong _ _ childStep =>
      cases childStep with
      | here _ headStep => nomatch headStep
      | there _ restStep =>
          cases restStep with
          | here _ headStep => nomatch headStep
          | there _ restStep2 => nomatch restStep2

-- probe the injection in isolation
example (first second : RawTerm 0)
    (eq : pairCell first second = pairCell boolTrueCell boolFalseCell) :
    first = boolTrueCell := by
  injection eq with childrenEq
  injection childrenEq with firstEq _restEq
  exact firstEq

theorem fstClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_fst () (.childCons (pairCell boolTrueCell boolFalseCell) .childNil)) :=
  fstClosedIsMember
    (pairValue_isMember (by decide) (by decide))
    (fun first second reaches => by
      have eq := StepStar.eq_of_noStep pairCell_noStep reaches
      injection eq with childrenEq
      injection childrenEq with firstEq _restEq
      subst firstEq
      exact boolTrueCell_isMember)

#print axioms fstClosedMembershipSmoke

end FX1Poly.Core
