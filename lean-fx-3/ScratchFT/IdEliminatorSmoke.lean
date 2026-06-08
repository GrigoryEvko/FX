import FX1Poly.Core.IdEliminatorClosedMembership
import FX1Poly.Core.ReflCanonicalFormsCandidate
import FX1Poly.Core.BoolCanonicalFormsCandidate

namespace FX1Poly.Core

theorem idJClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_idJ () (.childCons boolTrueCell (.childCons (reflCell boolTrueCell) .childNil))) :=
  idJClosedIsMember (isReflValue_isMember ⟨boolTrueCell, rfl, by decide⟩) boolTrueCell_isMember

theorem idStrictRecClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_idStrictRec () (.childCons boolTrueCell (.childCons (reflCell boolTrueCell) .childNil))) :=
  idStrictRecClosedIsMember (isReflValue_isMember ⟨boolTrueCell, rfl, by decide⟩) boolTrueCell_isMember

#print axioms idJClosedMembershipSmoke
#print axioms idStrictRecClosedMembershipSmoke

end FX1Poly.Core
