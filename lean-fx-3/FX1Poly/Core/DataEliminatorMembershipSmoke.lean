import FX1Poly.Core.BoolElimClosedMembership

/-! # FX1Poly/Core/DataEliminatorMembershipSmoke
    — concrete closed-witness regression for the data-eliminator MEMBERSHIP family (SN-149 corpus seed).

The data-reducibility-member layer is complete: every data eliminator has a closed-membership theorem
(`boolElimClosedIsMember` #736, `fstClosedIsMember`/`sndClosedIsMember` #690, `idJClosedIsMember`/
`idStrictRecClosedIsMember` #691, `optionMatchClosedIsMember`/`eitherMatchClosedIsMember` #692, and the
recursive `natElim`/`natRec`/`listElim` membership in `RecursorClosedMembership` #732/#733).  This file
EXERCISES that family at a CONCRETE closed witness — not an alias — confirming the membership theorem and the
canonical value-member witnesses compose end-to-end into an actual closed inhabitant of the candidate.

A permanent regression: if a refactor breaks `boolElimClosedIsMember` or `boolTrueCell_isMember`, this fails.

## Zero-axiom

A single application of the shipped `boolElimClosedIsMember` to the shipped concrete bool value-members.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Core

/-- **Concrete data-eliminator membership regression.**  The closed `boolElim` cell with scrutinee
`boolTrue` and branches `boolTrue` / `boolFalse` — all canonical bool members — is itself a member of the
bool candidate.  The SN-063 elimination half exercised at a closed witness via `boolElimClosedIsMember` fed
the shipped `boolTrueCell_isMember` / `boolFalseCell_isMember`. -/
theorem boolElimClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_boolElim ()
        (.childCons boolTrueCell (.childCons boolTrueCell (.childCons boolFalseCell .childNil)))) :=
  boolElimClosedIsMember boolTrueCell_isMember boolTrueCell_isMember boolFalseCell_isMember

end FX1Poly.Core
