import FX1Poly.Core.BoolElimClosedMembership
import FX1Poly.Core.IdEliminatorClosedMembership
import FX1Poly.Core.ReflCanonicalFormsCandidate

/-! # FX1Poly/Core/DataEliminatorMembershipSmoke
    — concrete closed-witness regression for the data-eliminator MEMBERSHIP family (SN-149 corpus seed).

The data-reducibility-member layer is complete: every data eliminator has a closed-membership theorem
(`boolElimClosedIsMember` #736, `fstClosedIsMember`/`sndClosedIsMember` #690, `idJClosedIsMember`/
`idStrictRecClosedIsMember` #691, `optionMatchClosedIsMember`/`eitherMatchClosedIsMember` #692, and the
recursive `natElim`/`natRec`/`listElim` membership in `RecursorClosedMembership` #732/#733).  This file
EXERCISES that family at a CONCRETE closed witness — not an alias — confirming the membership theorem and the
canonical value-member witnesses compose end-to-end into an actual closed inhabitant of the candidate.

A permanent regression: if a refactor breaks `boolElimClosedIsMember` or `boolTrueCell_isMember`, this fails.

## Corpus coverage (clean-signature slice complete)

Concrete smoke witnesses are shipped for every eliminator whose closed-membership lemma takes ONLY
`CanonicalFormsPredicate`-member hypotheses — no `↝*`-inversion, no `respectsSN` side condition:
`boolElimClosedMembershipSmoke` (#736), `idJClosedMembershipSmoke` / `idStrictRecClosedMembershipSmoke`
(#691, fed the `refl` value member).  The value-PROJECTING (`fstClosedIsMember` / `sndClosedIsMember`,
whose `firstComponentMember` quantifies over `scrutinee ↝* pairCell _ _`) and branch-APPLYING
(`optionMatch` / `eitherMatch`, with a `someBranchRespectsSN` obligation; the recursive `natElim` / `natRec`
/ `listElim` with an IH side) eliminators need closed-layer reduction-inversion machinery (the
StepStar-from-normal-form `StepStar.eq_of_noStep` plus a `childCons` injection, or a constant-branch
application weak-head expansion) to instantiate at a concrete witness — their MEMBERSHIP THEOREMS are
shipped and audit-gated; only the concrete regression witnesses await that inversion and are deferred.

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

/-- **Concrete idJ membership regression.**  The closed `idJ` cell with base case `boolTrue` and witness
`refl boolTrue` — the base case a canonical bool member, the witness a canonical refl member — is itself a
member of the bool candidate.  The SN-068 elimination half exercised at a closed witness via
`idJClosedIsMember` fed `boolTrueCell_isMember` and the refl member `isReflValue_isMember` (the witness'
inner term `boolTrue` is step-normal by `decide`). -/
theorem idJClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_idJ () (.childCons boolTrueCell (.childCons (reflCell boolTrueCell) .childNil))) :=
  idJClosedIsMember (isReflValue_isMember ⟨boolTrueCell, rfl, by decide⟩) boolTrueCell_isMember

/-- **Concrete idStrictRec membership regression.**  Identical to `idJClosedMembershipSmoke` at the strict
identity recursor `gen_idStrictRec` — the SN-069 elimination half at a closed witness via
`idStrictRecClosedIsMember`. -/
theorem idStrictRecClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_idStrictRec () (.childCons boolTrueCell (.childCons (reflCell boolTrueCell) .childNil))) :=
  idStrictRecClosedIsMember (isReflValue_isMember ⟨boolTrueCell, rfl, by decide⟩) boolTrueCell_isMember

end FX1Poly.Core
