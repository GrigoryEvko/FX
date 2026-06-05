import FX1Poly.Core.BoolElimClosedMembership
import FX1Poly.Core.IdEliminatorClosedMembership
import FX1Poly.Core.ReflCanonicalFormsCandidate
import FX1Poly.Core.SigmaProjectionClosedMembership
import FX1Poly.Core.PairCanonicalFormsCandidate

/-! # FX1Poly/Core/DataEliminatorMembershipSmoke
    — concrete closed-witness regression for the data-eliminator MEMBERSHIP family (SN-149 corpus seed).

The data-reducibility-member layer is complete: every data eliminator has a closed-membership theorem
(`boolElimClosedIsMember` #736, `fstClosedIsMember`/`sndClosedIsMember` #690, `idJClosedIsMember`/
`idStrictRecClosedIsMember` #691, `optionMatchClosedIsMember`/`eitherMatchClosedIsMember` #692, and the
recursive `natElim`/`natRec`/`listElim` membership in `RecursorClosedMembership` #732/#733).  This file
EXERCISES that family at a CONCRETE closed witness — not an alias — confirming the membership theorem and the
canonical value-member witnesses compose end-to-end into an actual closed inhabitant of the candidate.

A permanent regression: if a refactor breaks `boolElimClosedIsMember` or `boolTrueCell_isMember`, this fails.

## Corpus coverage (clean-signature + value-projecting slices complete)

Concrete smoke witnesses are shipped for every eliminator whose closed-membership lemma takes ONLY
`CanonicalFormsPredicate`-member hypotheses — no `↝*`-inversion, no `respectsSN` side condition:
`boolElimClosedMembershipSmoke` (#736), `idJClosedMembershipSmoke` / `idStrictRecClosedMembershipSmoke`
(#691, fed the `refl` value member).

The value-PROJECTING eliminators (`fstClosedIsMember` / `sndClosedIsMember`, whose component-member
obligation quantifies over `scrutinee ↝* pairCell _ _`) are now ALSO shipped at a concrete witness:
`fstClosedMembershipSmoke` / `sndClosedMembershipSmoke` instantiate at `pairCell boolTrue boolFalse`.  The
inversion uses exactly the route this docstring predicted — the pair is a structural normal form
(`RawTerm.isStepNormalForm_blocks_step` on `by decide`), so `StepStar.eq_of_noStep` forces the reaching
`↝*` reflexive and the `mkGen`/`childCons` injection (five outputs: scope / shift / restShifts / childHead /
childTail) pins the component to the canonical bool value.

The branch-APPLYING (`optionMatch` / `eitherMatch`, with a `someBranchRespectsSN` obligation; the recursive
`natElim` / `natRec` / `listElim` with an IH side) eliminators still need a constant-branch application
weak-head expansion to instantiate at a concrete witness — their MEMBERSHIP THEOREMS are shipped and
audit-gated; only those concrete regression witnesses remain deferred.

## Zero-axiom

The clean-signature witnesses are a single application of the shipped membership lemma to the shipped
concrete value-members.  The projection witnesses add `StepStar.eq_of_noStep` (fed `by decide`-discharged
normality through `RawTerm.isStepNormalForm_blocks_step`) and the structural `childCons` injection — both
`propext`/`Quot.sound`-free.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated.
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

/-- **Concrete `fst` projection membership regression.**  The closed `fst` cell over the canonical pair
`pairCell boolTrue boolFalse` is a member of the bool candidate (its first component `boolTrue` being a
member).  Exercises the value-PROJECTING half of SN-058 at a concrete witness via `fstClosedIsMember`.  The
component obligation is discharged by inverting the reaching `↝*`: the pair is a structural normal form, so
`RawTerm.isStepNormalForm_blocks_step` (on `by decide`) forces it reflexive through `StepStar.eq_of_noStep`,
and the `mkGen`/`childCons` injection pins the first component to `boolTrue`. -/
theorem fstClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_fst () (.childCons (pairCell boolTrueCell boolFalseCell) .childNil)) :=
  fstClosedIsMember
    (pairValue_isMember (by decide) (by decide))
    (fun first second reaches => by
      have componentEq := StepStar.eq_of_noStep
        (fun reduct step =>
          RawTerm.isStepNormalForm_blocks_step (by decide) reduct step) reaches
      injection componentEq with _scopeEq _genEq _payloadEq childrenEq
      injection childrenEq with _scopeChild _shiftChild _restShiftsChild firstEq _tailChild
      subst firstEq
      exact boolTrueCell_isMember)

/-- **Concrete `snd` projection membership regression.**  Symmetric to `fstClosedMembershipSmoke` at the
second projection — the closed `snd` cell over `pairCell boolTrue boolFalse` is a member of the bool
candidate (its second component `boolFalse` being a member).  The inversion drills one extra `childCons` to
reach the tail's head, pinning the second component to `boolFalse`. -/
theorem sndClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_snd () (.childCons (pairCell boolTrueCell boolFalseCell) .childNil)) :=
  sndClosedIsMember
    (pairValue_isMember (by decide) (by decide))
    (fun first second reaches => by
      have componentEq := StepStar.eq_of_noStep
        (fun reduct step =>
          RawTerm.isStepNormalForm_blocks_step (by decide) reduct step) reaches
      injection componentEq with _scopeEq _genEq _payloadEq childrenEq
      injection childrenEq with _scopeChild _shiftChild _restShiftsChild _firstEq tailEq
      injection tailEq with _scopeTail _shiftTail _restShiftsTail secondEq _nilTail
      subst secondEq
      exact boolFalseCell_isMember)

end FX1Poly.Core
