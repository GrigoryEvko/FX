import FX1Poly.Core.BoolElimClosedMembership
import FX1Poly.Core.IdEliminatorClosedMembership
import FX1Poly.Core.ReflCanonicalFormsCandidate
import FX1Poly.Core.SigmaProjectionClosedMembership
import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.MatchClosedMembership
import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Core.StrongNormalizationRedexes
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.WeakHeadStep

/-! # FX1Poly/Core/DataEliminatorMembershipSmoke
    — concrete closed-witness regression for the data-eliminator MEMBERSHIP family (SN-149 corpus seed).

The data-reducibility-member layer is complete: every data eliminator has a closed-membership theorem
(`boolElimClosedIsMember` #736, `fstClosedIsMember`/`sndClosedIsMember` #690, `idJClosedIsMember`/
`idStrictRecClosedIsMember` #691, `optionMatchClosedIsMember`/`eitherMatchClosedIsMember` #692, and the
recursive `natElim`/`natRec`/`listElim` membership in `RecursorClosedMembership` #732/#733).  This file
EXERCISES that family at a CONCRETE closed witness — not an alias — confirming the membership theorem and the
canonical value-member witnesses compose end-to-end into an actual closed inhabitant of the candidate.

A permanent regression: if a refactor breaks `boolElimClosedIsMember` or `boolTrueCell_isMember`, this fails.

## Corpus coverage (clean-signature + value-projecting + branch-applying slices complete)

Concrete smoke witnesses are shipped for every eliminator whose closed-membership lemma takes ONLY
`CanonicalFormsPredicate`-member hypotheses — no `↝*`-inversion, no `respectsSN` side condition:
`boolElimClosedMembershipSmoke` (#736), `idJClosedMembershipSmoke` / `idStrictRecClosedMembershipSmoke`
(#691, fed the `refl` value member).

The value-PROJECTING eliminators (`fstClosedIsMember` / `sndClosedIsMember`, whose component-member
obligation quantifies over `scrutinee ↝* pairCell _ _`) are shipped at a concrete witness:
`fstClosedMembershipSmoke` / `sndClosedMembershipSmoke` instantiate at `pairCell boolTrue boolFalse`.  The
inversion uses the route this docstring predicted — the pair is a structural normal form
(`RawTerm.isStepNormalForm_blocks_step` on `by decide`), so `StepStar.eq_of_noStep` forces the reaching
`↝*` reflexive and the `mkGen`/`childCons` injection (five outputs: scope / shift / restShifts / childHead /
childTail) pins the component to the canonical bool value.

The branch-APPLYING eliminators (`optionMatch` / `eitherMatch`, whose branch-respect-SN obligation quantifies
the branch APPLIED to an arbitrary SN argument) are now ALSO shipped:
`optionMatchClosedMembershipSmoke` (on `none`) / `eitherMatchClosedMembershipSmoke` (on `inl boolTrue`) feed
the constant branch `λ_. boolTrue` through `constLamBoolTrue_respectsSN` — the constant-branch weak-head
expansion this docstring named (`app (λ_. boolTrue) value` β-reduces to the bool value `boolTrue` for any
argument, SN by `appLamBoolTrue_isStronglyNormalizing_of_argument`).

The recursive `natElim` / `natRec` / `listElim` eliminators (with an IH side condition) remain the lone
deferred concrete witnesses — their MEMBERSHIP THEOREMS are shipped and audit-gated.

## Zero-axiom

The clean-signature witnesses are a single application of the shipped membership lemma to the shipped
concrete value-members.  The projection witnesses add `StepStar.eq_of_noStep` (fed `by decide`-discharged
normality through `RawTerm.isStepNormalForm_blocks_step`) and the structural `childCons` injection.  The
branch-applying witnesses add the single-β-step `WeakHeadStep.beta.toStep` (with `subst0 boolTrue value =
boolTrue` definitional) and `ofStepStarReachingValue` — all `propext`/`Quot.sound`-free.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Core

open StepStar

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

/-! ## Branch-applying eliminators (option / either) via the constant-branch weak-head expansion

The `optionMatch` / `eitherMatch` membership lemmas need a branch-respect-SN obligation: applying the branch
to an arbitrary SN argument must land in the result candidate.  The clean concrete witness is the CONSTANT
lambda `λ_. boolTrue` — its application β-reduces to `boolTrue` regardless of the argument.  `constLamBoolTrue_-
respectsSN` packages that: the redex `app (λ_. boolTrue) value` is SN
(`appLamBoolTrue_isStronglyNormalizing_of_argument`), β-reduces to `boolTrue` (`WeakHeadStep.beta.toStep`, with
`subst0 boolTrue value = boolTrue` definitional), and `boolTrue` is a bool value — so
`ofStepStarReachingValue` lifts it to candidate membership.  This is the "constant-branch weak-head expansion"
the corpus docstring named as the remaining prerequisite. -/

/-- The constant lambda `λ_. boolTrue` — its application reduces to `boolTrue` for any argument. -/
abbrev constLamBoolTrueCell : RawTerm 0 :=
  .mkGen .gen_lam () (.childCons boolTrueCell .childNil)

/-- **The constant lambda applied to any argument β-reduces to `boolTrue`.**  A single head β-step
(`WeakHeadStep.beta`): the contractum `subst0 boolTrue value` is `boolTrue` definitionally (the body is the
closed nullary `boolTrue`). -/
theorem constLamBoolTrue_app_stepStar (value : RawTerm 0) :
    StepStar (applicationCell constLamBoolTrueCell value) boolTrueCell :=
  StepStar.trans (WeakHeadStep.beta (body := boolTrueCell) (argument := value)).toStep
    (StepStar.refl _)

/-- **The constant branch respects SN.**  Applying `λ_. boolTrue` to ANY strongly-normalizing value yields a
bool-candidate member — the redex is SN and weak-head-reduces to the bool value `boolTrue`.  This is the
branch-respect-SN witness consumed by `optionMatchClosedIsMember` / `eitherMatchClosedIsMember`. -/
theorem constLamBoolTrue_respectsSN :
    ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate (boolIsValue (scope := 0))
        (applicationCell constLamBoolTrueCell value) :=
  fun value valueStronglyNormalizing =>
    CanonicalFormsPredicate.ofStepStarReachingValue
      (constLamBoolTrue_app_stepStar value)
      (appLamBoolTrue_isStronglyNormalizing_of_argument valueStronglyNormalizing)
      ⟨boolTrueCell, StepStar.refl _, Or.inl rfl⟩

/-- **Concrete `optionMatch` membership regression.**  The closed `optionMatch` on the `none` scrutinee with
none-branch `boolTrue` and some-branch `λ_. boolTrue` is a bool-candidate member.  Exercises the branch-applying
half of SN-065 at a concrete witness via `optionMatchClosedIsMember`: the `none` scrutinee is a canonical option
value, the none-branch is a bool member, and the some-branch terminates (`lam_isStronglyNormalizing_of_body`) and
respects SN (`constLamBoolTrue_respectsSN`). -/
theorem optionMatchClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_optionMatch ()
        (.childCons optionNoneCell
          (.childCons boolTrueCell (.childCons constLamBoolTrueCell .childNil)))) :=
  optionMatchClosedIsMember
    (isOptionValue_isMember (Or.inl rfl))
    boolTrueCell_isMember
    (lam_isStronglyNormalizing_of_body boolTrue_isStronglyNormalizing)
    constLamBoolTrue_respectsSN

/-- **Concrete `eitherMatch` membership regression.**  The closed `eitherMatch` on the `inl boolTrue` scrutinee
with both branches `λ_. boolTrue` is a bool-candidate member.  Symmetric to `optionMatchClosedMembershipSmoke`
but BOTH branches apply (no passive base), so both respect-SN witnesses are consumed.  The SN-066 elimination
half at a concrete witness. -/
theorem eitherMatchClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_eitherMatch ()
        (.childCons (eitherInlCell boolTrueCell)
          (.childCons constLamBoolTrueCell (.childCons constLamBoolTrueCell .childNil)))) :=
  eitherMatchClosedIsMember
    (isEitherValue_isMember (Or.inl ⟨boolTrueCell, rfl, by decide⟩))
    (lam_isStronglyNormalizing_of_body boolTrue_isStronglyNormalizing)
    (lam_isStronglyNormalizing_of_body boolTrue_isStronglyNormalizing)
    constLamBoolTrue_respectsSN
    constLamBoolTrue_respectsSN

end FX1Poly.Core
