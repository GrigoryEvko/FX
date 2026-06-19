import FX1Poly.Core.Eliminators.Sigma.SigmaProjectionClosedMembership
import FX1Poly.Core.Eliminators.Match.MatchClosedMembership
import FX1Poly.Core.Eliminators.Identity.IdEliminatorClosedMembership
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Core/Eliminators/Core/ClosedEliminatorDataTaitMembers
    — the closed-scope eliminator family over the head-expansion-closed data candidate (FTGEN-11)

The six NON-recursive, scope-0 eliminators — `fst`/`snd` (Σ projections), `optionMatch`/`eitherMatch` (sum
matchers), `idJ`/`idStrictRec` (path / strict identity recursors) — re-based onto `dataTaitCandidate`, the
head-expansion-closed candidate the fundamental theorem's FORMATION arm assigns.  Their Core companions
(`…ClosedIsMember`) are stated over `CanonicalFormsPredicate` (SN ∧ neutral-or-reaches-value) and are already
`headExpand`-free because at scope 0 data weak-head expansion holds unconditionally.

## The scope-0 bridge

At scope 0 the two candidates collapse to the SAME content: a closed term has NO neutral (`IsNeutral.noClosed`),
so `CanonicalFormsPredicate`'s "neutral ∨ reaches-value" collapses to "reaches-value" and `dataTaitCandidate`'s
"every reachable NF is value-or-neutral" collapses to "every reachable NF is a value".  The forward direction
`dataTaitCandidate → CanonicalFormsPredicate` is therefore UNCONDITIONAL at scope 0
(`dataTaitCandidate.toCanonicalFormsClosed`): take the SN-supplied normal form, dispatch the value-or-neutral
disjunct (neutral is impossible by `noClosed`), and that value witnesses "reaches-value".  This bridge feeds the
Core canonicity-reduction lemmas (which expect a `CanonicalFormsPredicate` scrutinee); the result is then built
DIRECTLY over `dataTaitCandidate` via `dataTaitCandidate_memberStepStarExpansion` (no reverse bridge needed,
which would require value-step-stability).

Each arm: cell SN (the eliminator's SN-from-SN-branches/base lemma); the scrutinee/witness canonical computation
(`pairCanonicalScrutineeProjectsToComponents` / `option·eitherMatchCanonicalScrutineeReduces` /
`id(StrictRec)CanonicalWitnessReducesToBase`, fed the bridged scrutinee) gives `cell ↝* contractum`; the
contractum is a `dataTaitCandidate` member (the component / branch-application / base-case premise, already over
`dataTaitCandidate`); `dataTaitCandidate_memberStepStarExpansion` lifts membership back to the cell.

Completes the FTGEN-11 reconciliation eliminator set: the four recursors (bool/nat/natRec/list) plus these six
closed eliminators are now ALL members of `dataTaitCandidate`, so the generic FT composes intro+elim on ONE
candidate.

## Zero-axiom verification

Direct composition of the shipped, audited Core lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The scope-0 forward bridge** `dataTaitCandidate → CanonicalFormsPredicate`.  A closed
`dataTaitCandidate` member is a `CanonicalFormsPredicate` member: it is SN (shared first conjunct), and its
SN-supplied normal form is a value (the value-or-neutral disjunct's neutral case is impossible at scope 0 by
`IsNeutral.noClosed`), witnessing the "reaches a value" disjunct.  Unconditional at scope 0; the ingredient the
closed eliminator arms use to feed the Core canonicity-reduction lemmas. -/
theorem dataTaitCandidate.toCanonicalFormsClosed {isValue : RawTerm 0 → Prop} {term : RawTerm 0}
    (member : dataTaitCandidate isValue term) : CanonicalFormsPredicate isValue term := by
  refine ⟨member.1, ?_⟩
  obtain ⟨normalForm, termToNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing member.1
  rcases member.2 normalForm termToNormalForm normalFormIsNormal with valueNormalForm | neutralNormalForm
  · exact Or.inr ⟨normalForm, termToNormalForm, valueNormalForm⟩
  · exact (IsNeutral.noClosed neutralNormalForm).elim

/-- **★ FTGEN-11 — closed `fst` over `dataTaitCandidate`.**  The first-projection of a Σ data-candidate member
scrutinee, whose first component is a member at every pair the scrutinee reaches, is a member. -/
theorem fstDataTaitMember {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (firstComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → dataTaitCandidate isValue first) :
    dataTaitCandidate isValue (.mkGen .gen_fst () (.childCons scrutinee .childNil)) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_fst () (.childCons scrutinee .childNil)) :=
    fst_isStronglyNormalizing_of_argument scrutineeMember.stronglyNormalizing
  obtain ⟨first, second, scrutineeToPair, fstReducesToFirst, _sndReducesToSecond⟩ :=
    pairCanonicalScrutineeProjectsToComponents (dataTaitCandidate.toCanonicalFormsClosed scrutineeMember)
  exact dataTaitCandidate_memberStepStarExpansion fstReducesToFirst cellStronglyNormalizing
    (firstComponentMember first second scrutineeToPair)

/-- **★ FTGEN-11 — closed `snd` over `dataTaitCandidate`.**  Symmetric to `fstDataTaitMember`. -/
theorem sndDataTaitMember {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (secondComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → dataTaitCandidate isValue second) :
    dataTaitCandidate isValue (.mkGen .gen_snd () (.childCons scrutinee .childNil)) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_snd () (.childCons scrutinee .childNil)) :=
    snd_isStronglyNormalizing_of_argument scrutineeMember.stronglyNormalizing
  obtain ⟨first, second, scrutineeToPair, _fstReducesToFirst, sndReducesToSecond⟩ :=
    pairCanonicalScrutineeProjectsToComponents (dataTaitCandidate.toCanonicalFormsClosed scrutineeMember)
  exact dataTaitCandidate_memberStepStarExpansion sndReducesToSecond cellStronglyNormalizing
    (secondComponentMember first second scrutineeToPair)

/-- **★ FTGEN-11 — closed `optionMatch` over `dataTaitCandidate`.**  The some-branch application premise and the
none-branch member are over `dataTaitCandidate`; the scrutinee is bridged to feed the canonical computation. -/
theorem optionMatchDataTaitMember {isValue : RawTerm 0 → Prop} {motive : RawTerm 1}
    {scrutinee noneBranch someBranch : RawTerm 0}
    (scrutineeMember : dataTaitCandidate isOptionValue scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (noneBranchMember : dataTaitCandidate isValue noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch)
    (someBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      dataTaitCandidate isValue (applicationCell someBranch value)) :
    dataTaitCandidate isValue
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) :=
    optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
      (fun value valueTerminates => (someBranchRespectsSN value valueTerminates).stronglyNormalizing)
      scrutineeMember.stronglyNormalizing motiveTerminates
      noneBranchMember.stronglyNormalizing someBranchTerminates
  rcases optionMatchCanonicalScrutineeReduces (motive := motive)
      (noneBranch := noneBranch) (someBranch := someBranch)
      (dataTaitCandidate.toCanonicalFormsClosed scrutineeMember) with
    reducesToNone | ⟨payload, scrutineeToSome, reducesToApp⟩
  · exact dataTaitCandidate_memberStepStarExpansion reducesToNone cellStronglyNormalizing noneBranchMember
  · have payloadTerminates : IsStronglyNormalizing payload :=
      StepStar.value_isStronglyNormalizing_of_optionSome
        (IsStronglyNormalizing.descendStepStar scrutineeMember.stronglyNormalizing scrutineeToSome)
    exact dataTaitCandidate_memberStepStarExpansion reducesToApp cellStronglyNormalizing
      (someBranchRespectsSN payload payloadTerminates)

/-- **★ FTGEN-11 — closed `eitherMatch` over `dataTaitCandidate`.**  Both branch-application premises over
`dataTaitCandidate`; symmetric to `optionMatchDataTaitMember` with no passive base. -/
theorem eitherMatchDataTaitMember {isValue : RawTerm 0 → Prop} {motive : RawTerm 1}
    {scrutinee leftBranch rightBranch : RawTerm 0}
    (scrutineeMember : dataTaitCandidate isEitherValue scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch)
    (leftBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      dataTaitCandidate isValue (applicationCell leftBranch value))
    (rightBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      dataTaitCandidate isValue (applicationCell rightBranch value)) :
    dataTaitCandidate isValue
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))) :=
    eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
      (fun value valueTerminates => (leftBranchRespectsSN value valueTerminates).stronglyNormalizing)
      (fun value valueTerminates => (rightBranchRespectsSN value valueTerminates).stronglyNormalizing)
      scrutineeMember.stronglyNormalizing motiveTerminates
      leftBranchTerminates rightBranchTerminates
  rcases eitherMatchCanonicalScrutineeReduces (motive := motive)
      (leftBranch := leftBranch) (rightBranch := rightBranch)
      (dataTaitCandidate.toCanonicalFormsClosed scrutineeMember) with
    ⟨payload, scrutineeToInl, reducesToLeftApp⟩ | ⟨payload, scrutineeToInr, reducesToRightApp⟩
  · have payloadTerminates : IsStronglyNormalizing payload :=
      StepStar.value_isStronglyNormalizing_of_eitherInl
        (IsStronglyNormalizing.descendStepStar scrutineeMember.stronglyNormalizing scrutineeToInl)
    exact dataTaitCandidate_memberStepStarExpansion reducesToLeftApp cellStronglyNormalizing
      (leftBranchRespectsSN payload payloadTerminates)
  · have payloadTerminates : IsStronglyNormalizing payload :=
      StepStar.value_isStronglyNormalizing_of_eitherInr
        (IsStronglyNormalizing.descendStepStar scrutineeMember.stronglyNormalizing scrutineeToInr)
    exact dataTaitCandidate_memberStepStarExpansion reducesToRightApp cellStronglyNormalizing
      (rightBranchRespectsSN payload payloadTerminates)

/-- **★ FTGEN-11 — closed `idJ` over `dataTaitCandidate`.**  The base case is a member at `dataTaitCandidate`;
the witness is bridged to feed the canonical witness computation `idJ base (refl w) ↝ base`. -/
theorem idJDataTaitMember {isValue : RawTerm 0 → Prop} {motive : RawTerm 2} {baseCase witness : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (witnessMember : dataTaitCandidate isReflValue witness)
    (baseCaseMember : dataTaitCandidate isValue baseCase) :
    dataTaitCandidate isValue
      (.mkGen .gen_idJ ()
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) := by
  have idJStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_idJ ()
          (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) :=
    idJ_isStronglyNormalizing_of_strongly_normalizing_base motiveStronglyNormalizing
      baseCaseMember.stronglyNormalizing witnessMember.stronglyNormalizing
  exact dataTaitCandidate_memberStepStarExpansion
    (idJCanonicalWitnessReducesToBase (dataTaitCandidate.toCanonicalFormsClosed witnessMember))
    idJStronglyNormalizing baseCaseMember

/-- **★ FTGEN-11 — closed `idStrictRec` over `dataTaitCandidate`.**  Symmetric to `idJDataTaitMember`. -/
theorem idStrictRecDataTaitMember {isValue : RawTerm 0 → Prop} {motive : RawTerm 2}
    {baseCase witness : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (witnessMember : dataTaitCandidate isReflValue witness)
    (baseCaseMember : dataTaitCandidate isValue baseCase) :
    dataTaitCandidate isValue
      (.mkGen .gen_idStrictRec ()
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) := by
  have idStrictRecStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_idStrictRec ()
          (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) :=
    idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base motiveStronglyNormalizing
      baseCaseMember.stronglyNormalizing witnessMember.stronglyNormalizing
  exact dataTaitCandidate_memberStepStarExpansion
    (idStrictRecCanonicalWitnessReducesToBase (dataTaitCandidate.toCanonicalFormsClosed witnessMember))
    idStrictRecStronglyNormalizing baseCaseMember

end FX1Poly.Core
