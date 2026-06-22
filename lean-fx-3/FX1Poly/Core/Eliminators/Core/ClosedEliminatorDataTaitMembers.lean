import FX1Poly.Core.Eliminators.Sigma.SigmaProjectionClosedMembership
import FX1Poly.Core.Eliminators.Match.MatchClosedMembership
import FX1Poly.Core.Eliminators.Identity.IdEliminatorClosedMembership
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Eliminators.Core.DataTaitEliminatorDispatch

/-! # FX1Poly/Core/Eliminators/Core/ClosedEliminatorDataTaitMembers
    — the non-recursive eliminator family over the head-expansion-closed data candidate (FTGEN-11.2, OPEN scope)

The six NON-recursive eliminators — `fst`/`snd` (Σ projections), `optionMatch`/`eitherMatch` (sum matchers),
`idJ`/`idStrictRec` (path / strict identity recursors) — as members of `dataTaitCandidate`, the
head-expansion-closed candidate the fundamental theorem's FORMATION arm assigns, at ARBITRARY scope
(FTGEN-11.2).  (The filename is historical: these were scope-0-only until FTGEN-11.2 lifted them to `{scope}`;
the four recursors `bool`/`nat`/`natRec`/`list` are the recursive companions in the sibling `…DataTaitMember`
files.)

## Value/neutral dispatch (the open route)

Each arm follows the recursive-eliminator template (`natElimDataTaitMember`): obtain the scrutinee/witness's
strongly-normalizing normal form (`exists_normalForm_of_isStronglyNormalizing`), then `rcases` on
`dataTaitCandidate`'s second conjunct — the normal form is a VALUE or `IsNeutral`.  In the VALUE case the value
predicate (`isPairValue`/`isOptionValue`/`isEitherValue`/`isReflValue`) `obtain`s the constructor decomposition,
the scope-polymorphic scrutinee congruence (`StepStar.fstScrutinee`/`optionMatchScrutinee`/`idJWitness`/…) carries
the scrutinee reduction under the eliminator, and the matching `IotaHeadStep` ι row (`iotaFstPair`/
`iotaOptionMatchNone`/`iotaOptionMatchSome`/`iotaEitherMatchInl`/`iotaEitherMatchInr`/`iotaIdJRefl`/…) projects /
selects / applies / computes the contractum; the contractum is a `dataTaitCandidate` member (the component /
branch-application / base-case premise, already over `dataTaitCandidate`).  In the NEUTRAL case the eliminator
cell stays neutral (`IsNeutral.fst`/`optionMatch`/`idJ`/…) and is a member by
`dataTaitCandidate.memberOfStronglyNormalizingNeutral`.  Both lift back through the same scrutinee congruence by
`dataTaitCandidate_memberStepStarExpansion`.  At scope 0 the neutral branch is vacuous (`IsNeutral.noClosed`), so
the open statements specialize exactly to the former closed ones.

The scope-0 forward bridge `dataTaitCandidate.toCanonicalFormsClosed` (retained below) is the scope-0 collapse it
superseded — kept as the `CanonicalFormsPredicate` interface for the closed canonical-computation lemmas.

Completes the FTGEN-11 reconciliation eliminator set at OPEN scope: the four recursors (bool/nat/natRec/list)
plus these six are now ALL members of `dataTaitCandidate` at arbitrary scope — the complete arm set the native
fundamental-theorem induction over the union typing relation consumes.

## Zero-axiom verification

Direct composition of the shipped, audited Core lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The scope-0 forward bridge** `dataTaitCandidate → CanonicalFormsPredicate`.  A closed
`dataTaitCandidate` member is a `CanonicalFormsPredicate` member: it is SN (shared first conjunct), and its
SN-supplied normal form is a value (the value-or-neutral disjunct's neutral case is impossible at scope 0 by
`IsNeutral.noClosed`), witnessing the "reaches a value" disjunct.  Unconditional at scope 0; retained as the
`CanonicalFormsPredicate` bridge feeding the closed canonical-computation lemmas (the eliminator arms above no
longer consume it since FTGEN-11.2 routes them through the open value/neutral dispatch). -/
theorem dataTaitCandidate.toCanonicalFormsClosed {isValue : RawTerm 0 → Prop} {term : RawTerm 0}
    (member : dataTaitCandidate isValue term) : CanonicalFormsPredicate isValue term := by
  refine ⟨member.1, ?_⟩
  obtain ⟨normalForm, termToNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing member.1
  rcases member.2 normalForm termToNormalForm normalFormIsNormal with valueNormalForm | neutralNormalForm
  · exact Or.inr ⟨normalForm, termToNormalForm, valueNormalForm⟩
  · exact (IsNeutral.noClosed neutralNormalForm).elim

/-- **★ FTGEN-11.2 — open `fst` over `dataTaitCandidate`.**  The first-projection of a Σ data-candidate member
scrutinee, whose first component is a member at every pair the scrutinee reaches, is a member — at ARBITRARY
scope.  The scrutinee's strongly-normalizing normal form is value-or-neutral (`dataTaitCandidate`'s second
conjunct): a pair VALUE ι-projects to its first component (`StepStar.fstScrutinee` congruence then
`IotaHeadStep.iotaFstPair`), while a NEUTRAL normal form leaves the projection cell neutral (`IsNeutral.fst` +
`memberOfStronglyNormalizingNeutral`); both lift back through the same scrutinee congruence by
`dataTaitCandidate_memberStepStarExpansion`.  Generalizes the former scope-0 statement (which routed through
`toCanonicalFormsClosed` and so could not see the neutral case); at scope 0 the neutral branch is vacuous. -/
theorem fstDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop} {scrutinee : RawTerm scope}
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (firstComponentMember : ∀ first second : RawTerm scope,
      StepStar scrutinee (pairCell first second) → dataTaitCandidate isValue first) :
    dataTaitCandidate isValue (.mkGen .gen_fst () (.childCons scrutinee .childNil)) :=
  dataTaitEliminatorMemberViaNormalForm
    (cellSpine := fun argument => .mkGen .gen_fst () (.childCons argument .childNil))
    scrutineeMember
    (fun argumentStronglyNormalizing => fst_isStronglyNormalizing_of_argument argumentStronglyNormalizing)
    (fun scrutineeReduction => StepStar.fstScrutinee scrutineeReduction)
    (fun normalFormIsPair valueStronglyNormalizing _reaches => by
      obtain ⟨firstComponent, secondComponent, normalFormEq, _firstNormal, _secondNormal⟩ := normalFormIsPair
      subst normalFormEq
      exact dataTaitCandidate_memberStepStarExpansion
        (StepStar.single IotaHeadStep.iotaFstPair.toStep)
        (fst_isStronglyNormalizing_of_argument valueStronglyNormalizing)
        (firstComponentMember firstComponent secondComponent _reaches))
    (fun normalFormIsNeutral => IsNeutral.fst normalFormIsNeutral)

/-- **★ FTGEN-11.2 — open `snd` over `dataTaitCandidate`.**  Symmetric to `fstDataTaitMember`: the
second-projection ι-selects the second component on a pair value (`IotaHeadStep.iotaSndPair`), stays neutral on
a neutral scrutinee (`IsNeutral.snd`), at arbitrary scope. -/
theorem sndDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop} {scrutinee : RawTerm scope}
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (secondComponentMember : ∀ first second : RawTerm scope,
      StepStar scrutinee (pairCell first second) → dataTaitCandidate isValue second) :
    dataTaitCandidate isValue (.mkGen .gen_snd () (.childCons scrutinee .childNil)) :=
  dataTaitEliminatorMemberViaNormalForm
    (cellSpine := fun argument => .mkGen .gen_snd () (.childCons argument .childNil))
    scrutineeMember
    (fun argumentStronglyNormalizing => snd_isStronglyNormalizing_of_argument argumentStronglyNormalizing)
    (fun scrutineeReduction => StepStar.sndScrutinee scrutineeReduction)
    (fun normalFormIsPair valueStronglyNormalizing reaches => by
      obtain ⟨firstComponent, secondComponent, normalFormEq, _firstNormal, _secondNormal⟩ := normalFormIsPair
      subst normalFormEq
      exact dataTaitCandidate_memberStepStarExpansion
        (StepStar.single IotaHeadStep.iotaSndPair.toStep)
        (snd_isStronglyNormalizing_of_argument valueStronglyNormalizing)
        (secondComponentMember firstComponent secondComponent reaches))
    (fun normalFormIsNeutral => IsNeutral.snd normalFormIsNeutral)

/-- **★ FTGEN-11.2 — open `optionMatch` over `dataTaitCandidate`.**  The some-branch application premise and the
none-branch member are over `dataTaitCandidate` — at ARBITRARY scope.  The scrutinee's SN normal form is
value-or-neutral: a `none` value ι-selects the none-branch (`IotaHeadStep.iotaOptionMatchNone`), a `some payload`
value ι-applies the some-branch to the (strongly-normalizing) payload (`IotaHeadStep.iotaOptionMatchSome` +
`value_isStronglyNormalizing_of_optionSome`), and a NEUTRAL scrutinee leaves the cell neutral
(`IsNeutral.optionMatch`); each lifts back through `StepStar.optionMatchScrutinee` by
`dataTaitCandidate_memberStepStarExpansion`.  Generalizes the former scope-0 statement. -/
theorem optionMatchDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop} {motive : RawTerm (scope + 1)}
    {scrutinee noneBranch someBranch : RawTerm scope}
    (scrutineeMember : dataTaitCandidate isOptionValue scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (noneBranchMember : dataTaitCandidate isValue noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch)
    (someBranchRespectsSN : ∀ value : RawTerm scope, IsStronglyNormalizing value →
      dataTaitCandidate isValue (applicationCell someBranch value)) :
    dataTaitCandidate isValue
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) :=
  dataTaitEliminatorMemberViaNormalForm
    (cellSpine := fun argument =>
      .mkGen .gen_optionMatch ()
        (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons argument .childNil)))))
    scrutineeMember
    (fun argumentStronglyNormalizing =>
      optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
        (fun value valueTerminates => (someBranchRespectsSN value valueTerminates).stronglyNormalizing)
        argumentStronglyNormalizing motiveTerminates
        noneBranchMember.stronglyNormalizing someBranchTerminates)
    (fun scrutineeReduction => StepStar.optionMatchScrutinee scrutineeReduction)
    (fun normalFormIsOption valueStronglyNormalizing _reaches => by
      rcases normalFormIsOption with normalFormIsNone | ⟨payload, normalFormIsSome, _payloadNormal⟩
      · subst normalFormIsNone
        exact dataTaitCandidate_memberStepStarExpansion
          (StepStar.single IotaHeadStep.iotaOptionMatchNone.toStep)
          (optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
            (fun value valueTerminates => (someBranchRespectsSN value valueTerminates).stronglyNormalizing)
            valueStronglyNormalizing motiveTerminates
            noneBranchMember.stronglyNormalizing someBranchTerminates)
          noneBranchMember
      · subst normalFormIsSome
        have payloadTerminates : IsStronglyNormalizing payload :=
          StepStar.value_isStronglyNormalizing_of_optionSome valueStronglyNormalizing
        exact dataTaitCandidate_memberStepStarExpansion
          (StepStar.single IotaHeadStep.iotaOptionMatchSome.toStep)
          (optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
            (fun value valueTerminates => (someBranchRespectsSN value valueTerminates).stronglyNormalizing)
            valueStronglyNormalizing motiveTerminates
            noneBranchMember.stronglyNormalizing someBranchTerminates)
          (someBranchRespectsSN payload payloadTerminates))
    (fun normalFormIsNeutral => IsNeutral.optionMatch normalFormIsNeutral)

/-- **★ FTGEN-11.2 — open `eitherMatch` over `dataTaitCandidate`.**  Both branch-application premises over
`dataTaitCandidate`; symmetric to `optionMatchDataTaitMember` with no passive base — an `inl`/`inr` value
ι-applies the matching branch to its (strongly-normalizing) payload, a neutral scrutinee stays neutral
(`IsNeutral.eitherMatch`), at arbitrary scope. -/
theorem eitherMatchDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop} {motive : RawTerm (scope + 1)}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    (scrutineeMember : dataTaitCandidate isEitherValue scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch)
    (leftBranchRespectsSN : ∀ value : RawTerm scope, IsStronglyNormalizing value →
      dataTaitCandidate isValue (applicationCell leftBranch value))
    (rightBranchRespectsSN : ∀ value : RawTerm scope, IsStronglyNormalizing value →
      dataTaitCandidate isValue (applicationCell rightBranch value)) :
    dataTaitCandidate isValue
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))) :=
  dataTaitEliminatorMemberViaNormalForm
    (cellSpine := fun argument =>
      .mkGen .gen_eitherMatch ()
        (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons argument .childNil)))))
    scrutineeMember
    (fun argumentStronglyNormalizing =>
      eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
        (fun value valueTerminates => (leftBranchRespectsSN value valueTerminates).stronglyNormalizing)
        (fun value valueTerminates => (rightBranchRespectsSN value valueTerminates).stronglyNormalizing)
        argumentStronglyNormalizing motiveTerminates
        leftBranchTerminates rightBranchTerminates)
    (fun scrutineeReduction => StepStar.eitherMatchScrutinee scrutineeReduction)
    (fun normalFormIsEither valueStronglyNormalizing _reaches => by
      rcases normalFormIsEither with
        ⟨payload, normalFormIsInl, _payloadNormal⟩ | ⟨payload, normalFormIsInr, _payloadNormal⟩
      · subst normalFormIsInl
        have payloadTerminates : IsStronglyNormalizing payload :=
          StepStar.value_isStronglyNormalizing_of_eitherInl valueStronglyNormalizing
        exact dataTaitCandidate_memberStepStarExpansion
          (StepStar.single IotaHeadStep.iotaEitherMatchInl.toStep)
          (eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
            (fun value valueTerminates => (leftBranchRespectsSN value valueTerminates).stronglyNormalizing)
            (fun value valueTerminates => (rightBranchRespectsSN value valueTerminates).stronglyNormalizing)
            valueStronglyNormalizing motiveTerminates
            leftBranchTerminates rightBranchTerminates)
          (leftBranchRespectsSN payload payloadTerminates)
      · subst normalFormIsInr
        have payloadTerminates : IsStronglyNormalizing payload :=
          StepStar.value_isStronglyNormalizing_of_eitherInr valueStronglyNormalizing
        exact dataTaitCandidate_memberStepStarExpansion
          (StepStar.single IotaHeadStep.iotaEitherMatchInr.toStep)
          (eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches (motive := motive)
            (fun value valueTerminates => (leftBranchRespectsSN value valueTerminates).stronglyNormalizing)
            (fun value valueTerminates => (rightBranchRespectsSN value valueTerminates).stronglyNormalizing)
            valueStronglyNormalizing motiveTerminates
            leftBranchTerminates rightBranchTerminates)
          (rightBranchRespectsSN payload payloadTerminates))
    (fun normalFormIsNeutral => IsNeutral.eitherMatch normalFormIsNeutral)

/-- **★ FTGEN-11.2 — open `idJ` over `dataTaitCandidate`.**  The base case is a member at `dataTaitCandidate`; at
arbitrary scope a `refl` witness value ι-computes the eliminator to the base case (`IotaHeadStep.iotaIdJRefl`
after the `StepStar.idJWitness` congruence), and a NEUTRAL witness leaves the cell neutral (`IsNeutral.idJ`). -/
theorem idJDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop} {motive : RawTerm (scope + 2)}
    {baseCase witness : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (witnessMember : dataTaitCandidate isReflValue witness)
    (baseCaseMember : dataTaitCandidate isValue baseCase) :
    dataTaitCandidate isValue
      (.mkGen .gen_idJ ()
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) :=
  dataTaitEliminatorMemberViaNormalForm
    (cellSpine := fun argument =>
      .mkGen .gen_idJ () (.childCons motive (.childCons baseCase (.childCons argument .childNil))))
    witnessMember
    (fun witnessStronglyNormalizing => idJ_isStronglyNormalizing_of_strongly_normalizing_base
      motiveStronglyNormalizing baseCaseMember.stronglyNormalizing witnessStronglyNormalizing)
    (fun witnessReduction => StepStar.idJWitness witnessReduction)
    (fun normalFormIsRefl valueStronglyNormalizing _reaches => by
      obtain ⟨reflWitness, normalFormEq, _reflWitnessNormal⟩ := normalFormIsRefl
      subst normalFormEq
      exact dataTaitCandidate_memberStepStarExpansion
        (StepStar.single IotaHeadStep.iotaIdJRefl.toStep)
        (idJ_isStronglyNormalizing_of_strongly_normalizing_base motiveStronglyNormalizing
          baseCaseMember.stronglyNormalizing valueStronglyNormalizing)
        baseCaseMember)
    (fun normalFormIsNeutral => IsNeutral.idJ normalFormIsNeutral)

/-- **★ FTGEN-11.2 — open `idStrictRec` over `dataTaitCandidate`.**  Symmetric to `idJDataTaitMember`:
`IotaHeadStep.iotaIdStrictRecRefl` on a refl witness, `IsNeutral.idStrictRec` on a neutral one, at arbitrary
scope. -/
theorem idStrictRecDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop} {motive : RawTerm (scope + 2)}
    {baseCase witness : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (witnessMember : dataTaitCandidate isReflValue witness)
    (baseCaseMember : dataTaitCandidate isValue baseCase) :
    dataTaitCandidate isValue
      (.mkGen .gen_idStrictRec ()
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) :=
  dataTaitEliminatorMemberViaNormalForm
    (cellSpine := fun argument =>
      .mkGen .gen_idStrictRec () (.childCons motive (.childCons baseCase (.childCons argument .childNil))))
    witnessMember
    (fun witnessStronglyNormalizing => idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base
      motiveStronglyNormalizing baseCaseMember.stronglyNormalizing witnessStronglyNormalizing)
    (fun witnessReduction => StepStar.idStrictRecWitness witnessReduction)
    (fun normalFormIsRefl valueStronglyNormalizing _reaches => by
      obtain ⟨reflWitness, normalFormEq, _reflWitnessNormal⟩ := normalFormIsRefl
      subst normalFormEq
      exact dataTaitCandidate_memberStepStarExpansion
        (StepStar.single IotaHeadStep.iotaIdStrictRecRefl.toStep)
        (idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base motiveStronglyNormalizing
          baseCaseMember.stronglyNormalizing valueStronglyNormalizing)
        baseCaseMember)
    (fun normalFormIsNeutral => IsNeutral.idStrictRec normalFormIsNeutral)

end FX1Poly.Core
