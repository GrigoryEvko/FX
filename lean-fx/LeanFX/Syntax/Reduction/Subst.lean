import LeanFX.Syntax.Reduction.Rename

/-! # Single-step `Step` substitution compatibility.

`Step.subst_compatible`: substitution preserves a single-step
reduction.  Structural induction on `Step` with one arm per
constructor, mirroring `Step.rename_compatible` (see
`Reduction/Rename.lean`) but with full term-level substitution
rather than mere index renaming.

β / ι arms invoke the corresponding `TermSubst.Commute.*` law
to push the outer substitution past the contractum's `subst0` /
`subst0_term`.  Cong arms apply the matching `Step` constructor
recursively. -/

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

theorem Step.subst_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    Step beforeTerm afterTerm →
      Step (Term.subst termSubstitution beforeTerm)
        (Term.subst termSubstitution afterTerm) := by
  intro stepProof
  induction stepProof generalizing targetScope targetCtx with
  | appLeft innerStep innerIH =>
      exact Step.appLeft (innerIH termSubstitution)
  | appRight innerStep innerIH =>
      exact Step.appRight (innerIH termSubstitution)
  | lamBody innerStep innerIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.lamBody
        (Step.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
          (innerIH (TermSubst.lift termSubstitution domainType)))
  | appPiLeft innerStep innerIH =>
      rename_i domainType codomainType functionBefore functionAfter argumentTerm
      exact Step.castBoth (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
        (Step.appPiLeft (innerIH termSubstitution))
  | appPiRight innerStep innerIH =>
      rename_i domainType codomainType functionTerm argumentBefore argumentAfter
      exact Step.castBoth (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
        (Step.appPiRight (innerIH termSubstitution))
  | lamPiBody innerStep innerIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.lamPiBody (innerIH (TermSubst.lift termSubstitution domainType))
  | pairLeft innerStep innerIH =>
      exact Step.pairLeft (innerIH termSubstitution)
  | pairRight innerStep innerIH =>
      rename_i firstType secondType firstVal secondBefore secondAfter
      exact Step.pairRight
        (Step.castBoth (Ty.subst0_subst_commute secondType firstType typeSubstitution)
          (innerIH termSubstitution))
  | fstCong innerStep innerIH =>
      exact Step.fstCong (innerIH termSubstitution)
  | sndCong innerStep innerIH =>
      rename_i firstType secondType pairBefore pairAfter
      exact Step.castBoth (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
        (Step.sndCong (innerIH termSubstitution))
  | betaApp body argumentTerm =>
      rename_i domainType codomainType
      let substitutedArgument : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst termSubstitution argumentTerm
      let substitutedBody :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift termSubstitution domainType) body
      let substitutedBetaStep :=
        Step.betaApp
          ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
          substitutedArgument
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
            substitutedArgument
      let targetEquality :
          primitiveTarget =
          Term.subst termSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body argumentTerm) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input termSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body argumentTerm))
          apply HEq.trans
            (Term.subst0_subst_HEq termSubstitution body argumentTerm)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.subst_weaken_commute codomainType typeSubstitution)
                substitutedBody
                substitutedArgument))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0
              ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
              substitutedArgument)))
      exact Step.castTarget targetEquality substitutedBetaStep
  | betaAppPi body argumentTerm =>
      rename_i domainType codomainType
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.castBoth resultTypeEquality.symm
          (Step.betaAppPi
            (Term.subst (TermSubst.lift termSubstitution domainType) body)
            (Term.subst termSubstitution argumentTerm))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift termSubstitution domainType) body)
                (Term.subst termSubstitution argumentTerm)
            = Term.subst termSubstitution (Term.subst0 body argumentTerm) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq termSubstitution body argumentTerm)))
      exact Step.castTarget targetEquality substitutedBetaStep
  | betaFstPair firstVal secondVal =>
      exact Step.betaFstPair _ _
  | betaSndPair firstVal secondVal =>
      rename_i firstType secondType
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.castBoth resultTypeEquality.symm
          (Step.betaSndPair
            (Term.subst termSubstitution firstVal)
            (resultTypeEquality ▸ Term.subst termSubstitution secondVal))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.subst termSubstitution secondVal)
            = Term.subst termSubstitution secondVal := by
        exact eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (eqRec_heq _ _))
      exact Step.castTarget targetEquality substitutedBetaStep
  | etaArrow functionTerm =>
      rename_i domainType codomainType
      let substitutedEtaStep := Step.etaArrow (Term.subst termSubstitution functionTerm)
      let bodyEquality :
          HEq
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸
              Term.subst (TermSubst.lift termSubstitution domainType)
                (Term.app (Term.weaken domainType functionTerm)
                  (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
            (Term.app
              (Term.weaken (domainType.subst typeSubstitution)
                (Term.subst termSubstitution functionTerm))
              (Term.var ⟨0, Nat.zero_lt_succ _⟩)) := by
        apply HEq.trans (eqRec_heq _ _)
        change HEq
          (Term.app
            (Term.subst (TermSubst.lift termSubstitution domainType)
              (Term.weaken domainType functionTerm))
            (Term.subst (TermSubst.lift termSubstitution domainType)
              (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
          (Term.app
            (Term.weaken (domainType.subst typeSubstitution)
              (Term.subst termSubstitution functionTerm))
            (Term.var ⟨0, Nat.zero_lt_succ _⟩))
        exact Term.app_HEq_congr
          (Ty.subst_weaken_commute domainType typeSubstitution)
          (Ty.subst_weaken_commute codomainType typeSubstitution)
          _ _ (Term.subst_weaken_commute_HEq termSubstitution domainType functionTerm)
          _ _ (eqRec_heq _ _)
      let sourceEquality :
          Term.lam
              (Term.app
                (Term.weaken (domainType.subst typeSubstitution)
                  (Term.subst termSubstitution functionTerm))
                (Term.var ⟨0, Nat.zero_lt_succ _⟩))
            =
          Term.subst termSubstitution
            (Term.lam (codomainType := codomainType)
              (Term.app (Term.weaken domainType functionTerm)
                (Term.var ⟨0, Nat.zero_lt_succ _⟩))) :=
        eq_of_heq
          (HEq.symm
            (Term.lam_HEq_congr rfl rfl _ _ bodyEquality))
      exact Step.castSource sourceEquality substitutedEtaStep
  | etaSigma pairTerm =>
      rename_i firstType secondType
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let firstProjectionEquality :
          HEq
            (Term.fst (Term.subst termSubstitution pairTerm))
            (Term.subst termSubstitution (Term.fst pairTerm)) :=
        HEq.refl _
      let secondProjectionEquality :
          HEq
            (Term.snd (Term.subst termSubstitution pairTerm))
            (resultTypeEquality ▸
              Term.subst termSubstitution (Term.snd pairTerm)) := by
        apply HEq.symm
        apply HEq.trans (eqRec_heq _ _)
        exact eqRec_heq _ _
      let sourceEquality :
          Term.pair
              (Term.fst (Term.subst termSubstitution pairTerm))
              (Term.snd (Term.subst termSubstitution pairTerm))
            =
          Term.subst termSubstitution
            (Term.pair (firstType := firstType) (secondType := secondType)
              (Term.fst pairTerm) (Term.snd pairTerm)) :=
        eq_of_heq
          (Term.pair_HEq_congr
            (mode := mode) (level := level) (scope := targetScope)
            (context := targetCtx)
            (sigmaFirstEq := rfl) (sigmaSecondEq := rfl)
            (Term.fst (Term.subst termSubstitution pairTerm))
            (Term.subst termSubstitution (Term.fst pairTerm))
            firstProjectionEquality
            (Term.snd (Term.subst termSubstitution pairTerm))
            (resultTypeEquality ▸ Term.subst termSubstitution (Term.snd pairTerm))
            secondProjectionEquality)
      exact Step.castSource sourceEquality
        (Step.etaSigma (Term.subst termSubstitution pairTerm))
  | boolElimScrutinee innerStep innerIH => exact Step.boolElimScrutinee (innerIH termSubstitution)
  | boolElimThen innerStep innerIH => exact Step.boolElimThen (innerIH termSubstitution)
  | boolElimElse innerStep innerIH => exact Step.boolElimElse (innerIH termSubstitution)
  | iotaBoolElimTrue thenBranch elseBranch => exact Step.iotaBoolElimTrue _ _
  | iotaBoolElimFalse thenBranch elseBranch => exact Step.iotaBoolElimFalse _ _
  | natSuccPred innerStep innerIH => exact Step.natSuccPred (innerIH termSubstitution)
  | natElimScrutinee innerStep innerIH => exact Step.natElimScrutinee (innerIH termSubstitution)
  | natElimZero innerStep innerIH => exact Step.natElimZero (innerIH termSubstitution)
  | natElimSucc innerStep innerIH => exact Step.natElimSucc (innerIH termSubstitution)
  | iotaNatElimZero zeroBranch succBranch => exact Step.iotaNatElimZero _ _
  | iotaNatElimSucc predecessor zeroBranch succBranch => exact Step.iotaNatElimSucc _ _ _
  | natRecScrutinee innerStep innerIH => exact Step.natRecScrutinee (innerIH termSubstitution)
  | natRecZero innerStep innerIH => exact Step.natRecZero (innerIH termSubstitution)
  | natRecSucc innerStep innerIH => exact Step.natRecSucc (innerIH termSubstitution)
  | iotaNatRecZero zeroBranch succBranch => exact Step.iotaNatRecZero _ _
  | iotaNatRecSucc predecessor zeroBranch succBranch => exact Step.iotaNatRecSucc _ _ _
  | listConsHead innerStep innerIH => exact Step.listConsHead (innerIH termSubstitution)
  | listConsTail innerStep innerIH => exact Step.listConsTail (innerIH termSubstitution)
  | listElimScrutinee innerStep innerIH => exact Step.listElimScrutinee (innerIH termSubstitution)
  | listElimNil innerStep innerIH => exact Step.listElimNil (innerIH termSubstitution)
  | listElimCons innerStep innerIH => exact Step.listElimCons (innerIH termSubstitution)
  | iotaListElimNil nilBranch consBranch => exact Step.iotaListElimNil _ _
  | iotaListElimCons head tail nilBranch consBranch => exact Step.iotaListElimCons _ _ _ _
  | optionSomeValue innerStep innerIH => exact Step.optionSomeValue (innerIH termSubstitution)
  | optionMatchScrutinee innerStep innerIH => exact Step.optionMatchScrutinee (innerIH termSubstitution)
  | optionMatchNone innerStep innerIH => exact Step.optionMatchNone (innerIH termSubstitution)
  | optionMatchSome innerStep innerIH => exact Step.optionMatchSome (innerIH termSubstitution)
  | iotaOptionMatchNone noneBranch someBranch => exact Step.iotaOptionMatchNone _ _
  | iotaOptionMatchSome value noneBranch someBranch => exact Step.iotaOptionMatchSome _ _ _
  | eitherInlValue innerStep innerIH => exact Step.eitherInlValue (innerIH termSubstitution)
  | eitherInrValue innerStep innerIH => exact Step.eitherInrValue (innerIH termSubstitution)
  | eitherMatchScrutinee innerStep innerIH => exact Step.eitherMatchScrutinee (innerIH termSubstitution)
  | eitherMatchLeft innerStep innerIH => exact Step.eitherMatchLeft (innerIH termSubstitution)
  | eitherMatchRight innerStep innerIH => exact Step.eitherMatchRight (innerIH termSubstitution)
  | iotaEitherMatchInl value leftBranch rightBranch => exact Step.iotaEitherMatchInl _ _ _
  | iotaEitherMatchInr value leftBranch rightBranch => exact Step.iotaEitherMatchInr _ _ _
  | idJBase innerStep innerIH => exact Step.idJBase (innerIH termSubstitution)
  | idJWitness baseCase innerStep innerIH => exact Step.idJWitness _ (innerIH termSubstitution)
  | iotaIdJRefl baseCase => exact Step.iotaIdJRefl _

end LeanFX.Syntax
