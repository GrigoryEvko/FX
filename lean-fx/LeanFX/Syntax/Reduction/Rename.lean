import LeanFX.Syntax.Reduction.ParToStar

/-! # Single-step `Step` rename compatibility.

`Step.rename_compatible`: if `t₁` reduces to `t₂` in one step,
then `rename termRenaming t₁` reduces to `rename termRenaming t₂`
in one step under any term renaming.

The proof is structural induction on the `Step` derivation.
β / ι arms call the relevant commute lemma from
`TermSubst.Commute.*` to push the renaming past the substitution
introduced by the redex contractum.  Most cong arms are direct
constructor applications.

WQ.3 (#1121) plans to refactor the β-arms here into structured
named lemmas to remove the boilerplate scaffolding around the
commute applications. -/

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

theorem Step.rename_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    Step beforeTerm afterTerm →
      Step (Term.rename termRenaming beforeTerm)
        (Term.rename termRenaming afterTerm) := by
  intro stepProof
  induction stepProof generalizing targetScope targetCtx with
  | appLeft innerStep innerIH =>
      exact Step.appLeft (innerIH termRenaming)
  | appRight innerStep innerIH =>
      exact Step.appRight (innerIH termRenaming)
  | lamBody innerStep innerIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.lamBody
        (Step.castBoth (Ty.rename_weaken_commute codomainType rawRenaming)
          (innerIH (TermRenaming.lift termRenaming domainType)))
  | appPiLeft innerStep innerIH =>
      rename_i domainType codomainType argumentRaw functionBefore functionAfter
                argumentTerm
      exact Step.castBoth
        (Ty.subst_termSingleton_rename_commute codomainType domainType
          argumentRaw rawRenaming).symm
        (Step.appPiLeft (innerIH termRenaming))
  | appPiRight innerStep innerIH =>
      rename_i domainType codomainType argumentRaw functionTerm argumentBefore
                argumentAfter
      exact Step.castBoth
        (Ty.subst_termSingleton_rename_commute codomainType domainType
          argumentRaw rawRenaming).symm
        (Step.appPiRight (innerIH termRenaming))
  | lamPiBody innerStep innerIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.lamPiBody (innerIH (TermRenaming.lift termRenaming domainType))
  | pairLeft innerStep innerIH =>
      exact Step.pairLeft (innerIH termRenaming)
  | pairRight innerStep innerIH =>
      rename_i firstType secondType firstVal secondBefore secondAfter
      exact Step.pairRight
        (Step.castBoth (Ty.subst0_rename_commute secondType firstType rawRenaming)
          (innerIH termRenaming))
  | fstCong innerStep innerIH =>
      exact Step.fstCong (innerIH termRenaming)
  | sndCong innerStep innerIH =>
      rename_i firstType secondType pairBefore pairAfter
      exact Step.castBoth (Ty.subst0_rename_commute secondType firstType rawRenaming).symm
        (Step.sndCong (innerIH termRenaming))
  | betaApp body arg =>
      rename_i domainType codomainType
      let renamedArgument : Term targetCtx (domainType.rename rawRenaming) :=
        Term.rename termRenaming arg
      let renamedBody :
          Term (targetCtx.cons (domainType.rename rawRenaming))
            (codomainType.weaken.rename rawRenaming.lift) :=
        Term.rename (TermRenaming.lift termRenaming domainType) body
      let renamedBetaStep :=
        Step.betaApp
          ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBody)
          renamedArgument
      let primitiveTarget : Term targetCtx (codomainType.rename rawRenaming) :=
        (Ty.weaken_subst_singleton
            (codomainType.rename rawRenaming)
            (domainType.rename rawRenaming)) ▸
          Term.subst0
            ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBody)
            renamedArgument
      let targetEquality :
          primitiveTarget =
          Term.rename termRenaming
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body arg) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.rename_HEq_cast_input termRenaming
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body arg))
          apply HEq.trans
            (Term.rename_subst0_HEq termRenaming body arg)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.rename_weaken_commute codomainType rawRenaming)
                renamedBody
                renamedArgument))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.rename rawRenaming)
              (domainType.rename rawRenaming))
            (Term.subst0
              ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBody)
              renamedArgument)))
      exact Step.castTarget targetEquality renamedBetaStep
  | betaAppPi body arg =>
      rename_i domainType codomainType
      let resultTypeEquality :=
        Ty.subst0_rename_commute codomainType domainType rawRenaming
      let renamedBetaStep :=
        Step.castBoth resultTypeEquality.symm
          (Step.betaAppPi
            (Term.rename (TermRenaming.lift termRenaming domainType) body)
            (Term.rename termRenaming arg))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.rename (TermRenaming.lift termRenaming domainType) body)
                (Term.rename termRenaming arg)
            = Term.rename termRenaming (Term.subst0 body arg) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.rename_subst0_HEq termRenaming body arg)))
      exact Step.castTarget
        targetEquality
        renamedBetaStep
  | betaFstPair firstVal secondVal =>
      exact Step.betaFstPair _ _
  | betaSndPair firstVal secondVal =>
      rename_i firstType secondType
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let renamedBetaStep :=
        Step.castBoth resultTypeEquality.symm
          (Step.betaSndPair
            (Term.rename termRenaming firstVal)
            (resultTypeEquality ▸ Term.rename termRenaming secondVal))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.rename termRenaming secondVal)
            = Term.rename termRenaming secondVal := by
        exact eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (eqRec_heq _ _))
      exact Step.castTarget targetEquality renamedBetaStep
  | etaArrow functionTerm =>
      rename_i domainType codomainType
      let renamedEtaStep := Step.etaArrow (Term.rename termRenaming functionTerm)
      let bodyEquality :
          HEq
            ((Ty.rename_weaken_commute codomainType rawRenaming) ▸
              Term.rename (TermRenaming.lift termRenaming domainType)
                (Term.app (Term.weaken domainType functionTerm)
                  (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
            (Term.app
              (Term.weaken (domainType.rename rawRenaming)
                (Term.rename termRenaming functionTerm))
              (Term.var ⟨0, Nat.zero_lt_succ _⟩)) := by
        apply HEq.trans (eqRec_heq _ _)
        change HEq
          (Term.app
            (Term.rename (TermRenaming.lift termRenaming domainType)
              (Term.weaken domainType functionTerm))
            (Term.rename (TermRenaming.lift termRenaming domainType)
              (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
          (Term.app
            (Term.weaken (domainType.rename rawRenaming)
              (Term.rename termRenaming functionTerm))
            (Term.var ⟨0, Nat.zero_lt_succ _⟩))
        exact Term.app_HEq_congr
          (Ty.rename_weaken_commute domainType rawRenaming)
          (Ty.rename_weaken_commute codomainType rawRenaming)
          _ _ (Term.rename_weaken_commute_HEq termRenaming domainType functionTerm)
          _ _ (eqRec_heq _ _)
      let sourceEquality :
          Term.lam
              (Term.app
                (Term.weaken (domainType.rename rawRenaming)
                  (Term.rename termRenaming functionTerm))
                (Term.var ⟨0, Nat.zero_lt_succ _⟩))
            =
          Term.rename termRenaming
            (Term.lam (codomainType := codomainType)
              (Term.app (Term.weaken domainType functionTerm)
                (Term.var ⟨0, Nat.zero_lt_succ _⟩))) :=
        eq_of_heq
          (HEq.symm
            (Term.lam_HEq_congr rfl rfl _ _ bodyEquality))
      exact Step.castSource sourceEquality renamedEtaStep
  | etaSigma pairTerm =>
      rename_i firstType secondType
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let firstProjectionEquality :
          HEq
            (Term.fst (Term.rename termRenaming pairTerm))
            (Term.rename termRenaming (Term.fst pairTerm)) :=
        HEq.refl _
      -- W9.B1.2: Term.snd takes rfl for resultEq.  Term.rename on
      -- (Term.snd pairTerm rfl) emits a double cast (resultEq.symm ▸
      -- subst0_rename_commute.symm ▸ Term.snd renamed rfl).  Since
      -- resultEq = rfl, the inner congrArg-of-rfl cast is itself rfl
      -- and collapses; only the subst0_rename_commute cast remains.
      let secondProjectionEquality :
          HEq
            (Term.snd (Term.rename termRenaming pairTerm) rfl)
            (resultTypeEquality ▸
              Term.rename termRenaming (Term.snd pairTerm rfl)) := by
        apply HEq.symm
        apply HEq.trans (eqRec_heq _ _)
        exact eqRec_heq _ _
      let sourceEquality :
          Term.pair
              (Term.fst (Term.rename termRenaming pairTerm))
              (Term.snd (Term.rename termRenaming pairTerm) rfl)
            =
          Term.rename termRenaming
            (Term.pair (firstType := firstType) (secondType := secondType)
              (Term.fst pairTerm) (Term.snd pairTerm rfl)) :=
        eq_of_heq
          (Term.pair_HEq_congr
            (mode := mode) (level := level) (scope := targetScope)
            (context := targetCtx)
            (sigmaFirstEq := rfl) (sigmaSecondEq := rfl)
            (Term.fst (Term.rename termRenaming pairTerm))
            (Term.rename termRenaming (Term.fst pairTerm))
            firstProjectionEquality
            (Term.snd (Term.rename termRenaming pairTerm) rfl)
            (resultTypeEquality ▸ Term.rename termRenaming (Term.snd pairTerm rfl))
            secondProjectionEquality)
      exact Step.castSource sourceEquality
        (Step.etaSigma (Term.rename termRenaming pairTerm))
  | boolElimScrutinee innerStep innerIH => exact Step.boolElimScrutinee (innerIH termRenaming)
  | boolElimThen innerStep innerIH => exact Step.boolElimThen (innerIH termRenaming)
  | boolElimElse innerStep innerIH => exact Step.boolElimElse (innerIH termRenaming)
  | iotaBoolElimTrue thenBranch elseBranch => exact Step.iotaBoolElimTrue _ _
  | iotaBoolElimFalse thenBranch elseBranch => exact Step.iotaBoolElimFalse _ _
  | natSuccPred innerStep innerIH => exact Step.natSuccPred (innerIH termRenaming)
  | natElimScrutinee innerStep innerIH => exact Step.natElimScrutinee (innerIH termRenaming)
  | natElimZero innerStep innerIH => exact Step.natElimZero (innerIH termRenaming)
  | natElimSucc innerStep innerIH => exact Step.natElimSucc (innerIH termRenaming)
  | iotaNatElimZero zeroBranch succBranch => exact Step.iotaNatElimZero _ _
  | iotaNatElimSucc predecessor zeroBranch succBranch => exact Step.iotaNatElimSucc _ _ _
  | natRecScrutinee innerStep innerIH => exact Step.natRecScrutinee (innerIH termRenaming)
  | natRecZero innerStep innerIH => exact Step.natRecZero (innerIH termRenaming)
  | natRecSucc innerStep innerIH => exact Step.natRecSucc (innerIH termRenaming)
  | iotaNatRecZero zeroBranch succBranch => exact Step.iotaNatRecZero _ _
  | iotaNatRecSucc predecessor zeroBranch succBranch => exact Step.iotaNatRecSucc _ _ _
  | listConsHead innerStep innerIH => exact Step.listConsHead (innerIH termRenaming)
  | listConsTail innerStep innerIH => exact Step.listConsTail (innerIH termRenaming)
  | listElimScrutinee innerStep innerIH => exact Step.listElimScrutinee (innerIH termRenaming)
  | listElimNil innerStep innerIH => exact Step.listElimNil (innerIH termRenaming)
  | listElimCons innerStep innerIH => exact Step.listElimCons (innerIH termRenaming)
  | iotaListElimNil nilBranch consBranch => exact Step.iotaListElimNil _ _
  | iotaListElimCons head tail nilBranch consBranch => exact Step.iotaListElimCons _ _ _ _
  | optionSomeValue innerStep innerIH => exact Step.optionSomeValue (innerIH termRenaming)
  | optionMatchScrutinee innerStep innerIH => exact Step.optionMatchScrutinee (innerIH termRenaming)
  | optionMatchNone innerStep innerIH => exact Step.optionMatchNone (innerIH termRenaming)
  | optionMatchSome innerStep innerIH => exact Step.optionMatchSome (innerIH termRenaming)
  | iotaOptionMatchNone noneBranch someBranch => exact Step.iotaOptionMatchNone _ _
  | iotaOptionMatchSome value noneBranch someBranch => exact Step.iotaOptionMatchSome _ _ _
  | eitherInlValue innerStep innerIH => exact Step.eitherInlValue (innerIH termRenaming)
  | eitherInrValue innerStep innerIH => exact Step.eitherInrValue (innerIH termRenaming)
  | eitherMatchScrutinee innerStep innerIH => exact Step.eitherMatchScrutinee (innerIH termRenaming)
  | eitherMatchLeft innerStep innerIH => exact Step.eitherMatchLeft (innerIH termRenaming)
  | eitherMatchRight innerStep innerIH => exact Step.eitherMatchRight (innerIH termRenaming)
  | iotaEitherMatchInl value leftBranch rightBranch => exact Step.iotaEitherMatchInl _ _ _
  | iotaEitherMatchInr value leftBranch rightBranch => exact Step.iotaEitherMatchInr _ _ _
  | idJBase innerStep innerIH => exact Step.idJBase (innerIH termRenaming)
  | idJWitness baseCase innerStep innerIH => exact Step.idJWitness _ (innerIH termRenaming)
  | iotaIdJRefl baseCase => exact Step.iotaIdJRefl _

end LeanFX.Syntax
