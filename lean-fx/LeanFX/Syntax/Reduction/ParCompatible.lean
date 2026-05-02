import LeanFX.Syntax.Reduction.Subst

/-! # Parallel reduction rename / subst compatibility.

`Step.par.rename_compatible` and `Step.par.subst_compatible`:
parallel reduction is preserved by renaming and substitution.
Each is structural induction on `Step.par` with a per-ctor arm.
β-arms (`betaApp`, `betaAppPi`, `betaFstPair`, `betaSndPair`,
`betaAppDeep`, `betaAppPiDeep`) require the substitution /
renaming commute laws from `TermSubst.Commute.*` to push the
rename / subst past the redex's contractum-side `subst0` /
`subst0_term`.

ι-arms (`iotaBoolElim`, `iotaNatRec`, `iotaListElim`,
`iotaOptionMatch`, `iotaEitherMatch`, `iotaIdJRefl`) similarly
push the rename / subst through the eliminator's contractum.

η-arms (`etaArrow`, `etaSigma`) — these constructors do NOT
satisfy `isBi` (parallel-reduction-with-extensional-η is not
confluent without additional structure); their compat proofs
are present but the constructors are excluded from `isBi`-gated
contexts (see `Reduction/ParBi.lean`).

This is the deepest non-trivial leaf in the typed compat
chain — `Reduction/Compatible.lean` (StepStar) builds on top.
Wave 5 (#1069) plans to migrate β-arms here from
`Subst.singleton` to `Subst.termSingleton` for cleaner commutes. -/

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

theorem Step.par.rename_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    Step.par beforeTerm afterTerm →
      Step.par (Term.rename termRenaming beforeTerm)
        (Term.rename termRenaming afterTerm) := by
  intro parallelStep
  induction parallelStep generalizing targetScope targetCtx with
  | refl term => exact Step.par.refl _
  | app functionStep argumentStep functionIH argumentIH =>
      exact Step.par.app (functionIH termRenaming) (argumentIH termRenaming)
  | lam bodyStep bodyIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.par.lam
        (Step.par.castBoth (Ty.rename_weaken_commute codomainType rawRenaming)
          (bodyIH (TermRenaming.lift termRenaming domainType)))
  | lamPi bodyStep bodyIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.par.lamPi (bodyIH (TermRenaming.lift termRenaming domainType))
  | appPi functionStep argumentStep functionIH argumentIH =>
      rename_i domainType codomainType functionBefore functionAfter argumentBefore argumentAfter
      exact Step.par.castBoth (Ty.subst0_rename_commute codomainType domainType rawRenaming).symm
        (Step.par.appPi (functionIH termRenaming) (argumentIH termRenaming))
  | pair firstStep secondStep firstIH secondIH =>
      rename_i firstType secondType firstBefore firstAfter secondBefore secondAfter
      exact Step.par.pair
        (firstIH termRenaming)
        (Step.par.castBoth (Ty.subst0_rename_commute secondType firstType rawRenaming)
          (secondIH termRenaming))
  | fst pairStep pairIH =>
      exact Step.par.fst (pairIH termRenaming)
  | snd pairStep pairIH =>
      rename_i firstType secondType pairBefore pairAfter
      exact Step.par.castBoth (Ty.subst0_rename_commute secondType firstType rawRenaming).symm
        (Step.par.snd (pairIH termRenaming))
  | boolElim scrutineeStep thenStep elseStep scrutineeIH thenIH elseIH =>
      exact Step.par.boolElim
        (scrutineeIH termRenaming) (thenIH termRenaming) (elseIH termRenaming)
  | betaApp bodyStep argumentStep bodyIH argumentIH =>
      rename_i domainType codomainType bodyBefore bodyAfter argumentBefore argumentAfter
      let renamedArgumentAfter : Term targetCtx (domainType.rename rawRenaming) :=
        Term.rename termRenaming argumentAfter
      let renamedBodyAfter :
          Term (targetCtx.cons (domainType.rename rawRenaming))
            (codomainType.weaken.rename rawRenaming.lift) :=
        Term.rename (TermRenaming.lift termRenaming domainType) bodyAfter
      let renamedBetaStep :=
        Step.par.betaApp
          (Step.par.castBoth (Ty.rename_weaken_commute codomainType rawRenaming)
            (bodyIH (TermRenaming.lift termRenaming domainType)))
          (argumentIH termRenaming)
      let primitiveTarget : Term targetCtx (codomainType.rename rawRenaming) :=
        (Ty.weaken_subst_singleton
            (codomainType.rename rawRenaming)
            (domainType.rename rawRenaming)) ▸
          Term.subst0
            ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBodyAfter)
            renamedArgumentAfter
      let targetEquality :
          primitiveTarget =
          Term.rename termRenaming
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.rename_HEq_cast_input termRenaming
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 bodyAfter argumentAfter))
          apply HEq.trans
            (Term.rename_subst0_HEq termRenaming bodyAfter argumentAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.rename_weaken_commute codomainType rawRenaming)
                renamedBodyAfter
                renamedArgumentAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.rename rawRenaming)
              (domainType.rename rawRenaming))
            (Term.subst0
              ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBodyAfter)
              renamedArgumentAfter)))
      exact Step.par.castTarget targetEquality renamedBetaStep
  | betaAppPi bodyStep argumentStep bodyIH argumentIH =>
      rename_i domainType codomainType bodyBefore bodyAfter argumentBefore argumentAfter
      let resultTypeEquality :=
        Ty.subst0_rename_commute codomainType domainType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPi
            (bodyIH (TermRenaming.lift termRenaming domainType))
            (argumentIH termRenaming))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.rename (TermRenaming.lift termRenaming domainType) bodyAfter)
                (Term.rename termRenaming argumentAfter)
            = Term.rename termRenaming (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.rename_subst0_HEq termRenaming bodyAfter argumentAfter)))
      exact Step.par.castTarget targetEquality renamedBetaStep
  | betaFstPair secondVal firstStep firstIH =>
      rename_i firstType secondType firstBefore firstAfter
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      exact Step.par.betaFstPair
        (resultTypeEquality ▸ Term.rename termRenaming secondVal)
        (firstIH termRenaming)
  | betaSndPair firstVal secondStep secondIH =>
      rename_i firstType secondType secondBefore secondAfter
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPair
            (Term.rename termRenaming firstVal)
            (Step.par.castBoth resultTypeEquality (secondIH termRenaming)))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.rename termRenaming secondAfter)
            = Term.rename termRenaming secondAfter := by
        exact eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (eqRec_heq _ _))
      exact Step.par.castTarget targetEquality renamedBetaStep
  | iotaBoolElimTrue elseBranch thenStep thenIH =>
      exact Step.par.iotaBoolElimTrue (Term.rename termRenaming elseBranch) (thenIH termRenaming)
  | iotaBoolElimFalse thenBranch elseStep elseIH =>
      exact Step.par.iotaBoolElimFalse (Term.rename termRenaming thenBranch) (elseIH termRenaming)
  | natSucc predecessorStep predecessorIH =>
      exact Step.par.natSucc (predecessorIH termRenaming)
  | natElim scrutineeStep zeroStep succStep scrutineeIH zeroIH succIH =>
      exact Step.par.natElim
        (scrutineeIH termRenaming) (zeroIH termRenaming) (succIH termRenaming)
  | iotaNatElimZero succBranch zeroStep zeroIH =>
      exact Step.par.iotaNatElimZero (Term.rename termRenaming succBranch) (zeroIH termRenaming)
  | natRec scrutineeStep zeroStep succStep scrutineeIH zeroIH succIH =>
      exact Step.par.natRec
        (scrutineeIH termRenaming) (zeroIH termRenaming) (succIH termRenaming)
  | iotaNatRecZero succBranch zeroStep zeroIH =>
      exact Step.par.iotaNatRecZero (Term.rename termRenaming succBranch) (zeroIH termRenaming)
  | iotaNatRecSucc predecessorStep zeroStep succStep predecessorIH zeroIH succIH =>
      exact Step.par.iotaNatRecSucc
        (predecessorIH termRenaming) (zeroIH termRenaming) (succIH termRenaming)
  | iotaNatElimSucc zeroBranch predecessorStep succStep predecessorIH succIH =>
      exact Step.par.iotaNatElimSucc
        (Term.rename termRenaming zeroBranch)
        (predecessorIH termRenaming) (succIH termRenaming)
  | listCons headStep tailStep headIH tailIH =>
      exact Step.par.listCons (headIH termRenaming) (tailIH termRenaming)
  | listElim scrutineeStep nilStep consStep scrutineeIH nilIH consIH =>
      exact Step.par.listElim
        (scrutineeIH termRenaming) (nilIH termRenaming) (consIH termRenaming)
  | iotaListElimNil consBranch nilStep nilIH =>
      exact Step.par.iotaListElimNil (Term.rename termRenaming consBranch) (nilIH termRenaming)
  | iotaListElimCons nilBranch headStep tailStep consStep headIH tailIH consIH =>
      exact Step.par.iotaListElimCons
        (Term.rename termRenaming nilBranch)
        (headIH termRenaming) (tailIH termRenaming) (consIH termRenaming)
  | optionSome valueStep valueIH =>
      exact Step.par.optionSome (valueIH termRenaming)
  | optionMatch scrutineeStep noneStep someStep scrutineeIH noneIH someIH =>
      exact Step.par.optionMatch
        (scrutineeIH termRenaming) (noneIH termRenaming) (someIH termRenaming)
  | iotaOptionMatchNone someBranch noneStep noneIH =>
      exact Step.par.iotaOptionMatchNone (Term.rename termRenaming someBranch) (noneIH termRenaming)
  | iotaOptionMatchSome noneBranch valueStep someStep valueIH someIH =>
      exact Step.par.iotaOptionMatchSome
        (Term.rename termRenaming noneBranch) (valueIH termRenaming) (someIH termRenaming)
  | eitherInl valueStep valueIH =>
      exact Step.par.eitherInl (valueIH termRenaming)
  | eitherInr valueStep valueIH =>
      exact Step.par.eitherInr (valueIH termRenaming)
  | eitherMatch scrutineeStep leftStep rightStep scrutineeIH leftIH rightIH =>
      exact Step.par.eitherMatch
        (scrutineeIH termRenaming) (leftIH termRenaming) (rightIH termRenaming)
  | iotaEitherMatchInl rightBranch valueStep leftStep valueIH leftIH =>
      exact Step.par.iotaEitherMatchInl
        (Term.rename termRenaming rightBranch) (valueIH termRenaming) (leftIH termRenaming)
  | iotaEitherMatchInr leftBranch valueStep rightStep valueIH rightIH =>
      exact Step.par.iotaEitherMatchInr
        (Term.rename termRenaming leftBranch) (valueIH termRenaming) (rightIH termRenaming)
  | etaArrow functionTerm =>
      rename_i domainType codomainType
      let renamedEtaStep := Step.par.etaArrow (Term.rename termRenaming functionTerm)
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
      exact Step.par.castSource sourceEquality renamedEtaStep
  | etaSigma pairTerm =>
      rename_i firstType secondType
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let firstProjectionEquality :
          HEq
            (Term.fst (Term.rename termRenaming pairTerm))
            (Term.rename termRenaming (Term.fst pairTerm)) :=
        HEq.refl _
      -- W9.B1.2: Term.snd takes rfl for resultEq.  rfl-resultEq cast collapses.
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
      exact Step.par.castSource sourceEquality
        (Step.par.etaSigma (Term.rename termRenaming pairTerm))
  | idJ baseStep witnessStep baseIH witnessIH =>
      exact Step.par.idJ (baseIH termRenaming) (witnessIH termRenaming)
  | iotaIdJRefl baseStep baseIH =>
      exact Step.par.iotaIdJRefl (baseIH termRenaming)
  -- Deep redex cases.  IH on the deep premise gives the renamed
  -- parallel reduction to the literal redex shape; apply the deep
  -- ctor with the IH outputs.  Term.rename of a literal lam reduces
  -- definitionally to Term.lam (cast ▸ rename body), so the deep
  -- ctor's body-type-pattern lines up automatically.
  | betaAppDeep functionStep argStep functionIH argIH =>
      rename_i domainType codomainType functionTerm body argBefore argAfter
      let renamedArgAfter : Term targetCtx (domainType.rename rawRenaming) :=
        Term.rename termRenaming argAfter
      let renamedBody :
          Term (targetCtx.cons (domainType.rename rawRenaming))
            (codomainType.weaken.rename rawRenaming.lift) :=
        Term.rename (TermRenaming.lift termRenaming domainType) body
      let renamedBetaStep :=
        Step.par.betaAppDeep
          (functionIH termRenaming) (argIH termRenaming)
      let primitiveTarget : Term targetCtx (codomainType.rename rawRenaming) :=
        (Ty.weaken_subst_singleton
            (codomainType.rename rawRenaming)
            (domainType.rename rawRenaming)) ▸
          Term.subst0
            ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBody)
            renamedArgAfter
      let targetEquality :
          primitiveTarget =
          Term.rename termRenaming
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body argAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.rename_HEq_cast_input termRenaming
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body argAfter))
          apply HEq.trans
            (Term.rename_subst0_HEq termRenaming body argAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.rename_weaken_commute codomainType rawRenaming)
                renamedBody
                renamedArgAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.rename rawRenaming)
              (domainType.rename rawRenaming))
            (Term.subst0
              ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBody)
              renamedArgAfter)))
      exact Step.par.castTarget targetEquality renamedBetaStep
  | betaAppPiDeep functionStep argStep functionIH argIH =>
      rename_i domainType codomainType functionTerm body argBefore argAfter
      let resultTypeEquality :=
        Ty.subst0_rename_commute codomainType domainType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPiDeep
            (functionIH termRenaming) (argIH termRenaming))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.rename (TermRenaming.lift termRenaming domainType) body)
                (Term.rename termRenaming argAfter)
            = Term.rename termRenaming (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.rename_subst0_HEq termRenaming body argAfter)))
      exact Step.par.castTarget targetEquality renamedBetaStep
  | betaFstPairDeep pairStep pairIH =>
      exact Step.par.betaFstPairDeep (pairIH termRenaming)
  | betaSndPairDeep pairStep pairIH =>
      rename_i firstType secondType pairTerm firstVal secondVal
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPairDeep (pairIH termRenaming))
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_rename_commute secondType firstType rawRenaming) ▸
                Term.rename termRenaming secondVal)
            = Term.rename termRenaming secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.par.castTarget targetEquality renamedBetaStep
  | iotaBoolElimTrueDeep elseBranch scrutineeStep thenStep scrutineeIH thenIH =>
      exact Step.par.iotaBoolElimTrueDeep
        (Term.rename termRenaming elseBranch)
        (scrutineeIH termRenaming) (thenIH termRenaming)
  | iotaBoolElimFalseDeep thenBranch scrutineeStep elseStep scrutineeIH elseIH =>
      exact Step.par.iotaBoolElimFalseDeep
        (Term.rename termRenaming thenBranch)
        (scrutineeIH termRenaming) (elseIH termRenaming)
  | iotaNatElimZeroDeep succBranch scrutineeStep zeroStep scrutineeIH zeroIH =>
      exact Step.par.iotaNatElimZeroDeep
        (Term.rename termRenaming succBranch)
        (scrutineeIH termRenaming) (zeroIH termRenaming)
  | iotaNatElimSuccDeep zeroBranch scrutineeStep succStep scrutineeIH succIH =>
      exact Step.par.iotaNatElimSuccDeep
        (Term.rename termRenaming zeroBranch)
        (scrutineeIH termRenaming) (succIH termRenaming)
  | iotaNatRecZeroDeep succBranch scrutineeStep zeroStep scrutineeIH zeroIH =>
      exact Step.par.iotaNatRecZeroDeep
        (Term.rename termRenaming succBranch)
        (scrutineeIH termRenaming) (zeroIH termRenaming)
  | iotaNatRecSuccDeep scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      exact Step.par.iotaNatRecSuccDeep
        (scrutineeIH termRenaming) (zeroIH termRenaming) (succIH termRenaming)
  | iotaListElimNilDeep consBranch scrutineeStep nilStep scrutineeIH nilIH =>
      exact Step.par.iotaListElimNilDeep
        (Term.rename termRenaming consBranch)
        (scrutineeIH termRenaming) (nilIH termRenaming)
  | iotaListElimConsDeep nilBranch scrutineeStep consStep scrutineeIH consIH =>
      exact Step.par.iotaListElimConsDeep
        (Term.rename termRenaming nilBranch)
        (scrutineeIH termRenaming) (consIH termRenaming)
  | iotaOptionMatchNoneDeep someBranch scrutineeStep noneStep
        scrutineeIH noneIH =>
      exact Step.par.iotaOptionMatchNoneDeep
        (Term.rename termRenaming someBranch)
        (scrutineeIH termRenaming) (noneIH termRenaming)
  | iotaOptionMatchSomeDeep noneBranch scrutineeStep someStep
        scrutineeIH someIH =>
      exact Step.par.iotaOptionMatchSomeDeep
        (Term.rename termRenaming noneBranch)
        (scrutineeIH termRenaming) (someIH termRenaming)
  | iotaEitherMatchInlDeep rightBranch scrutineeStep leftStep
        scrutineeIH leftIH =>
      exact Step.par.iotaEitherMatchInlDeep
        (Term.rename termRenaming rightBranch)
        (scrutineeIH termRenaming) (leftIH termRenaming)
  | iotaEitherMatchInrDeep leftBranch scrutineeStep rightStep
        scrutineeIH rightIH =>
      exact Step.par.iotaEitherMatchInrDeep
        (Term.rename termRenaming leftBranch)
        (scrutineeIH termRenaming) (rightIH termRenaming)
  | iotaIdJReflDeep witnessStep baseStep witnessIH baseIH =>
      exact Step.par.iotaIdJReflDeep
        (witnessIH termRenaming) (baseIH termRenaming)


theorem Step.par.subst_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    Step.par beforeTerm afterTerm →
      Step.par (Term.subst termSubstitution beforeTerm)
        (Term.subst termSubstitution afterTerm) := by
  intro parallelStep
  induction parallelStep generalizing targetScope targetCtx with
  | refl term => exact Step.par.refl _
  | app functionStep argumentStep functionIH argumentIH =>
      exact Step.par.app (functionIH termSubstitution) (argumentIH termSubstitution)
  | lam bodyStep bodyIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.par.lam
        (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
          (bodyIH (TermSubst.lift termSubstitution domainType)))
  | lamPi bodyStep bodyIH =>
      rename_i domainType codomainType bodyBefore bodyAfter
      exact Step.par.lamPi (bodyIH (TermSubst.lift termSubstitution domainType))
  | appPi functionStep argumentStep functionIH argumentIH =>
      rename_i domainType codomainType functionBefore functionAfter argumentBefore argumentAfter
      exact Step.par.castBoth (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
        (Step.par.appPi (functionIH termSubstitution) (argumentIH termSubstitution))
  | pair firstStep secondStep firstIH secondIH =>
      rename_i firstType secondType firstBefore firstAfter secondBefore secondAfter
      exact Step.par.pair
        (firstIH termSubstitution)
        (Step.par.castBoth (Ty.subst0_subst_commute secondType firstType typeSubstitution)
          (secondIH termSubstitution))
  | fst pairStep pairIH =>
      exact Step.par.fst (pairIH termSubstitution)
  | snd pairStep pairIH =>
      rename_i firstType secondType pairBefore pairAfter
      exact Step.par.castBoth (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
        (Step.par.snd (pairIH termSubstitution))
  | boolElim scrutineeStep thenStep elseStep scrutineeIH thenIH elseIH =>
      exact Step.par.boolElim
        (scrutineeIH termSubstitution) (thenIH termSubstitution) (elseIH termSubstitution)
  | betaApp bodyStep argumentStep bodyIH argumentIH =>
      rename_i domainType codomainType bodyBefore bodyAfter argumentBefore argumentAfter
      let substitutedArgumentAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst termSubstitution argumentAfter
      let substitutedBodyAfter :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift termSubstitution domainType) bodyAfter
      let substitutedBetaStep :=
        Step.par.betaApp
          (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
            (bodyIH (TermSubst.lift termSubstitution domainType)))
          (argumentIH termSubstitution)
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBodyAfter)
            substitutedArgumentAfter
      let targetEquality :
          primitiveTarget =
          Term.subst termSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input termSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 bodyAfter argumentAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq termSubstitution bodyAfter argumentAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.subst_weaken_commute codomainType typeSubstitution)
                substitutedBodyAfter
                substitutedArgumentAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0
              ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBodyAfter)
              substitutedArgumentAfter)))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | betaAppPi bodyStep argumentStep bodyIH argumentIH =>
      rename_i domainType codomainType bodyBefore bodyAfter argumentBefore argumentAfter
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPi
            (bodyIH (TermSubst.lift termSubstitution domainType))
            (argumentIH termSubstitution))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift termSubstitution domainType) bodyAfter)
                (Term.subst termSubstitution argumentAfter)
            = Term.subst termSubstitution (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq termSubstitution bodyAfter argumentAfter)))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | betaFstPair secondVal firstStep firstIH =>
      rename_i firstType secondType firstBefore firstAfter
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      exact Step.par.betaFstPair
        (resultTypeEquality ▸ Term.subst termSubstitution secondVal)
        (firstIH termSubstitution)
  | betaSndPair firstVal secondStep secondIH =>
      rename_i firstType secondType secondBefore secondAfter
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPair
            (Term.subst termSubstitution firstVal)
            (Step.par.castBoth resultTypeEquality (secondIH termSubstitution)))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.subst termSubstitution secondAfter)
            = Term.subst termSubstitution secondAfter := by
        exact eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (eqRec_heq _ _))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | iotaBoolElimTrue elseBranch thenStep thenIH =>
      exact Step.par.iotaBoolElimTrue (Term.subst termSubstitution elseBranch) (thenIH termSubstitution)
  | iotaBoolElimFalse thenBranch elseStep elseIH =>
      exact Step.par.iotaBoolElimFalse (Term.subst termSubstitution thenBranch) (elseIH termSubstitution)
  | natSucc predecessorStep predecessorIH =>
      exact Step.par.natSucc (predecessorIH termSubstitution)
  | natElim scrutineeStep zeroStep succStep scrutineeIH zeroIH succIH =>
      exact Step.par.natElim
        (scrutineeIH termSubstitution) (zeroIH termSubstitution) (succIH termSubstitution)
  | iotaNatElimZero succBranch zeroStep zeroIH =>
      exact Step.par.iotaNatElimZero (Term.subst termSubstitution succBranch) (zeroIH termSubstitution)
  | natRec scrutineeStep zeroStep succStep scrutineeIH zeroIH succIH =>
      exact Step.par.natRec
        (scrutineeIH termSubstitution) (zeroIH termSubstitution) (succIH termSubstitution)
  | iotaNatRecZero succBranch zeroStep zeroIH =>
      exact Step.par.iotaNatRecZero (Term.subst termSubstitution succBranch) (zeroIH termSubstitution)
  | iotaNatRecSucc predecessorStep zeroStep succStep predecessorIH zeroIH succIH =>
      exact Step.par.iotaNatRecSucc
        (predecessorIH termSubstitution) (zeroIH termSubstitution) (succIH termSubstitution)
  | iotaNatElimSucc zeroBranch predecessorStep succStep predecessorIH succIH =>
      exact Step.par.iotaNatElimSucc
        (Term.subst termSubstitution zeroBranch)
        (predecessorIH termSubstitution) (succIH termSubstitution)
  | listCons headStep tailStep headIH tailIH =>
      exact Step.par.listCons (headIH termSubstitution) (tailIH termSubstitution)
  | listElim scrutineeStep nilStep consStep scrutineeIH nilIH consIH =>
      exact Step.par.listElim
        (scrutineeIH termSubstitution) (nilIH termSubstitution) (consIH termSubstitution)
  | iotaListElimNil consBranch nilStep nilIH =>
      exact Step.par.iotaListElimNil (Term.subst termSubstitution consBranch) (nilIH termSubstitution)
  | iotaListElimCons nilBranch headStep tailStep consStep headIH tailIH consIH =>
      exact Step.par.iotaListElimCons
        (Term.subst termSubstitution nilBranch)
        (headIH termSubstitution) (tailIH termSubstitution) (consIH termSubstitution)
  | optionSome valueStep valueIH =>
      exact Step.par.optionSome (valueIH termSubstitution)
  | optionMatch scrutineeStep noneStep someStep scrutineeIH noneIH someIH =>
      exact Step.par.optionMatch
        (scrutineeIH termSubstitution) (noneIH termSubstitution) (someIH termSubstitution)
  | iotaOptionMatchNone someBranch noneStep noneIH =>
      exact Step.par.iotaOptionMatchNone (Term.subst termSubstitution someBranch) (noneIH termSubstitution)
  | iotaOptionMatchSome noneBranch valueStep someStep valueIH someIH =>
      exact Step.par.iotaOptionMatchSome
        (Term.subst termSubstitution noneBranch) (valueIH termSubstitution) (someIH termSubstitution)
  | eitherInl valueStep valueIH =>
      exact Step.par.eitherInl (valueIH termSubstitution)
  | eitherInr valueStep valueIH =>
      exact Step.par.eitherInr (valueIH termSubstitution)
  | eitherMatch scrutineeStep leftStep rightStep scrutineeIH leftIH rightIH =>
      exact Step.par.eitherMatch
        (scrutineeIH termSubstitution) (leftIH termSubstitution) (rightIH termSubstitution)
  | iotaEitherMatchInl rightBranch valueStep leftStep valueIH leftIH =>
      exact Step.par.iotaEitherMatchInl
        (Term.subst termSubstitution rightBranch) (valueIH termSubstitution) (leftIH termSubstitution)
  | iotaEitherMatchInr leftBranch valueStep rightStep valueIH rightIH =>
      exact Step.par.iotaEitherMatchInr
        (Term.subst termSubstitution leftBranch) (valueIH termSubstitution) (rightIH termSubstitution)
  | etaArrow functionTerm =>
      rename_i domainType codomainType
      let substitutedEtaStep := Step.par.etaArrow (Term.subst termSubstitution functionTerm)
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
      exact Step.par.castSource sourceEquality substitutedEtaStep
  | etaSigma pairTerm =>
      rename_i firstType secondType
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let firstProjectionEquality :
          HEq
            (Term.fst (Term.subst termSubstitution pairTerm))
            (Term.subst termSubstitution (Term.fst pairTerm)) :=
        HEq.refl _
      -- W9.B1.2: Term.snd takes rfl for resultEq.  rfl-resultEq cast collapses.
      let secondProjectionEquality :
          HEq
            (Term.snd (Term.subst termSubstitution pairTerm) rfl)
            (resultTypeEquality ▸
              Term.subst termSubstitution (Term.snd pairTerm rfl)) := by
        apply HEq.symm
        apply HEq.trans (eqRec_heq _ _)
        exact eqRec_heq _ _
      let sourceEquality :
          Term.pair
              (Term.fst (Term.subst termSubstitution pairTerm))
              (Term.snd (Term.subst termSubstitution pairTerm) rfl)
            =
          Term.subst termSubstitution
            (Term.pair (firstType := firstType) (secondType := secondType)
              (Term.fst pairTerm) (Term.snd pairTerm rfl)) :=
        eq_of_heq
          (Term.pair_HEq_congr
            (mode := mode) (level := level) (scope := targetScope)
            (context := targetCtx)
            (sigmaFirstEq := rfl) (sigmaSecondEq := rfl)
            (Term.fst (Term.subst termSubstitution pairTerm))
            (Term.subst termSubstitution (Term.fst pairTerm))
            firstProjectionEquality
            (Term.snd (Term.subst termSubstitution pairTerm) rfl)
            (resultTypeEquality ▸ Term.subst termSubstitution (Term.snd pairTerm rfl))
            secondProjectionEquality)
      exact Step.par.castSource sourceEquality
        (Step.par.etaSigma (Term.subst termSubstitution pairTerm))
  | idJ baseStep witnessStep baseIH witnessIH =>
      exact Step.par.idJ (baseIH termSubstitution) (witnessIH termSubstitution)
  | iotaIdJRefl baseStep baseIH =>
      exact Step.par.iotaIdJRefl (baseIH termSubstitution)
  -- Deep redex cases for substitution — same pattern as the rename
  -- side, swapping Renaming machinery for Subst.  Term.subst on a
  -- literal Term.lam reduces definitionally to Term.lam (cast ▸
  -- subst_lift body); the deep ctor accepts that shape directly.
  | betaAppDeep functionStep argStep functionIH argIH =>
      rename_i domainType codomainType functionTerm body argBefore argAfter
      let substitutedArgAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst termSubstitution argAfter
      let substitutedBody :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift termSubstitution domainType) body
      let substitutedBetaStep :=
        Step.par.betaAppDeep
          (functionIH termSubstitution) (argIH termSubstitution)
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
            substitutedArgAfter
      let targetEquality :
          primitiveTarget =
          Term.subst termSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body argAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input termSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body argAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq termSubstitution body argAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.subst_weaken_commute codomainType typeSubstitution)
                substitutedBody
                substitutedArgAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0
              ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
              substitutedArgAfter)))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | betaAppPiDeep functionStep argStep functionIH argIH =>
      rename_i domainType codomainType functionTerm body argBefore argAfter
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPiDeep
            (functionIH termSubstitution) (argIH termSubstitution))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift termSubstitution domainType) body)
                (Term.subst termSubstitution argAfter)
            = Term.subst termSubstitution (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq termSubstitution body argAfter)))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | betaFstPairDeep pairStep pairIH =>
      exact Step.par.betaFstPairDeep (pairIH termSubstitution)
  | betaSndPairDeep pairStep pairIH =>
      rename_i firstType secondType pairTerm firstVal secondVal
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPairDeep (pairIH termSubstitution))
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_subst_commute secondType firstType typeSubstitution) ▸
                Term.subst termSubstitution secondVal)
            = Term.subst termSubstitution secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | iotaBoolElimTrueDeep elseBranch scrutineeStep thenStep scrutineeIH thenIH =>
      exact Step.par.iotaBoolElimTrueDeep
        (Term.subst termSubstitution elseBranch)
        (scrutineeIH termSubstitution) (thenIH termSubstitution)
  | iotaBoolElimFalseDeep thenBranch scrutineeStep elseStep scrutineeIH elseIH =>
      exact Step.par.iotaBoolElimFalseDeep
        (Term.subst termSubstitution thenBranch)
        (scrutineeIH termSubstitution) (elseIH termSubstitution)
  | iotaNatElimZeroDeep succBranch scrutineeStep zeroStep scrutineeIH zeroIH =>
      exact Step.par.iotaNatElimZeroDeep
        (Term.subst termSubstitution succBranch)
        (scrutineeIH termSubstitution) (zeroIH termSubstitution)
  | iotaNatElimSuccDeep zeroBranch scrutineeStep succStep scrutineeIH succIH =>
      exact Step.par.iotaNatElimSuccDeep
        (Term.subst termSubstitution zeroBranch)
        (scrutineeIH termSubstitution) (succIH termSubstitution)
  | iotaNatRecZeroDeep succBranch scrutineeStep zeroStep scrutineeIH zeroIH =>
      exact Step.par.iotaNatRecZeroDeep
        (Term.subst termSubstitution succBranch)
        (scrutineeIH termSubstitution) (zeroIH termSubstitution)
  | iotaNatRecSuccDeep scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      exact Step.par.iotaNatRecSuccDeep
        (scrutineeIH termSubstitution) (zeroIH termSubstitution)
        (succIH termSubstitution)
  | iotaListElimNilDeep consBranch scrutineeStep nilStep scrutineeIH nilIH =>
      exact Step.par.iotaListElimNilDeep
        (Term.subst termSubstitution consBranch)
        (scrutineeIH termSubstitution) (nilIH termSubstitution)
  | iotaListElimConsDeep nilBranch scrutineeStep consStep scrutineeIH consIH =>
      exact Step.par.iotaListElimConsDeep
        (Term.subst termSubstitution nilBranch)
        (scrutineeIH termSubstitution) (consIH termSubstitution)
  | iotaOptionMatchNoneDeep someBranch scrutineeStep noneStep
        scrutineeIH noneIH =>
      exact Step.par.iotaOptionMatchNoneDeep
        (Term.subst termSubstitution someBranch)
        (scrutineeIH termSubstitution) (noneIH termSubstitution)
  | iotaOptionMatchSomeDeep noneBranch scrutineeStep someStep
        scrutineeIH someIH =>
      exact Step.par.iotaOptionMatchSomeDeep
        (Term.subst termSubstitution noneBranch)
        (scrutineeIH termSubstitution) (someIH termSubstitution)
  | iotaEitherMatchInlDeep rightBranch scrutineeStep leftStep
        scrutineeIH leftIH =>
      exact Step.par.iotaEitherMatchInlDeep
        (Term.subst termSubstitution rightBranch)
        (scrutineeIH termSubstitution) (leftIH termSubstitution)
  | iotaEitherMatchInrDeep leftBranch scrutineeStep rightStep
        scrutineeIH rightIH =>
      exact Step.par.iotaEitherMatchInrDeep
        (Term.subst termSubstitution leftBranch)
        (scrutineeIH termSubstitution) (rightIH termSubstitution)
  | iotaIdJReflDeep witnessStep baseStep witnessIH baseIH =>
      exact Step.par.iotaIdJReflDeep
        (witnessIH termSubstitution) (baseIH termSubstitution)


end LeanFX.Syntax
