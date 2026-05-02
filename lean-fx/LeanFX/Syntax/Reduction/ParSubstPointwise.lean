import LeanFX.Syntax.Reduction.ParBi
import LeanFX.Syntax.Reduction.ParSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! # Joint single-step βι substitution lemma — typed.

Mirrors `RawStep.par.subst_par` (RawParCompatible.lean line 379)
at the typed level, gated on `Step.par.isBi`.  Statement: given
two `TermSubst`s that are pointwise `Step.par`-related and a
single `Step.par.isBi` step on the term, produces a single
`Step.par` between substituted forms — the **before** term is
substituted with the **first** TermSubst, the **after** term
with the **second**.

This is the prerequisite for `Step.par.cd_monotone` (Confluence
/ CdParMono.lean) — every β case of cd_monotone needs a single
par from `b'.subst0 a'` to `(cd b').subst0 (cd a')` via
cd_dominates on body and argument, then `cd_lemma_star_with_bi`
to bridge to `cd (b'.subst0 a')`.

η is excluded from the case enumeration because `Step.par.isBi`
omits it; η rules are refl-like and have no joint-subst
formulation without transitivity. -/

/-- Joint pointwise substitution lemma (typed, single step,
βι-restricted).  See file docstring for full design. -/
theorem Step.par.subst_par_isBi
    {mode : Mode} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    {firstTermSubstitution secondTermSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep)
    (pointwise : ∀ position,
      Step.par (firstTermSubstitution position)
        (secondTermSubstitution position)) :
    Step.par
      (Term.subst firstTermSubstitution beforeTerm)
      (Term.subst secondTermSubstitution afterTerm) := by
  induction stepBi generalizing targetScope targetCtx with
  | refl term => exact Term.subst_par_pointwise pointwise term
  | app _functionBi _argumentBi functionIH argumentIH =>
      exact Step.par.app (functionIH pointwise) (argumentIH pointwise)
  | lam _bodyBi bodyIH =>
      rename_i domainType codomainType _ _ _
      exact Step.par.lam
        (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
          (bodyIH (TermSubst.par_lift pointwise domainType)))
  | lamPi _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      exact Step.par.lamPi
        (bodyIH (TermSubst.par_lift pointwise domainType))
  | appPi _functionBi _argumentBi functionIH argumentIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      exact Step.par.castBoth
        (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
        (Step.par.appPi (functionIH pointwise) (argumentIH pointwise))
  | pair _firstBi _secondBi firstIH secondIH =>
      rename_i firstType secondType _ _ _ _ _ _
      exact Step.par.pair
        (firstIH pointwise)
        (Step.par.castBoth (Ty.subst0_subst_commute secondType firstType typeSubstitution)
          (secondIH pointwise))
  | fst _pairBi pairIH =>
      exact Step.par.fst (pairIH pointwise)
  | snd _pairBi pairIH =>
      rename_i firstType secondType _ _ _
      exact Step.par.castBoth
        (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
        (Step.par.snd (pairIH pointwise))
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      exact Step.par.boolElim
        (scrutIH pointwise) (thenIH pointwise) (elseIH pointwise)
  | betaApp _bodyBi _argumentBi bodyIH argumentIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let substitutedArgumentAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst secondTermSubstitution argumentAfter
      let substitutedBodyAfter :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift secondTermSubstitution domainType) bodyAfter
      let substitutedBetaStep :=
        Step.par.betaApp
          (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
            (bodyIH (TermSubst.par_lift pointwise domainType)))
          (argumentIH pointwise)
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBodyAfter)
            substitutedArgumentAfter
      let targetEquality :
          primitiveTarget =
          Term.subst secondTermSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input secondTermSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 bodyAfter argumentAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq secondTermSubstitution bodyAfter argumentAfter)
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
  | betaAppPi _bodyBi _argumentBi bodyIH argumentIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPi
            (bodyIH (TermSubst.par_lift pointwise domainType))
            (argumentIH pointwise))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift secondTermSubstitution domainType) bodyAfter)
                (Term.subst secondTermSubstitution argumentAfter)
            = Term.subst secondTermSubstitution (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq secondTermSubstitution bodyAfter argumentAfter)))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | betaFstPair _firstBi firstIH =>
      rename_i firstType secondType _ _ secondVal _
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      exact Step.par.betaFstPair
        (resultTypeEquality ▸ Term.subst firstTermSubstitution secondVal)
        (firstIH pointwise)
  | betaSndPair _secondBi secondIH =>
      rename_i firstType secondType firstVal _ secondAfter _
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPair
            (Term.subst firstTermSubstitution firstVal)
            (Step.par.castBoth resultTypeEquality (secondIH pointwise)))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.subst secondTermSubstitution secondAfter)
            = Term.subst secondTermSubstitution secondAfter := by
        exact eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (eqRec_heq _ _))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | iotaBoolElimTrue elseBranch _thenBi thenIH =>
      exact Step.par.iotaBoolElimTrue
        (Term.subst firstTermSubstitution elseBranch) (thenIH pointwise)
  | iotaBoolElimFalse thenBranch _elseBi elseIH =>
      exact Step.par.iotaBoolElimFalse
        (Term.subst firstTermSubstitution thenBranch) (elseIH pointwise)
  | natSucc _predBi predIH =>
      exact Step.par.natSucc (predIH pointwise)
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      exact Step.par.natElim
        (scrutIH pointwise) (zeroIH pointwise) (succIH pointwise)
  | iotaNatElimZero succBranch _zeroBi zeroIH =>
      exact Step.par.iotaNatElimZero
        (Term.subst firstTermSubstitution succBranch) (zeroIH pointwise)
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      exact Step.par.natRec
        (scrutIH pointwise) (zeroIH pointwise) (succIH pointwise)
  | iotaNatRecZero succBranch _zeroBi zeroIH =>
      exact Step.par.iotaNatRecZero
        (Term.subst firstTermSubstitution succBranch) (zeroIH pointwise)
  | iotaNatRecSucc _predBi _zeroBi _succBi predIH zeroIH succIH =>
      exact Step.par.iotaNatRecSucc
        (predIH pointwise) (zeroIH pointwise) (succIH pointwise)
  | iotaNatElimSucc zeroBranch _predBi _succBi predIH succIH =>
      exact Step.par.iotaNatElimSucc
        (Term.subst firstTermSubstitution zeroBranch)
        (predIH pointwise) (succIH pointwise)
  | listCons _headBi _tailBi headIH tailIH =>
      exact Step.par.listCons (headIH pointwise) (tailIH pointwise)
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      exact Step.par.listElim
        (scrutIH pointwise) (nilIH pointwise) (consIH pointwise)
  | iotaListElimNil consBranch _nilBi nilIH =>
      exact Step.par.iotaListElimNil
        (Term.subst firstTermSubstitution consBranch) (nilIH pointwise)
  | iotaListElimCons nilBranch _headBi _tailBi _consBi headIH tailIH consIH =>
      exact Step.par.iotaListElimCons
        (Term.subst firstTermSubstitution nilBranch)
        (headIH pointwise) (tailIH pointwise) (consIH pointwise)
  | optionSome _valueBi valueIH =>
      exact Step.par.optionSome (valueIH pointwise)
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      exact Step.par.optionMatch
        (scrutIH pointwise) (noneIH pointwise) (someIH pointwise)
  | iotaOptionMatchNone someBranch _noneBi noneIH =>
      exact Step.par.iotaOptionMatchNone
        (Term.subst firstTermSubstitution someBranch) (noneIH pointwise)
  | iotaOptionMatchSome noneBranch _valueBi _someBi valueIH someIH =>
      exact Step.par.iotaOptionMatchSome
        (Term.subst firstTermSubstitution noneBranch)
        (valueIH pointwise) (someIH pointwise)
  | eitherInl _valueBi valueIH =>
      exact Step.par.eitherInl (valueIH pointwise)
  | eitherInr _valueBi valueIH =>
      exact Step.par.eitherInr (valueIH pointwise)
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      exact Step.par.eitherMatch
        (scrutIH pointwise) (leftIH pointwise) (rightIH pointwise)
  | iotaEitherMatchInl rightBranch _valueBi _leftBi valueIH leftIH =>
      exact Step.par.iotaEitherMatchInl
        (Term.subst firstTermSubstitution rightBranch)
        (valueIH pointwise) (leftIH pointwise)
  | iotaEitherMatchInr leftBranch _valueBi _rightBi valueIH rightIH =>
      exact Step.par.iotaEitherMatchInr
        (Term.subst firstTermSubstitution leftBranch)
        (valueIH pointwise) (rightIH pointwise)
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      exact Step.par.idJ (baseIH pointwise) (witnessIH pointwise)
  | iotaIdJRefl _baseBi baseIH =>
      exact Step.par.iotaIdJRefl (baseIH pointwise)
  | betaAppDeep _functionBi _argBi functionIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let substitutedArgAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst secondTermSubstitution argAfter
      let substitutedBody :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift secondTermSubstitution domainType) body
      let substitutedBetaStep :=
        Step.par.betaAppDeep
          (functionIH pointwise) (argIH pointwise)
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
            substitutedArgAfter
      let targetEquality :
          primitiveTarget =
          Term.subst secondTermSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body argAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input secondTermSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body argAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq secondTermSubstitution body argAfter)
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
  | betaAppPiDeep _functionBi _argBi functionIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPiDeep
            (functionIH pointwise) (argIH pointwise))
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift secondTermSubstitution domainType) body)
                (Term.subst secondTermSubstitution argAfter)
            = Term.subst secondTermSubstitution (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq secondTermSubstitution body argAfter)))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | betaFstPairDeep _pairBi pairIH =>
      exact Step.par.betaFstPairDeep (pairIH pointwise)
  | betaSndPairDeep _pairBi pairIH =>
      rename_i firstType secondType _ _ secondVal _
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPairDeep (pairIH pointwise))
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_subst_commute secondType firstType typeSubstitution) ▸
                Term.subst secondTermSubstitution secondVal)
            = Term.subst secondTermSubstitution secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.par.castTarget targetEquality substitutedBetaStep
  | iotaBoolElimTrueDeep elseBranch _scrutBi _thenBi scrutIH thenIH =>
      exact Step.par.iotaBoolElimTrueDeep
        (Term.subst firstTermSubstitution elseBranch)
        (scrutIH pointwise) (thenIH pointwise)
  | iotaBoolElimFalseDeep thenBranch _scrutBi _elseBi scrutIH elseIH =>
      exact Step.par.iotaBoolElimFalseDeep
        (Term.subst firstTermSubstitution thenBranch)
        (scrutIH pointwise) (elseIH pointwise)
  | iotaNatElimZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      exact Step.par.iotaNatElimZeroDeep
        (Term.subst firstTermSubstitution succBranch)
        (scrutIH pointwise) (zeroIH pointwise)
  | iotaNatElimSuccDeep zeroBranch _scrutBi _succBi scrutIH succIH =>
      exact Step.par.iotaNatElimSuccDeep
        (Term.subst firstTermSubstitution zeroBranch)
        (scrutIH pointwise) (succIH pointwise)
  | iotaNatRecZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      exact Step.par.iotaNatRecZeroDeep
        (Term.subst firstTermSubstitution succBranch)
        (scrutIH pointwise) (zeroIH pointwise)
  | iotaNatRecSuccDeep _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      exact Step.par.iotaNatRecSuccDeep
        (scrutIH pointwise) (zeroIH pointwise) (succIH pointwise)
  | iotaListElimNilDeep consBranch _scrutBi _nilBi scrutIH nilIH =>
      exact Step.par.iotaListElimNilDeep
        (Term.subst firstTermSubstitution consBranch)
        (scrutIH pointwise) (nilIH pointwise)
  | iotaListElimConsDeep nilBranch _scrutBi _consBi scrutIH consIH =>
      exact Step.par.iotaListElimConsDeep
        (Term.subst firstTermSubstitution nilBranch)
        (scrutIH pointwise) (consIH pointwise)
  | iotaOptionMatchNoneDeep someBranch _scrutBi _noneBi scrutIH noneIH =>
      exact Step.par.iotaOptionMatchNoneDeep
        (Term.subst firstTermSubstitution someBranch)
        (scrutIH pointwise) (noneIH pointwise)
  | iotaOptionMatchSomeDeep noneBranch _scrutBi _someBi scrutIH someIH =>
      exact Step.par.iotaOptionMatchSomeDeep
        (Term.subst firstTermSubstitution noneBranch)
        (scrutIH pointwise) (someIH pointwise)
  | iotaEitherMatchInlDeep rightBranch _scrutBi _leftBi scrutIH leftIH =>
      exact Step.par.iotaEitherMatchInlDeep
        (Term.subst firstTermSubstitution rightBranch)
        (scrutIH pointwise) (leftIH pointwise)
  | iotaEitherMatchInrDeep leftBranch _scrutBi _rightBi scrutIH rightIH =>
      exact Step.par.iotaEitherMatchInrDeep
        (Term.subst firstTermSubstitution leftBranch)
        (scrutIH pointwise) (rightIH pointwise)
  | iotaIdJReflDeep _witnessBi _baseBi witnessIH baseIH =>
      exact Step.par.iotaIdJReflDeep
        (witnessIH pointwise) (baseIH pointwise)

/-- **The β-case workhorse** for typed `cd_monotone`: single-step
joint substitution at the singleton, βι-restricted.  Specializes
`Step.par.subst_par_isBi` to a singleton substitution.

Given `par body body'` with isBi witness and `par arg arg'` with
isBi witness, produces a single par `Step.par (body.subst0 arg)
(body'.subst0 arg')` — exactly what `cd_lemma_star_with_bi`
needs to bridge step 2 of cd_monotone's β cases via cd_dominates
(whose Step.par witnesses are isBi by `cd_dominates_isBi`). -/
theorem Step.par.subst0_par_isBi
    {mode : Mode} {scope : Nat} {ctx : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    {bodyBefore bodyAfter : Term (ctx.cons argType) bodyType}
    {argumentBefore argumentAfter : Term ctx argType}
    {bodyStep : Step.par bodyBefore bodyAfter}
    {argumentStep : Step.par argumentBefore argumentAfter}
    (bodyBi : Step.par.isBi bodyStep)
    (_argumentBi : Step.par.isBi argumentStep) :
    Step.par
      (Term.subst0 bodyBefore argumentBefore)
      (Term.subst0 bodyAfter argumentAfter) :=
  Step.par.subst_par_isBi bodyBi
    (TermSubst.singleton_par_pointwise argumentStep)

end LeanFX.Syntax
