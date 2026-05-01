import LeanFX.Syntax.Reduction.ParCompatible
import LeanFX.Syntax.Reduction.ParBi
import LeanFX.Syntax.Reduction.CdDominatesIsBi

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! # `Step.par.{rename,subst}_compatible_witnessed` — βι-witnessed compat.

The parWithBi-valued companions to `Step.par.rename_compatible` and
`Step.par.subst_compatible`.  Same case enumeration as the underlying
compat theorems, but building `Step.parWithBi` (a paired Step.par +
Step.par.isBi) at each site rather than just Step.par.

η-cases (`etaArrow`, `etaSigma`) are excluded — `Step.par.isBi` omits
them by design (the η rules don't fit the βι-only regime needed for
confluence).

These are the rename/subst preservation properties needed by the
witnessed joint substitution lemma `Step.par.subst_par_witnessed`,
which in turn drives the β cases of `Step.par.cd_monotone` for typed
Church-Rosser (W8.3 / #885 / #1167).

Proof strategy: induction on the `Step.par.isBi` witness.  Each case
constructs `Step.parWithBi.mk <par> <isBi>` directly, where:
- The par-step is built via `Step.par.<C>` constructors (with the
  same cast plumbing as the underlying compat theorem).
- The isBi-witness is built via the matching `Step.par.isBi.<C>`
  constructors (with `Step.par.isBi.castBoth_eq` /
  `castSource_eq` / `castTarget_eq` for cast preservation).

Both pieces share the same let-bound `targetEquality` value where
needed (β cases), so Lean's unifier sees a consistent picture and
doesn't need to recover the equality from the underlying compat
theorem's opaque body. -/

/-! ## §1 — `Step.par.rename_compatible_witnessed`. -/

/-- Renaming a βι-witnessed parallel reduction yields a renamed,
βι-witnessed parallel reduction. -/
theorem Step.par.rename_compatible_witnessed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.parWithBi
      (Term.rename termRenaming beforeTerm)
      (Term.rename termRenaming afterTerm) := by
  induction stepBi generalizing targetScope targetCtx with
  | refl _ =>
      exact Step.parWithBi.refl _
  | app _funBi _argBi funIH argIH =>
      let funWB := funIH termRenaming
      let argWB := argIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.app funWB.toStep argWB.toStep)
        (Step.par.isBi.app funWB.toIsBi argWB.toIsBi)
  | lam _bodyBi bodyIH =>
      rename_i domainType codomainType _ _ _
      let bodyWB := bodyIH (TermRenaming.lift termRenaming domainType)
      exact Step.parWithBi.mk
        (Step.par.lam
          (Step.par.castBoth (Ty.rename_weaken_commute codomainType rawRenaming)
            bodyWB.toStep))
        (Step.par.isBi.lam
          (Step.par.isBi.castBoth_eq
            (Ty.rename_weaken_commute codomainType rawRenaming)
            bodyWB.toIsBi))
  | lamPi _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      let bodyWB := bodyIH (TermRenaming.lift termRenaming domainType)
      exact Step.parWithBi.mk
        (Step.par.lamPi bodyWB.toStep)
        (Step.par.isBi.lamPi bodyWB.toIsBi)
  | appPi _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      let funWB := funIH termRenaming
      let argWB := argIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.castBoth
          (Ty.subst0_rename_commute codomainType domainType rawRenaming).symm
          (Step.par.appPi funWB.toStep argWB.toStep))
        (Step.par.isBi.castBoth_eq
          (Ty.subst0_rename_commute codomainType domainType rawRenaming).symm
          (Step.par.isBi.appPi funWB.toIsBi argWB.toIsBi))
  | pair _firstBi _secondBi firstIH secondIH =>
      rename_i firstType secondType _ _ _ _ _ _
      let firstWB := firstIH termRenaming
      let secondWB := secondIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.pair
          firstWB.toStep
          (Step.par.castBoth
            (Ty.subst0_rename_commute secondType firstType rawRenaming)
            secondWB.toStep))
        (Step.par.isBi.pair
          firstWB.toIsBi
          (Step.par.isBi.castBoth_eq
            (Ty.subst0_rename_commute secondType firstType rawRenaming)
            secondWB.toIsBi))
  | fst _pairBi pairIH =>
      let pairWB := pairIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.fst pairWB.toStep)
        (Step.par.isBi.fst pairWB.toIsBi)
  | snd _pairBi pairIH =>
      rename_i firstType secondType _ _ _
      let pairWB := pairIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.castBoth
          (Ty.subst0_rename_commute secondType firstType rawRenaming).symm
          (Step.par.snd pairWB.toStep))
        (Step.par.isBi.castBoth_eq
          (Ty.subst0_rename_commute secondType firstType rawRenaming).symm
          (Step.par.isBi.snd pairWB.toIsBi))
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      let scrutWB := scrutIH termRenaming
      let thenWB := thenIH termRenaming
      let elseWB := elseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.boolElim scrutWB.toStep thenWB.toStep elseWB.toStep)
        (Step.par.isBi.boolElim scrutWB.toIsBi thenWB.toIsBi elseWB.toIsBi)
  | natSucc _predBi predIH =>
      let predWB := predIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.natSucc predWB.toStep)
        (Step.par.isBi.natSucc predWB.toIsBi)
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH termRenaming
      let zeroWB := zeroIH termRenaming
      let succWB := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.natElim scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.natElim scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH termRenaming
      let zeroWB := zeroIH termRenaming
      let succWB := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.natRec scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.natRec scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | listCons _headBi _tailBi headIH tailIH =>
      let headWB := headIH termRenaming
      let tailWB := tailIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.listCons headWB.toStep tailWB.toStep)
        (Step.par.isBi.listCons headWB.toIsBi tailWB.toIsBi)
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      let scrutWB := scrutIH termRenaming
      let nilWB := nilIH termRenaming
      let consWB := consIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.listElim scrutWB.toStep nilWB.toStep consWB.toStep)
        (Step.par.isBi.listElim scrutWB.toIsBi nilWB.toIsBi consWB.toIsBi)
  | optionSome _valueBi valueIH =>
      let valueWB := valueIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.optionSome valueWB.toStep)
        (Step.par.isBi.optionSome valueWB.toIsBi)
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      let scrutWB := scrutIH termRenaming
      let noneWB := noneIH termRenaming
      let someWB := someIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.optionMatch scrutWB.toStep noneWB.toStep someWB.toStep)
        (Step.par.isBi.optionMatch scrutWB.toIsBi noneWB.toIsBi someWB.toIsBi)
  | eitherInl _valueBi valueIH =>
      let valueWB := valueIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.eitherInl valueWB.toStep)
        (Step.par.isBi.eitherInl valueWB.toIsBi)
  | eitherInr _valueBi valueIH =>
      let valueWB := valueIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.eitherInr valueWB.toStep)
        (Step.par.isBi.eitherInr valueWB.toIsBi)
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      let scrutWB := scrutIH termRenaming
      let leftWB := leftIH termRenaming
      let rightWB := rightIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.eitherMatch scrutWB.toStep leftWB.toStep rightWB.toStep)
        (Step.par.isBi.eitherMatch scrutWB.toIsBi leftWB.toIsBi rightWB.toIsBi)
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      let baseWB := baseIH termRenaming
      let witnessWB := witnessIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.idJ baseWB.toStep witnessWB.toStep)
        (Step.par.isBi.idJ baseWB.toIsBi witnessWB.toIsBi)
  -- Shallow ι cases.
  | iotaBoolElimTrue elseBranch _thenBi thenIH =>
      let thenWB := thenIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrue (Term.rename termRenaming elseBranch) thenWB.toStep)
        (Step.par.isBi.iotaBoolElimTrue (Term.rename termRenaming elseBranch) thenWB.toIsBi)
  | iotaBoolElimFalse thenBranch _elseBi elseIH =>
      let elseWB := elseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalse (Term.rename termRenaming thenBranch) elseWB.toStep)
        (Step.par.isBi.iotaBoolElimFalse (Term.rename termRenaming thenBranch) elseWB.toIsBi)
  | iotaNatElimZero succBranch _zeroBi zeroIH =>
      let zeroWB := zeroIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZero (Term.rename termRenaming succBranch) zeroWB.toStep)
        (Step.par.isBi.iotaNatElimZero (Term.rename termRenaming succBranch) zeroWB.toIsBi)
  | iotaNatElimSucc zeroBranch _predBi _succBi predIH succIH =>
      let predWB := predIH termRenaming
      let succWB := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSucc (Term.rename termRenaming zeroBranch)
          predWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatElimSucc (Term.rename termRenaming zeroBranch)
          predWB.toIsBi succWB.toIsBi)
  | iotaNatRecZero succBranch _zeroBi zeroIH =>
      let zeroWB := zeroIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZero (Term.rename termRenaming succBranch) zeroWB.toStep)
        (Step.par.isBi.iotaNatRecZero (Term.rename termRenaming succBranch) zeroWB.toIsBi)
  | iotaNatRecSucc _predBi _zeroBi _succBi predIH zeroIH succIH =>
      let predWB := predIH termRenaming
      let zeroWB := zeroIH termRenaming
      let succWB := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSucc predWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatRecSucc predWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | iotaListElimNil consBranch _nilBi nilIH =>
      let nilWB := nilIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNil (Term.rename termRenaming consBranch) nilWB.toStep)
        (Step.par.isBi.iotaListElimNil (Term.rename termRenaming consBranch) nilWB.toIsBi)
  | iotaListElimCons nilBranch _headBi _tailBi _consBi headIH tailIH consIH =>
      let headWB := headIH termRenaming
      let tailWB := tailIH termRenaming
      let consWB := consIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaListElimCons (Term.rename termRenaming nilBranch)
          headWB.toStep tailWB.toStep consWB.toStep)
        (Step.par.isBi.iotaListElimCons (Term.rename termRenaming nilBranch)
          headWB.toIsBi tailWB.toIsBi consWB.toIsBi)
  | iotaOptionMatchNone someBranch _noneBi noneIH =>
      let noneWB := noneIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNone (Term.rename termRenaming someBranch) noneWB.toStep)
        (Step.par.isBi.iotaOptionMatchNone (Term.rename termRenaming someBranch) noneWB.toIsBi)
  | iotaOptionMatchSome noneBranch _valueBi _someBi valueIH someIH =>
      let valueWB := valueIH termRenaming
      let someWB := someIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSome (Term.rename termRenaming noneBranch)
          valueWB.toStep someWB.toStep)
        (Step.par.isBi.iotaOptionMatchSome (Term.rename termRenaming noneBranch)
          valueWB.toIsBi someWB.toIsBi)
  | iotaEitherMatchInl rightBranch _valueBi _leftBi valueIH leftIH =>
      let valueWB := valueIH termRenaming
      let leftWB := leftIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInl (Term.rename termRenaming rightBranch)
          valueWB.toStep leftWB.toStep)
        (Step.par.isBi.iotaEitherMatchInl (Term.rename termRenaming rightBranch)
          valueWB.toIsBi leftWB.toIsBi)
  | iotaEitherMatchInr leftBranch _valueBi _rightBi valueIH rightIH =>
      let valueWB := valueIH termRenaming
      let rightWB := rightIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInr (Term.rename termRenaming leftBranch)
          valueWB.toStep rightWB.toStep)
        (Step.par.isBi.iotaEitherMatchInr (Term.rename termRenaming leftBranch)
          valueWB.toIsBi rightWB.toIsBi)
  | iotaIdJRefl _baseBi baseIH =>
      let baseWB := baseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaIdJRefl baseWB.toStep)
        (Step.par.isBi.iotaIdJRefl baseWB.toIsBi)
  -- Shallow β cases — HEq plumbing through `castTarget` to align
  -- renamed `subst0` with the original cast-bearing target.
  | betaApp _bodyBi _argBi bodyIH argIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let bodyWB := bodyIH (TermRenaming.lift termRenaming domainType)
      let argWB := argIH termRenaming
      let renamedArgumentAfter : Term targetCtx (domainType.rename rawRenaming) :=
        Term.rename termRenaming argumentAfter
      let renamedBodyAfter :
          Term (targetCtx.cons (domainType.rename rawRenaming))
            (codomainType.weaken.rename rawRenaming.lift) :=
        Term.rename (TermRenaming.lift termRenaming domainType) bodyAfter
      let renamedBetaStep :=
        Step.par.betaApp
          (Step.par.castBoth (Ty.rename_weaken_commute codomainType rawRenaming)
            bodyWB.toStep)
          argWB.toStep
      let renamedBetaStepIsBi :=
        Step.par.isBi.betaApp
          (Step.par.isBi.castBoth_eq (Ty.rename_weaken_commute codomainType rawRenaming)
            bodyWB.toIsBi)
          argWB.toIsBi
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
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality renamedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality renamedBetaStepIsBi)
  | betaAppPi _bodyBi _argBi bodyIH argIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let bodyWB := bodyIH (TermRenaming.lift termRenaming domainType)
      let argWB := argIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute codomainType domainType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPi bodyWB.toStep argWB.toStep)
      let renamedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaAppPi bodyWB.toIsBi argWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.rename (TermRenaming.lift termRenaming domainType) bodyAfter)
                (Term.rename termRenaming argumentAfter)
            = Term.rename termRenaming (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.rename_subst0_HEq termRenaming bodyAfter argumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality renamedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality renamedBetaStepIsBi)
  | betaFstPair _firstBi firstIH =>
      rename_i firstType secondType _ _ secondVal _
      let firstWB := firstIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      simp only [Term.rename]
      exact Step.parWithBi.mk
        (Step.par.betaFstPair
          (resultTypeEquality ▸ Term.rename termRenaming secondVal)
          firstWB.toStep)
        (Step.par.isBi.betaFstPair
          (secondVal := resultTypeEquality ▸ Term.rename termRenaming secondVal)
          firstWB.toIsBi)
  | betaSndPair _secondBi secondIH =>
      rename_i firstType secondType firstVal _ secondAfter _
      let secondWB := secondIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPair
            (Term.rename termRenaming firstVal)
            (Step.par.castBoth resultTypeEquality secondWB.toStep))
      let renamedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaSndPair
            (firstVal := Term.rename termRenaming firstVal)
            (Step.par.isBi.castBoth_eq resultTypeEquality secondWB.toIsBi))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.rename termRenaming secondAfter)
            = Term.rename termRenaming secondAfter :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality renamedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality renamedBetaStepIsBi)
  -- Deep β cases.
  | betaAppDeep _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let funWB := funIH termRenaming
      let argWB := argIH termRenaming
      let renamedArgAfter : Term targetCtx (domainType.rename rawRenaming) :=
        Term.rename termRenaming argAfter
      let renamedBody :
          Term (targetCtx.cons (domainType.rename rawRenaming))
            (codomainType.weaken.rename rawRenaming.lift) :=
        Term.rename (TermRenaming.lift termRenaming domainType) body
      let renamedBetaStep :=
        Step.par.betaAppDeep funWB.toStep argWB.toStep
      let renamedBetaStepIsBi :=
        Step.par.isBi.betaAppDeep funWB.toIsBi argWB.toIsBi
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
                renamedBody renamedArgAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.rename rawRenaming)
              (domainType.rename rawRenaming))
            (Term.subst0
              ((Ty.rename_weaken_commute codomainType rawRenaming) ▸ renamedBody)
              renamedArgAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality renamedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality renamedBetaStepIsBi)
  | betaAppPiDeep _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let funWB := funIH termRenaming
      let argWB := argIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute codomainType domainType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPiDeep funWB.toStep argWB.toStep)
      let renamedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaAppPiDeep funWB.toIsBi argWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.rename (TermRenaming.lift termRenaming domainType) body)
                (Term.rename termRenaming argAfter)
            = Term.rename termRenaming (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.rename_subst0_HEq termRenaming body argAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality renamedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality renamedBetaStepIsBi)
  | betaFstPairDeep _pairBi pairIH =>
      let pairWB := pairIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.betaFstPairDeep pairWB.toStep)
        (Step.par.isBi.betaFstPairDeep pairWB.toIsBi)
  | betaSndPairDeep _pairBi pairIH =>
      rename_i firstType secondType _ _ secondVal _
      let pairWB := pairIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let renamedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPairDeep pairWB.toStep)
      let renamedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaSndPairDeep pairWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_rename_commute secondType firstType rawRenaming) ▸
                Term.rename termRenaming secondVal)
            = Term.rename termRenaming secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality renamedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality renamedBetaStepIsBi)
  -- Deep ι cases.
  | iotaBoolElimTrueDeep elseBranch _scrutBi _thenBi scrutIH thenIH =>
      let scrutWB := scrutIH termRenaming
      let thenWB := thenIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrueDeep (Term.rename termRenaming elseBranch)
          scrutWB.toStep thenWB.toStep)
        (Step.par.isBi.iotaBoolElimTrueDeep (Term.rename termRenaming elseBranch)
          scrutWB.toIsBi thenWB.toIsBi)
  | iotaBoolElimFalseDeep thenBranch _scrutBi _elseBi scrutIH elseIH =>
      let scrutWB := scrutIH termRenaming
      let elseWB := elseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalseDeep (Term.rename termRenaming thenBranch)
          scrutWB.toStep elseWB.toStep)
        (Step.par.isBi.iotaBoolElimFalseDeep (Term.rename termRenaming thenBranch)
          scrutWB.toIsBi elseWB.toIsBi)
  | iotaNatElimZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      let scrutWB := scrutIH termRenaming
      let zeroWB := zeroIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZeroDeep (Term.rename termRenaming succBranch)
          scrutWB.toStep zeroWB.toStep)
        (Step.par.isBi.iotaNatElimZeroDeep (Term.rename termRenaming succBranch)
          scrutWB.toIsBi zeroWB.toIsBi)
  | iotaNatElimSuccDeep zeroBranch _scrutBi _succBi scrutIH succIH =>
      let scrutWB := scrutIH termRenaming
      let succWB := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSuccDeep (Term.rename termRenaming zeroBranch)
          scrutWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatElimSuccDeep (Term.rename termRenaming zeroBranch)
          scrutWB.toIsBi succWB.toIsBi)
  | iotaNatRecZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      let scrutWB := scrutIH termRenaming
      let zeroWB := zeroIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZeroDeep (Term.rename termRenaming succBranch)
          scrutWB.toStep zeroWB.toStep)
        (Step.par.isBi.iotaNatRecZeroDeep (Term.rename termRenaming succBranch)
          scrutWB.toIsBi zeroWB.toIsBi)
  | iotaNatRecSuccDeep _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH termRenaming
      let zeroWB := zeroIH termRenaming
      let succWB := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSuccDeep scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatRecSuccDeep scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | iotaListElimNilDeep consBranch _scrutBi _nilBi scrutIH nilIH =>
      let scrutWB := scrutIH termRenaming
      let nilWB := nilIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNilDeep (Term.rename termRenaming consBranch)
          scrutWB.toStep nilWB.toStep)
        (Step.par.isBi.iotaListElimNilDeep (Term.rename termRenaming consBranch)
          scrutWB.toIsBi nilWB.toIsBi)
  | iotaListElimConsDeep nilBranch _scrutBi _consBi scrutIH consIH =>
      let scrutWB := scrutIH termRenaming
      let consWB := consIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaListElimConsDeep (Term.rename termRenaming nilBranch)
          scrutWB.toStep consWB.toStep)
        (Step.par.isBi.iotaListElimConsDeep (Term.rename termRenaming nilBranch)
          scrutWB.toIsBi consWB.toIsBi)
  | iotaOptionMatchNoneDeep someBranch _scrutBi _noneBi scrutIH noneIH =>
      let scrutWB := scrutIH termRenaming
      let noneWB := noneIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNoneDeep (Term.rename termRenaming someBranch)
          scrutWB.toStep noneWB.toStep)
        (Step.par.isBi.iotaOptionMatchNoneDeep (Term.rename termRenaming someBranch)
          scrutWB.toIsBi noneWB.toIsBi)
  | iotaOptionMatchSomeDeep noneBranch _scrutBi _someBi scrutIH someIH =>
      let scrutWB := scrutIH termRenaming
      let someWB := someIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSomeDeep (Term.rename termRenaming noneBranch)
          scrutWB.toStep someWB.toStep)
        (Step.par.isBi.iotaOptionMatchSomeDeep (Term.rename termRenaming noneBranch)
          scrutWB.toIsBi someWB.toIsBi)
  | iotaEitherMatchInlDeep rightBranch _scrutBi _leftBi scrutIH leftIH =>
      let scrutWB := scrutIH termRenaming
      let leftWB := leftIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInlDeep (Term.rename termRenaming rightBranch)
          scrutWB.toStep leftWB.toStep)
        (Step.par.isBi.iotaEitherMatchInlDeep (Term.rename termRenaming rightBranch)
          scrutWB.toIsBi leftWB.toIsBi)
  | iotaEitherMatchInrDeep leftBranch _scrutBi _rightBi scrutIH rightIH =>
      let scrutWB := scrutIH termRenaming
      let rightWB := rightIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInrDeep (Term.rename termRenaming leftBranch)
          scrutWB.toStep rightWB.toStep)
        (Step.par.isBi.iotaEitherMatchInrDeep (Term.rename termRenaming leftBranch)
          scrutWB.toIsBi rightWB.toIsBi)
  | iotaIdJReflDeep _witnessBi _baseBi witnessIH baseIH =>
      let witnessWB := witnessIH termRenaming
      let baseWB := baseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaIdJReflDeep witnessWB.toStep baseWB.toStep)
        (Step.par.isBi.iotaIdJReflDeep witnessWB.toIsBi baseWB.toIsBi)

/-! ## §2 — `Step.par.subst_compatible_witnessed`. -/

/-- Substituting a βι-witnessed parallel reduction yields a substituted,
βι-witnessed parallel reduction. -/
theorem Step.par.subst_compatible_witnessed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.parWithBi
      (Term.subst termSubstitution beforeTerm)
      (Term.subst termSubstitution afterTerm) := by
  induction stepBi generalizing targetScope targetCtx with
  | refl _ =>
      exact Step.parWithBi.refl _
  | app _funBi _argBi funIH argIH =>
      let funWB := funIH termSubstitution
      let argWB := argIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.app funWB.toStep argWB.toStep)
        (Step.par.isBi.app funWB.toIsBi argWB.toIsBi)
  | lam _bodyBi bodyIH =>
      rename_i domainType codomainType _ _ _
      let bodyWB := bodyIH (TermSubst.lift termSubstitution domainType)
      exact Step.parWithBi.mk
        (Step.par.lam
          (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toStep))
        (Step.par.isBi.lam
          (Step.par.isBi.castBoth_eq
            (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toIsBi))
  | lamPi _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      let bodyWB := bodyIH (TermSubst.lift termSubstitution domainType)
      exact Step.parWithBi.mk
        (Step.par.lamPi bodyWB.toStep)
        (Step.par.isBi.lamPi bodyWB.toIsBi)
  | appPi _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      let funWB := funIH termSubstitution
      let argWB := argIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.castBoth
          (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
          (Step.par.appPi funWB.toStep argWB.toStep))
        (Step.par.isBi.castBoth_eq
          (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
          (Step.par.isBi.appPi funWB.toIsBi argWB.toIsBi))
  | pair _firstBi _secondBi firstIH secondIH =>
      rename_i firstType secondType _ _ _ _ _ _
      let firstWB := firstIH termSubstitution
      let secondWB := secondIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.pair
          firstWB.toStep
          (Step.par.castBoth
            (Ty.subst0_subst_commute secondType firstType typeSubstitution)
            secondWB.toStep))
        (Step.par.isBi.pair
          firstWB.toIsBi
          (Step.par.isBi.castBoth_eq
            (Ty.subst0_subst_commute secondType firstType typeSubstitution)
            secondWB.toIsBi))
  | fst _pairBi pairIH =>
      let pairWB := pairIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.fst pairWB.toStep)
        (Step.par.isBi.fst pairWB.toIsBi)
  | snd _pairBi pairIH =>
      rename_i firstType secondType _ _ _
      let pairWB := pairIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.castBoth
          (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
          (Step.par.snd pairWB.toStep))
        (Step.par.isBi.castBoth_eq
          (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
          (Step.par.isBi.snd pairWB.toIsBi))
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      let scrutWB := scrutIH termSubstitution
      let thenWB := thenIH termSubstitution
      let elseWB := elseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.boolElim scrutWB.toStep thenWB.toStep elseWB.toStep)
        (Step.par.isBi.boolElim scrutWB.toIsBi thenWB.toIsBi elseWB.toIsBi)
  | natSucc _predBi predIH =>
      let predWB := predIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.natSucc predWB.toStep)
        (Step.par.isBi.natSucc predWB.toIsBi)
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH termSubstitution
      let zeroWB := zeroIH termSubstitution
      let succWB := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.natElim scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.natElim scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH termSubstitution
      let zeroWB := zeroIH termSubstitution
      let succWB := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.natRec scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.natRec scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | listCons _headBi _tailBi headIH tailIH =>
      let headWB := headIH termSubstitution
      let tailWB := tailIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.listCons headWB.toStep tailWB.toStep)
        (Step.par.isBi.listCons headWB.toIsBi tailWB.toIsBi)
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      let scrutWB := scrutIH termSubstitution
      let nilWB := nilIH termSubstitution
      let consWB := consIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.listElim scrutWB.toStep nilWB.toStep consWB.toStep)
        (Step.par.isBi.listElim scrutWB.toIsBi nilWB.toIsBi consWB.toIsBi)
  | optionSome _valueBi valueIH =>
      let valueWB := valueIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.optionSome valueWB.toStep)
        (Step.par.isBi.optionSome valueWB.toIsBi)
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      let scrutWB := scrutIH termSubstitution
      let noneWB := noneIH termSubstitution
      let someWB := someIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.optionMatch scrutWB.toStep noneWB.toStep someWB.toStep)
        (Step.par.isBi.optionMatch scrutWB.toIsBi noneWB.toIsBi someWB.toIsBi)
  | eitherInl _valueBi valueIH =>
      let valueWB := valueIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.eitherInl valueWB.toStep)
        (Step.par.isBi.eitherInl valueWB.toIsBi)
  | eitherInr _valueBi valueIH =>
      let valueWB := valueIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.eitherInr valueWB.toStep)
        (Step.par.isBi.eitherInr valueWB.toIsBi)
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      let scrutWB := scrutIH termSubstitution
      let leftWB := leftIH termSubstitution
      let rightWB := rightIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.eitherMatch scrutWB.toStep leftWB.toStep rightWB.toStep)
        (Step.par.isBi.eitherMatch scrutWB.toIsBi leftWB.toIsBi rightWB.toIsBi)
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      let baseWB := baseIH termSubstitution
      let witnessWB := witnessIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.idJ baseWB.toStep witnessWB.toStep)
        (Step.par.isBi.idJ baseWB.toIsBi witnessWB.toIsBi)
  -- Shallow ι cases.
  | iotaBoolElimTrue elseBranch _thenBi thenIH =>
      let thenWB := thenIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrue (Term.subst termSubstitution elseBranch) thenWB.toStep)
        (Step.par.isBi.iotaBoolElimTrue (Term.subst termSubstitution elseBranch) thenWB.toIsBi)
  | iotaBoolElimFalse thenBranch _elseBi elseIH =>
      let elseWB := elseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalse (Term.subst termSubstitution thenBranch) elseWB.toStep)
        (Step.par.isBi.iotaBoolElimFalse (Term.subst termSubstitution thenBranch) elseWB.toIsBi)
  | iotaNatElimZero succBranch _zeroBi zeroIH =>
      let zeroWB := zeroIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZero (Term.subst termSubstitution succBranch) zeroWB.toStep)
        (Step.par.isBi.iotaNatElimZero (Term.subst termSubstitution succBranch) zeroWB.toIsBi)
  | iotaNatElimSucc zeroBranch _predBi _succBi predIH succIH =>
      let predWB := predIH termSubstitution
      let succWB := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSucc (Term.subst termSubstitution zeroBranch)
          predWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatElimSucc (Term.subst termSubstitution zeroBranch)
          predWB.toIsBi succWB.toIsBi)
  | iotaNatRecZero succBranch _zeroBi zeroIH =>
      let zeroWB := zeroIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZero (Term.subst termSubstitution succBranch) zeroWB.toStep)
        (Step.par.isBi.iotaNatRecZero (Term.subst termSubstitution succBranch) zeroWB.toIsBi)
  | iotaNatRecSucc _predBi _zeroBi _succBi predIH zeroIH succIH =>
      let predWB := predIH termSubstitution
      let zeroWB := zeroIH termSubstitution
      let succWB := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSucc predWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatRecSucc predWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | iotaListElimNil consBranch _nilBi nilIH =>
      let nilWB := nilIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNil (Term.subst termSubstitution consBranch) nilWB.toStep)
        (Step.par.isBi.iotaListElimNil (Term.subst termSubstitution consBranch) nilWB.toIsBi)
  | iotaListElimCons nilBranch _headBi _tailBi _consBi headIH tailIH consIH =>
      let headWB := headIH termSubstitution
      let tailWB := tailIH termSubstitution
      let consWB := consIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaListElimCons (Term.subst termSubstitution nilBranch)
          headWB.toStep tailWB.toStep consWB.toStep)
        (Step.par.isBi.iotaListElimCons (Term.subst termSubstitution nilBranch)
          headWB.toIsBi tailWB.toIsBi consWB.toIsBi)
  | iotaOptionMatchNone someBranch _noneBi noneIH =>
      let noneWB := noneIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNone (Term.subst termSubstitution someBranch) noneWB.toStep)
        (Step.par.isBi.iotaOptionMatchNone (Term.subst termSubstitution someBranch) noneWB.toIsBi)
  | iotaOptionMatchSome noneBranch _valueBi _someBi valueIH someIH =>
      let valueWB := valueIH termSubstitution
      let someWB := someIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSome (Term.subst termSubstitution noneBranch)
          valueWB.toStep someWB.toStep)
        (Step.par.isBi.iotaOptionMatchSome (Term.subst termSubstitution noneBranch)
          valueWB.toIsBi someWB.toIsBi)
  | iotaEitherMatchInl rightBranch _valueBi _leftBi valueIH leftIH =>
      let valueWB := valueIH termSubstitution
      let leftWB := leftIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInl (Term.subst termSubstitution rightBranch)
          valueWB.toStep leftWB.toStep)
        (Step.par.isBi.iotaEitherMatchInl (Term.subst termSubstitution rightBranch)
          valueWB.toIsBi leftWB.toIsBi)
  | iotaEitherMatchInr leftBranch _valueBi _rightBi valueIH rightIH =>
      let valueWB := valueIH termSubstitution
      let rightWB := rightIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInr (Term.subst termSubstitution leftBranch)
          valueWB.toStep rightWB.toStep)
        (Step.par.isBi.iotaEitherMatchInr (Term.subst termSubstitution leftBranch)
          valueWB.toIsBi rightWB.toIsBi)
  | iotaIdJRefl _baseBi baseIH =>
      let baseWB := baseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaIdJRefl baseWB.toStep)
        (Step.par.isBi.iotaIdJRefl baseWB.toIsBi)
  -- Shallow β cases.
  | betaApp _bodyBi _argBi bodyIH argIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let bodyWB := bodyIH (TermSubst.lift termSubstitution domainType)
      let argWB := argIH termSubstitution
      let substitutedArgumentAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst termSubstitution argumentAfter
      let substitutedBodyAfter :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift termSubstitution domainType) bodyAfter
      let substitutedBetaStep :=
        Step.par.betaApp
          (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toStep)
          argWB.toStep
      let substitutedBetaStepIsBi :=
        Step.par.isBi.betaApp
          (Step.par.isBi.castBoth_eq (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toIsBi)
          argWB.toIsBi
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
                substitutedBodyAfter substitutedArgumentAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0
              ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBodyAfter)
              substitutedArgumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaAppPi _bodyBi _argBi bodyIH argIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let bodyWB := bodyIH (TermSubst.lift termSubstitution domainType)
      let argWB := argIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPi bodyWB.toStep argWB.toStep)
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaAppPi bodyWB.toIsBi argWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift termSubstitution domainType) bodyAfter)
                (Term.subst termSubstitution argumentAfter)
            = Term.subst termSubstitution (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq termSubstitution bodyAfter argumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaFstPair _firstBi firstIH =>
      rename_i firstType secondType _ _ secondVal _
      let firstWB := firstIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      simp only [Term.subst]
      exact Step.parWithBi.mk
        (Step.par.betaFstPair
          (resultTypeEquality ▸ Term.subst termSubstitution secondVal)
          firstWB.toStep)
        (Step.par.isBi.betaFstPair
          (secondVal := resultTypeEquality ▸ Term.subst termSubstitution secondVal)
          firstWB.toIsBi)
  | betaSndPair _secondBi secondIH =>
      rename_i firstType secondType firstVal _ secondAfter _
      let secondWB := secondIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPair
            (Term.subst termSubstitution firstVal)
            (Step.par.castBoth resultTypeEquality secondWB.toStep))
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaSndPair
            (firstVal := Term.subst termSubstitution firstVal)
            (Step.par.isBi.castBoth_eq resultTypeEquality secondWB.toIsBi))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.subst termSubstitution secondAfter)
            = Term.subst termSubstitution secondAfter :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  -- Deep β cases.
  | betaAppDeep _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let funWB := funIH termSubstitution
      let argWB := argIH termSubstitution
      let substitutedArgAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst termSubstitution argAfter
      let substitutedBody :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift termSubstitution domainType) body
      let substitutedBetaStep :=
        Step.par.betaAppDeep funWB.toStep argWB.toStep
      let substitutedBetaStepIsBi :=
        Step.par.isBi.betaAppDeep funWB.toIsBi argWB.toIsBi
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
                substitutedBody substitutedArgAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0
              ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
              substitutedArgAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaAppPiDeep _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let funWB := funIH termSubstitution
      let argWB := argIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPiDeep funWB.toStep argWB.toStep)
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaAppPiDeep funWB.toIsBi argWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift termSubstitution domainType) body)
                (Term.subst termSubstitution argAfter)
            = Term.subst termSubstitution (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq termSubstitution body argAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaFstPairDeep _pairBi pairIH =>
      let pairWB := pairIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.betaFstPairDeep pairWB.toStep)
        (Step.par.isBi.betaFstPairDeep pairWB.toIsBi)
  | betaSndPairDeep _pairBi pairIH =>
      rename_i firstType secondType _ _ secondVal _
      let pairWB := pairIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPairDeep pairWB.toStep)
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaSndPairDeep pairWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_subst_commute secondType firstType typeSubstitution) ▸
                Term.subst termSubstitution secondVal)
            = Term.subst termSubstitution secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  -- Deep ι cases.
  | iotaBoolElimTrueDeep elseBranch _scrutBi _thenBi scrutIH thenIH =>
      let scrutWB := scrutIH termSubstitution
      let thenWB := thenIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrueDeep (Term.subst termSubstitution elseBranch)
          scrutWB.toStep thenWB.toStep)
        (Step.par.isBi.iotaBoolElimTrueDeep (Term.subst termSubstitution elseBranch)
          scrutWB.toIsBi thenWB.toIsBi)
  | iotaBoolElimFalseDeep thenBranch _scrutBi _elseBi scrutIH elseIH =>
      let scrutWB := scrutIH termSubstitution
      let elseWB := elseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalseDeep (Term.subst termSubstitution thenBranch)
          scrutWB.toStep elseWB.toStep)
        (Step.par.isBi.iotaBoolElimFalseDeep (Term.subst termSubstitution thenBranch)
          scrutWB.toIsBi elseWB.toIsBi)
  | iotaNatElimZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      let scrutWB := scrutIH termSubstitution
      let zeroWB := zeroIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZeroDeep (Term.subst termSubstitution succBranch)
          scrutWB.toStep zeroWB.toStep)
        (Step.par.isBi.iotaNatElimZeroDeep (Term.subst termSubstitution succBranch)
          scrutWB.toIsBi zeroWB.toIsBi)
  | iotaNatElimSuccDeep zeroBranch _scrutBi _succBi scrutIH succIH =>
      let scrutWB := scrutIH termSubstitution
      let succWB := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSuccDeep (Term.subst termSubstitution zeroBranch)
          scrutWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatElimSuccDeep (Term.subst termSubstitution zeroBranch)
          scrutWB.toIsBi succWB.toIsBi)
  | iotaNatRecZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      let scrutWB := scrutIH termSubstitution
      let zeroWB := zeroIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZeroDeep (Term.subst termSubstitution succBranch)
          scrutWB.toStep zeroWB.toStep)
        (Step.par.isBi.iotaNatRecZeroDeep (Term.subst termSubstitution succBranch)
          scrutWB.toIsBi zeroWB.toIsBi)
  | iotaNatRecSuccDeep _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH termSubstitution
      let zeroWB := zeroIH termSubstitution
      let succWB := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSuccDeep scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatRecSuccDeep scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | iotaListElimNilDeep consBranch _scrutBi _nilBi scrutIH nilIH =>
      let scrutWB := scrutIH termSubstitution
      let nilWB := nilIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNilDeep (Term.subst termSubstitution consBranch)
          scrutWB.toStep nilWB.toStep)
        (Step.par.isBi.iotaListElimNilDeep (Term.subst termSubstitution consBranch)
          scrutWB.toIsBi nilWB.toIsBi)
  | iotaListElimConsDeep nilBranch _scrutBi _consBi scrutIH consIH =>
      let scrutWB := scrutIH termSubstitution
      let consWB := consIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaListElimConsDeep (Term.subst termSubstitution nilBranch)
          scrutWB.toStep consWB.toStep)
        (Step.par.isBi.iotaListElimConsDeep (Term.subst termSubstitution nilBranch)
          scrutWB.toIsBi consWB.toIsBi)
  | iotaOptionMatchNoneDeep someBranch _scrutBi _noneBi scrutIH noneIH =>
      let scrutWB := scrutIH termSubstitution
      let noneWB := noneIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNoneDeep (Term.subst termSubstitution someBranch)
          scrutWB.toStep noneWB.toStep)
        (Step.par.isBi.iotaOptionMatchNoneDeep (Term.subst termSubstitution someBranch)
          scrutWB.toIsBi noneWB.toIsBi)
  | iotaOptionMatchSomeDeep noneBranch _scrutBi _someBi scrutIH someIH =>
      let scrutWB := scrutIH termSubstitution
      let someWB := someIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSomeDeep (Term.subst termSubstitution noneBranch)
          scrutWB.toStep someWB.toStep)
        (Step.par.isBi.iotaOptionMatchSomeDeep (Term.subst termSubstitution noneBranch)
          scrutWB.toIsBi someWB.toIsBi)
  | iotaEitherMatchInlDeep rightBranch _scrutBi _leftBi scrutIH leftIH =>
      let scrutWB := scrutIH termSubstitution
      let leftWB := leftIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInlDeep (Term.subst termSubstitution rightBranch)
          scrutWB.toStep leftWB.toStep)
        (Step.par.isBi.iotaEitherMatchInlDeep (Term.subst termSubstitution rightBranch)
          scrutWB.toIsBi leftWB.toIsBi)
  | iotaEitherMatchInrDeep leftBranch _scrutBi _rightBi scrutIH rightIH =>
      let scrutWB := scrutIH termSubstitution
      let rightWB := rightIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInrDeep (Term.subst termSubstitution leftBranch)
          scrutWB.toStep rightWB.toStep)
        (Step.par.isBi.iotaEitherMatchInrDeep (Term.subst termSubstitution leftBranch)
          scrutWB.toIsBi rightWB.toIsBi)
  | iotaIdJReflDeep _witnessBi _baseBi witnessIH baseIH =>
      let witnessWB := witnessIH termSubstitution
      let baseWB := baseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaIdJReflDeep witnessWB.toStep baseWB.toStep)
        (Step.par.isBi.iotaIdJReflDeep witnessWB.toIsBi baseWB.toIsBi)

end LeanFX.Syntax
