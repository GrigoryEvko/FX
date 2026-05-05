import LeanFX2.Confluence.RawCd
import LeanFX2.Reduction.RawPar

/-! # Confluence/RawCdDominates — every raw term parallel-reduces to its cd

`RawStep.par.cd_dominates : ∀ t, RawStep.par t (RawTerm.cd t)`.

Proof shape: structural induction on the raw term.  For each ctor:
* Atomic (var/unit/booleans/zero/Nil/None) — `RawStep.par.refl _`.
* Pure cong (lam/pair/listCons/optionSome/eitherInl/Inr/natSucc/refl
  /modIntro/modElim/subsume) — apply the cong rule with IH.
* Redex-bearing (app/fst/snd/boolElim/natElim/natRec/listElim
  /optionMatch/eitherMatch/idJ) — `simp only [RawTerm.cd]; split`
  produces one goal per ctor of the inner match's scrutinee; the
  redex case fires the appropriate Deep β/ι rule using the IH;
  `all_goals` discharges the cong-shape fallthrough.

Pairs with `cd_lemma` (every parallel reduct lands in cd t) to give
the Tait–Martin-Löf complete-development pair from which raw
diamond and confluence follow.

## Modal cases

`modIntro`/`modElim`/`subsume` are pure cong (no `iotaModal*` rule
in lean-fx-2's RawStep.par yet — Layer 6 will add modal reductions
when the modality theory ships).  Each modal arm is a one-line
`simp + cong rule + recursive call`.
-/

-- D1.6 grew RawTerm to 55 ctors and `RawTerm.cd` to a match with
-- 10 inner matches × 55 arms ≈ 550 branches.  `simp only [RawTerm.cd]`
-- and the per-arm `split` tactic exceed the 200K-heartbeat default
-- when reducing the now-large cd into shape.  Set to 0 to disable
-- the heartbeat check entirely; the proof structure is unchanged.
set_option maxHeartbeats 0

namespace LeanFX2

/-- Every raw term parallel-reduces to its complete development.
Pairs with `cd_lemma` to bound parallel-reduction chains: every
reduct of `t` reaches `cd t`, and `cd t` is a parallel-reduct of `t`. -/
theorem RawStep.par.cd_dominates :
    {scope : Nat} → (rawTerm : RawTerm scope) →
    RawStep.par rawTerm (RawTerm.cd rawTerm)
  | _, .var _ => RawStep.par.refl _
  | _, .unit => RawStep.par.refl _
  | _, .lam body =>
      RawStep.par.lam (RawStep.par.cd_dominates body)
  | _, .app functionTerm argumentTerm => by
      let functionParStep := RawStep.par.cd_dominates functionTerm
      let argumentParStep := RawStep.par.cd_dominates argumentTerm
      unfold RawTerm.cd
      unfold RawTerm.cdAppCase
      split
      case _ body bodyEqn =>
          exact RawStep.par.betaAppDeep
            (bodyEqn ▸ functionParStep) argumentParStep
      all_goals exact RawStep.par.app functionParStep argumentParStep
  | _, .pair firstValue secondValue =>
      RawStep.par.pair
        (RawStep.par.cd_dominates firstValue)
        (RawStep.par.cd_dominates secondValue)
  | _, .fst pairTerm => by
      let pairParStep := RawStep.par.cd_dominates pairTerm
      unfold RawTerm.cd
      unfold RawTerm.cdFstCase
      split
      case _ firstValue secondValue pairEqn =>
          exact RawStep.par.betaFstPairDeep (pairEqn ▸ pairParStep)
      all_goals exact RawStep.par.fst pairParStep
  | _, .snd pairTerm => by
      let pairParStep := RawStep.par.cd_dominates pairTerm
      unfold RawTerm.cd
      unfold RawTerm.cdSndCase
      split
      case _ firstValue secondValue pairEqn =>
          exact RawStep.par.betaSndPairDeep (pairEqn ▸ pairParStep)
      all_goals exact RawStep.par.snd pairParStep
  | _, .boolTrue => RawStep.par.refl _
  | _, .boolFalse => RawStep.par.refl _
  | _, .boolElim scrutinee thenBranch elseBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let thenParStep := RawStep.par.cd_dominates thenBranch
      let elseParStep := RawStep.par.cd_dominates elseBranch
      unfold RawTerm.cd
      unfold RawTerm.cdBoolElimCase
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaBoolElimTrueDeep elseBranch
            (scrutineeEqn ▸ scrutineeParStep) thenParStep
      case _ scrutineeEqn =>
          exact RawStep.par.iotaBoolElimFalseDeep thenBranch
            (scrutineeEqn ▸ scrutineeParStep) elseParStep
      all_goals
        exact RawStep.par.boolElim scrutineeParStep thenParStep elseParStep
  | _, .natZero => RawStep.par.refl _
  | _, .natSucc predecessor =>
      RawStep.par.natSucc (RawStep.par.cd_dominates predecessor)
  | _, .natElim scrutinee zeroBranch succBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let zeroParStep := RawStep.par.cd_dominates zeroBranch
      let succParStep := RawStep.par.cd_dominates succBranch
      unfold RawTerm.cd
      unfold RawTerm.cdNatElimCase
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaNatElimZeroDeep succBranch
            (scrutineeEqn ▸ scrutineeParStep) zeroParStep
      case _ predecessor scrutineeEqn =>
          exact RawStep.par.iotaNatElimSuccDeep zeroBranch
            (scrutineeEqn ▸ scrutineeParStep) succParStep
      all_goals
        exact RawStep.par.natElim scrutineeParStep zeroParStep succParStep
  | _, .natRec scrutinee zeroBranch succBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let zeroParStep := RawStep.par.cd_dominates zeroBranch
      let succParStep := RawStep.par.cd_dominates succBranch
      unfold RawTerm.cd
      unfold RawTerm.cdNatRecCase
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaNatRecZeroDeep succBranch
            (scrutineeEqn ▸ scrutineeParStep) zeroParStep
      case _ predecessor scrutineeEqn =>
          exact RawStep.par.iotaNatRecSuccDeep
            (scrutineeEqn ▸ scrutineeParStep) zeroParStep succParStep
      all_goals
        exact RawStep.par.natRec scrutineeParStep zeroParStep succParStep
  | _, .listNil => RawStep.par.refl _
  | _, .listCons headTerm tailTerm =>
      RawStep.par.listCons
        (RawStep.par.cd_dominates headTerm)
        (RawStep.par.cd_dominates tailTerm)
  | _, .listElim scrutinee nilBranch consBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let nilParStep := RawStep.par.cd_dominates nilBranch
      let consParStep := RawStep.par.cd_dominates consBranch
      unfold RawTerm.cd
      unfold RawTerm.cdListElimCase
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaListElimNilDeep consBranch
            (scrutineeEqn ▸ scrutineeParStep) nilParStep
      case _ headTerm tailTerm scrutineeEqn =>
          exact RawStep.par.iotaListElimConsDeep nilBranch
            (scrutineeEqn ▸ scrutineeParStep) consParStep
      all_goals
        exact RawStep.par.listElim scrutineeParStep nilParStep consParStep
  | _, .optionNone => RawStep.par.refl _
  | _, .optionSome valueTerm =>
      RawStep.par.optionSome (RawStep.par.cd_dominates valueTerm)
  | _, .optionMatch scrutinee noneBranch someBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let noneParStep := RawStep.par.cd_dominates noneBranch
      let someParStep := RawStep.par.cd_dominates someBranch
      unfold RawTerm.cd
      unfold RawTerm.cdOptionMatchCase
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaOptionMatchNoneDeep someBranch
            (scrutineeEqn ▸ scrutineeParStep) noneParStep
      case _ valueTerm scrutineeEqn =>
          exact RawStep.par.iotaOptionMatchSomeDeep noneBranch
            (scrutineeEqn ▸ scrutineeParStep) someParStep
      all_goals
        exact RawStep.par.optionMatch scrutineeParStep noneParStep someParStep
  | _, .eitherInl valueTerm =>
      RawStep.par.eitherInl (RawStep.par.cd_dominates valueTerm)
  | _, .eitherInr valueTerm =>
      RawStep.par.eitherInr (RawStep.par.cd_dominates valueTerm)
  | _, .eitherMatch scrutinee leftBranch rightBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let leftParStep := RawStep.par.cd_dominates leftBranch
      let rightParStep := RawStep.par.cd_dominates rightBranch
      unfold RawTerm.cd
      unfold RawTerm.cdEitherMatchCase
      split
      case _ valueTerm scrutineeEqn =>
          exact RawStep.par.iotaEitherMatchInlDeep rightBranch
            (scrutineeEqn ▸ scrutineeParStep) leftParStep
      case _ valueTerm scrutineeEqn =>
          exact RawStep.par.iotaEitherMatchInrDeep leftBranch
            (scrutineeEqn ▸ scrutineeParStep) rightParStep
      all_goals
        exact RawStep.par.eitherMatch scrutineeParStep leftParStep rightParStep
  | _, .refl rawWitness =>
      RawStep.par.reflCong (RawStep.par.cd_dominates rawWitness)
  | _, .idJ baseCase witness => by
      let baseParStep := RawStep.par.cd_dominates baseCase
      let witnessParStep := RawStep.par.cd_dominates witness
      unfold RawTerm.cd
      unfold RawTerm.cdIdJCase
      split
      case _ rawTerm witnessEqn =>
          exact RawStep.par.iotaIdJReflDeep
            (witnessEqn ▸ witnessParStep) baseParStep
      all_goals exact RawStep.par.idJ baseParStep witnessParStep
  | _, .modIntro innerTerm =>
      RawStep.par.modIntro (RawStep.par.cd_dominates innerTerm)
  | _, .modElim innerTerm =>
      RawStep.par.modElim (RawStep.par.cd_dominates innerTerm)
  | _, .subsume innerTerm =>
      RawStep.par.subsume (RawStep.par.cd_dominates innerTerm)
  -- D1.6: 27 new ctors are pure cong at raw level (no β/ι rules).
  -- We use term-mode (no `by`) so Lean elaborates by unifying the
  -- expected type against the cong rule directly, avoiding the
  -- 550-branch `simp only [RawTerm.cd]` whnf blowup.  Each ctor's
  -- `cd` arm is a single rfl-equation (no inner match), so the
  -- target type computes to the cong-rule's output shape via
  -- definitional reduction during unification.
  | _, .interval0 => RawStep.par.refl _
  | _, .interval1 => RawStep.par.refl _
  | _, .intervalOpp intervalTerm =>
      RawStep.par.intervalOppCong (RawStep.par.cd_dominates intervalTerm)
  | _, .intervalMeet leftInterval rightInterval =>
      RawStep.par.intervalMeetCong
        (RawStep.par.cd_dominates leftInterval)
        (RawStep.par.cd_dominates rightInterval)
  | _, .intervalJoin leftInterval rightInterval =>
      RawStep.par.intervalJoinCong
        (RawStep.par.cd_dominates leftInterval)
        (RawStep.par.cd_dominates rightInterval)
  | _, .pathLam body =>
      RawStep.par.pathLamCong (RawStep.par.cd_dominates body)
  | _, .pathApp pathTerm intervalArg =>
      RawStep.par.pathAppCong
        (RawStep.par.cd_dominates pathTerm)
        (RawStep.par.cd_dominates intervalArg)
  | _, .glueIntro baseValue partialValue =>
      RawStep.par.glueIntroCong
        (RawStep.par.cd_dominates baseValue)
        (RawStep.par.cd_dominates partialValue)
  | _, .glueElim gluedValue =>
      RawStep.par.glueElimCong (RawStep.par.cd_dominates gluedValue)
  | _, .transp pathTerm sourceTerm =>
      RawStep.par.transpCong
        (RawStep.par.cd_dominates pathTerm)
        (RawStep.par.cd_dominates sourceTerm)
  | _, .hcomp sidesTerm capTerm =>
      RawStep.par.hcompCong
        (RawStep.par.cd_dominates sidesTerm)
        (RawStep.par.cd_dominates capTerm)
  | _, .oeqRefl witnessTerm =>
      RawStep.par.oeqReflCong (RawStep.par.cd_dominates witnessTerm)
  | _, .oeqJ baseCase witness =>
      RawStep.par.oeqJCong
        (RawStep.par.cd_dominates baseCase)
        (RawStep.par.cd_dominates witness)
  | _, .oeqFunext pointwiseEquality =>
      RawStep.par.oeqFunextCong (RawStep.par.cd_dominates pointwiseEquality)
  | _, .idStrictRefl witnessTerm =>
      RawStep.par.idStrictReflCong (RawStep.par.cd_dominates witnessTerm)
  | _, .idStrictRec baseCase witness =>
      RawStep.par.idStrictRecCong
        (RawStep.par.cd_dominates baseCase)
        (RawStep.par.cd_dominates witness)
  | _, .equivIntro forwardFn backwardFn =>
      RawStep.par.equivIntroCong
        (RawStep.par.cd_dominates forwardFn)
        (RawStep.par.cd_dominates backwardFn)
  | _, .equivApp equivTerm argument =>
      RawStep.par.equivAppCong
        (RawStep.par.cd_dominates equivTerm)
        (RawStep.par.cd_dominates argument)
  | _, .refineIntro rawValue predicateProof =>
      RawStep.par.refineIntroCong
        (RawStep.par.cd_dominates rawValue)
        (RawStep.par.cd_dominates predicateProof)
  | _, .refineElim refinedValue =>
      RawStep.par.refineElimCong (RawStep.par.cd_dominates refinedValue)
  | _, .recordIntro firstField =>
      RawStep.par.recordIntroCong (RawStep.par.cd_dominates firstField)
  | _, .recordProj recordValue =>
      RawStep.par.recordProjCong (RawStep.par.cd_dominates recordValue)
  | _, .codataUnfold initialState transition =>
      RawStep.par.codataUnfoldCong
        (RawStep.par.cd_dominates initialState)
        (RawStep.par.cd_dominates transition)
  | _, .codataDest codataValue =>
      RawStep.par.codataDestCong (RawStep.par.cd_dominates codataValue)
  | _, .sessionSend channel payload =>
      RawStep.par.sessionSendCong
        (RawStep.par.cd_dominates channel)
        (RawStep.par.cd_dominates payload)
  | _, .sessionRecv channel =>
      RawStep.par.sessionRecvCong (RawStep.par.cd_dominates channel)
  | _, .effectPerform operationTag arguments =>
      RawStep.par.effectPerformCong
        (RawStep.par.cd_dominates operationTag)
        (RawStep.par.cd_dominates arguments)
  | _, .universeCode _ => RawStep.par.refl _
  -- CUMUL-2.1 per-shape type codes: pure cong (no β/ι rule).  Each
  -- arm uses the corresponding `*CodeCong` rule from `RawStep.par`
  -- (added in CUMUL-2.1's RawPar.lean extension) to recurse on all
  -- subterms.
  | _, .arrowCode domainCode codomainCode =>
      RawStep.par.arrowCodeCong
        (RawStep.par.cd_dominates domainCode)
        (RawStep.par.cd_dominates codomainCode)
  | _, .piTyCode domainCode codomainCode =>
      RawStep.par.piTyCodeCong
        (RawStep.par.cd_dominates domainCode)
        (RawStep.par.cd_dominates codomainCode)
  | _, .sigmaTyCode domainCode codomainCode =>
      RawStep.par.sigmaTyCodeCong
        (RawStep.par.cd_dominates domainCode)
        (RawStep.par.cd_dominates codomainCode)
  | _, .productCode firstCode secondCode =>
      RawStep.par.productCodeCong
        (RawStep.par.cd_dominates firstCode)
        (RawStep.par.cd_dominates secondCode)
  | _, .sumCode leftCode rightCode =>
      RawStep.par.sumCodeCong
        (RawStep.par.cd_dominates leftCode)
        (RawStep.par.cd_dominates rightCode)
  | _, .listCode elementCode =>
      RawStep.par.listCodeCong (RawStep.par.cd_dominates elementCode)
  | _, .optionCode elementCode =>
      RawStep.par.optionCodeCong (RawStep.par.cd_dominates elementCode)
  | _, .eitherCode leftCode rightCode =>
      RawStep.par.eitherCodeCong
        (RawStep.par.cd_dominates leftCode)
        (RawStep.par.cd_dominates rightCode)
  | _, .idCode typeCode leftRaw rightRaw =>
      RawStep.par.idCodeCong
        (RawStep.par.cd_dominates typeCode)
        (RawStep.par.cd_dominates leftRaw)
        (RawStep.par.cd_dominates rightRaw)
  | _, .equivCode leftTypeCode rightTypeCode =>
      RawStep.par.equivCodeCong
        (RawStep.par.cd_dominates leftTypeCode)
        (RawStep.par.cd_dominates rightTypeCode)
  -- CUMUL-2.6: cumulUpMarker — pure cong, recurse on inner.
  | _, .cumulUpMarker innerCodeRaw =>
      RawStep.par.cumulUpMarkerCong
        (RawStep.par.cd_dominates innerCodeRaw)

end LeanFX2
