import LeanFX2.Confluence.RawCd
import LeanFX2.Reduction.RawPar

/-! # Confluence/RawCdDominates — every raw term parallel-reduces to its cd

`RawStep.par.cd_dominates : ∀ t, RawStep.par t (RawTerm.cd t)`.

Proof shape: structural induction on the raw term.  For each ctor:
* Atomic (var/unit/booleans/zero/Nil/None) — `RawStep.par.refl _`.
* Pure cong (lam/pair/listCons/optionSome/eitherInl/Inr/natSucc/refl
  /modIntro/modElim/subsume) — apply the cong rule with IH.
* Redex-bearing (app/pathApp/glueElim/refineElim/recordProj/fst/snd
  /boolElim/natElim/natRec/listElim/optionMatch/eitherMatch/idJ) —
  `simp only [RawTerm.cd]; split` produces one goal per ctor of the
  inner match's scrutinee; the redex case fires the appropriate Deep
  β/ι rule using the IH; `all_goals` discharges the cong-shape
  fallthrough.

Pairs with `cd_lemma` (every parallel reduct lands in cd t) to give
the Tait–Martin-Löf complete-development pair from which raw
diamond and confluence follow.

## Modal cases

`modIntro` and `subsume` are pure cong.  `modElim` is now
redex-bearing: when its developed payload is `modIntro value`, cd
contracts by the modal β rule; otherwise it rebuilds by congruence.
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
  | _, .modElim innerTerm => by
      let innerParStep := RawStep.par.cd_dominates innerTerm
      unfold RawTerm.cd
      unfold RawTerm.cdModElimCase
      split
      case _ payloadTarget innerEqn =>
          exact RawStep.par.betaModElimIntroDeep
            (innerEqn ▸ innerParStep)
      all_goals exact RawStep.par.modElim innerParStep
  | _, .subsume innerTerm =>
      RawStep.par.subsume (RawStep.par.cd_dominates innerTerm)
  -- D1.6/D2.5/D2.7: most new ctors are pure cong at raw level;
  -- pathApp, glueElim, refineElim, recordProj, and codataDest now have β
  -- redexes below.
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
  | _, .pathApp pathTerm intervalArg => by
      let pathParStep := RawStep.par.cd_dominates pathTerm
      let intervalParStep := RawStep.par.cd_dominates intervalArg
      unfold RawTerm.cd
      unfold RawTerm.cdPathAppCase
      split
      case _ bodyRawTarget pathEqn =>
          exact RawStep.par.betaPathAppDeep
            (pathEqn ▸ pathParStep) intervalParStep
      all_goals exact RawStep.par.pathAppCong pathParStep intervalParStep
  | _, .glueIntro baseValue partialValue =>
      RawStep.par.glueIntroCong
        (RawStep.par.cd_dominates baseValue)
        (RawStep.par.cd_dominates partialValue)
  | _, .glueElim gluedValue => by
      let gluedParStep := RawStep.par.cd_dominates gluedValue
      unfold RawTerm.cd
      unfold RawTerm.cdGlueElimCase
      split
      case _ baseRawTarget partialRawTarget gluedEqn =>
          exact RawStep.par.betaGlueElimIntroDeep
            (gluedEqn ▸ gluedParStep)
      all_goals exact RawStep.par.glueElimCong gluedParStep
  | _, .transp pathTerm sourceTerm => by
      let pathParStep := RawStep.par.cd_dominates pathTerm
      let sourceParStep := RawStep.par.cd_dominates sourceTerm
      unfold RawTerm.cd
      unfold RawTerm.cdTranspCase
      split
      case _ pathBody pathBodyEqn =>
          -- cd pathTerm = pathLam pathBody.  Rewrite pathParStep via cd-eqn.
          rw [pathBodyEqn] at pathParStep
          split
          case _ innerType unwknEqn =>
              -- unweaken? pathBody = some innerType, so pathBody = innerType.weaken.
              have hPath : pathBody = innerType.weaken :=
                RawTerm.unweaken?_imp_weaken pathBody innerType unwknEqn
              rw [hPath] at pathParStep
              exact RawStep.par.transpReflBetaDeep pathParStep sourceParStep
          case _ _unwknEqn =>
              exact RawStep.par.transpCong pathParStep sourceParStep
      -- D3.6-S1 cd activation: when cd pathTerm = uaToEquiv proofRaw,
      -- fire the deep univalence-β rule.  D3.6-S3 cd activation: when
      -- cd pathTerm = pathCompose left right, fire the deep
      -- compose-β rule.  Each leftover `split` arm defaults to
      -- `transpCong`; the uaToEquiv arm overrides with `uaBetaDeep`,
      -- and the pathCompose arm overrides with `transpComposeDeep`.
      -- Use `first` over each leftover goal: try the uaToEquiv-specific
      -- tactic, otherwise the pathCompose-specific tactic, otherwise
      -- close via transpCong.
      all_goals first
        | (rename_i proofRaw cdPathEqn
           rw [cdPathEqn] at pathParStep
           exact RawStep.par.uaBetaDeep pathParStep sourceParStep)
        | (rename_i leftPathRaw rightPathRaw cdPathEqn
           rw [cdPathEqn] at pathParStep
           exact RawStep.par.transpComposeDeep pathParStep sourceParStep)
        | exact RawStep.par.transpCong pathParStep sourceParStep
  | _, .transpFill pathTerm intervalTerm sourceTerm =>
      RawStep.par.transpFillCong
        (RawStep.par.cd_dominates pathTerm)
        (RawStep.par.cd_dominates intervalTerm)
        (RawStep.par.cd_dominates sourceTerm)
  | _, .hcomp sidesTerm capTerm => by
      -- D2.5.2: dispatch on cd-developed sides via cdHcompCase.  When
      -- the developed sides is `pathLam X.weaken`, fire `hcompBetaDeep`
      -- so the LHS hcomp parallel-reduces to the cap.  Otherwise fall
      -- through to `hcompCong`.  Mirror of the transp arm above.
      let sidesParStep := RawStep.par.cd_dominates sidesTerm
      let capParStep := RawStep.par.cd_dominates capTerm
      unfold RawTerm.cd
      unfold RawTerm.cdHcompCase
      split
      case _ sidesBody sidesBodyEqn =>
          rw [sidesBodyEqn] at sidesParStep
          split
          case _ innerCap unwknEqn =>
              have hSides : sidesBody = innerCap.weaken :=
                RawTerm.unweaken?_imp_weaken sidesBody innerCap unwknEqn
              rw [hSides] at sidesParStep
              exact RawStep.par.hcompBetaDeep sidesParStep capParStep
          case _ _unwknEqn =>
              exact RawStep.par.hcompCong sidesParStep capParStep
      all_goals exact RawStep.par.hcompCong sidesParStep capParStep
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
  | _, .idStrictRec baseCase witness => by
      let baseParStep := RawStep.par.cd_dominates baseCase
      let witnessParStep := RawStep.par.cd_dominates witness
      unfold RawTerm.cd
      unfold RawTerm.cdIdStrictRecCase
      split
      case _ rawTerm witnessEqn =>
          exact RawStep.par.iotaIdStrictRecReflDeep
            (witnessEqn ▸ witnessParStep) baseParStep
      all_goals exact RawStep.par.idStrictRecCong baseParStep witnessParStep
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
  | _, .refineElim refinedValue => by
      let refinedParStep := RawStep.par.cd_dominates refinedValue
      unfold RawTerm.cd
      unfold RawTerm.cdRefineElimCase
      split
      case _ valueRawTarget proofRawTarget refinedEqn =>
          exact RawStep.par.betaRefineElimIntroDeep
            (refinedEqn ▸ refinedParStep)
      all_goals exact RawStep.par.refineElimCong refinedParStep
  | _, .recordIntro firstField =>
      RawStep.par.recordIntroCong (RawStep.par.cd_dominates firstField)
  | _, .recordProj recordValue => by
      let recordParStep := RawStep.par.cd_dominates recordValue
      unfold RawTerm.cd
      unfold RawTerm.cdRecordProjCase
      split
      case _ firstRawTarget recordEqn =>
          exact RawStep.par.betaRecordProjIntroDeep
            (recordEqn ▸ recordParStep)
      all_goals exact RawStep.par.recordProjCong recordParStep
  | _, .codataUnfold initialState transition =>
      RawStep.par.codataUnfoldCong
        (RawStep.par.cd_dominates initialState)
        (RawStep.par.cd_dominates transition)
  | _, .codataDest codataValue => by
      let codataParStep := RawStep.par.cd_dominates codataValue
      unfold RawTerm.cd
      unfold RawTerm.cdCodataDestCase
      split
      case _ stateTarget transitionTarget codataEqn =>
          exact RawStep.par.betaCodataDestUnfoldDeep
            (codataEqn ▸ codataParStep)
      all_goals exact RawStep.par.codataDestCong codataParStep
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
  -- D3.6-P1: uaToEquiv — pure cong, recurse on inner proof raw.
  | _, .uaToEquiv proofRaw =>
      RawStep.par.uaToEquivCong
        (RawStep.par.cd_dominates proofRaw)
  -- D3.6-P2/S6: equivApply — when cd equivRaw = uaToEquiv (oeqRefl _),
  -- fire the deep round-trip-β rule (uaReflEquivApplyDeep).  Otherwise
  -- default cong.  Dispatch by pattern-matching on `cd equivRaw` first;
  -- the inner `uaToEquiv` arm then matches the proof against `oeqRefl`
  -- so cdEquivApplyCase / cdUaToEquivApplyCase see the expected ctor
  -- shape.
  | _, .equivApply equivRaw argRaw => by
      let equivParStep := RawStep.par.cd_dominates equivRaw
      let argParStep := RawStep.par.cd_dominates argRaw
      unfold RawTerm.cd
      match hCdEquiv : RawTerm.cd equivRaw with
      | .uaToEquiv innerProof =>
          rw [hCdEquiv] at equivParStep
          show RawStep.par (RawTerm.equivApply equivRaw argRaw)
                           (RawTerm.cdEquivApplyCase
                             (RawTerm.uaToEquiv innerProof)
                             (RawTerm.cd argRaw))
          unfold RawTerm.cdEquivApplyCase
          match innerProof with
          | .oeqRefl witnessRaw =>
              show RawStep.par (RawTerm.equivApply equivRaw argRaw)
                               (RawTerm.cdUaToEquivApplyCase
                                 (RawTerm.oeqRefl witnessRaw)
                                 (RawTerm.cd argRaw))
              unfold RawTerm.cdUaToEquivApplyCase
              exact RawStep.par.uaReflEquivApplyDeep equivParStep argParStep
          | .var _ | .unit | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
          | .boolTrue | .boolFalse | .boolElim _ _ _ | .natZero | .natSucc _
          | .natElim _ _ _ | .natRec _ _ _ | .listNil | .listCons _ _
          | .listElim _ _ _ | .optionNone | .optionSome _ | .optionMatch _ _ _
          | .eitherInl _ | .eitherInr _ | .eitherMatch _ _ _ | .refl _
          | .idJ _ _ | .modIntro _ | .modElim _ | .subsume _
          | .interval0 | .interval1 | .intervalOpp _ | .intervalMeet _ _
          | .intervalJoin _ _ | .pathLam _ | .pathApp _ _ | .glueIntro _ _
          | .glueElim _ | .transp _ _ | .transpFill _ _ _
          | .hcomp _ _ | .oeqJ _ _ | .oeqFunext _
          | .idStrictRefl _ | .idStrictRec _ _ | .equivIntro _ _ | .equivApp _ _
          | .refineIntro _ _ | .refineElim _ | .recordIntro _ | .recordProj _
          | .codataUnfold _ _ | .codataDest _ | .sessionSend _ _ | .sessionRecv _
          | .effectPerform _ _ | .universeCode _ | .arrowCode _ _ | .piTyCode _ _
          | .sigmaTyCode _ _ | .productCode _ _ | .sumCode _ _ | .listCode _
          | .optionCode _ | .eitherCode _ _ | .idCode _ _ _ | .equivCode _ _
          | .cumulUpMarker _ | .uaToEquiv _ | .equivApply _ _ | .pathCompose _ _
          | .idToEquiv _ | .oeqTrans _ _ | .equivCompose _ _ =>
              show RawStep.par (RawTerm.equivApply equivRaw argRaw)
                               (RawTerm.cdUaToEquivApplyCase _ (RawTerm.cd argRaw))
              unfold RawTerm.cdUaToEquivApplyCase
              exact RawStep.par.equivApplyCong equivParStep argParStep
      | .var _ | .unit | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
      | .boolTrue | .boolFalse | .boolElim _ _ _ | .natZero | .natSucc _
      | .natElim _ _ _ | .natRec _ _ _ | .listNil | .listCons _ _
      | .listElim _ _ _ | .optionNone | .optionSome _ | .optionMatch _ _ _
      | .eitherInl _ | .eitherInr _ | .eitherMatch _ _ _ | .refl _
      | .idJ _ _ | .modIntro _ | .modElim _ | .subsume _
      | .interval0 | .interval1 | .intervalOpp _ | .intervalMeet _ _
      | .intervalJoin _ _ | .pathLam _ | .pathApp _ _ | .glueIntro _ _
      | .glueElim _ | .transp _ _ | .transpFill _ _ _
      | .hcomp _ _ | .oeqRefl _ | .oeqJ _ _
      | .oeqFunext _ | .idStrictRefl _ | .idStrictRec _ _ | .equivIntro _ _
      | .equivApp _ _ | .refineIntro _ _ | .refineElim _ | .recordIntro _
      | .recordProj _ | .codataUnfold _ _ | .codataDest _ | .sessionSend _ _
      | .sessionRecv _ | .effectPerform _ _ | .universeCode _ | .arrowCode _ _
      | .piTyCode _ _ | .sigmaTyCode _ _ | .productCode _ _ | .sumCode _ _
      | .listCode _ | .optionCode _ | .eitherCode _ _ | .idCode _ _ _
      | .equivCode _ _ | .cumulUpMarker _ | .equivApply _ _ | .pathCompose _ _
      | .idToEquiv _ | .oeqTrans _ _ | .equivCompose _ _ =>
          rw [hCdEquiv] at equivParStep
          show RawStep.par (RawTerm.equivApply equivRaw argRaw)
                           (RawTerm.cdEquivApplyCase _ (RawTerm.cd argRaw))
          unfold RawTerm.cdEquivApplyCase
          exact RawStep.par.equivApplyCong equivParStep argParStep
  -- D3.6-S3: pathCompose — pure cong, recurse on left and right path raws.
  -- The actual β rule fires through `cdTranspCase` when pathCompose is
  -- the developed path of a transp.
  | _, .pathCompose leftPathRaw rightPathRaw =>
      RawStep.par.pathComposeCong
        (RawStep.par.cd_dominates leftPathRaw)
        (RawStep.par.cd_dominates rightPathRaw)
  -- D3.6-S4: idToEquiv — when cd proofRaw = refl witness, fire the
  -- deep identity-β rule (idToEquivReflDeep).  D3.6-S5: when cd
  -- proofRaw = oeqTrans first second, fire the deep compose-β rule
  -- (idToEquivComposeDeep).  Otherwise default cong.  We dispatch by
  -- pattern-matching on `cd proofRaw` before unfolding cdIdToEquivCase
  -- so the β arms see exactly the expected ctor shape.
  | _, .idToEquiv proofRaw => by
      let proofParStep := RawStep.par.cd_dominates proofRaw
      unfold RawTerm.cd
      match hCd : RawTerm.cd proofRaw with
      | .refl witnessRaw =>
          rw [hCd] at proofParStep
          show RawStep.par (RawTerm.idToEquiv proofRaw)
                           (RawTerm.cdIdToEquivCase (RawTerm.refl witnessRaw))
          unfold RawTerm.cdIdToEquivCase
          exact RawStep.par.idToEquivReflDeep proofParStep
      | .oeqTrans firstRaw secondRaw =>
          rw [hCd] at proofParStep
          show RawStep.par (RawTerm.idToEquiv proofRaw)
                           (RawTerm.cdIdToEquivCase
                             (RawTerm.oeqTrans firstRaw secondRaw))
          unfold RawTerm.cdIdToEquivCase
          exact RawStep.par.idToEquivComposeDeep proofParStep
      | .var _ | .unit | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
      | .boolTrue | .boolFalse | .boolElim _ _ _ | .natZero | .natSucc _
      | .natElim _ _ _ | .natRec _ _ _ | .listNil | .listCons _ _
      | .listElim _ _ _ | .optionNone | .optionSome _ | .optionMatch _ _ _
      | .eitherInl _ | .eitherInr _ | .eitherMatch _ _ _ | .idJ _ _
      | .modIntro _ | .modElim _ | .subsume _ | .interval0 | .interval1
      | .intervalOpp _ | .intervalMeet _ _ | .intervalJoin _ _
      | .pathLam _ | .pathApp _ _ | .glueIntro _ _ | .glueElim _
      | .transp _ _ | .transpFill _ _ _
      | .hcomp _ _ | .oeqRefl _ | .oeqJ _ _ | .oeqFunext _
      | .idStrictRefl _ | .idStrictRec _ _ | .equivIntro _ _ | .equivApp _ _
      | .refineIntro _ _ | .refineElim _ | .recordIntro _ | .recordProj _
      | .codataUnfold _ _ | .codataDest _ | .sessionSend _ _ | .sessionRecv _
      | .effectPerform _ _ | .universeCode _ | .arrowCode _ _ | .piTyCode _ _
      | .sigmaTyCode _ _ | .productCode _ _ | .sumCode _ _ | .listCode _
      | .optionCode _ | .eitherCode _ _ | .idCode _ _ _ | .equivCode _ _
      | .cumulUpMarker _ | .uaToEquiv _ | .equivApply _ _ | .pathCompose _ _
      | .idToEquiv _ | .equivCompose _ _ =>
          rw [hCd] at proofParStep
          show RawStep.par (RawTerm.idToEquiv proofRaw)
                           (RawTerm.cdIdToEquivCase _)
          unfold RawTerm.cdIdToEquivCase
          exact RawStep.par.idToEquivCong proofParStep
  -- D3.6-S5: oeqTrans — pure cong, recurse on first and second proof
  -- raws.  The actual β rule fires through `cdIdToEquivCase` when
  -- oeqTrans is the developed proof of an idToEquiv.
  | _, .oeqTrans firstProof secondProof =>
      RawStep.par.oeqTransCong
        (RawStep.par.cd_dominates firstProof)
        (RawStep.par.cd_dominates secondProof)
  -- D3.6-S5: equivCompose — pure cong, recurse on first and second
  -- equivalence raws.  This ctor is the contractum target of the
  -- compose-β rule; no β fires when it is the source itself.
  | _, .equivCompose firstEquiv secondEquiv =>
      RawStep.par.equivComposeCong
        (RawStep.par.cd_dominates firstEquiv)
        (RawStep.par.cd_dominates secondEquiv)

end LeanFX2
