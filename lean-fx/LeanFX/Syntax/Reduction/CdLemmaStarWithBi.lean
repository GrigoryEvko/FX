import LeanFX.Syntax.Reduction.CdLemmaStar
import LeanFX.Syntax.Reduction.CdDominatesIsBi

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.cd_lemma_star_with_bi` — paired complete-development lemma.

The paired version of the typed complete-development lemma:

  `stepBi : Step.par.isBi parStep` (where `parStep : Step.par a b`)
  ⟹  `Step.parStarWithBi b (Term.cd a)`

Projects to plain `Step.par.cd_lemma_star` via `.toParStar` and to
chain isBi via `.toIsBi`.  Both projections are needed by the diamond
property argument downstream.

Proof: induction on `stepBi` (54 βι cases), mirroring the case
helpers in `CdLemmaStar.lean`.  Each `Step.parStar` operation in the
plain version is replaced by its `Step.parStarWithBi` counterpart.
Deep-ι cases use the paired source inversions
(`Step.parStarWithBi.<C>_source_inv` for each constructor C). -/

/-- Transport a `Step.parStarWithBi` chain across a Ty equality on
both endpoints.  Used by β-cases where source and target carry
matching Ty.weaken_subst_singleton casts. -/
private theorem Step.parStarWithBi.castBoth_chain
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {beforeTerm afterTerm : Term ctx sourceType}
    (chain : Step.parStarWithBi beforeTerm afterTerm) :
    Step.parStarWithBi (typeEquality ▸ beforeTerm)
                        (typeEquality ▸ afterTerm) := by
  cases typeEquality
  exact chain

/-- **The paired typed complete-development lemma.**  Every
isBi-witnessed parallel step lands in the complete development via
a βι-only chain. -/
theorem Step.par.cd_lemma_star_with_bi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    Step.parStarWithBi targetTerm (Term.cd sourceTerm) := by
  induction stepBi with
  | refl term =>
      exact (Step.par.cd_dominates_with_isBi term).toIsBi.toParStarWithBi
  | lam _bodyBi bodyIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.lam_cong bodyIH
  | lamPi _bodyBi bodyIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.lamPi_cong bodyIH
  | pair _firstBi _secondBi firstIH secondIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.pair_cong firstIH secondIH
  | natSucc _predBi predIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.natSucc_cong predIH
  | listCons _headBi _tailBi headIH tailIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.listCons_cong headIH tailIH
  | optionSome _valueBi valueIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.optionSome_cong valueIH
  | eitherInl _valueBi valueIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.eitherInl_cong valueIH
  | eitherInr _valueBi valueIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.eitherInr_cong valueIH
  -- Eliminator-cong cases: cd may contract a redex on one branch.
  | app _functionBi _argumentBi functionIH argumentIH =>
      simp only [Term.cd]
      split
      case _ developedBody developedFunctionEq =>
          have functionIHcast :
              Step.parStarWithBi _ (Term.lam developedBody) :=
            developedFunctionEq ▸ functionIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.app_cong functionIHcast argumentIH)
            (Step.par.isBi.betaApp (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.app_cong functionIH argumentIH
  | appPi _functionBi _argumentBi functionIH argumentIH =>
      simp only [Term.cd]
      split
      case _ developedBody developedFunctionEq =>
          have functionIHcast :
              Step.parStarWithBi _ (Term.lamPi developedBody) :=
            developedFunctionEq ▸ functionIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.appPi_cong functionIHcast argumentIH)
            (Step.par.isBi.betaAppPi (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.appPi_cong functionIH argumentIH
  | fst _pairBi pairIH =>
      simp only [Term.cd]
      split
      case _ developedFirst developedSecond developedPairEq =>
          have pairIHcast :
              Step.parStarWithBi _ (Term.pair developedFirst developedSecond) :=
            developedPairEq ▸ pairIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.fst_cong pairIHcast)
            (Step.par.isBi.betaFstPair (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.fst_cong pairIH
  | snd _pairBi pairIH =>
      simp only [Term.cd]
      split
      case _ developedFirst developedSecond developedPairEq =>
          have pairIHcast :
              Step.parStarWithBi _ (Term.pair developedFirst developedSecond) :=
            developedPairEq ▸ pairIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.snd_cong pairIHcast)
            (Step.par.isBi.betaSndPair (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.snd_cong pairIH
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      simp only [Term.cd]
      split
      case _ developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ Term.boolTrue :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.boolElim_cong scrutIHcast thenIH elseIH)
            (Step.par.isBi.iotaBoolElimTrue _ (Step.par.isBi.refl _))
      case _ developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ Term.boolFalse :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.boolElim_cong scrutIHcast thenIH elseIH)
            (Step.par.isBi.iotaBoolElimFalse _ (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.boolElim_cong scrutIH thenIH elseIH
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      simp only [Term.cd]
      split
      case _ developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ Term.natZero :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.natElim_cong scrutIHcast zeroIH succIH)
            (Step.par.isBi.iotaNatElimZero _ (Step.par.isBi.refl _))
      case _ developedPredecessor developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ (Term.natSucc developedPredecessor) :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.natElim_cong scrutIHcast zeroIH succIH)
            (Step.par.isBi.iotaNatElimSucc _ (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.natElim_cong scrutIH zeroIH succIH
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      simp only [Term.cd]
      split
      case _ developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ Term.natZero :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.natRec_cong scrutIHcast zeroIH succIH)
            (Step.par.isBi.iotaNatRecZero _ (Step.par.isBi.refl _))
      case _ developedPredecessor developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ (Term.natSucc developedPredecessor) :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.natRec_cong scrutIHcast zeroIH succIH)
            (Step.par.isBi.iotaNatRecSucc (Step.par.isBi.refl _)
               (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.natRec_cong scrutIH zeroIH succIH
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      simp only [Term.cd]
      split
      case _ developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ Term.listNil :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.listElim_cong scrutIHcast nilIH consIH)
            (Step.par.isBi.iotaListElimNil _ (Step.par.isBi.refl _))
      case _ developedHead developedTail developedScrutEq =>
          have scrutIHcast :
              Step.parStarWithBi _ (Term.listCons developedHead developedTail) :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.listElim_cong scrutIHcast nilIH consIH)
            (Step.par.isBi.iotaListElimCons _
              (Step.par.isBi.refl _) (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.listElim_cong scrutIH nilIH consIH
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      simp only [Term.cd]
      split
      case _ developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ Term.optionNone :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.optionMatch_cong scrutIHcast noneIH someIH)
            (Step.par.isBi.iotaOptionMatchNone _ (Step.par.isBi.refl _))
      case _ developedValue developedScrutEq =>
          have scrutIHcast : Step.parStarWithBi _ (Term.optionSome developedValue) :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.optionMatch_cong scrutIHcast noneIH someIH)
            (Step.par.isBi.iotaOptionMatchSome _ (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.optionMatch_cong scrutIH noneIH someIH
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      simp only [Term.cd]
      split
      case _ developedValue developedScrutEq =>
          have scrutIHcast :
              Step.parStarWithBi _ (Term.eitherInl developedValue) :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.eitherMatch_cong scrutIHcast leftIH rightIH)
            (Step.par.isBi.iotaEitherMatchInl _ (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ developedValue developedScrutEq =>
          have scrutIHcast :
              Step.parStarWithBi _ (Term.eitherInr developedValue) :=
            developedScrutEq ▸ scrutIH
          exact Step.parStarWithBi.snoc
            (Step.parStarWithBi.eitherMatch_cong scrutIHcast leftIH rightIH)
            (Step.par.isBi.iotaEitherMatchInr _ (Step.par.isBi.refl _) (Step.par.isBi.refl _))
      case _ =>
          exact Step.parStarWithBi.eitherMatch_cong scrutIH leftIH rightIH
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      simp only [Term.cd, Term.cd_idJ_redex]
      split
      case _ endpointsEqual =>
          subst endpointsEqual
          simp only [Term.cd_idJ_redex_aligned]
          split
          next _ developedWitnessEq =>
              have witnessIHcast : Step.parStarWithBi _ (Term.refl _) :=
                developedWitnessEq ▸ witnessIH
              exact Step.parStarWithBi.snoc
                (Step.parStarWithBi.idJ_cong baseIH witnessIHcast)
                (Step.par.isBi.iotaIdJRefl (Step.par.isBi.refl _))
          next =>
              exact Step.parStarWithBi.idJ_cong baseIH witnessIH
      case _ =>
          exact Step.parStarWithBi.idJ_cong baseIH witnessIH
  -- Shallow β cases: source is a literal redex; cd contracts the same redex.
  | betaApp _bodyBi _argBi bodyIH argIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      simp only [Term.cd]
      exact Step.parStarWithBi.castBoth_chain
        (Ty.weaken_subst_singleton codomainType domainType)
        (Step.parStarWithBi.subst0_parStarWithBi bodyIH argIH)
  | betaAppPi _bodyBi _argBi bodyIH argIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.subst0_parStarWithBi bodyIH argIH
  | betaFstPair _firstBi firstIH =>
      simp only [Term.cd]
      exact firstIH
  | betaSndPair _secondBi secondIH =>
      simp only [Term.cd]
      exact secondIH
  -- Shallow ι cases.
  | iotaBoolElimTrue _elseBranch _thenBi thenIH =>
      simp only [Term.cd]
      exact thenIH
  | iotaBoolElimFalse _thenBranch _elseBi elseIH =>
      simp only [Term.cd]
      exact elseIH
  | iotaNatElimZero _succBranch _zeroBi zeroIH =>
      simp only [Term.cd]
      exact zeroIH
  | iotaNatElimSucc _zeroBranch _predBi _succBi predIH succIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.app_cong succIH predIH
  | iotaNatRecZero _succBranch _zeroBi zeroIH =>
      simp only [Term.cd]
      exact zeroIH
  | iotaNatRecSucc _predBi _zeroBi _succBi predIH zeroIH succIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.app_cong
        (Step.parStarWithBi.app_cong succIH predIH)
        (Step.parStarWithBi.natRec_cong predIH zeroIH succIH)
  | iotaListElimNil _consBranch _nilBi nilIH =>
      simp only [Term.cd]
      exact nilIH
  | iotaListElimCons _nilBranch _headBi _tailBi _consBi headIH tailIH consIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.app_cong
        (Step.parStarWithBi.app_cong consIH headIH)
        tailIH
  | iotaOptionMatchNone _someBranch _noneBi noneIH =>
      simp only [Term.cd]
      exact noneIH
  | iotaOptionMatchSome _noneBranch _valueBi _someBi valueIH someIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.app_cong someIH valueIH
  | iotaEitherMatchInl _rightBranch _valueBi _leftBi valueIH leftIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.app_cong leftIH valueIH
  | iotaEitherMatchInr _leftBranch _valueBi _rightBi valueIH rightIH =>
      simp only [Term.cd]
      exact Step.parStarWithBi.app_cong rightIH valueIH
  | iotaIdJRefl _baseBi baseIH =>
      -- Implicits (least-recent first per rename_i): scope, ctx,
      -- carrier, endpoint, resultType, baseCase, baseCase', baseStep.
      rename_i _ _ carrier endpoint _ baseCase _ _
      have cdEq :
          Term.cd (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                            (rightEnd := endpoint) baseCase
                            (Term.refl (carrier := carrier) endpoint))
            = Term.cd baseCase := by
        simp only [Term.cd]
        unfold Term.cd_idJ_redex
        rw [dif_pos rfl]
        rfl
      rw [cdEq]
      exact baseIH
  -- Deep β cases.
  | betaAppDeep _functionBi _argBi functionIH argIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      obtain ⟨body', cdEq, bodyWithBi⟩ :=
        Step.parStarWithBi.lam_target_inv functionIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.castBoth_chain
        (Ty.weaken_subst_singleton codomainType domainType)
        (Step.parStarWithBi.subst0_parStarWithBi bodyWithBi argIH)
  | betaAppPiDeep _functionBi _argBi functionIH argIH =>
      obtain ⟨body', cdEq, bodyWithBi⟩ :=
        Step.parStarWithBi.lamPi_target_inv functionIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.subst0_parStarWithBi bodyWithBi argIH
  | betaFstPairDeep _pairBi pairIH =>
      obtain ⟨firstVal', _secondVal', cdEq, firstWithBi, _secondWithBi⟩ :=
        Step.parStarWithBi.pair_target_inv pairIH
      simp only [Term.cd, cdEq]
      exact firstWithBi
  | betaSndPairDeep _pairBi pairIH =>
      obtain ⟨_firstVal', _secondVal', cdEq, _firstWithBi, secondWithBi⟩ :=
        Step.parStarWithBi.pair_target_inv pairIH
      simp only [Term.cd, cdEq]
      exact secondWithBi
  -- Deep ι cases (use paired source inversions).
  | iotaBoolElimTrueDeep _elseBranch _scrutBi _thenBi scrutIH thenIH =>
      have cdEq : Term.cd _ = Term.boolTrue :=
        Step.parStar.boolTrue_source_inv scrutIH.toParStar
      simp only [Term.cd, cdEq]
      exact thenIH
  | iotaBoolElimFalseDeep _thenBranch _scrutBi _elseBi scrutIH elseIH =>
      have cdEq : Term.cd _ = Term.boolFalse :=
        Step.parStar.boolFalse_source_inv scrutIH.toParStar
      simp only [Term.cd, cdEq]
      exact elseIH
  | iotaNatElimZeroDeep _succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      have cdEq : Term.cd _ = Term.natZero :=
        Step.parStar.natZero_source_inv scrutIH.toParStar
      simp only [Term.cd, cdEq]
      exact zeroIH
  | iotaNatElimSuccDeep _zeroBranch _scrutBi _succBi scrutIH succIH =>
      obtain ⟨pred', cdEq, predWithBi⟩ :=
        Step.parStarWithBi.natSucc_source_inv scrutIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.app_cong succIH predWithBi
  | iotaNatRecZeroDeep _succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      have cdEq : Term.cd _ = Term.natZero :=
        Step.parStar.natZero_source_inv scrutIH.toParStar
      simp only [Term.cd, cdEq]
      exact zeroIH
  | iotaNatRecSuccDeep _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      obtain ⟨pred', cdEq, predWithBi⟩ :=
        Step.parStarWithBi.natSucc_source_inv scrutIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.app_cong
        (Step.parStarWithBi.app_cong succIH predWithBi)
        (Step.parStarWithBi.natRec_cong predWithBi zeroIH succIH)
  | iotaListElimNilDeep _consBranch _scrutBi _nilBi scrutIH nilIH =>
      have cdEq : Term.cd _ = Term.listNil :=
        Step.parStar.listNil_source_inv scrutIH.toParStar
      simp only [Term.cd, cdEq]
      exact nilIH
  | iotaListElimConsDeep _nilBranch _scrutBi _consBi scrutIH consIH =>
      obtain ⟨head', tail', cdEq, headWithBi, tailWithBi⟩ :=
        Step.parStarWithBi.listCons_source_inv scrutIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.app_cong
        (Step.parStarWithBi.app_cong consIH headWithBi)
        tailWithBi
  | iotaOptionMatchNoneDeep _someBranch _scrutBi _noneBi scrutIH noneIH =>
      have cdEq : Term.cd _ = Term.optionNone :=
        Step.parStar.optionNone_source_inv scrutIH.toParStar
      simp only [Term.cd, cdEq]
      exact noneIH
  | iotaOptionMatchSomeDeep _noneBranch _scrutBi _someBi scrutIH someIH =>
      obtain ⟨value', cdEq, valueWithBi⟩ :=
        Step.parStarWithBi.optionSome_source_inv scrutIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.app_cong someIH valueWithBi
  | iotaEitherMatchInlDeep _rightBranch _scrutBi _leftBi scrutIH leftIH =>
      obtain ⟨value', cdEq, valueWithBi⟩ :=
        Step.parStarWithBi.eitherInl_source_inv scrutIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.app_cong leftIH valueWithBi
  | iotaEitherMatchInrDeep _leftBranch _scrutBi _rightBi scrutIH rightIH =>
      obtain ⟨value', cdEq, valueWithBi⟩ :=
        Step.parStarWithBi.eitherInr_source_inv scrutIH
      simp only [Term.cd, cdEq]
      exact Step.parStarWithBi.app_cong rightIH valueWithBi
  | iotaIdJReflDeep _witnessBi _baseBi witnessIH baseIH =>
      -- Implicits: scope, ctx, carrier, endpoint, resultType, baseCase,
      -- baseCase', witness, witnessStep, baseStep.
      rename_i _ _ carrier endpoint _ baseCase _ witness _ _
      have cdEq : Term.cd witness = Term.refl endpoint :=
        Step.parStar.refl_source_inv witnessIH.toParStar
      have cdIdJEq :
          Term.cd (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                            (rightEnd := endpoint) baseCase witness)
            = Term.cd baseCase := by
        simp only [Term.cd, cdEq]
        unfold Term.cd_idJ_redex
        rw [dif_pos rfl]
        rfl
      rw [cdIdJEq]
      exact baseIH

/-! ## Plain projections.

`cd_lemma_star_with_bi` packages both the chain itself and the
βι-witness on every link.  Two projections recover the
single-purpose corollaries the rest of the kernel consumes:

* `Step.par.cd_lemma_star` — every isBi-witnessed parallel step
  `parStep : Step.par a b` lands in `Term.cd a` via a plain
  `Step.parStar` chain.  This is the typed complete-development
  lemma that closes #883 and unblocks the diamond property
  (#884), Church-Rosser (#885), and Conv-canonical-form (#886).

* `Step.par.cd_lemma_star_isBi` — the chain produced by
  `cd_lemma_star` is itself βι-only (every link satisfies isBi).
  Needed by the diamond construction so the second leg of the
  square stays in the βι-restricted regime.

Both projections are one-liners: `cd_lemma_star_with_bi` already
did all the work; we just discard part of the structure. -/

/-- **Typed complete-development lemma.** Every isBi-witnessed
parallel step lands in `Term.cd` via a `Step.parStar` chain. -/
theorem Step.par.cd_lemma_star
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    Step.parStar targetTerm (Term.cd sourceTerm) :=
  (Step.par.cd_lemma_star_with_bi stepBi).toParStar

/-- The chain produced by `cd_lemma_star` is itself βι-only.
Every link satisfies `Step.par.isBi`, so the result chain is in
the same βι-restricted regime that drives confluence. -/
theorem Step.par.cd_lemma_star_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    Step.parStar.isBi (Step.par.cd_lemma_star stepBi) :=
  (Step.par.cd_lemma_star_with_bi stepBi).toIsBi

end LeanFX.Syntax
