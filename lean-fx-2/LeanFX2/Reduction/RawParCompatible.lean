import LeanFX2.Reduction.RawParRename

/-! # Reduction/RawParCompatible — RawStep.par closed under substitution

The substitution-compatibility chain for raw parallel reduction:

* `RawTerm.subst0_subst_commute` — combinator equation for β reduct
* `RawTermSubst.par_lift` — lifted subst respects pointwise par
* `RawTerm.subst_par_pointwise` — same term, parallel substs → parallel
* `RawStep.par.subst_par` — joint: parallel terms + parallel substs → parallel
* `RawStep.par.subst0_par` — singleton corollary (β workhorse)

The headline `subst0_par` is exactly what `RawStep.par.cd_lemma`'s
`betaApp` case needs to discharge.  Mirrors lean-fx's
`RawParCompatible.lean`, extended for lean-fx-2's 3 modal cong rules.

## Zero-axiom

All proofs use `induction` on Prop-valued single-Nat-indexed
inductives.  Per `feedback_lean_match_arity_axioms.md`, no propext
leak.  β cases use `RawTerm.subst0_subst_commute` to reshape
`(body.subst0 arg).subst σ` into `(body.subst σ.lift).subst0 (arg.subst σ)`
so the β rule applies.
-/

namespace LeanFX2

/-! ## Combinator equation: subst commutes with subst0. -/

/-- `(body.subst0 arg).subst σ = (body.subst σ.lift).subst0 (arg.subst σ)`.
The β-redex contractum reshape lemma needed in subst_par's β cases. -/
theorem RawTerm.subst0_subst_commute {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 1)) (rawArg : RawTerm sourceScope)
    (sigma : RawTermSubst sourceScope targetScope) :
    (body.subst0 rawArg).subst sigma =
      (body.subst sigma.lift).subst0 (rawArg.subst sigma) := by
  unfold RawTerm.subst0
  rw [RawTerm.subst_compose (RawTermSubst.singleton rawArg) sigma body]
  rw [RawTerm.subst_compose sigma.lift
        (RawTermSubst.singleton (rawArg.subst sigma)) body]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨k + 1, isLt⟩ =>
      dsimp only [RawTermSubst.compose, RawTermSubst.singleton,
                  RawTermSubst.lift, RawTerm.subst]
      exact (RawTerm.weaken_subst_singleton _ _).symm

/-! ## Parallel-substitution lift. -/

/-- Lifting a substitution preserves the pointwise par relation. -/
theorem RawTermSubst.par_lift {sourceScope targetScope : Nat}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position)) :
    ∀ position,
      RawStep.par (firstSubst.lift position)
                  (secondSubst.lift position) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact RawStep.par.refl _
  | ⟨_ + 1, _⟩ =>
      simp only [RawTermSubst.lift]
      exact RawStep.par.rename RawRenaming.weaken (substsRelated _)

/-! ## Pointwise: same term, parallel substitutions. -/

/-- Substituting a fixed term through pointwise-par-related
substitutions produces parallel-related terms.  Structural recursion
on the term; each ctor descends into subterms.  -/
theorem RawTerm.subst_par_pointwise {sourceScope targetScope : Nat} :
    ∀ (rawTerm : RawTerm sourceScope)
      {firstSubst secondSubst : RawTermSubst sourceScope targetScope},
      (∀ position,
        RawStep.par (firstSubst position) (secondSubst position)) →
      RawStep.par (rawTerm.subst firstSubst)
                  (rawTerm.subst secondSubst)
  | .var _, _, _, substsRelated => substsRelated _
  | .unit, _, _, _ => RawStep.par.refl _
  | .boolTrue, _, _, _ => RawStep.par.refl _
  | .boolFalse, _, _, _ => RawStep.par.refl _
  | .natZero, _, _, _ => RawStep.par.refl _
  | .listNil, _, _, _ => RawStep.par.refl _
  | .optionNone, _, _, _ => RawStep.par.refl _
  | .lam body, _, _, substsRelated =>
      RawStep.par.lam
        (RawTerm.subst_par_pointwise body
          (RawTermSubst.par_lift substsRelated))
  | .app functionTerm argumentTerm, _, _, substsRelated =>
      RawStep.par.app
        (RawTerm.subst_par_pointwise functionTerm substsRelated)
        (RawTerm.subst_par_pointwise argumentTerm substsRelated)
  | .pair firstValue secondValue, _, _, substsRelated =>
      RawStep.par.pair
        (RawTerm.subst_par_pointwise firstValue substsRelated)
        (RawTerm.subst_par_pointwise secondValue substsRelated)
  | .fst pairTerm, _, _, substsRelated =>
      RawStep.par.fst
        (RawTerm.subst_par_pointwise pairTerm substsRelated)
  | .snd pairTerm, _, _, substsRelated =>
      RawStep.par.snd
        (RawTerm.subst_par_pointwise pairTerm substsRelated)
  | .boolElim scrutinee thenBranch elseBranch, _, _, substsRelated =>
      RawStep.par.boolElim
        (RawTerm.subst_par_pointwise scrutinee substsRelated)
        (RawTerm.subst_par_pointwise thenBranch substsRelated)
        (RawTerm.subst_par_pointwise elseBranch substsRelated)
  | .natSucc predecessor, _, _, substsRelated =>
      RawStep.par.natSucc
        (RawTerm.subst_par_pointwise predecessor substsRelated)
  | .natElim scrutinee zeroBranch succBranch, _, _, substsRelated =>
      RawStep.par.natElim
        (RawTerm.subst_par_pointwise scrutinee substsRelated)
        (RawTerm.subst_par_pointwise zeroBranch substsRelated)
        (RawTerm.subst_par_pointwise succBranch substsRelated)
  | .natRec scrutinee zeroBranch succBranch, _, _, substsRelated =>
      RawStep.par.natRec
        (RawTerm.subst_par_pointwise scrutinee substsRelated)
        (RawTerm.subst_par_pointwise zeroBranch substsRelated)
        (RawTerm.subst_par_pointwise succBranch substsRelated)
  | .listCons headTerm tailTerm, _, _, substsRelated =>
      RawStep.par.listCons
        (RawTerm.subst_par_pointwise headTerm substsRelated)
        (RawTerm.subst_par_pointwise tailTerm substsRelated)
  | .listElim scrutinee nilBranch consBranch, _, _, substsRelated =>
      RawStep.par.listElim
        (RawTerm.subst_par_pointwise scrutinee substsRelated)
        (RawTerm.subst_par_pointwise nilBranch substsRelated)
        (RawTerm.subst_par_pointwise consBranch substsRelated)
  | .optionSome valueTerm, _, _, substsRelated =>
      RawStep.par.optionSome
        (RawTerm.subst_par_pointwise valueTerm substsRelated)
  | .optionMatch scrutinee noneBranch someBranch, _, _, substsRelated =>
      RawStep.par.optionMatch
        (RawTerm.subst_par_pointwise scrutinee substsRelated)
        (RawTerm.subst_par_pointwise noneBranch substsRelated)
        (RawTerm.subst_par_pointwise someBranch substsRelated)
  | .eitherInl valueTerm, _, _, substsRelated =>
      RawStep.par.eitherInl
        (RawTerm.subst_par_pointwise valueTerm substsRelated)
  | .eitherInr valueTerm, _, _, substsRelated =>
      RawStep.par.eitherInr
        (RawTerm.subst_par_pointwise valueTerm substsRelated)
  | .eitherMatch scrutinee leftBranch rightBranch, _, _, substsRelated =>
      RawStep.par.eitherMatch
        (RawTerm.subst_par_pointwise scrutinee substsRelated)
        (RawTerm.subst_par_pointwise leftBranch substsRelated)
        (RawTerm.subst_par_pointwise rightBranch substsRelated)
  | .refl rawWitness, _, _, substsRelated =>
      RawStep.par.reflCong
        (RawTerm.subst_par_pointwise rawWitness substsRelated)
  | .idJ baseCase witness, _, _, substsRelated =>
      RawStep.par.idJ
        (RawTerm.subst_par_pointwise baseCase substsRelated)
        (RawTerm.subst_par_pointwise witness substsRelated)
  | .modIntro innerTerm, _, _, substsRelated =>
      RawStep.par.modIntro
        (RawTerm.subst_par_pointwise innerTerm substsRelated)
  | .modElim innerTerm, _, _, substsRelated =>
      RawStep.par.modElim
        (RawTerm.subst_par_pointwise innerTerm substsRelated)
  | .subsume innerTerm, _, _, substsRelated =>
      RawStep.par.subsume
        (RawTerm.subst_par_pointwise innerTerm substsRelated)
  -- D1.6: pure cong rules for the 27 new RawTerm ctors.
  | .interval0, _, _, _ => RawStep.par.refl _
  | .interval1, _, _, _ => RawStep.par.refl _
  | .intervalOpp intervalTerm, _, _, substsRelated =>
      RawStep.par.intervalOppCong
        (RawTerm.subst_par_pointwise intervalTerm substsRelated)
  | .intervalMeet leftInterval rightInterval, _, _, substsRelated =>
      RawStep.par.intervalMeetCong
        (RawTerm.subst_par_pointwise leftInterval substsRelated)
        (RawTerm.subst_par_pointwise rightInterval substsRelated)
  | .intervalJoin leftInterval rightInterval, _, _, substsRelated =>
      RawStep.par.intervalJoinCong
        (RawTerm.subst_par_pointwise leftInterval substsRelated)
        (RawTerm.subst_par_pointwise rightInterval substsRelated)
  | .pathLam body, _, _, substsRelated =>
      RawStep.par.pathLamCong
        (RawTerm.subst_par_pointwise body
          (RawTermSubst.par_lift substsRelated))
  | .pathApp pathTerm intervalArg, _, _, substsRelated =>
      RawStep.par.pathAppCong
        (RawTerm.subst_par_pointwise pathTerm substsRelated)
        (RawTerm.subst_par_pointwise intervalArg substsRelated)
  | .glueIntro baseValue partialValue, _, _, substsRelated =>
      RawStep.par.glueIntroCong
        (RawTerm.subst_par_pointwise baseValue substsRelated)
        (RawTerm.subst_par_pointwise partialValue substsRelated)
  | .glueElim gluedValue, _, _, substsRelated =>
      RawStep.par.glueElimCong
        (RawTerm.subst_par_pointwise gluedValue substsRelated)
  | .transp pathTerm sourceTerm, _, _, substsRelated =>
      RawStep.par.transpCong
        (RawTerm.subst_par_pointwise pathTerm substsRelated)
        (RawTerm.subst_par_pointwise sourceTerm substsRelated)
  | .hcomp sidesTerm capTerm, _, _, substsRelated =>
      RawStep.par.hcompCong
        (RawTerm.subst_par_pointwise sidesTerm substsRelated)
        (RawTerm.subst_par_pointwise capTerm substsRelated)
  | .oeqRefl witnessTerm, _, _, substsRelated =>
      RawStep.par.oeqReflCong
        (RawTerm.subst_par_pointwise witnessTerm substsRelated)
  | .oeqJ baseCase witness, _, _, substsRelated =>
      RawStep.par.oeqJCong
        (RawTerm.subst_par_pointwise baseCase substsRelated)
        (RawTerm.subst_par_pointwise witness substsRelated)
  | .oeqFunext pointwiseEquality, _, _, substsRelated =>
      RawStep.par.oeqFunextCong
        (RawTerm.subst_par_pointwise pointwiseEquality substsRelated)
  | .idStrictRefl witnessTerm, _, _, substsRelated =>
      RawStep.par.idStrictReflCong
        (RawTerm.subst_par_pointwise witnessTerm substsRelated)
  | .idStrictRec baseCase witness, _, _, substsRelated =>
      RawStep.par.idStrictRecCong
        (RawTerm.subst_par_pointwise baseCase substsRelated)
        (RawTerm.subst_par_pointwise witness substsRelated)
  | .equivIntro forwardFn backwardFn, _, _, substsRelated =>
      RawStep.par.equivIntroCong
        (RawTerm.subst_par_pointwise forwardFn substsRelated)
        (RawTerm.subst_par_pointwise backwardFn substsRelated)
  | .equivApp equivTerm argument, _, _, substsRelated =>
      RawStep.par.equivAppCong
        (RawTerm.subst_par_pointwise equivTerm substsRelated)
        (RawTerm.subst_par_pointwise argument substsRelated)
  | .refineIntro rawValue predicateProof, _, _, substsRelated =>
      RawStep.par.refineIntroCong
        (RawTerm.subst_par_pointwise rawValue substsRelated)
        (RawTerm.subst_par_pointwise predicateProof substsRelated)
  | .refineElim refinedValue, _, _, substsRelated =>
      RawStep.par.refineElimCong
        (RawTerm.subst_par_pointwise refinedValue substsRelated)
  | .recordIntro firstField, _, _, substsRelated =>
      RawStep.par.recordIntroCong
        (RawTerm.subst_par_pointwise firstField substsRelated)
  | .recordProj recordValue, _, _, substsRelated =>
      RawStep.par.recordProjCong
        (RawTerm.subst_par_pointwise recordValue substsRelated)
  | .codataUnfold initialState transition, _, _, substsRelated =>
      RawStep.par.codataUnfoldCong
        (RawTerm.subst_par_pointwise initialState substsRelated)
        (RawTerm.subst_par_pointwise transition substsRelated)
  | .codataDest codataValue, _, _, substsRelated =>
      RawStep.par.codataDestCong
        (RawTerm.subst_par_pointwise codataValue substsRelated)
  | .sessionSend channel payload, _, _, substsRelated =>
      RawStep.par.sessionSendCong
        (RawTerm.subst_par_pointwise channel substsRelated)
        (RawTerm.subst_par_pointwise payload substsRelated)
  | .sessionRecv channel, _, _, substsRelated =>
      RawStep.par.sessionRecvCong
        (RawTerm.subst_par_pointwise channel substsRelated)
  | .effectPerform operationTag arguments, _, _, substsRelated =>
      RawStep.par.effectPerformCong
        (RawTerm.subst_par_pointwise operationTag substsRelated)
        (RawTerm.subst_par_pointwise arguments substsRelated)
  | .universeCode _, _, _, _ => RawStep.par.refl _
  -- CUMUL-2.1 per-shape type codes — descend into subterms via the
  -- shape-specific cong rules (`arrowCodeCong`, `piTyCodeCong`, ...)
  -- defined in `Reduction/RawPar.lean`.  Binder-shape ctors
  -- (`piTyCode`, `sigmaTyCode`) recurse with `RawTermSubst.par_lift
  -- substsRelated` to thread the parallelism under the binder.
  | .arrowCode domainCode codomainCode, _, _, substsRelated =>
      RawStep.par.arrowCodeCong
        (RawTerm.subst_par_pointwise domainCode substsRelated)
        (RawTerm.subst_par_pointwise codomainCode substsRelated)
  | .piTyCode domainCode codomainCode, _, _, substsRelated =>
      RawStep.par.piTyCodeCong
        (RawTerm.subst_par_pointwise domainCode substsRelated)
        (RawTerm.subst_par_pointwise codomainCode
          (RawTermSubst.par_lift substsRelated))
  | .sigmaTyCode domainCode codomainCode, _, _, substsRelated =>
      RawStep.par.sigmaTyCodeCong
        (RawTerm.subst_par_pointwise domainCode substsRelated)
        (RawTerm.subst_par_pointwise codomainCode
          (RawTermSubst.par_lift substsRelated))
  | .productCode firstCode secondCode, _, _, substsRelated =>
      RawStep.par.productCodeCong
        (RawTerm.subst_par_pointwise firstCode substsRelated)
        (RawTerm.subst_par_pointwise secondCode substsRelated)
  | .sumCode leftCode rightCode, _, _, substsRelated =>
      RawStep.par.sumCodeCong
        (RawTerm.subst_par_pointwise leftCode substsRelated)
        (RawTerm.subst_par_pointwise rightCode substsRelated)
  | .listCode elementCode, _, _, substsRelated =>
      RawStep.par.listCodeCong
        (RawTerm.subst_par_pointwise elementCode substsRelated)
  | .optionCode elementCode, _, _, substsRelated =>
      RawStep.par.optionCodeCong
        (RawTerm.subst_par_pointwise elementCode substsRelated)
  | .eitherCode leftCode rightCode, _, _, substsRelated =>
      RawStep.par.eitherCodeCong
        (RawTerm.subst_par_pointwise leftCode substsRelated)
        (RawTerm.subst_par_pointwise rightCode substsRelated)
  | .idCode typeCode leftRaw rightRaw, _, _, substsRelated =>
      RawStep.par.idCodeCong
        (RawTerm.subst_par_pointwise typeCode substsRelated)
        (RawTerm.subst_par_pointwise leftRaw substsRelated)
        (RawTerm.subst_par_pointwise rightRaw substsRelated)
  | .equivCode leftTypeCode rightTypeCode, _, _, substsRelated =>
      RawStep.par.equivCodeCong
        (RawTerm.subst_par_pointwise leftTypeCode substsRelated)
        (RawTerm.subst_par_pointwise rightTypeCode substsRelated)
  -- CUMUL-2.6: cumulUpMarker recurses on inner code raw.
  | .cumulUpMarker innerCodeRaw, _, _, substsRelated =>
      RawStep.par.cumulUpMarkerCong
        (RawTerm.subst_par_pointwise innerCodeRaw substsRelated)
  -- D3.6-P1: uaToEquiv recurses on inner proof raw.
  | .uaToEquiv proofRaw, _, _, substsRelated =>
      RawStep.par.uaToEquivCong
        (RawTerm.subst_par_pointwise proofRaw substsRelated)
  -- D3.6-P2: equivApply recurses on equiv and arg raws.
  | .equivApply equivRaw argRaw, _, _, substsRelated =>
      RawStep.par.equivApplyCong
        (RawTerm.subst_par_pointwise equivRaw substsRelated)
        (RawTerm.subst_par_pointwise argRaw substsRelated)
  -- D3.6-S3: pathCompose recurses on left and right path raws.
  | .pathCompose leftPathRaw rightPathRaw, _, _, substsRelated =>
      RawStep.par.pathComposeCong
        (RawTerm.subst_par_pointwise leftPathRaw substsRelated)
        (RawTerm.subst_par_pointwise rightPathRaw substsRelated)
  -- D3.6-S4: idToEquiv recurses on the proof raw.
  | .idToEquiv proofRaw, _, _, substsRelated =>
      RawStep.par.idToEquivCong
        (RawTerm.subst_par_pointwise proofRaw substsRelated)
  -- D3.6-S5: oeqTrans recurses on both proof raws.
  | .oeqTrans firstProof secondProof, _, _, substsRelated =>
      RawStep.par.oeqTransCong
        (RawTerm.subst_par_pointwise firstProof substsRelated)
        (RawTerm.subst_par_pointwise secondProof substsRelated)
  -- D3.6-S5: equivCompose recurses on both equiv raws.
  | .equivCompose firstEquiv secondEquiv, _, _, substsRelated =>
      RawStep.par.equivComposeCong
        (RawTerm.subst_par_pointwise firstEquiv substsRelated)
        (RawTerm.subst_par_pointwise secondEquiv substsRelated)

/-! ## Joint substitution: parallel terms + parallel substs → parallel. -/

/-- Joint substitution lemma: parallel reduction is preserved by
substitution where both the substituted term and the substitution
itself step in parallel.  cd_lemma's β-case workhorse. -/
theorem RawStep.par.subst_par {sourceScope targetScope : Nat}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    {beforeTerm afterTerm : RawTerm sourceScope} :
    RawStep.par beforeTerm afterTerm →
    RawStep.par (beforeTerm.subst firstSubst)
                (afterTerm.subst secondSubst) := by
  intro parallelStep
  induction parallelStep generalizing targetScope with
  -- Reflexivity: same term, related substs ⇒ subst_par_pointwise.
  | refl term =>
      exact RawTerm.subst_par_pointwise term substsRelated
  -- Cong cases.
  | lam _ bodyIH =>
      exact RawStep.par.lam (bodyIH (RawTermSubst.par_lift substsRelated))
  | app _ _ functionIH argumentIH =>
      exact RawStep.par.app (functionIH substsRelated) (argumentIH substsRelated)
  | pair _ _ firstIH secondIH =>
      exact RawStep.par.pair (firstIH substsRelated) (secondIH substsRelated)
  | fst _ pairIH => exact RawStep.par.fst (pairIH substsRelated)
  | snd _ pairIH => exact RawStep.par.snd (pairIH substsRelated)
  | boolElim _ _ _ scrutineeIH thenIH elseIH =>
      exact RawStep.par.boolElim (scrutineeIH substsRelated)
        (thenIH substsRelated) (elseIH substsRelated)
  | natSucc _ predecessorIH =>
      exact RawStep.par.natSucc (predecessorIH substsRelated)
  | natElim _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.natElim (scrutineeIH substsRelated)
        (zeroIH substsRelated) (succIH substsRelated)
  | natRec _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.natRec (scrutineeIH substsRelated)
        (zeroIH substsRelated) (succIH substsRelated)
  | listCons _ _ headIH tailIH =>
      exact RawStep.par.listCons (headIH substsRelated) (tailIH substsRelated)
  | listElim _ _ _ scrutineeIH nilIH consIH =>
      exact RawStep.par.listElim (scrutineeIH substsRelated)
        (nilIH substsRelated) (consIH substsRelated)
  | optionSome _ valueIH =>
      exact RawStep.par.optionSome (valueIH substsRelated)
  | optionMatch _ _ _ scrutineeIH noneIH someIH =>
      exact RawStep.par.optionMatch (scrutineeIH substsRelated)
        (noneIH substsRelated) (someIH substsRelated)
  | eitherInl _ valueIH =>
      exact RawStep.par.eitherInl (valueIH substsRelated)
  | eitherInr _ valueIH =>
      exact RawStep.par.eitherInr (valueIH substsRelated)
  | eitherMatch _ _ _ scrutineeIH leftIH rightIH =>
      exact RawStep.par.eitherMatch (scrutineeIH substsRelated)
        (leftIH substsRelated) (rightIH substsRelated)
  | reflCong _ witnessIH =>
      exact RawStep.par.reflCong (witnessIH substsRelated)
  | idJ _ _ baseIH witnessIH =>
      exact RawStep.par.idJ (baseIH substsRelated) (witnessIH substsRelated)
  | modIntro _ innerIH =>
      exact RawStep.par.modIntro (innerIH substsRelated)
  | modElim _ innerIH =>
      exact RawStep.par.modElim (innerIH substsRelated)
  | betaModElimIntro _ innerIH =>
      exact RawStep.par.betaModElimIntro (innerIH substsRelated)
  | betaModElimIntroDeep _ innerIH =>
      exact RawStep.par.betaModElimIntroDeep (innerIH substsRelated)
  | subsume _ innerIH =>
      exact RawStep.par.subsume (innerIH substsRelated)
  -- Shallow β rules: reshape via subst0_subst_commute.
  | betaApp _ _ bodyIH argumentIH =>
      simp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaApp
        (bodyIH (RawTermSubst.par_lift substsRelated))
        (argumentIH substsRelated)
  | betaFstPair secondValue _ firstIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaFstPair (secondValue.subst firstSubst)
        (firstIH substsRelated)
  | betaSndPair firstValue _ secondIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaSndPair (firstValue.subst firstSubst)
        (secondIH substsRelated)
  -- Shallow ι rules.
  | iotaBoolElimTrue elseBranch _ thenIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimTrue (elseBranch.subst firstSubst)
        (thenIH substsRelated)
  | iotaBoolElimFalse thenBranch _ elseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimFalse (thenBranch.subst firstSubst)
        (elseIH substsRelated)
  | iotaNatElimZero succBranch _ zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimZero (succBranch.subst firstSubst)
        (zeroIH substsRelated)
  | iotaNatElimSucc zeroBranch _ _ predecessorIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimSucc (zeroBranch.subst firstSubst)
        (predecessorIH substsRelated) (succIH substsRelated)
  | iotaNatRecZero succBranch _ zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecZero (succBranch.subst firstSubst)
        (zeroIH substsRelated)
  | iotaNatRecSucc _ _ _ predecessorIH zeroIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecSucc (predecessorIH substsRelated)
        (zeroIH substsRelated) (succIH substsRelated)
  | iotaListElimNil consBranch _ nilIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimNil (consBranch.subst firstSubst)
        (nilIH substsRelated)
  | iotaListElimCons nilBranch _ _ _ headIH tailIH consIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimCons (nilBranch.subst firstSubst)
        (headIH substsRelated) (tailIH substsRelated) (consIH substsRelated)
  | iotaOptionMatchNone someBranch _ noneIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchNone (someBranch.subst firstSubst)
        (noneIH substsRelated)
  | iotaOptionMatchSome noneBranch _ _ valueIH someIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchSome (noneBranch.subst firstSubst)
        (valueIH substsRelated) (someIH substsRelated)
  | iotaEitherMatchInl rightBranch _ _ valueIH leftIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInl (rightBranch.subst firstSubst)
        (valueIH substsRelated) (leftIH substsRelated)
  | iotaEitherMatchInr leftBranch _ _ valueIH rightIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInr (leftBranch.subst firstSubst)
        (valueIH substsRelated) (rightIH substsRelated)
  | iotaIdJRefl witnessRaw _ baseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaIdJRefl (witnessRaw.subst firstSubst)
        (baseIH substsRelated)
  | iotaIdStrictRecRefl witnessRaw _ baseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaIdStrictRecRefl (witnessRaw.subst firstSubst)
        (baseIH substsRelated)
  -- Deep β rules.
  | betaAppDeep _ _ functionIH argumentIH =>
      simp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaAppDeep
        (functionIH substsRelated)
        (argumentIH substsRelated)
  | betaFstPairDeep _ pairIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaFstPairDeep (pairIH substsRelated)
  | betaSndPairDeep _ pairIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaSndPairDeep (pairIH substsRelated)
  -- Deep ι rules.
  | iotaBoolElimTrueDeep elseBranch _ _ scrutineeIH thenIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimTrueDeep (elseBranch.subst firstSubst)
        (scrutineeIH substsRelated) (thenIH substsRelated)
  | iotaBoolElimFalseDeep thenBranch _ _ scrutineeIH elseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimFalseDeep (thenBranch.subst firstSubst)
        (scrutineeIH substsRelated) (elseIH substsRelated)
  | iotaNatElimZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimZeroDeep (succBranch.subst firstSubst)
        (scrutineeIH substsRelated) (zeroIH substsRelated)
  | iotaNatElimSuccDeep zeroBranch _ _ scrutineeIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimSuccDeep (zeroBranch.subst firstSubst)
        (scrutineeIH substsRelated) (succIH substsRelated)
  | iotaNatRecZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecZeroDeep (succBranch.subst firstSubst)
        (scrutineeIH substsRelated) (zeroIH substsRelated)
  | iotaNatRecSuccDeep _ _ _ scrutineeIH zeroIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecSuccDeep
        (scrutineeIH substsRelated) (zeroIH substsRelated) (succIH substsRelated)
  | iotaListElimNilDeep consBranch _ _ scrutineeIH nilIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimNilDeep (consBranch.subst firstSubst)
        (scrutineeIH substsRelated) (nilIH substsRelated)
  | iotaListElimConsDeep nilBranch _ _ scrutineeIH consIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimConsDeep (nilBranch.subst firstSubst)
        (scrutineeIH substsRelated) (consIH substsRelated)
  | iotaOptionMatchNoneDeep someBranch _ _ scrutineeIH noneIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchNoneDeep (someBranch.subst firstSubst)
        (scrutineeIH substsRelated) (noneIH substsRelated)
  | iotaOptionMatchSomeDeep noneBranch _ _ scrutineeIH someIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchSomeDeep (noneBranch.subst firstSubst)
        (scrutineeIH substsRelated) (someIH substsRelated)
  | iotaEitherMatchInlDeep rightBranch _ _ scrutineeIH leftIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInlDeep (rightBranch.subst firstSubst)
        (scrutineeIH substsRelated) (leftIH substsRelated)
  | iotaEitherMatchInrDeep leftBranch _ _ scrutineeIH rightIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInrDeep (leftBranch.subst firstSubst)
        (scrutineeIH substsRelated) (rightIH substsRelated)
  | iotaIdJReflDeep _ _ witnessIH baseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaIdJReflDeep
        (witnessIH substsRelated) (baseIH substsRelated)
  | iotaIdStrictRecReflDeep _ _ witnessIH baseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaIdStrictRecReflDeep
        (witnessIH substsRelated) (baseIH substsRelated)
  -- D1.6: cong cases for the 27 new RawTerm ctors.
  | intervalOppCong _ intervalIH =>
      exact RawStep.par.intervalOppCong (intervalIH substsRelated)
  | intervalMeetCong _ _ leftIH rightIH =>
      exact RawStep.par.intervalMeetCong (leftIH substsRelated) (rightIH substsRelated)
  | intervalJoinCong _ _ leftIH rightIH =>
      exact RawStep.par.intervalJoinCong (leftIH substsRelated) (rightIH substsRelated)
  | pathLamCong _ bodyIH =>
      exact RawStep.par.pathLamCong (bodyIH (RawTermSubst.par_lift substsRelated))
  | pathAppCong _ _ pathIH intervalIH =>
      exact RawStep.par.pathAppCong (pathIH substsRelated) (intervalIH substsRelated)
  | betaPathApp _ _ bodyIH intervalIH =>
      simp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaPathApp
        (bodyIH (RawTermSubst.par_lift substsRelated))
        (intervalIH substsRelated)
  | betaPathAppDeep _ _ pathIH intervalIH =>
      simp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaPathAppDeep
        (pathIH substsRelated)
        (intervalIH substsRelated)
  | @betaPathReflApp _ valueRawSource _ _ _ _ _ valueIH intervalIH =>
      -- Source: pathApp (pathLam valueRawSource.weaken) intervalRawSource.
      -- After subst rho: pathApp (pathLam (valueRawSource.weaken.subst rho.lift))
      --                          (intervalRawSource.subst rho)
      -- We need: valueRawSource.weaken.subst rho.lift =
      --            (valueRawSource.subst rho).weaken.
      -- That is `weaken_subst_commute`, mirroring the transpReflBeta arm.
      simp only [RawTerm.subst]
      rw [RawTerm.weaken_subst_commute firstSubst valueRawSource]
      exact RawStep.par.betaPathReflApp
        (valueIH substsRelated) (intervalIH substsRelated)
  | glueIntroCong _ _ baseIH partialIH =>
      exact RawStep.par.glueIntroCong (baseIH substsRelated) (partialIH substsRelated)
  | betaGlueElimIntro _ _ baseIH partialIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaGlueElimIntro
        (baseIH substsRelated)
        (partialIH substsRelated)
  | betaGlueElimIntroDeep _ gluedIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaGlueElimIntroDeep (gluedIH substsRelated)
  | glueElimCong _ gluedIH =>
      exact RawStep.par.glueElimCong (gluedIH substsRelated)
  | transpCong _ _ pathIH sourceIH =>
      exact RawStep.par.transpCong (pathIH substsRelated) (sourceIH substsRelated)
  | @transpReflBeta _ typeRawSource _ _ _ _ _ typeIH sourceIH =>
      simp only [RawTerm.subst]
      rw [RawTerm.weaken_subst_commute firstSubst typeRawSource]
      exact RawStep.par.transpReflBeta
        (typeIH substsRelated) (sourceIH substsRelated)
  | @transpReflBetaDeep _ _ typeRawTarget _ _ _ _ pathIH sourceIH =>
      simp only [RawTerm.subst]
      have pathSubstStep := pathIH substsRelated
      simp only [RawTerm.subst, RawTerm.weaken_subst_commute] at pathSubstStep
      exact RawStep.par.transpReflBetaDeep pathSubstStep
        (sourceIH substsRelated)
  | @hcompBeta _ pathBodyRawSource _ _ _ _ _ pathBodyIH capIH =>
      -- Source: hcomp (pathLam pathBodyRawSource.weaken) capRawSource.
      -- After subst rho: hcomp (pathLam (pathBodyRawSource.weaken.subst rho.lift))
      --                        (capRawSource.subst rho).
      -- Need: pathBodyRawSource.weaken.subst rho.lift =
      --         (pathBodyRawSource.subst rho).weaken
      -- via `weaken_subst_commute`, mirroring the transpReflBeta arm.
      simp only [RawTerm.subst]
      rw [RawTerm.weaken_subst_commute firstSubst pathBodyRawSource]
      exact RawStep.par.hcompBeta
        (pathBodyIH substsRelated) (capIH substsRelated)
  | @hcompBetaDeep _ _ _ _ _ _ _ sidesIH capIH =>
      -- sidesIH : par sidesRawSource (pathLam pathBodyRawTarget.weaken).
      -- After subst rho, the IH gives par on substituted sides; the target
      -- becomes pathLam ((pathBodyRawTarget.weaken).subst rho.lift), rewritten via
      -- weaken_subst_commute to pathLam (pathBodyRawTarget.subst rho).weaken.
      simp only [RawTerm.subst]
      have sidesSubstStep := sidesIH substsRelated
      simp only [RawTerm.subst, RawTerm.weaken_subst_commute] at sidesSubstStep
      exact RawStep.par.hcompBetaDeep sidesSubstStep
        (capIH substsRelated)
  | hcompCong _ _ sidesIH capIH =>
      exact RawStep.par.hcompCong (sidesIH substsRelated) (capIH substsRelated)
  | oeqReflCong _ witnessIH =>
      exact RawStep.par.oeqReflCong (witnessIH substsRelated)
  | oeqJCong _ _ baseIH witnessIH =>
      exact RawStep.par.oeqJCong (baseIH substsRelated) (witnessIH substsRelated)
  | oeqFunextCong _ pointwiseIH =>
      exact RawStep.par.oeqFunextCong (pointwiseIH substsRelated)
  | idStrictReflCong _ witnessIH =>
      exact RawStep.par.idStrictReflCong (witnessIH substsRelated)
  | idStrictRecCong _ _ baseIH witnessIH =>
      exact RawStep.par.idStrictRecCong (baseIH substsRelated) (witnessIH substsRelated)
  | equivIntroCong _ _ forwardIH backwardIH =>
      exact RawStep.par.equivIntroCong (forwardIH substsRelated) (backwardIH substsRelated)
  | equivAppCong _ _ equivIH argumentIH =>
      exact RawStep.par.equivAppCong (equivIH substsRelated) (argumentIH substsRelated)
  | refineIntroCong _ _ valueIH proofIH =>
      exact RawStep.par.refineIntroCong (valueIH substsRelated) (proofIH substsRelated)
  | betaRefineElimIntro _ _ valueIH proofIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaRefineElimIntro
        (valueIH substsRelated)
        (proofIH substsRelated)
  | betaRefineElimIntroDeep _ refinedIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaRefineElimIntroDeep (refinedIH substsRelated)
  | refineElimCong _ refinedIH =>
      exact RawStep.par.refineElimCong (refinedIH substsRelated)
  | recordIntroCong _ firstIH =>
      exact RawStep.par.recordIntroCong (firstIH substsRelated)
  | betaRecordProjIntro _ firstIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaRecordProjIntro (firstIH substsRelated)
  | betaRecordProjIntroDeep _ recordIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaRecordProjIntroDeep (recordIH substsRelated)
  | recordProjCong _ recordIH =>
      exact RawStep.par.recordProjCong (recordIH substsRelated)
  | codataUnfoldCong _ _ stateIH transitionIH =>
      exact RawStep.par.codataUnfoldCong (stateIH substsRelated) (transitionIH substsRelated)
  | betaCodataDestUnfold _ _ stateIH transitionIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaCodataDestUnfold
        (stateIH substsRelated)
        (transitionIH substsRelated)
  | betaCodataDestUnfoldDeep _ codataIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaCodataDestUnfoldDeep
        (codataIH substsRelated)
  | codataDestCong _ codataIH =>
      exact RawStep.par.codataDestCong (codataIH substsRelated)
  | sessionSendCong _ _ channelIH payloadIH =>
      exact RawStep.par.sessionSendCong (channelIH substsRelated) (payloadIH substsRelated)
  | sessionRecvCong _ channelIH =>
      exact RawStep.par.sessionRecvCong (channelIH substsRelated)
  | effectPerformCong _ _ operationIH argumentsIH =>
      exact RawStep.par.effectPerformCong (operationIH substsRelated) (argumentsIH substsRelated)
  -- CUMUL-2.1 per-shape type-code cong rules.  Binder-shape ctors
  -- (`piTyCode`, `sigmaTyCode`) recurse with `RawTermSubst.par_lift
  -- substsRelated` to thread parallelism under the binder.
  | arrowCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.arrowCodeCong (domainIH substsRelated) (codomainIH substsRelated)
  | piTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.piTyCodeCong
        (domainIH substsRelated)
        (codomainIH (RawTermSubst.par_lift substsRelated))
  | sigmaTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.sigmaTyCodeCong
        (domainIH substsRelated)
        (codomainIH (RawTermSubst.par_lift substsRelated))
  | productCodeCong _ _ firstIH secondIH =>
      exact RawStep.par.productCodeCong (firstIH substsRelated) (secondIH substsRelated)
  | sumCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.sumCodeCong (leftIH substsRelated) (rightIH substsRelated)
  | listCodeCong _ elementIH =>
      exact RawStep.par.listCodeCong (elementIH substsRelated)
  | optionCodeCong _ elementIH =>
      exact RawStep.par.optionCodeCong (elementIH substsRelated)
  | eitherCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.eitherCodeCong (leftIH substsRelated) (rightIH substsRelated)
  | idCodeCong _ _ _ typeIH leftIH rightIH =>
      exact RawStep.par.idCodeCong
        (typeIH substsRelated) (leftIH substsRelated) (rightIH substsRelated)
  | equivCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.equivCodeCong (leftIH substsRelated) (rightIH substsRelated)
  | cumulUpMarkerCong _ innerIH =>
      exact RawStep.par.cumulUpMarkerCong (innerIH substsRelated)
  | uaToEquivCong _ innerIH =>
      exact RawStep.par.uaToEquivCong (innerIH substsRelated)
  | equivApplyCong _ _ equivIH argIH =>
      exact RawStep.par.equivApplyCong
        (equivIH substsRelated) (argIH substsRelated)
  | uaBeta _ _ proofIH sourceIH =>
      -- D3.6-S1: parallel substitution preserves the univalence-β
      -- contractum.  LHS subst pushes through transp/uaToEquiv heads;
      -- RHS subst pushes through equivApply/uaToEquiv heads.  Both
      -- sides are mechanical via the definition of `RawTerm.subst`
      -- on the involved ctors (no binder shift since none of the
      -- involved ctors carry binders at this level).
      simp only [RawTerm.subst]
      exact RawStep.par.uaBeta (proofIH substsRelated) (sourceIH substsRelated)
  | uaBetaDeep _ _ pathIH sourceIH =>
      -- D3.6-S1 deep variant: parallel substitution pushes through
      -- transp/equivApply/uaToEquiv heads.  Lift pathIH via subst on
      -- its uaToEquiv-headed target, then assemble.
      simp only [RawTerm.subst]
      have pathSubstStep := pathIH substsRelated
      simp only [RawTerm.subst] at pathSubstStep
      exact RawStep.par.uaBetaDeep pathSubstStep (sourceIH substsRelated)
  | pathComposeCong _ _ leftIH rightIH =>
      -- D3.6-S3: parallel substitution distributes over the binary
      -- pathCompose ctor; each path raw gets the same substitution.
      exact RawStep.par.pathComposeCong
        (leftIH substsRelated) (rightIH substsRelated)
  | transpCompose _ _ _ leftIH rightIH sourceIH =>
      -- D3.6-S3: parallel substitution preserves the compose-β
      -- contractum.  LHS subst pushes through transp/pathCompose heads;
      -- RHS subst pushes through nested transp.  Mechanical via the
      -- definition of `RawTerm.subst` on the involved ctors (no binder
      -- shift since none of the involved ctors carry binders at this
      -- level).
      simp only [RawTerm.subst]
      exact RawStep.par.transpCompose
        (leftIH substsRelated) (rightIH substsRelated) (sourceIH substsRelated)
  | transpComposeDeep _ _ pathIH sourceIH =>
      -- D3.6-S3 deep variant: parallel substitution pushes through
      -- transp/pathCompose heads.  Lift pathIH via subst on its
      -- pathCompose-headed target, then assemble the nested-transp RHS.
      simp only [RawTerm.subst]
      have pathSubstStep := pathIH substsRelated
      simp only [RawTerm.subst] at pathSubstStep
      exact RawStep.par.transpComposeDeep pathSubstStep (sourceIH substsRelated)
  | idToEquivCong _ proofIH =>
      -- D3.6-S4: parallel substitution distributes over the unary
      -- idToEquiv ctor.
      exact RawStep.par.idToEquivCong (proofIH substsRelated)
  | idToEquivRefl _ witnessIH =>
      -- D3.6-S4: parallel substitution preserves the identity-equiv
      -- contractum.  LHS subst pushes through idToEquiv/refl heads;
      -- RHS subst over equivIntro/lam/var (var 0 is the bound binder
      -- variable, so it's unchanged by the outer subst).  Mechanical
      -- via the definition of `RawTerm.subst` on the involved ctors.
      simp only [RawTerm.subst]
      exact RawStep.par.idToEquivRefl (witnessIH substsRelated)
  | idToEquivReflDeep _ proofIH =>
      -- D3.6-S4 deep variant: parallel substitution pushes through
      -- idToEquiv heads.  proofIH substituted gives a par step on the
      -- substituted proof landing at refl of the substituted witness.
      simp only [RawTerm.subst]
      have proofSubstStep := proofIH substsRelated
      simp only [RawTerm.subst] at proofSubstStep
      exact RawStep.par.idToEquivReflDeep proofSubstStep
  | oeqTransCong _ _ firstIH secondIH =>
      -- D3.6-S5: parallel substitution distributes over the binary
      -- oeqTrans ctor.
      exact RawStep.par.oeqTransCong (firstIH substsRelated) (secondIH substsRelated)
  | equivComposeCong _ _ firstIH secondIH =>
      -- D3.6-S5: parallel substitution distributes over the binary
      -- equivCompose ctor.
      exact RawStep.par.equivComposeCong (firstIH substsRelated) (secondIH substsRelated)
  | idToEquivCompose _ _ firstIH secondIH =>
      -- D3.6-S5 shallow compose-β: parallel substitution preserves the
      -- equivCompose contractum.  LHS subst pushes through
      -- idToEquiv/oeqTrans heads; RHS subst over equivCompose/idToEquiv
      -- pushes through both arms.
      simp only [RawTerm.subst]
      exact RawStep.par.idToEquivCompose (firstIH substsRelated) (secondIH substsRelated)
  | idToEquivComposeDeep _ proofIH =>
      -- D3.6-S5 deep compose-β: parallel substitution pushes through
      -- idToEquiv heads.  proofIH substituted gives a par step on the
      -- substituted proof landing at oeqTrans of the substituted
      -- targets.
      simp only [RawTerm.subst]
      have proofSubstStep := proofIH substsRelated
      simp only [RawTerm.subst] at proofSubstStep
      exact RawStep.par.idToEquivComposeDeep proofSubstStep
  | uaReflEquivApply _ _ witnessIH sourceIH =>
      -- D3.6-S6 shallow round-trip-β: parallel substitution preserves
      -- the round-trip contractum.  LHS subst pushes through
      -- equivApply/uaToEquiv/oeqRefl heads; RHS subst pushes through
      -- bare source raw.  Both mechanical via `RawTerm.subst` on the
      -- involved ctors (no binder shift since none carry binders here).
      simp only [RawTerm.subst]
      exact RawStep.par.uaReflEquivApply
        (witnessIH substsRelated) (sourceIH substsRelated)
  | uaReflEquivApplyDeep _ _ equivIH sourceIH =>
      -- D3.6-S6 deep round-trip-β: parallel substitution pushes through
      -- equivApply heads.  equivIH substituted gives a par step on the
      -- substituted equiv landing at uaToEquiv (oeqRefl _) of the
      -- substituted witness, then assemble.
      simp only [RawTerm.subst]
      have equivSubstStep := equivIH substsRelated
      simp only [RawTerm.subst] at equivSubstStep
      exact RawStep.par.uaReflEquivApplyDeep
        equivSubstStep (sourceIH substsRelated)
  | funextReflCong _ applyIH =>
      exact RawStep.par.funextReflCong (applyIH (RawTermSubst.par_lift substsRelated))
  | funextReflAtIdCong _ applyIH =>
      exact RawStep.par.funextReflAtIdCong (applyIH (RawTermSubst.par_lift substsRelated))
  | funextIntroHetCong _ applyAIH =>
      exact RawStep.par.funextIntroHetCong (applyAIH (RawTermSubst.par_lift substsRelated))

/-! ## β-corollary: parallel substitution at position 0. -/

/-- Singleton corollary: parallel body + parallel arg ⇒ parallel β-redex. -/
theorem RawStep.par.subst0_par {scope : Nat}
    {bodySource bodyTarget : RawTerm (scope + 1)}
    {argumentSource argumentTarget : RawTerm scope}
    (bodyStep : RawStep.par bodySource bodyTarget)
    (argumentStep : RawStep.par argumentSource argumentTarget) :
    RawStep.par (bodySource.subst0 argumentSource)
                (bodyTarget.subst0 argumentTarget) := by
  apply RawStep.par.subst_par _ bodyStep
  intro position
  match position with
  | ⟨0, _⟩ => exact argumentStep
  | ⟨_ + 1, _⟩ => exact RawStep.par.refl _

end LeanFX2
