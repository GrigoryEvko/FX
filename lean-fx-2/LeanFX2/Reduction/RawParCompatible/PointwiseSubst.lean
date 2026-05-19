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
  | .transpFill pathTerm intervalTerm sourceTerm, _, _, substsRelated =>
      RawStep.par.transpFillCong
        (RawTerm.subst_par_pointwise pathTerm substsRelated)
        (RawTerm.subst_par_pointwise intervalTerm substsRelated)
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

end LeanFX2
