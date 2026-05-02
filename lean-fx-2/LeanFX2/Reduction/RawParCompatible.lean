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
