import LeanFX.Syntax.Reduction.RawPar
import LeanFX.Syntax.Reduction.RawParInversion

namespace LeanFX.Syntax

/-! ## Compatibility of `RawStep.par` with renaming and substitution.

Single-side preservation: if `RawStep.par t t'`, then renamed/substituted
versions of `t` and `t'` are also related.  These are then combined into
the joint lemma `RawStep.par.subst_par` which is the workhorse for
`cd_lemma`'s β cases.

Mirror of `Step.par.{rename,subst}_compatible` for raw terms — simpler
since raw terms have no Ty-level casts. -/

/-- Substitution at position 0 commutes with renaming.  Specifically:
applying a renaming after a singleton substitution equals lifting the
renaming over the body and then substituting the renamed argument. -/
theorem RawTerm.subst0_rename_commute {source target : Nat}
    (body : RawTerm (source + 1)) (argument : RawTerm source)
    (rawRenaming : Renaming source target) :
    (body.subst0 argument).rename rawRenaming =
      (body.rename rawRenaming.lift).subst0 (argument.rename rawRenaming) := by
  unfold RawTerm.subst0
  rw [RawTerm.rename_subst_commute body (RawTermSubst.singleton argument)
        rawRenaming]
  rw [RawTerm.subst_rename_commute body rawRenaming.lift
        (RawTermSubst.singleton (argument.rename rawRenaming))]
  apply RawTerm.subst_congr
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- Renaming compatibility: parallel reduction is preserved by any fixed
renaming. -/
theorem RawStep.par.rename {scope targetScope : Nat}
    (rawRenaming : Renaming scope targetScope)
    {beforeTerm afterTerm : RawTerm scope} :
    RawStep.par beforeTerm afterTerm →
    RawStep.par (beforeTerm.rename rawRenaming)
                (afterTerm.rename rawRenaming) := by
  intro parallelStep
  induction parallelStep generalizing targetScope with
  | refl term => exact RawStep.par.refl _
  | lam bodyStep bodyIH => exact RawStep.par.lam (bodyIH _)
  | app functionStep argumentStep functionIH argumentIH =>
      exact RawStep.par.app (functionIH _) (argumentIH _)
  | pair firstStep secondStep firstIH secondIH =>
      exact RawStep.par.pair (firstIH _) (secondIH _)
  | fst pairStep pairIH => exact RawStep.par.fst (pairIH _)
  | snd pairStep pairIH => exact RawStep.par.snd (pairIH _)
  | boolElim scrutineeStep thenStep elseStep
        scrutineeIH thenIH elseIH =>
      exact RawStep.par.boolElim (scrutineeIH _) (thenIH _) (elseIH _)
  | natSucc predecessorStep predecessorIH =>
      exact RawStep.par.natSucc (predecessorIH _)
  | natElim scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      exact RawStep.par.natElim (scrutineeIH _) (zeroIH _) (succIH _)
  | natRec scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      exact RawStep.par.natRec (scrutineeIH _) (zeroIH _) (succIH _)
  | listCons headStep tailStep headIH tailIH =>
      exact RawStep.par.listCons (headIH _) (tailIH _)
  | listElim scrutineeStep nilStep consStep
        scrutineeIH nilIH consIH =>
      exact RawStep.par.listElim (scrutineeIH _) (nilIH _) (consIH _)
  | optionSome valueStep valueIH =>
      exact RawStep.par.optionSome (valueIH _)
  | optionMatch scrutineeStep noneStep someStep
        scrutineeIH noneIH someIH =>
      exact RawStep.par.optionMatch (scrutineeIH _) (noneIH _) (someIH _)
  | eitherInl valueStep valueIH =>
      exact RawStep.par.eitherInl (valueIH _)
  | eitherInr valueStep valueIH =>
      exact RawStep.par.eitherInr (valueIH _)
  | eitherMatch scrutineeStep leftStep rightStep
        scrutineeIH leftIH rightIH =>
      exact RawStep.par.eitherMatch (scrutineeIH _) (leftIH _) (rightIH _)
  | idJ baseStep witnessStep baseIH witnessIH =>
      exact RawStep.par.idJ (baseIH _) (witnessIH _)
  | reflCong rawTermStep rawTermIH =>
      exact RawStep.par.reflCong (rawTermIH _)
  -- Shallow β rules.
  | betaApp bodyStep argumentStep bodyIH argumentIH =>
      rename_i body body' argBefore argAfter
      simp only [RawTerm.rename]
      rw [RawTerm.subst0_rename_commute body' argAfter rawRenaming]
      exact RawStep.par.betaApp (bodyIH _) (argumentIH _)
  | betaFstPair secondVal firstStep firstIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaFstPair (RawTerm.rename secondVal rawRenaming)
        (firstIH _)
  | betaSndPair firstVal secondStep secondIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaSndPair (RawTerm.rename firstVal rawRenaming)
        (secondIH _)
  -- Shallow ι rules.
  | iotaBoolElimTrue elseBranch thenStep thenIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimTrue
        (RawTerm.rename elseBranch rawRenaming) (thenIH _)
  | iotaBoolElimFalse thenBranch elseStep elseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimFalse
        (RawTerm.rename thenBranch rawRenaming) (elseIH _)
  | iotaNatElimZero succBranch zeroStep zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimZero
        (RawTerm.rename succBranch rawRenaming) (zeroIH _)
  | iotaNatElimSucc zeroBranch predStep succStep predIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimSucc
        (RawTerm.rename zeroBranch rawRenaming) (predIH _) (succIH _)
  | iotaNatRecZero succBranch zeroStep zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecZero
        (RawTerm.rename succBranch rawRenaming) (zeroIH _)
  | iotaNatRecSucc predStep zeroStep succStep predIH zeroIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecSucc (predIH _) (zeroIH _) (succIH _)
  | iotaListElimNil consBranch nilStep nilIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimNil
        (RawTerm.rename consBranch rawRenaming) (nilIH _)
  | iotaListElimCons nilBranch headStep tailStep consStep
        headIH tailIH consIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimCons
        (RawTerm.rename nilBranch rawRenaming)
        (headIH _) (tailIH _) (consIH _)
  | iotaOptionMatchNone someBranch noneStep noneIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchNone
        (RawTerm.rename someBranch rawRenaming) (noneIH _)
  | iotaOptionMatchSome noneBranch valueStep someStep valueIH someIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchSome
        (RawTerm.rename noneBranch rawRenaming) (valueIH _) (someIH _)
  | iotaEitherMatchInl rightBranch valueStep leftStep valueIH leftIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInl
        (RawTerm.rename rightBranch rawRenaming) (valueIH _) (leftIH _)
  | iotaEitherMatchInr leftBranch valueStep rightStep valueIH rightIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInr
        (RawTerm.rename leftBranch rawRenaming) (valueIH _) (rightIH _)
  | iotaIdJRefl rawTerm baseStep baseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaIdJRefl
        (RawTerm.rename rawTerm rawRenaming) (baseIH _)
  -- Deep β rules.
  | betaAppDeep functionStep argumentStep functionIH argumentIH =>
      rename_i function body argBefore argAfter
      simp only [RawTerm.rename]
      rw [RawTerm.subst0_rename_commute body argAfter rawRenaming]
      exact RawStep.par.betaAppDeep (functionIH _) (argumentIH _)
  | betaFstPairDeep pairStep pairIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaFstPairDeep (pairIH _)
  | betaSndPairDeep pairStep pairIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaSndPairDeep (pairIH _)
  -- Deep ι rules.
  | iotaBoolElimTrueDeep elseBranch scrutineeStep thenStep
        scrutineeIH thenIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimTrueDeep
        (RawTerm.rename elseBranch rawRenaming) (scrutineeIH _) (thenIH _)
  | iotaBoolElimFalseDeep thenBranch scrutineeStep elseStep
        scrutineeIH elseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimFalseDeep
        (RawTerm.rename thenBranch rawRenaming) (scrutineeIH _) (elseIH _)
  | iotaNatElimZeroDeep succBranch scrutineeStep zeroStep
        scrutineeIH zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimZeroDeep
        (RawTerm.rename succBranch rawRenaming) (scrutineeIH _) (zeroIH _)
  | iotaNatElimSuccDeep zeroBranch scrutineeStep succStep
        scrutineeIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimSuccDeep
        (RawTerm.rename zeroBranch rawRenaming) (scrutineeIH _) (succIH _)
  | iotaNatRecZeroDeep succBranch scrutineeStep zeroStep
        scrutineeIH zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecZeroDeep
        (RawTerm.rename succBranch rawRenaming) (scrutineeIH _) (zeroIH _)
  | iotaNatRecSuccDeep scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecSuccDeep
        (scrutineeIH _) (zeroIH _) (succIH _)
  | iotaListElimNilDeep consBranch scrutineeStep nilStep
        scrutineeIH nilIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimNilDeep
        (RawTerm.rename consBranch rawRenaming) (scrutineeIH _) (nilIH _)
  | iotaListElimConsDeep nilBranch scrutineeStep consStep
        scrutineeIH consIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimConsDeep
        (RawTerm.rename nilBranch rawRenaming) (scrutineeIH _) (consIH _)
  | iotaOptionMatchNoneDeep someBranch scrutineeStep noneStep
        scrutineeIH noneIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchNoneDeep
        (RawTerm.rename someBranch rawRenaming) (scrutineeIH _) (noneIH _)
  | iotaOptionMatchSomeDeep noneBranch scrutineeStep someStep
        scrutineeIH someIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchSomeDeep
        (RawTerm.rename noneBranch rawRenaming) (scrutineeIH _) (someIH _)
  | iotaEitherMatchInlDeep rightBranch scrutineeStep leftStep
        scrutineeIH leftIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInlDeep
        (RawTerm.rename rightBranch rawRenaming) (scrutineeIH _) (leftIH _)
  | iotaEitherMatchInrDeep leftBranch scrutineeStep rightStep
        scrutineeIH rightIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInrDeep
        (RawTerm.rename leftBranch rawRenaming) (scrutineeIH _) (rightIH _)
  | iotaIdJReflDeep witnessStep baseStep witnessIH baseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaIdJReflDeep (witnessIH _) (baseIH _)

/-! ### Helper commute lemmas. -/

/-- A weakened raw term is unaffected by singleton substitution: any
position k in the original becomes k+1 in the weakened term, and
singleton's k+1 case rebuilds `var k`.  Composition of weaken and
singleton is therefore the identity substitution. -/
theorem RawTerm.weaken_subst_singleton {scope : Nat}
    (rawTerm : RawTerm scope) (substituent : RawTerm scope) :
    rawTerm.weaken.subst (RawTermSubst.singleton substituent) = rawTerm := by
  unfold RawTerm.weaken
  rw [RawTerm.subst_rename_commute rawTerm Renaming.weaken
        (RawTermSubst.singleton substituent)]
  have afterIsIdentity :
      RawTermSubst.equiv
        (RawTermSubst.afterRenaming Renaming.weaken
          (RawTermSubst.singleton substituent))
        RawTermSubst.identity := by
    intro position
    rfl
  exact (RawTerm.subst_congr afterIsIdentity rawTerm).trans
    (RawTerm.subst_id rawTerm)

/-- Subst-of-subst0 commute lemma.  Substituting `σ` after `subst0
arg` equals lifting `σ` over the body's binder, then substituting
the σ-substituted argument. -/
theorem RawTerm.subst0_subst_commute {source target : Nat}
    (body : RawTerm (source + 1)) (argument : RawTerm source)
    (rawSubstitution : RawTermSubst source target) :
    (body.subst0 argument).subst rawSubstitution =
      (body.subst rawSubstitution.lift).subst0
        (argument.subst rawSubstitution) := by
  unfold RawTerm.subst0
  rw [RawTerm.subst_compose body (RawTermSubst.singleton argument)
        rawSubstitution]
  rw [RawTerm.subst_compose body rawSubstitution.lift
        (RawTermSubst.singleton (argument.subst rawSubstitution))]
  apply RawTerm.subst_congr
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨k + 1, isWithinBound⟩ =>
      -- LHS: compose (singleton arg) σ ⟨k+1⟩ = (var k).subst σ = σ k
      -- RHS: compose σ.lift (singleton (arg.subst σ)) ⟨k+1⟩
      --      = (σ.lift ⟨k+1⟩).subst (singleton (arg.subst σ))
      --      = ((σ k).rename weaken).subst (singleton (arg.subst σ))
      --      = (σ k) by weaken_subst_singleton
      simp only [RawTermSubst.compose, RawTermSubst.singleton,
        RawTermSubst.lift]
      exact (RawTerm.weaken_subst_singleton _ _).symm

/-! ### Joint substitution lemma (the cd_lemma workhorse).

`RawStep.par.subst_par` says that if `body` and `body'` are related
by `par` and `σ` and `σ'` are pointwise related, then their
substitutions are related.  Used for cd_lemma's β cases. -/

/-- Lifting a substitution preserves the pointwise par relation. -/
theorem RawTermSubst.par_lift {source target : Nat}
    {firstSubstitution secondSubstitution : RawTermSubst source target}
    (substitutionsRelated : ∀ position,
      RawStep.par (firstSubstitution position) (secondSubstitution position)) :
    ∀ position,
      RawStep.par (firstSubstitution.lift position)
                  (secondSubstitution.lift position) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact RawStep.par.refl _
  | ⟨_ + 1, _⟩ =>
      simp only [RawTermSubst.lift]
      exact RawStep.par.rename Renaming.weaken (substitutionsRelated _)

/-- Substitution of a fixed term varying with related substitutions:
when σ ≈p σ' (pointwise par), then `t.subst σ ≈p t.subst σ'`.  Proof
by structural induction on `t`.  This is the "refl" case of the joint
substitution lemma. -/
theorem RawTerm.subst_par_pointwise {source target : Nat} :
    ∀ (rawTerm : RawTerm source)
      {firstSubstitution secondSubstitution : RawTermSubst source target},
      (∀ position,
        RawStep.par (firstSubstitution position)
                    (secondSubstitution position)) →
      RawStep.par (rawTerm.subst firstSubstitution)
                  (rawTerm.subst secondSubstitution)
  | .var position, _, _, substitutionsRelated => substitutionsRelated _
  | .unit, _, _, _ => RawStep.par.refl _
  | .boolTrue, _, _, _ => RawStep.par.refl _
  | .boolFalse, _, _, _ => RawStep.par.refl _
  | .natZero, _, _, _ => RawStep.par.refl _
  | .listNil, _, _, _ => RawStep.par.refl _
  | .optionNone, _, _, _ => RawStep.par.refl _
  | .lam body, _, _, substitutionsRelated =>
      RawStep.par.lam
        (RawTerm.subst_par_pointwise body
          (RawTermSubst.par_lift substitutionsRelated))
  | .app function argument, _, _, substitutionsRelated =>
      RawStep.par.app
        (RawTerm.subst_par_pointwise function substitutionsRelated)
        (RawTerm.subst_par_pointwise argument substitutionsRelated)
  | .pair firstVal secondVal, _, _, substitutionsRelated =>
      RawStep.par.pair
        (RawTerm.subst_par_pointwise firstVal substitutionsRelated)
        (RawTerm.subst_par_pointwise secondVal substitutionsRelated)
  | .fst pairTerm, _, _, substitutionsRelated =>
      RawStep.par.fst
        (RawTerm.subst_par_pointwise pairTerm substitutionsRelated)
  | .snd pairTerm, _, _, substitutionsRelated =>
      RawStep.par.snd
        (RawTerm.subst_par_pointwise pairTerm substitutionsRelated)
  | .boolElim scrutinee thenBranch elseBranch, _, _, substitutionsRelated =>
      RawStep.par.boolElim
        (RawTerm.subst_par_pointwise scrutinee substitutionsRelated)
        (RawTerm.subst_par_pointwise thenBranch substitutionsRelated)
        (RawTerm.subst_par_pointwise elseBranch substitutionsRelated)
  | .natSucc predecessor, _, _, substitutionsRelated =>
      RawStep.par.natSucc
        (RawTerm.subst_par_pointwise predecessor substitutionsRelated)
  | .natElim scrutinee zeroBranch succBranch, _, _, substitutionsRelated =>
      RawStep.par.natElim
        (RawTerm.subst_par_pointwise scrutinee substitutionsRelated)
        (RawTerm.subst_par_pointwise zeroBranch substitutionsRelated)
        (RawTerm.subst_par_pointwise succBranch substitutionsRelated)
  | .natRec scrutinee zeroBranch succBranch, _, _, substitutionsRelated =>
      RawStep.par.natRec
        (RawTerm.subst_par_pointwise scrutinee substitutionsRelated)
        (RawTerm.subst_par_pointwise zeroBranch substitutionsRelated)
        (RawTerm.subst_par_pointwise succBranch substitutionsRelated)
  | .listCons head tail, _, _, substitutionsRelated =>
      RawStep.par.listCons
        (RawTerm.subst_par_pointwise head substitutionsRelated)
        (RawTerm.subst_par_pointwise tail substitutionsRelated)
  | .listElim scrutinee nilBranch consBranch, _, _, substitutionsRelated =>
      RawStep.par.listElim
        (RawTerm.subst_par_pointwise scrutinee substitutionsRelated)
        (RawTerm.subst_par_pointwise nilBranch substitutionsRelated)
        (RawTerm.subst_par_pointwise consBranch substitutionsRelated)
  | .optionSome value, _, _, substitutionsRelated =>
      RawStep.par.optionSome
        (RawTerm.subst_par_pointwise value substitutionsRelated)
  | .optionMatch scrutinee noneBranch someBranch, _, _, substitutionsRelated =>
      RawStep.par.optionMatch
        (RawTerm.subst_par_pointwise scrutinee substitutionsRelated)
        (RawTerm.subst_par_pointwise noneBranch substitutionsRelated)
        (RawTerm.subst_par_pointwise someBranch substitutionsRelated)
  | .eitherInl value, _, _, substitutionsRelated =>
      RawStep.par.eitherInl
        (RawTerm.subst_par_pointwise value substitutionsRelated)
  | .eitherInr value, _, _, substitutionsRelated =>
      RawStep.par.eitherInr
        (RawTerm.subst_par_pointwise value substitutionsRelated)
  | .eitherMatch scrutinee leftBranch rightBranch, _, _, substitutionsRelated =>
      RawStep.par.eitherMatch
        (RawTerm.subst_par_pointwise scrutinee substitutionsRelated)
        (RawTerm.subst_par_pointwise leftBranch substitutionsRelated)
        (RawTerm.subst_par_pointwise rightBranch substitutionsRelated)
  | .refl rawTerm, _, _, substitutionsRelated =>
      RawStep.par.reflCong
        (RawTerm.subst_par_pointwise rawTerm substitutionsRelated)
  | .idJ baseCase witness, _, _, substitutionsRelated =>
      RawStep.par.idJ
        (RawTerm.subst_par_pointwise baseCase substitutionsRelated)
        (RawTerm.subst_par_pointwise witness substitutionsRelated)

/-- Joint substitution lemma: parallel reduction is preserved by
substitution where both the substituted term and the substitution
itself step in parallel.  This is the cd_lemma's β-case workhorse. -/
theorem RawStep.par.subst_par {source target : Nat}
    {firstSubstitution secondSubstitution : RawTermSubst source target}
    (substitutionsRelated : ∀ position,
      RawStep.par (firstSubstitution position) (secondSubstitution position))
    {beforeTerm afterTerm : RawTerm source} :
    RawStep.par beforeTerm afterTerm →
    RawStep.par (beforeTerm.subst firstSubstitution)
                (afterTerm.subst secondSubstitution) := by
  intro parallelStep
  induction parallelStep generalizing target with
  | refl term =>
      exact RawTerm.subst_par_pointwise term substitutionsRelated
  | lam bodyStep bodyIH =>
      exact RawStep.par.lam
        (bodyIH (RawTermSubst.par_lift substitutionsRelated))
  | app functionStep argumentStep functionIH argumentIH =>
      exact RawStep.par.app (functionIH substitutionsRelated)
        (argumentIH substitutionsRelated)
  | pair firstStep secondStep firstIH secondIH =>
      exact RawStep.par.pair (firstIH substitutionsRelated)
        (secondIH substitutionsRelated)
  | fst pairStep pairIH =>
      exact RawStep.par.fst (pairIH substitutionsRelated)
  | snd pairStep pairIH =>
      exact RawStep.par.snd (pairIH substitutionsRelated)
  | boolElim scrutineeStep thenStep elseStep
        scrutineeIH thenIH elseIH =>
      exact RawStep.par.boolElim
        (scrutineeIH substitutionsRelated)
        (thenIH substitutionsRelated)
        (elseIH substitutionsRelated)
  | natSucc predecessorStep predecessorIH =>
      exact RawStep.par.natSucc (predecessorIH substitutionsRelated)
  | natElim scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      exact RawStep.par.natElim
        (scrutineeIH substitutionsRelated)
        (zeroIH substitutionsRelated)
        (succIH substitutionsRelated)
  | natRec scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      exact RawStep.par.natRec
        (scrutineeIH substitutionsRelated)
        (zeroIH substitutionsRelated)
        (succIH substitutionsRelated)
  | listCons headStep tailStep headIH tailIH =>
      exact RawStep.par.listCons
        (headIH substitutionsRelated) (tailIH substitutionsRelated)
  | listElim scrutineeStep nilStep consStep
        scrutineeIH nilIH consIH =>
      exact RawStep.par.listElim
        (scrutineeIH substitutionsRelated)
        (nilIH substitutionsRelated)
        (consIH substitutionsRelated)
  | optionSome valueStep valueIH =>
      exact RawStep.par.optionSome (valueIH substitutionsRelated)
  | optionMatch scrutineeStep noneStep someStep
        scrutineeIH noneIH someIH =>
      exact RawStep.par.optionMatch
        (scrutineeIH substitutionsRelated)
        (noneIH substitutionsRelated)
        (someIH substitutionsRelated)
  | eitherInl valueStep valueIH =>
      exact RawStep.par.eitherInl (valueIH substitutionsRelated)
  | eitherInr valueStep valueIH =>
      exact RawStep.par.eitherInr (valueIH substitutionsRelated)
  | eitherMatch scrutineeStep leftStep rightStep
        scrutineeIH leftIH rightIH =>
      exact RawStep.par.eitherMatch
        (scrutineeIH substitutionsRelated)
        (leftIH substitutionsRelated)
        (rightIH substitutionsRelated)
  | idJ baseStep witnessStep baseIH witnessIH =>
      exact RawStep.par.idJ
        (baseIH substitutionsRelated) (witnessIH substitutionsRelated)
  | reflCong rawTermStep rawTermIH =>
      exact RawStep.par.reflCong (rawTermIH substitutionsRelated)
  -- Shallow β rules.
  | betaApp bodyStep argumentStep bodyIH argumentIH =>
      rename_i body body' argBefore argAfter
      simp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute body' argAfter secondSubstitution]
      exact RawStep.par.betaApp
        (bodyIH (RawTermSubst.par_lift substitutionsRelated))
        (argumentIH substitutionsRelated)
  | betaFstPair secondVal firstStep firstIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaFstPair
        (RawTerm.subst secondVal firstSubstitution)
        (firstIH substitutionsRelated)
  | betaSndPair firstVal secondStep secondIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaSndPair
        (RawTerm.subst firstVal firstSubstitution)
        (secondIH substitutionsRelated)
  -- Shallow ι rules.
  | iotaBoolElimTrue elseBranch thenStep thenIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimTrue
        (RawTerm.subst elseBranch firstSubstitution)
        (thenIH substitutionsRelated)
  | iotaBoolElimFalse thenBranch elseStep elseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimFalse
        (RawTerm.subst thenBranch firstSubstitution)
        (elseIH substitutionsRelated)
  | iotaNatElimZero succBranch zeroStep zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimZero
        (RawTerm.subst succBranch firstSubstitution)
        (zeroIH substitutionsRelated)
  | iotaNatElimSucc zeroBranch predStep succStep predIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimSucc
        (RawTerm.subst zeroBranch firstSubstitution)
        (predIH substitutionsRelated) (succIH substitutionsRelated)
  | iotaNatRecZero succBranch zeroStep zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecZero
        (RawTerm.subst succBranch firstSubstitution)
        (zeroIH substitutionsRelated)
  | iotaNatRecSucc predStep zeroStep succStep predIH zeroIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecSucc
        (predIH substitutionsRelated) (zeroIH substitutionsRelated)
        (succIH substitutionsRelated)
  | iotaListElimNil consBranch nilStep nilIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimNil
        (RawTerm.subst consBranch firstSubstitution)
        (nilIH substitutionsRelated)
  | iotaListElimCons nilBranch headStep tailStep consStep
        headIH tailIH consIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimCons
        (RawTerm.subst nilBranch firstSubstitution)
        (headIH substitutionsRelated) (tailIH substitutionsRelated)
        (consIH substitutionsRelated)
  | iotaOptionMatchNone someBranch noneStep noneIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchNone
        (RawTerm.subst someBranch firstSubstitution)
        (noneIH substitutionsRelated)
  | iotaOptionMatchSome noneBranch valueStep someStep valueIH someIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchSome
        (RawTerm.subst noneBranch firstSubstitution)
        (valueIH substitutionsRelated) (someIH substitutionsRelated)
  | iotaEitherMatchInl rightBranch valueStep leftStep valueIH leftIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInl
        (RawTerm.subst rightBranch firstSubstitution)
        (valueIH substitutionsRelated) (leftIH substitutionsRelated)
  | iotaEitherMatchInr leftBranch valueStep rightStep valueIH rightIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInr
        (RawTerm.subst leftBranch firstSubstitution)
        (valueIH substitutionsRelated) (rightIH substitutionsRelated)
  | iotaIdJRefl rawTerm baseStep baseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaIdJRefl
        (RawTerm.subst rawTerm firstSubstitution)
        (baseIH substitutionsRelated)
  -- Deep β rules.
  | betaAppDeep functionStep argumentStep functionIH argumentIH =>
      rename_i function body argBefore argAfter
      simp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute body argAfter secondSubstitution]
      exact RawStep.par.betaAppDeep
        (functionIH substitutionsRelated)
        (argumentIH substitutionsRelated)
  | betaFstPairDeep pairStep pairIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaFstPairDeep (pairIH substitutionsRelated)
  | betaSndPairDeep pairStep pairIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.betaSndPairDeep (pairIH substitutionsRelated)
  -- Deep ι rules.
  | iotaBoolElimTrueDeep elseBranch scrutineeStep thenStep
        scrutineeIH thenIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimTrueDeep
        (RawTerm.subst elseBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (thenIH substitutionsRelated)
  | iotaBoolElimFalseDeep thenBranch scrutineeStep elseStep
        scrutineeIH elseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimFalseDeep
        (RawTerm.subst thenBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (elseIH substitutionsRelated)
  | iotaNatElimZeroDeep succBranch scrutineeStep zeroStep
        scrutineeIH zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimZeroDeep
        (RawTerm.subst succBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (zeroIH substitutionsRelated)
  | iotaNatElimSuccDeep zeroBranch scrutineeStep succStep
        scrutineeIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimSuccDeep
        (RawTerm.subst zeroBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (succIH substitutionsRelated)
  | iotaNatRecZeroDeep succBranch scrutineeStep zeroStep
        scrutineeIH zeroIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecZeroDeep
        (RawTerm.subst succBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (zeroIH substitutionsRelated)
  | iotaNatRecSuccDeep scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecSuccDeep
        (scrutineeIH substitutionsRelated)
        (zeroIH substitutionsRelated)
        (succIH substitutionsRelated)
  | iotaListElimNilDeep consBranch scrutineeStep nilStep
        scrutineeIH nilIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimNilDeep
        (RawTerm.subst consBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (nilIH substitutionsRelated)
  | iotaListElimConsDeep nilBranch scrutineeStep consStep
        scrutineeIH consIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaListElimConsDeep
        (RawTerm.subst nilBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (consIH substitutionsRelated)
  | iotaOptionMatchNoneDeep someBranch scrutineeStep noneStep
        scrutineeIH noneIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchNoneDeep
        (RawTerm.subst someBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (noneIH substitutionsRelated)
  | iotaOptionMatchSomeDeep noneBranch scrutineeStep someStep
        scrutineeIH someIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchSomeDeep
        (RawTerm.subst noneBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (someIH substitutionsRelated)
  | iotaEitherMatchInlDeep rightBranch scrutineeStep leftStep
        scrutineeIH leftIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInlDeep
        (RawTerm.subst rightBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (leftIH substitutionsRelated)
  | iotaEitherMatchInrDeep leftBranch scrutineeStep rightStep
        scrutineeIH rightIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInrDeep
        (RawTerm.subst leftBranch firstSubstitution)
        (scrutineeIH substitutionsRelated) (rightIH substitutionsRelated)
  | iotaIdJReflDeep witnessStep baseStep witnessIH baseIH =>
      simp only [RawTerm.subst]
      exact RawStep.par.iotaIdJReflDeep
        (witnessIH substitutionsRelated) (baseIH substitutionsRelated)

/-- β-corollary: parallel substitution at position 0.  Specializes
`subst_par` to a singleton substitution, where σ ≈p σ' iff
par arg arg' (the only non-trivial position). -/
theorem RawStep.par.subst0_par {scope : Nat}
    {body body' : RawTerm (scope + 1)} {arg arg' : RawTerm scope}
    (bodyStep : RawStep.par body body')
    (argumentStep : RawStep.par arg arg') :
    RawStep.par (body.subst0 arg) (body'.subst0 arg') := by
  apply RawStep.par.subst_par _ bodyStep
  intro position
  match position with
  | ⟨0, _⟩ => exact argumentStep
  | ⟨_ + 1, _⟩ => exact RawStep.par.refl _

end LeanFX.Syntax
