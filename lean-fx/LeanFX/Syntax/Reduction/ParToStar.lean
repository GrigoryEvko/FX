import LeanFX.Syntax.Reduction.ParRed
import LeanFX.Syntax.Reduction.Congruence

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.toStar` — parallel reduction lifts to multi-step.

Each Step.par constructor decomposes into a sequence of single Step's
chained via StepStar congruences.  Subterm-parallel cases use the
corresponding StepStar congruence directly; β/Σ cases chain congruences
first then append a final Step.beta_* via StepStar.append; ι cases
similarly chain boolElim_cong with Step.iota_*; η cases lift directly
via Step.toStar.

Placed AFTER StepStar.append and the boolean StepStar congruences
(which v1.49 needs but were originally defined later in the file).

Together with Step.toPar (v1.48), this establishes the bridge between
StepStar and the reflexive-transitive closure of Step.par — the
Tait–Martin-Löf reformulation that makes confluence tractable. -/
theorem Step.par.toStar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} : Step.par t₁ t₂ → StepStar t₁ t₂
  | .refl t                  => StepStar.refl t
  | .app par_f par_a         =>
      StepStar.app_cong (Step.par.toStar par_f) (Step.par.toStar par_a)
  | .lam par_body            =>
      StepStar.lam_cong (Step.par.toStar par_body)
  | .lamPi par_body          =>
      StepStar.lamPi_cong (Step.par.toStar par_body)
  | .appPi par_f par_a       =>
      StepStar.appPi_cong (Step.par.toStar par_f) (Step.par.toStar par_a)
  | .pair par_v par_w        =>
      StepStar.pair_cong (Step.par.toStar par_v) (Step.par.toStar par_w)
  | .fst par_p               => StepStar.fst_cong (Step.par.toStar par_p)
  | .snd par_p               => StepStar.snd_cong (Step.par.toStar par_p)
  | .boolElim par_s par_t par_e =>
      StepStar.boolElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_t)
        (Step.par.toStar par_e)
  | .betaApp (body' := body') (arg' := arg') par_body par_arg =>
      -- StepStar (app (lam body) arg) (app (lam body') arg')
      --   via app_cong of lam_cong (par_body.toStar) and par_arg.toStar
      -- then Step.betaApp body' arg' completes the β-step.
      StepStar.append
        (StepStar.app_cong
          (StepStar.lam_cong (Step.par.toStar par_body))
          (Step.par.toStar par_arg))
        (Step.betaApp body' arg')
  | .betaAppPi (body' := body') (arg' := arg') par_body par_arg =>
      StepStar.append
        (StepStar.appPi_cong
          (StepStar.lamPi_cong (Step.par.toStar par_body))
          (Step.par.toStar par_arg))
        (Step.betaAppPi body' arg')
  | .betaFstPair (firstVal' := v') secondVal par_v =>
      StepStar.append
        (StepStar.fst_cong
          (StepStar.pair_cong
            (Step.par.toStar par_v) (StepStar.refl secondVal)))
        (Step.betaFstPair v' secondVal)
  | .betaSndPair (secondVal' := w') firstVal par_w =>
      StepStar.append
        (StepStar.snd_cong
          (StepStar.pair_cong
            (StepStar.refl firstVal) (Step.par.toStar par_w)))
        (Step.betaSndPair firstVal w')
  | .iotaBoolElimTrue (thenBr' := t') elseBr par_t =>
      StepStar.append
        (StepStar.boolElim_cong
          (StepStar.refl Term.boolTrue)
          (Step.par.toStar par_t)
          (StepStar.refl elseBr))
        (Step.iotaBoolElimTrue t' elseBr)
  | .iotaBoolElimFalse (elseBr' := e') thenBr par_e =>
      StepStar.append
        (StepStar.boolElim_cong
          (StepStar.refl Term.boolFalse)
          (StepStar.refl thenBr)
          (Step.par.toStar par_e))
        (Step.iotaBoolElimFalse thenBr e')
  | .natSucc par_pred        =>
      StepStar.natSucc_cong (Step.par.toStar par_pred)
  | .natElim par_s par_z par_f =>
      StepStar.natElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_z)
        (Step.par.toStar par_f)
  | .iotaNatElimZero (zeroBranch' := z') succBranch par_z =>
      StepStar.append
        (StepStar.natElim_cong
          (StepStar.refl Term.natZero)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatElimZero z' succBranch)
  | .iotaNatElimSucc
        (predecessor' := n') (succBranch' := f')
        zeroBranch par_n par_f =>
      StepStar.trans
        (StepStar.natElim_cong
          (StepStar.natSucc_cong (Step.par.toStar par_n))
          (StepStar.refl zeroBranch)
          (Step.par.toStar par_f))
        (Step.toStar (Step.iotaNatElimSucc n' zeroBranch f'))
  | .natRec par_s par_z par_f =>
      StepStar.natRec_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_z)
        (Step.par.toStar par_f)
  | .iotaNatRecZero (zeroBranch' := z') succBranch par_z =>
      StepStar.append
        (StepStar.natRec_cong
          (StepStar.refl Term.natZero)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatRecZero z' succBranch)
  | .iotaNatRecSucc
        (predecessor' := n') (zeroBranch' := z') (succBranch' := s')
        par_n par_z par_s =>
      StepStar.trans
        (StepStar.natRec_cong
          (StepStar.natSucc_cong (Step.par.toStar par_n))
          (Step.par.toStar par_z)
          (Step.par.toStar par_s))
        (Step.toStar (Step.iotaNatRecSucc n' z' s'))
  | .listCons par_hd par_tl  =>
      StepStar.listCons_cong (Step.par.toStar par_hd) (Step.par.toStar par_tl)
  | .listElim par_s par_n par_c =>
      StepStar.listElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_n)
        (Step.par.toStar par_c)
  | .iotaListElimNil (nilBranch' := n') consBranch par_n =>
      StepStar.append
        (StepStar.listElim_cong
          (StepStar.refl Term.listNil)
          (Step.par.toStar par_n)
          (StepStar.refl consBranch))
        (Step.iotaListElimNil n' consBranch)
  | .iotaListElimCons
        (head' := h') (tail' := t') (consBranch' := c')
        nilBranch par_h par_t par_c =>
      StepStar.trans
        (StepStar.listElim_cong
          (StepStar.listCons_cong (Step.par.toStar par_h) (Step.par.toStar par_t))
          (StepStar.refl nilBranch)
          (Step.par.toStar par_c))
        (Step.toStar (Step.iotaListElimCons h' t' nilBranch c'))
  | .optionSome par_value    =>
      StepStar.optionSome_cong (Step.par.toStar par_value)
  | .optionMatch par_s par_n par_sm =>
      StepStar.optionMatch_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_n)
        (Step.par.toStar par_sm)
  | .iotaOptionMatchNone (noneBranch' := n') someBranch par_n =>
      StepStar.append
        (StepStar.optionMatch_cong
          (StepStar.refl Term.optionNone)
          (Step.par.toStar par_n)
          (StepStar.refl someBranch))
        (Step.iotaOptionMatchNone n' someBranch)
  | .iotaOptionMatchSome
        (value' := v') (someBranch' := sm')
        noneBranch par_value par_some =>
      StepStar.trans
        (StepStar.optionMatch_cong
          (StepStar.optionSome_cong (Step.par.toStar par_value))
          (StepStar.refl noneBranch)
          (Step.par.toStar par_some))
        (Step.toStar (Step.iotaOptionMatchSome v' noneBranch sm'))
  | .eitherInl par_value     =>
      StepStar.eitherInl_cong (Step.par.toStar par_value)
  | .eitherInr par_value     =>
      StepStar.eitherInr_cong (Step.par.toStar par_value)
  | .eitherMatch par_s par_l par_r =>
      StepStar.eitherMatch_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_l)
        (Step.par.toStar par_r)
  | .iotaEitherMatchInl
        (value' := v') (leftBranch' := lb')
        rightBranch par_value par_left =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (StepStar.eitherInl_cong (Step.par.toStar par_value))
          (Step.par.toStar par_left)
          (StepStar.refl rightBranch))
        (Step.toStar (Step.iotaEitherMatchInl v' lb' rightBranch))
  | .iotaEitherMatchInr
        (value' := v') (rightBranch' := rb')
        leftBranch par_value par_right =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (StepStar.eitherInr_cong (Step.par.toStar par_value))
          (StepStar.refl leftBranch)
          (Step.par.toStar par_right))
        (Step.toStar (Step.iotaEitherMatchInr v' leftBranch rb'))
  | .etaArrow f              => Step.toStar (Step.etaArrow f)
  | .etaSigma p              => Step.toStar (Step.etaSigma p)
  | .idJ par_base par_witness =>
      StepStar.idJ_cong (Step.par.toStar par_base) (Step.par.toStar par_witness)
  | .iotaIdJRefl (baseCase' := base') par_base =>
      StepStar.append
        (StepStar.idJ_cong_base _ (Step.par.toStar par_base))
        (Step.iotaIdJRefl base')
  -- Deep redex cases: parallel reduction of the inner term to a redex
  -- shape, then the literal Step contraction at the redex.
  | .betaAppDeep (body := body) (arg' := arg') par_f par_arg =>
      StepStar.append
        (StepStar.app_cong
          (Step.par.toStar par_f) (Step.par.toStar par_arg))
        (Step.betaApp body arg')
  | .betaAppPiDeep (body := body) (arg' := arg') par_f par_arg =>
      StepStar.append
        (StepStar.appPi_cong
          (Step.par.toStar par_f) (Step.par.toStar par_arg))
        (Step.betaAppPi body arg')
  | .betaFstPairDeep (firstVal := v) (secondVal := w) par_p =>
      StepStar.append
        (StepStar.fst_cong (Step.par.toStar par_p))
        (Step.betaFstPair v w)
  | .betaSndPairDeep (firstVal := v) (secondVal := w) par_p =>
      StepStar.append
        (StepStar.snd_cong (Step.par.toStar par_p))
        (Step.betaSndPair v w)
  | .iotaBoolElimTrueDeep (thenBr' := t') elseBr par_scrut par_t =>
      StepStar.append
        (StepStar.boolElim_cong
          (Step.par.toStar par_scrut)
          (Step.par.toStar par_t)
          (StepStar.refl elseBr))
        (Step.iotaBoolElimTrue t' elseBr)
  | .iotaBoolElimFalseDeep (elseBr' := e') thenBr par_scrut par_e =>
      StepStar.append
        (StepStar.boolElim_cong
          (Step.par.toStar par_scrut)
          (StepStar.refl thenBr)
          (Step.par.toStar par_e))
        (Step.iotaBoolElimFalse thenBr e')
  | .iotaNatElimZeroDeep (zeroBranch' := z') succBranch par_scrut par_z =>
      StepStar.append
        (StepStar.natElim_cong
          (Step.par.toStar par_scrut)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatElimZero z' succBranch)
  | .iotaNatElimSuccDeep
        (predecessor := pred) (succBranch' := f')
        zeroBranch par_scrut par_f =>
      StepStar.trans
        (StepStar.natElim_cong
          (Step.par.toStar par_scrut)
          (StepStar.refl zeroBranch)
          (Step.par.toStar par_f))
        (Step.toStar (Step.iotaNatElimSucc pred zeroBranch f'))
  | .iotaNatRecZeroDeep (zeroBranch' := z') succBranch par_scrut par_z =>
      StepStar.append
        (StepStar.natRec_cong
          (Step.par.toStar par_scrut)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatRecZero z' succBranch)
  | .iotaNatRecSuccDeep
        (predecessor := pred) (zeroBranch' := z') (succBranch' := s')
        par_scrut par_z par_s =>
      StepStar.trans
        (StepStar.natRec_cong
          (Step.par.toStar par_scrut)
          (Step.par.toStar par_z)
          (Step.par.toStar par_s))
        (Step.toStar (Step.iotaNatRecSucc pred z' s'))
  | .iotaListElimNilDeep (nilBranch' := n') consBranch par_scrut par_n =>
      StepStar.append
        (StepStar.listElim_cong
          (Step.par.toStar par_scrut)
          (Step.par.toStar par_n)
          (StepStar.refl consBranch))
        (Step.iotaListElimNil n' consBranch)
  | .iotaListElimConsDeep
        (head := h) (tail := t) (consBranch' := c')
        nilBranch par_scrut par_c =>
      StepStar.trans
        (StepStar.listElim_cong
          (Step.par.toStar par_scrut)
          (StepStar.refl nilBranch)
          (Step.par.toStar par_c))
        (Step.toStar (Step.iotaListElimCons h t nilBranch c'))
  | .iotaOptionMatchNoneDeep
        (noneBranch' := n') someBranch par_scrut par_n =>
      StepStar.append
        (StepStar.optionMatch_cong
          (Step.par.toStar par_scrut)
          (Step.par.toStar par_n)
          (StepStar.refl someBranch))
        (Step.iotaOptionMatchNone n' someBranch)
  | .iotaOptionMatchSomeDeep
        (value := v) (someBranch' := sm')
        noneBranch par_scrut par_some =>
      StepStar.trans
        (StepStar.optionMatch_cong
          (Step.par.toStar par_scrut)
          (StepStar.refl noneBranch)
          (Step.par.toStar par_some))
        (Step.toStar (Step.iotaOptionMatchSome v noneBranch sm'))
  | .iotaEitherMatchInlDeep
        (value := v) (leftBranch' := lb')
        rightBranch par_scrut par_left =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (Step.par.toStar par_scrut)
          (Step.par.toStar par_left)
          (StepStar.refl rightBranch))
        (Step.toStar (Step.iotaEitherMatchInl v lb' rightBranch))
  | .iotaEitherMatchInrDeep
        (value := v) (rightBranch' := rb')
        leftBranch par_scrut par_right =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (Step.par.toStar par_scrut)
          (StepStar.refl leftBranch)
          (Step.par.toStar par_right))
        (Step.toStar (Step.iotaEitherMatchInr v leftBranch rb'))
  | .iotaIdJReflDeep (baseCase' := base') par_witness par_base =>
      StepStar.append
        (StepStar.idJ_cong
          (Step.par.toStar par_base) (Step.par.toStar par_witness))
        (Step.iotaIdJRefl base')


end LeanFX.Syntax
