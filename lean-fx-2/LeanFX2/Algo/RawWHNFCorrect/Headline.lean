import LeanFX2.Algo.RawWHNFCorrect.Base
import LeanFX2.Algo.RawWHNFCorrect.ElimInversions

/-! # LeanFX2.Algo.RawWHNFCorrect.Headline — `whnf_reaches`

The headline soundness theorem for the raw WHNF evaluator: every
output of `RawTerm.whnf fuel term` is reachable from `term` via
the reflexive-transitive closure of parallel reduction.

The proof inducts on fuel and performs a full enumeration of
`RawTerm`'s constructors.  Canonical heads close with
`parStar.refl`; elim heads with potential redex recurse via the
WHNF evaluator and append a β / ι contraction step.

## Root status

Layer 3 algorithm correctness headline. -/

namespace LeanFX2

variable {scope : Nat}

/-! ## Headline theorem: `RawTerm.whnf` reaches a parallel reduct

The function `RawTerm.whnf fuel term` produces a term reachable
from `term` via the reflexive-transitive closure of parallel
reduction.  Soundness of the WHNF reducer with respect to the
kernel reduction relation. -/

/-- `RawTerm.whnf fuel term` is reachable from `term` via `parStar`. -/
theorem RawTerm.whnf_reaches : ∀ (fuel : Nat) {scope : Nat}
    (term : RawTerm scope),
    RawStep.parStar term (RawTerm.whnf fuel term)
  | 0, _, term => RawStep.parStar.refl term
  | fuel + 1, _, term => by
    cases term with
    | var _ => exact RawStep.parStar.refl _
    | unit => exact RawStep.parStar.refl _
    | lam _ => exact RawStep.parStar.refl _
    | app functionTerm argumentTerm =>
        -- whnf returns either β-contractum or .app whnf(fn) arg
        have functionChain : RawStep.parStar functionTerm
            (RawTerm.whnf fuel functionTerm) :=
          RawTerm.whnf_reaches fuel functionTerm
        match h : RawTerm.lamBody? (RawTerm.whnf fuel functionTerm) with
        | some body =>
            -- whnf reduces functionWhnf to .lam body, then β-fires
            have functionWhnfLam : RawTerm.whnf fuel functionTerm = .lam body :=
              RawTerm.eq_lam_of_lamBody?_eq_some _ h
            have functionStarLam : RawStep.parStar functionTerm (.lam body) :=
              functionWhnfLam ▸ functionChain
            have appStarLamApp : RawStep.parStar
                (.app functionTerm argumentTerm)
                (.app (.lam body) argumentTerm) :=
              RawStep.parStar.appLeft argumentTerm functionStarLam
            have betaStep : RawStep.par
                (.app (.lam body) argumentTerm)
                (body.subst0 argumentTerm) :=
              RawStep.par.betaApp (.refl _) (.refl _)
            have betaStar : RawStep.parStar
                (.app (.lam body) argumentTerm)
                (body.subst0 argumentTerm) :=
              RawStep.par.toStar betaStep
            have contractumChain : RawStep.parStar
                (body.subst0 argumentTerm)
                (RawTerm.whnf fuel (body.subst0 argumentTerm)) :=
              RawTerm.whnf_reaches fuel (body.subst0 argumentTerm)
            have appStarContractum : RawStep.parStar
                (.app functionTerm argumentTerm)
                (RawTerm.whnf fuel (body.subst0 argumentTerm)) :=
              RawStep.parStar.append
                (RawStep.parStar.append appStarLamApp betaStar)
                contractumChain
            -- Now show the goal: parStar (.app fn arg) (whnf (n+1) (.app fn arg))
            -- whnf (n+1) (.app fn arg) reduces via the match: since lamBody? = some body,
            -- it yields whnf fuel (body.subst0 arg).
            show RawStep.parStar (.app functionTerm argumentTerm)
                (RawTerm.whnf (fuel + 1) (.app functionTerm argumentTerm))
            simp only [RawTerm.whnf, h]
            exact appStarContractum
        | none =>
            -- whnf returns .app (whnf fuel fn) arg
            have appChain : RawStep.parStar
                (.app functionTerm argumentTerm)
                (.app (RawTerm.whnf fuel functionTerm) argumentTerm) :=
              RawStep.parStar.appLeft argumentTerm functionChain
            show RawStep.parStar (.app functionTerm argumentTerm)
                (RawTerm.whnf (fuel + 1) (.app functionTerm argumentTerm))
            simp only [RawTerm.whnf, h]
            exact appChain
    | pair _ _ => exact RawStep.parStar.refl _
    | fst pairTerm =>
        have pairChain : RawStep.parStar pairTerm
            (RawTerm.whnf fuel pairTerm) :=
          RawTerm.whnf_reaches fuel pairTerm
        match h : RawTerm.pairComponents? (RawTerm.whnf fuel pairTerm) with
        | some (firstValue, secondValue) =>
            have pairWhnfPair : RawTerm.whnf fuel pairTerm
                = .pair firstValue secondValue :=
              RawTerm.eq_pair_of_pairComponents?_eq_some _ h
            have pairStarPair : RawStep.parStar pairTerm
                (.pair firstValue secondValue) :=
              pairWhnfPair ▸ pairChain
            have fstStarFstPair : RawStep.parStar (.fst pairTerm)
                (.fst (.pair firstValue secondValue)) :=
              RawStep.parStar.fst pairStarPair
            have iotaStep : RawStep.par
                (.fst (.pair firstValue secondValue)) firstValue :=
              RawStep.par.betaFstPair secondValue (RawStep.par.refl firstValue)
            have iotaStar : RawStep.parStar
                (.fst (.pair firstValue secondValue)) firstValue :=
              RawStep.par.toStar iotaStep
            have firstChain : RawStep.parStar firstValue
                (RawTerm.whnf fuel firstValue) :=
              RawTerm.whnf_reaches fuel firstValue
            show RawStep.parStar (.fst pairTerm)
                (RawTerm.whnf (fuel + 1) (.fst pairTerm))
            simp only [RawTerm.whnf, h]
            exact RawStep.parStar.append
              (RawStep.parStar.append fstStarFstPair iotaStar) firstChain
        | none =>
            have fstChain : RawStep.parStar (.fst pairTerm)
                (.fst (RawTerm.whnf fuel pairTerm)) :=
              RawStep.parStar.fst pairChain
            show RawStep.parStar (.fst pairTerm)
                (RawTerm.whnf (fuel + 1) (.fst pairTerm))
            simp only [RawTerm.whnf, h]
            exact fstChain
    | snd pairTerm =>
        have pairChain : RawStep.parStar pairTerm
            (RawTerm.whnf fuel pairTerm) :=
          RawTerm.whnf_reaches fuel pairTerm
        match h : RawTerm.pairComponents? (RawTerm.whnf fuel pairTerm) with
        | some (firstValue, secondValue) =>
            have pairWhnfPair : RawTerm.whnf fuel pairTerm
                = .pair firstValue secondValue :=
              RawTerm.eq_pair_of_pairComponents?_eq_some _ h
            have pairStarPair : RawStep.parStar pairTerm
                (.pair firstValue secondValue) :=
              pairWhnfPair ▸ pairChain
            have sndStarSndPair : RawStep.parStar (.snd pairTerm)
                (.snd (.pair firstValue secondValue)) :=
              RawStep.parStar.snd pairStarPair
            have iotaStep : RawStep.par
                (.snd (.pair firstValue secondValue)) secondValue :=
              RawStep.par.betaSndPair firstValue (RawStep.par.refl secondValue)
            have iotaStar : RawStep.parStar
                (.snd (.pair firstValue secondValue)) secondValue :=
              RawStep.par.toStar iotaStep
            have secondChain : RawStep.parStar secondValue
                (RawTerm.whnf fuel secondValue) :=
              RawTerm.whnf_reaches fuel secondValue
            show RawStep.parStar (.snd pairTerm)
                (RawTerm.whnf (fuel + 1) (.snd pairTerm))
            simp only [RawTerm.whnf, h]
            exact RawStep.parStar.append
              (RawStep.parStar.append sndStarSndPair iotaStar) secondChain
        | none =>
            have sndChain : RawStep.parStar (.snd pairTerm)
                (.snd (RawTerm.whnf fuel pairTerm)) :=
              RawStep.parStar.snd pairChain
            show RawStep.parStar (.snd pairTerm)
                (RawTerm.whnf (fuel + 1) (.snd pairTerm))
            simp only [RawTerm.whnf, h]
            exact sndChain
    | boolTrue => exact RawStep.parStar.refl _
    | boolFalse => exact RawStep.parStar.refl _
    | boolElim scrutinee thenBranch elseBranch =>
        have scrutineeChain : RawStep.parStar scrutinee
            (RawTerm.whnf fuel scrutinee) :=
          RawTerm.whnf_reaches fuel scrutinee
        show RawStep.parStar (.boolElim scrutinee thenBranch elseBranch)
            (RawTerm.whnf (fuel + 1) (.boolElim scrutinee thenBranch elseBranch))
        simp only [RawTerm.whnf]
        cases hScrutineeWhnf : RawTerm.whnf fuel scrutinee with
        | boolTrue =>
            rw [hScrutineeWhnf] at scrutineeChain
            have thenChain : RawStep.parStar thenBranch
                (RawTerm.whnf fuel thenBranch) :=
              RawTerm.whnf_reaches fuel thenBranch
            have congStar : RawStep.parStar
                (.boolElim scrutinee thenBranch elseBranch)
                (.boolElim .boolTrue thenBranch elseBranch) :=
              RawStep.parStar.boolElimScrutinee thenBranch elseBranch scrutineeChain
            have iotaStep : RawStep.par
                (.boolElim .boolTrue thenBranch elseBranch) thenBranch :=
              RawStep.par.iotaBoolElimTrue elseBranch (RawStep.par.refl _)
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              thenChain
        | boolFalse =>
            rw [hScrutineeWhnf] at scrutineeChain
            have elseChain : RawStep.parStar elseBranch
                (RawTerm.whnf fuel elseBranch) :=
              RawTerm.whnf_reaches fuel elseBranch
            have congStar : RawStep.parStar
                (.boolElim scrutinee thenBranch elseBranch)
                (.boolElim .boolFalse thenBranch elseBranch) :=
              RawStep.parStar.boolElimScrutinee thenBranch elseBranch scrutineeChain
            have iotaStep : RawStep.par
                (.boolElim .boolFalse thenBranch elseBranch) elseBranch :=
              RawStep.par.iotaBoolElimFalse thenBranch (RawStep.par.refl _)
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              elseChain
        | var _ | unit | lam _ | app _ _ | pair _ _ | fst _ | snd _
        | boolElim _ _ _
        | natZero | natSucc _ | natElim _ _ _ | natRec _ _ _
        | listNil | listCons _ _ | listElim _ _ _
        | optionNone | optionSome _ | optionMatch _ _ _
        | eitherInl _ | eitherInr _ | eitherMatch _ _ _
        | refl _ | idJ _ _
        | modIntro _ | modElim _ | subsume _
        | interval0 | interval1 | intervalOpp _
        | intervalMeet _ _ | intervalJoin _ _
        | pathLam _ | pathApp _ _ | glueIntro _ _ | glueElim _
        | transp _ _ | transpFill _ _ _ | hcomp _ _
        | oeqRefl _ | oeqJ _ _ | oeqFunext _
        | idStrictRefl _ | idStrictRec _ _
        | equivIntro _ _ | equivApp _ _
        | refineIntro _ _ | refineElim _
        | recordIntro _ | recordProj _
        | codataUnfold _ _ | codataDest _
        | sessionSend _ _ | sessionRecv _
        | effectPerform _ _ | universeCode _
        | arrowCode _ _ | piTyCode _ _ | sigmaTyCode _ _
        | productCode _ _ | sumCode _ _
        | listCode _ | optionCode _ | eitherCode _ _
        | idCode _ _ _ | equivCode _ _ | cumulUpMarker _
        | uaToEquiv _ | equivApply _ _ | pathCompose _ _ | idToEquiv _
        | oeqTrans _ _ | equivCompose _ _ =>
            rw [hScrutineeWhnf] at scrutineeChain
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.boolElimScrutinee thenBranch elseBranch
                  scrutineeChain
    | natZero => exact RawStep.parStar.refl _
    | natSucc _ => exact RawStep.parStar.refl _
    | natElim scrutinee zeroBranch succBranch =>
        have scrutineeChain : RawStep.parStar scrutinee
            (RawTerm.whnf fuel scrutinee) :=
          RawTerm.whnf_reaches fuel scrutinee
        show RawStep.parStar (.natElim scrutinee zeroBranch succBranch)
            (RawTerm.whnf (fuel + 1) (.natElim scrutinee zeroBranch succBranch))
        simp only [RawTerm.whnf]
        cases hScrutineeWhnf : RawTerm.whnf fuel scrutinee with
        | natZero =>
            rw [hScrutineeWhnf] at scrutineeChain
            have zeroChain : RawStep.parStar zeroBranch
                (RawTerm.whnf fuel zeroBranch) :=
              RawTerm.whnf_reaches fuel zeroBranch
            have congStar : RawStep.parStar
                (.natElim scrutinee zeroBranch succBranch)
                (.natElim .natZero zeroBranch succBranch) :=
              RawStep.parStar.natElimScrutinee zeroBranch succBranch scrutineeChain
            have iotaStep : RawStep.par
                (.natElim .natZero zeroBranch succBranch) zeroBranch :=
              RawStep.par.iotaNatElimZero succBranch (RawStep.par.refl _)
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              zeroChain
        | natSucc predecessor =>
            rw [hScrutineeWhnf] at scrutineeChain
            have appChain : RawStep.parStar (.app succBranch predecessor)
                (RawTerm.whnf fuel (.app succBranch predecessor)) :=
              RawTerm.whnf_reaches fuel (.app succBranch predecessor)
            have congStar : RawStep.parStar
                (.natElim scrutinee zeroBranch succBranch)
                (.natElim (.natSucc predecessor) zeroBranch succBranch) :=
              RawStep.parStar.natElimScrutinee zeroBranch succBranch scrutineeChain
            have iotaStep : RawStep.par
                (.natElim (.natSucc predecessor) zeroBranch succBranch)
                (.app succBranch predecessor) :=
              RawStep.par.iotaNatElimSucc zeroBranch
                (RawStep.par.refl _) (RawStep.par.refl _)
            simp only [RawTerm.headCtor, RawTerm.natSuccPred?]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              appChain
        | var _ | unit | lam _ | app _ _ | pair _ _ | fst _ | snd _
        | boolTrue | boolFalse | boolElim _ _ _
        | natElim _ _ _ | natRec _ _ _
        | listNil | listCons _ _ | listElim _ _ _
        | optionNone | optionSome _ | optionMatch _ _ _
        | eitherInl _ | eitherInr _ | eitherMatch _ _ _
        | refl _ | idJ _ _
        | modIntro _ | modElim _ | subsume _
        | interval0 | interval1 | intervalOpp _
        | intervalMeet _ _ | intervalJoin _ _
        | pathLam _ | pathApp _ _ | glueIntro _ _ | glueElim _
        | transp _ _ | transpFill _ _ _ | hcomp _ _
        | oeqRefl _ | oeqJ _ _ | oeqFunext _
        | idStrictRefl _ | idStrictRec _ _
        | equivIntro _ _ | equivApp _ _
        | refineIntro _ _ | refineElim _
        | recordIntro _ | recordProj _
        | codataUnfold _ _ | codataDest _
        | sessionSend _ _ | sessionRecv _
        | effectPerform _ _ | universeCode _
        | arrowCode _ _ | piTyCode _ _ | sigmaTyCode _ _
        | productCode _ _ | sumCode _ _
        | listCode _ | optionCode _ | eitherCode _ _
        | idCode _ _ _ | equivCode _ _ | cumulUpMarker _
        | uaToEquiv _ | equivApply _ _ | pathCompose _ _ | idToEquiv _
        | oeqTrans _ _ | equivCompose _ _ =>
            rw [hScrutineeWhnf] at scrutineeChain
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.natElimScrutinee zeroBranch succBranch
                  scrutineeChain
    | natRec scrutinee zeroBranch succBranch =>
        have scrutineeChain : RawStep.parStar scrutinee
            (RawTerm.whnf fuel scrutinee) :=
          RawTerm.whnf_reaches fuel scrutinee
        show RawStep.parStar (.natRec scrutinee zeroBranch succBranch)
            (RawTerm.whnf (fuel + 1) (.natRec scrutinee zeroBranch succBranch))
        simp only [RawTerm.whnf]
        cases hScrutineeWhnf : RawTerm.whnf fuel scrutinee with
        | natZero =>
            rw [hScrutineeWhnf] at scrutineeChain
            have zeroChain : RawStep.parStar zeroBranch
                (RawTerm.whnf fuel zeroBranch) :=
              RawTerm.whnf_reaches fuel zeroBranch
            have congStar : RawStep.parStar
                (.natRec scrutinee zeroBranch succBranch)
                (.natRec .natZero zeroBranch succBranch) :=
              RawStep.parStar.natRecScrutinee zeroBranch succBranch scrutineeChain
            have iotaStep : RawStep.par
                (.natRec .natZero zeroBranch succBranch) zeroBranch :=
              RawStep.par.iotaNatRecZero succBranch (RawStep.par.refl _)
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              zeroChain
        | natSucc predecessor =>
            rw [hScrutineeWhnf] at scrutineeChain
            have contractumChain : RawStep.parStar
                (.app (.app succBranch predecessor)
                      (.natRec predecessor zeroBranch succBranch))
                (RawTerm.whnf fuel
                  (.app (.app succBranch predecessor)
                        (.natRec predecessor zeroBranch succBranch))) :=
              RawTerm.whnf_reaches fuel _
            have congStar : RawStep.parStar
                (.natRec scrutinee zeroBranch succBranch)
                (.natRec (.natSucc predecessor) zeroBranch succBranch) :=
              RawStep.parStar.natRecScrutinee zeroBranch succBranch scrutineeChain
            have iotaStep : RawStep.par
                (.natRec (.natSucc predecessor) zeroBranch succBranch)
                (.app (.app succBranch predecessor)
                      (.natRec predecessor zeroBranch succBranch)) :=
              RawStep.par.iotaNatRecSucc
                (RawStep.par.refl _) (RawStep.par.refl _) (RawStep.par.refl _)
            simp only [RawTerm.headCtor, RawTerm.natSuccPred?]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              contractumChain
        | var _ | unit | lam _ | app _ _ | pair _ _ | fst _ | snd _
        | boolTrue | boolFalse | boolElim _ _ _
        | natElim _ _ _ | natRec _ _ _
        | listNil | listCons _ _ | listElim _ _ _
        | optionNone | optionSome _ | optionMatch _ _ _
        | eitherInl _ | eitherInr _ | eitherMatch _ _ _
        | refl _ | idJ _ _
        | modIntro _ | modElim _ | subsume _
        | interval0 | interval1 | intervalOpp _
        | intervalMeet _ _ | intervalJoin _ _
        | pathLam _ | pathApp _ _ | glueIntro _ _ | glueElim _
        | transp _ _ | transpFill _ _ _ | hcomp _ _
        | oeqRefl _ | oeqJ _ _ | oeqFunext _
        | idStrictRefl _ | idStrictRec _ _
        | equivIntro _ _ | equivApp _ _
        | refineIntro _ _ | refineElim _
        | recordIntro _ | recordProj _
        | codataUnfold _ _ | codataDest _
        | sessionSend _ _ | sessionRecv _
        | effectPerform _ _ | universeCode _
        | arrowCode _ _ | piTyCode _ _ | sigmaTyCode _ _
        | productCode _ _ | sumCode _ _
        | listCode _ | optionCode _ | eitherCode _ _
        | idCode _ _ _ | equivCode _ _ | cumulUpMarker _
        | uaToEquiv _ | equivApply _ _ | pathCompose _ _ | idToEquiv _
        | oeqTrans _ _ | equivCompose _ _ =>
            rw [hScrutineeWhnf] at scrutineeChain
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.natRecScrutinee zeroBranch succBranch
                  scrutineeChain
    | listNil => exact RawStep.parStar.refl _
    | listCons _ _ => exact RawStep.parStar.refl _
    | listElim scrutinee nilBranch consBranch =>
        have scrutineeChain : RawStep.parStar scrutinee
            (RawTerm.whnf fuel scrutinee) :=
          RawTerm.whnf_reaches fuel scrutinee
        show RawStep.parStar (.listElim scrutinee nilBranch consBranch)
            (RawTerm.whnf (fuel + 1) (.listElim scrutinee nilBranch consBranch))
        simp only [RawTerm.whnf]
        cases hScrutineeWhnf : RawTerm.whnf fuel scrutinee with
        | listNil =>
            rw [hScrutineeWhnf] at scrutineeChain
            have nilChain : RawStep.parStar nilBranch
                (RawTerm.whnf fuel nilBranch) :=
              RawTerm.whnf_reaches fuel nilBranch
            have congStar : RawStep.parStar
                (.listElim scrutinee nilBranch consBranch)
                (.listElim .listNil nilBranch consBranch) :=
              RawStep.parStar.listElimScrutinee nilBranch consBranch scrutineeChain
            have iotaStep : RawStep.par
                (.listElim .listNil nilBranch consBranch) nilBranch :=
              RawStep.par.iotaListElimNil consBranch (RawStep.par.refl _)
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              nilChain
        | listCons headTerm tailTerm =>
            rw [hScrutineeWhnf] at scrutineeChain
            have appChain : RawStep.parStar
                (.app (.app consBranch headTerm) tailTerm)
                (RawTerm.whnf fuel (.app (.app consBranch headTerm) tailTerm)) :=
              RawTerm.whnf_reaches fuel _
            have congStar : RawStep.parStar
                (.listElim scrutinee nilBranch consBranch)
                (.listElim (.listCons headTerm tailTerm) nilBranch consBranch) :=
              RawStep.parStar.listElimScrutinee nilBranch consBranch scrutineeChain
            have iotaStep : RawStep.par
                (.listElim (.listCons headTerm tailTerm) nilBranch consBranch)
                (.app (.app consBranch headTerm) tailTerm) :=
              RawStep.par.iotaListElimCons nilBranch
                (RawStep.par.refl _) (RawStep.par.refl _) (RawStep.par.refl _)
            simp only [RawTerm.headCtor, RawTerm.listConsParts?]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              appChain
        | var _ | unit | lam _ | app _ _ | pair _ _ | fst _ | snd _
        | boolTrue | boolFalse | boolElim _ _ _
        | natZero | natSucc _ | natElim _ _ _ | natRec _ _ _
        | listElim _ _ _
        | optionNone | optionSome _ | optionMatch _ _ _
        | eitherInl _ | eitherInr _ | eitherMatch _ _ _
        | refl _ | idJ _ _
        | modIntro _ | modElim _ | subsume _
        | interval0 | interval1 | intervalOpp _
        | intervalMeet _ _ | intervalJoin _ _
        | pathLam _ | pathApp _ _ | glueIntro _ _ | glueElim _
        | transp _ _ | transpFill _ _ _ | hcomp _ _
        | oeqRefl _ | oeqJ _ _ | oeqFunext _
        | idStrictRefl _ | idStrictRec _ _
        | equivIntro _ _ | equivApp _ _
        | refineIntro _ _ | refineElim _
        | recordIntro _ | recordProj _
        | codataUnfold _ _ | codataDest _
        | sessionSend _ _ | sessionRecv _
        | effectPerform _ _ | universeCode _
        | arrowCode _ _ | piTyCode _ _ | sigmaTyCode _ _
        | productCode _ _ | sumCode _ _
        | listCode _ | optionCode _ | eitherCode _ _
        | idCode _ _ _ | equivCode _ _ | cumulUpMarker _
        | uaToEquiv _ | equivApply _ _ | pathCompose _ _ | idToEquiv _
        | oeqTrans _ _ | equivCompose _ _ =>
            rw [hScrutineeWhnf] at scrutineeChain
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.listElimScrutinee nilBranch consBranch
                  scrutineeChain
    | optionNone => exact RawStep.parStar.refl _
    | optionSome _ => exact RawStep.parStar.refl _
    | optionMatch scrutinee noneBranch someBranch =>
        have scrutineeChain : RawStep.parStar scrutinee
            (RawTerm.whnf fuel scrutinee) :=
          RawTerm.whnf_reaches fuel scrutinee
        show RawStep.parStar (.optionMatch scrutinee noneBranch someBranch)
            (RawTerm.whnf (fuel + 1) (.optionMatch scrutinee noneBranch someBranch))
        simp only [RawTerm.whnf]
        cases hScrutineeWhnf : RawTerm.whnf fuel scrutinee with
        | optionNone =>
            rw [hScrutineeWhnf] at scrutineeChain
            have noneChain : RawStep.parStar noneBranch
                (RawTerm.whnf fuel noneBranch) :=
              RawTerm.whnf_reaches fuel noneBranch
            have congStar : RawStep.parStar
                (.optionMatch scrutinee noneBranch someBranch)
                (.optionMatch .optionNone noneBranch someBranch) :=
              RawStep.parStar.optionMatchScrutinee noneBranch someBranch
                scrutineeChain
            have iotaStep : RawStep.par
                (.optionMatch .optionNone noneBranch someBranch) noneBranch :=
              RawStep.par.iotaOptionMatchNone someBranch (RawStep.par.refl _)
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              noneChain
        | optionSome valueTerm =>
            rw [hScrutineeWhnf] at scrutineeChain
            have appChain : RawStep.parStar (.app someBranch valueTerm)
                (RawTerm.whnf fuel (.app someBranch valueTerm)) :=
              RawTerm.whnf_reaches fuel _
            have congStar : RawStep.parStar
                (.optionMatch scrutinee noneBranch someBranch)
                (.optionMatch (.optionSome valueTerm) noneBranch someBranch) :=
              RawStep.parStar.optionMatchScrutinee noneBranch someBranch
                scrutineeChain
            have iotaStep : RawStep.par
                (.optionMatch (.optionSome valueTerm) noneBranch someBranch)
                (.app someBranch valueTerm) :=
              RawStep.par.iotaOptionMatchSome noneBranch
                (RawStep.par.refl _) (RawStep.par.refl _)
            simp only [RawTerm.headCtor, RawTerm.optionSomeValue?]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              appChain
        | var _ | unit | lam _ | app _ _ | pair _ _ | fst _ | snd _
        | boolTrue | boolFalse | boolElim _ _ _
        | natZero | natSucc _ | natElim _ _ _ | natRec _ _ _
        | listNil | listCons _ _ | listElim _ _ _
        | optionMatch _ _ _
        | eitherInl _ | eitherInr _ | eitherMatch _ _ _
        | refl _ | idJ _ _
        | modIntro _ | modElim _ | subsume _
        | interval0 | interval1 | intervalOpp _
        | intervalMeet _ _ | intervalJoin _ _
        | pathLam _ | pathApp _ _ | glueIntro _ _ | glueElim _
        | transp _ _ | transpFill _ _ _ | hcomp _ _
        | oeqRefl _ | oeqJ _ _ | oeqFunext _
        | idStrictRefl _ | idStrictRec _ _
        | equivIntro _ _ | equivApp _ _
        | refineIntro _ _ | refineElim _
        | recordIntro _ | recordProj _
        | codataUnfold _ _ | codataDest _
        | sessionSend _ _ | sessionRecv _
        | effectPerform _ _ | universeCode _
        | arrowCode _ _ | piTyCode _ _ | sigmaTyCode _ _
        | productCode _ _ | sumCode _ _
        | listCode _ | optionCode _ | eitherCode _ _
        | idCode _ _ _ | equivCode _ _ | cumulUpMarker _
        | uaToEquiv _ | equivApply _ _ | pathCompose _ _ | idToEquiv _
        | oeqTrans _ _ | equivCompose _ _ =>
            rw [hScrutineeWhnf] at scrutineeChain
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.optionMatchScrutinee noneBranch someBranch
                  scrutineeChain
    | eitherInl _ => exact RawStep.parStar.refl _
    | eitherInr _ => exact RawStep.parStar.refl _
    | eitherMatch scrutinee leftBranch rightBranch =>
        have scrutineeChain : RawStep.parStar scrutinee
            (RawTerm.whnf fuel scrutinee) :=
          RawTerm.whnf_reaches fuel scrutinee
        show RawStep.parStar (.eitherMatch scrutinee leftBranch rightBranch)
            (RawTerm.whnf (fuel + 1)
              (.eitherMatch scrutinee leftBranch rightBranch))
        simp only [RawTerm.whnf]
        cases hScrutineeWhnf : RawTerm.whnf fuel scrutinee with
        | eitherInl valueTerm =>
            rw [hScrutineeWhnf] at scrutineeChain
            have appChain : RawStep.parStar (.app leftBranch valueTerm)
                (RawTerm.whnf fuel (.app leftBranch valueTerm)) :=
              RawTerm.whnf_reaches fuel _
            have congStar : RawStep.parStar
                (.eitherMatch scrutinee leftBranch rightBranch)
                (.eitherMatch (.eitherInl valueTerm) leftBranch rightBranch) :=
              RawStep.parStar.eitherMatchScrutinee leftBranch rightBranch
                scrutineeChain
            have iotaStep : RawStep.par
                (.eitherMatch (.eitherInl valueTerm) leftBranch rightBranch)
                (.app leftBranch valueTerm) :=
              RawStep.par.iotaEitherMatchInl rightBranch
                (RawStep.par.refl _) (RawStep.par.refl _)
            simp only [RawTerm.headCtor, RawTerm.eitherInlValue?]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              appChain
        | eitherInr valueTerm =>
            rw [hScrutineeWhnf] at scrutineeChain
            have appChain : RawStep.parStar (.app rightBranch valueTerm)
                (RawTerm.whnf fuel (.app rightBranch valueTerm)) :=
              RawTerm.whnf_reaches fuel _
            have congStar : RawStep.parStar
                (.eitherMatch scrutinee leftBranch rightBranch)
                (.eitherMatch (.eitherInr valueTerm) leftBranch rightBranch) :=
              RawStep.parStar.eitherMatchScrutinee leftBranch rightBranch
                scrutineeChain
            have iotaStep : RawStep.par
                (.eitherMatch (.eitherInr valueTerm) leftBranch rightBranch)
                (.app rightBranch valueTerm) :=
              RawStep.par.iotaEitherMatchInr leftBranch
                (RawStep.par.refl _) (RawStep.par.refl _)
            simp only [RawTerm.headCtor, RawTerm.eitherInrValue?]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              appChain
        | var _ | unit | lam _ | app _ _ | pair _ _ | fst _ | snd _
        | boolTrue | boolFalse | boolElim _ _ _
        | natZero | natSucc _ | natElim _ _ _ | natRec _ _ _
        | listNil | listCons _ _ | listElim _ _ _
        | optionNone | optionSome _ | optionMatch _ _ _
        | eitherMatch _ _ _
        | refl _ | idJ _ _
        | modIntro _ | modElim _ | subsume _
        | interval0 | interval1 | intervalOpp _
        | intervalMeet _ _ | intervalJoin _ _
        | pathLam _ | pathApp _ _ | glueIntro _ _ | glueElim _
        | transp _ _ | transpFill _ _ _ | hcomp _ _
        | oeqRefl _ | oeqJ _ _ | oeqFunext _
        | idStrictRefl _ | idStrictRec _ _
        | equivIntro _ _ | equivApp _ _
        | refineIntro _ _ | refineElim _
        | recordIntro _ | recordProj _
        | codataUnfold _ _ | codataDest _
        | sessionSend _ _ | sessionRecv _
        | effectPerform _ _ | universeCode _
        | arrowCode _ _ | piTyCode _ _ | sigmaTyCode _ _
        | productCode _ _ | sumCode _ _
        | listCode _ | optionCode _ | eitherCode _ _
        | idCode _ _ _ | equivCode _ _ | cumulUpMarker _
        | uaToEquiv _ | equivApply _ _ | pathCompose _ _ | idToEquiv _
        | oeqTrans _ _ | equivCompose _ _ =>
            rw [hScrutineeWhnf] at scrutineeChain
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.eitherMatchScrutinee leftBranch rightBranch
                  scrutineeChain
    | refl _ => exact RawStep.parStar.refl _
    | idJ baseCase witness =>
        have witnessChain : RawStep.parStar witness
            (RawTerm.whnf fuel witness) :=
          RawTerm.whnf_reaches fuel witness
        show RawStep.parStar (.idJ baseCase witness)
            (RawTerm.whnf (fuel + 1) (.idJ baseCase witness))
        simp only [RawTerm.whnf]
        cases hWitnessWhnf : RawTerm.whnf fuel witness with
        | refl rawWitness =>
            rw [hWitnessWhnf] at witnessChain
            have baseChain : RawStep.parStar baseCase
                (RawTerm.whnf fuel baseCase) :=
              RawTerm.whnf_reaches fuel baseCase
            have congStar : RawStep.parStar (.idJ baseCase witness)
                (.idJ baseCase (.refl rawWitness)) :=
              RawStep.parStar.idJWitness baseCase witnessChain
            have iotaStep : RawStep.par
                (.idJ baseCase (.refl rawWitness)) baseCase :=
              RawStep.par.iotaIdJRefl rawWitness (RawStep.par.refl _)
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.append
              (RawStep.parStar.append congStar (RawStep.par.toStar iotaStep))
              baseChain
        | var _ | unit | lam _ | app _ _ | pair _ _ | fst _ | snd _
        | boolTrue | boolFalse | boolElim _ _ _
        | natZero | natSucc _ | natElim _ _ _ | natRec _ _ _
        | listNil | listCons _ _ | listElim _ _ _
        | optionNone | optionSome _ | optionMatch _ _ _
        | eitherInl _ | eitherInr _ | eitherMatch _ _ _
        | idJ _ _
        | modIntro _ | modElim _ | subsume _
        | interval0 | interval1 | intervalOpp _
        | intervalMeet _ _ | intervalJoin _ _
        | pathLam _ | pathApp _ _ | glueIntro _ _ | glueElim _
        | transp _ _ | transpFill _ _ _ | hcomp _ _
        | oeqRefl _ | oeqJ _ _ | oeqFunext _
        | idStrictRefl _ | idStrictRec _ _
        | equivIntro _ _ | equivApp _ _
        | refineIntro _ _ | refineElim _
        | recordIntro _ | recordProj _
        | codataUnfold _ _ | codataDest _
        | sessionSend _ _ | sessionRecv _
        | effectPerform _ _ | universeCode _
        | arrowCode _ _ | piTyCode _ _ | sigmaTyCode _ _
        | productCode _ _ | sumCode _ _
        | listCode _ | optionCode _ | eitherCode _ _
        | idCode _ _ _ | equivCode _ _ | cumulUpMarker _
        | uaToEquiv _ | equivApply _ _ | pathCompose _ _ | idToEquiv _
        | oeqTrans _ _ | equivCompose _ _ =>
            rw [hWitnessWhnf] at witnessChain
            simp only [RawTerm.headCtor]
            exact RawStep.parStar.idJWitness baseCase witnessChain
    | modIntro _ => exact RawStep.parStar.refl _
    | modElim _ => exact RawStep.parStar.refl _
    | subsume _ => exact RawStep.parStar.refl _
    -- D1.6: 27 new ctors are pure cong at raw level — no β/ι rule
    -- fires in whnf, so whnf returns the term unchanged.
    | interval0 => exact RawStep.parStar.refl _
    | interval1 => exact RawStep.parStar.refl _
    | intervalOpp _ => exact RawStep.parStar.refl _
    | intervalMeet _ _ => exact RawStep.parStar.refl _
    | intervalJoin _ _ => exact RawStep.parStar.refl _
    | pathLam _ => exact RawStep.parStar.refl _
    | pathApp _ _ => exact RawStep.parStar.refl _
    | glueIntro _ _ => exact RawStep.parStar.refl _
    | glueElim _ => exact RawStep.parStar.refl _
    | transp _ _ => exact RawStep.parStar.refl _
    | transpFill _ _ _ => exact RawStep.parStar.refl _
    | hcomp _ _ => exact RawStep.parStar.refl _
    | oeqRefl _ => exact RawStep.parStar.refl _
    | oeqJ _ _ => exact RawStep.parStar.refl _
    | oeqFunext _ => exact RawStep.parStar.refl _
    | idStrictRefl _ => exact RawStep.parStar.refl _
    | idStrictRec _ _ => exact RawStep.parStar.refl _
    | equivIntro _ _ => exact RawStep.parStar.refl _
    | equivApp _ _ => exact RawStep.parStar.refl _
    | refineIntro _ _ => exact RawStep.parStar.refl _
    | refineElim _ => exact RawStep.parStar.refl _
    | recordIntro _ => exact RawStep.parStar.refl _
    | recordProj _ => exact RawStep.parStar.refl _
    | codataUnfold _ _ => exact RawStep.parStar.refl _
    | codataDest _ => exact RawStep.parStar.refl _
    | sessionSend _ _ => exact RawStep.parStar.refl _
    | sessionRecv _ => exact RawStep.parStar.refl _
    | effectPerform _ _ => exact RawStep.parStar.refl _
    | universeCode _ => exact RawStep.parStar.refl _
    -- CUMUL-2.1 per-shape type codes — canonical, no β/ι, refl.
    | arrowCode _ _ => exact RawStep.parStar.refl _
    | piTyCode _ _ => exact RawStep.parStar.refl _
    | sigmaTyCode _ _ => exact RawStep.parStar.refl _
    | productCode _ _ => exact RawStep.parStar.refl _
    | sumCode _ _ => exact RawStep.parStar.refl _
    | listCode _ => exact RawStep.parStar.refl _
    | optionCode _ => exact RawStep.parStar.refl _
    | eitherCode _ _ => exact RawStep.parStar.refl _
    | idCode _ _ _ => exact RawStep.parStar.refl _
    | equivCode _ _ => exact RawStep.parStar.refl _
    -- CUMUL-2.6: cumulUpMarker — canonical, no β/ι, refl.
    | cumulUpMarker _ => exact RawStep.parStar.refl _
    -- D3.6-P1: uaToEquiv — vocabulary-only, no β/ι, refl.
    | uaToEquiv _ => exact RawStep.parStar.refl _
    -- D3.6-P2: equivApply — vocabulary-only, no β/ι, refl.
    | equivApply _ _ => exact RawStep.parStar.refl _
    -- D3.6-S3: pathCompose — vocabulary-only, no β/ι, refl.
    -- The β rule fires under transp, not inside pathCompose itself.
    | pathCompose _ _ => exact RawStep.parStar.refl _
    -- D3.6-S4: idToEquiv — vocabulary-only, no β/ι, refl.
    -- The β rule fires through cdIdToEquivCase, not inside idToEquiv
    -- itself.
    | idToEquiv _ => exact RawStep.parStar.refl _
    -- D3.6-S5: oeqTrans — vocabulary-only, no β/ι, refl.
    -- The β rule fires through cdIdToEquivCase's oeqTrans arm.
    | oeqTrans _ _ => exact RawStep.parStar.refl _
    -- D3.6-S5: equivCompose — vocabulary-only, no β/ι, refl.
    -- This ctor is the contractum target of the compose-β rule.
    | equivCompose _ _ => exact RawStep.parStar.refl _

end LeanFX2
