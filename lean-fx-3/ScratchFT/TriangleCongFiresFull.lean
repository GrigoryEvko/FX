import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.ParStepSubstPointwise

namespace FX1Poly.Core

open Foundation

theorem ParStep.triangleCongFires {scope : Nat} (gen : Generator) (payload : gen.payload scope)
    {children children' : RawTermChildren gen.binderShifts scope}
    (childrenStep : ParStepChildren children children')
    (ihChildren : ParStepChildren children' (RawTerm.completeDevelopmentChildren children))
    {reduct : RawTerm scope}
    (hfire : RawTerm.fireRootRedex gen payload children = some reduct) :
    ParStep (.mkGen gen payload children')
      (RawTerm.fireRootRedexOrSelf gen payload (RawTerm.completeDevelopmentChildren children)) := by
  by_cases hApp : gen = .gen_app
  · subst hApp
    cases childrenStep with
    | cons funcStep tailStep => cases tailStep with
      | cons argStep tailNil => cases tailNil with
        | nil =>
            cases ihChildren with
            | cons ihFunc ihTail => cases ihTail with
              | cons ihArg ihNil => cases ihNil with
                | nil =>
                    rename_i func _func' _arg _arg'
                    cases func with
                    | mkGen ig ip ic =>
                        by_cases hLam : ig = .gen_lam
                        · subst hLam
                          cases ic with | childCons body icNil => cases icNil with
                            | childNil =>
                                cases funcStep with
                                | cong _ _ csF => cases csF with
                                  | cons _bs rF => cases rF with
                                    | nil =>
                                        cases ihFunc with
                                        | cong _ _ csI => cases csI with
                                          | cons bodyDevStep rI => cases rI with
                                            | nil => exact ParStep.beta bodyDevStep ihArg
                        · have key : RawTerm.fireRootRedex .gen_app payload
                              (.childCons (.mkGen ig ip ic) (.childCons _arg .childNil)) = none :=
                            dif_neg hLam
                          rw [key] at hfire; nomatch hfire
  · by_cases hBoolElim : gen = .gen_boolElim
    · subst hBoolElim
      cases childrenStep with
      | cons scrutStep tailStep => cases tailStep with
        | cons _thenStep tail2 => cases tail2 with
          | cons _elseStep tailNil => cases tailNil with
            | nil =>
                cases ihChildren with
                | cons _ihScrut ihTail => cases ihTail with
                  | cons ihThen ihTail2 => cases ihTail2 with
                    | cons ihElse ihNil => cases ihNil with
                      | nil =>
                          rename_i scrut _scrut' thenB _thenB' elseB _elseB'
                          cases scrut with
                          | mkGen sg sp sc =>
                              by_cases hTrue : sg = .gen_boolTrue
                              · subst hTrue
                                cases sc with | childNil =>
                                    cases scrutStep with
                                    | cong _ _ csS => cases csS with
                                      | nil => exact ParStep.iotaBoolTrue ihThen
                              · by_cases hFalse : sg = .gen_boolFalse
                                · subst hFalse
                                  cases sc with | childNil =>
                                      cases scrutStep with
                                      | cong _ _ csS => cases csS with
                                        | nil => exact ParStep.iotaBoolFalse ihElse
                                · have key : RawTerm.fireRootRedex .gen_boolElim payload
                                      (.childCons (.mkGen sg sp sc)
                                        (.childCons thenB (.childCons elseB .childNil))) = none :=
                                    (if_neg hTrue).trans (if_neg hFalse)
                                  rw [key] at hfire; nomatch hfire
    · by_cases hFst : gen = .gen_fst
      · subst hFst
        cases childrenStep with
        | cons pairStep tailNil => cases tailNil with
          | nil =>
              cases ihChildren with
              | cons ihPair ihNil => cases ihNil with
                | nil =>
                    rename_i pairC _pairC'
                    cases pairC with
                    | mkGen pg pp pc =>
                        by_cases hPair : pg = .gen_pair
                        · subst hPair
                          cases pc with | childCons _first pcTail => cases pcTail with
                            | childCons _second pcNil => cases pcNil with
                              | childNil =>
                                  cases pairStep with
                                  | cong _ _ csP => cases csP with
                                    | cons _fs rP => cases rP with
                                      | cons _ss rP2 => cases rP2 with
                                        | nil =>
                                            cases ihPair with
                                            | cong _ _ csI => cases csI with
                                              | cons firstDev rI => cases rI with
                                                | cons _secondDev rI2 => cases rI2 with
                                                  | nil => exact ParStep.iotaFstPair firstDev
                        · have key : RawTerm.fireRootRedex .gen_fst payload
                              (.childCons (.mkGen pg pp pc) .childNil) = none := dif_neg hPair
                          rw [key] at hfire; nomatch hfire
      · by_cases hSnd : gen = .gen_snd
        · subst hSnd
          cases childrenStep with
          | cons pairStep tailNil => cases tailNil with
            | nil =>
                cases ihChildren with
                | cons ihPair ihNil => cases ihNil with
                  | nil =>
                      rename_i pairC _pairC'
                      cases pairC with
                      | mkGen pg pp pc =>
                          by_cases hPair : pg = .gen_pair
                          · subst hPair
                            cases pc with | childCons _first pcTail => cases pcTail with
                              | childCons _second pcNil => cases pcNil with
                                | childNil =>
                                    cases pairStep with
                                    | cong _ _ csP => cases csP with
                                      | cons _fs rP => cases rP with
                                        | cons _ss rP2 => cases rP2 with
                                          | nil =>
                                              cases ihPair with
                                              | cong _ _ csI => cases csI with
                                                | cons _firstDev rI => cases rI with
                                                  | cons secondDev rI2 => cases rI2 with
                                                    | nil => exact ParStep.iotaSndPair secondDev
                          · have key : RawTerm.fireRootRedex .gen_snd payload
                                (.childCons (.mkGen pg pp pc) .childNil) = none := dif_neg hPair
                            rw [key] at hfire; nomatch hfire
        · by_cases hNatElim : gen = .gen_natElim
          · subst hNatElim
            cases childrenStep with
            | cons scrutStep tailStep => cases tailStep with
              | cons _zeroStep tail2 => cases tail2 with
                | cons _succStep tailNil => cases tailNil with
                  | nil =>
                      cases ihChildren with
                      | cons ihScrut ihTail => cases ihTail with
                        | cons ihZero ihTail2 => cases ihTail2 with
                          | cons ihSucc ihNil => cases ihNil with
                            | nil =>
                                rename_i scrut _scrut' zeroB _zeroB' succB _succB'
                                cases scrut with
                                | mkGen sg sp sc =>
                                    by_cases hZero : sg = .gen_natZero
                                    · subst hZero
                                      cases sc with | childNil =>
                                          cases scrutStep with
                                          | cong _ _ csS => cases csS with
                                            | nil => exact ParStep.iotaNatElimZero ihZero
                                    · by_cases hSucc : sg = .gen_natSucc
                                      · subst hSucc
                                        cases sc with | childCons _pred scNil => cases scNil with
                                          | childNil =>
                                              cases scrutStep with
                                              | cong _ _ csS => cases csS with
                                                | cons _ps rS => cases rS with
                                                  | nil =>
                                                      cases ihScrut with
                                                      | cong _ _ csI => cases csI with
                                                        | cons predDevStep rI => cases rI with
                                                          | nil =>
                                                              exact ParStep.iotaNatElimSucc predDevStep ihZero ihSucc
                                      · have key : RawTerm.fireRootRedex .gen_natElim payload
                                            (.childCons (.mkGen sg sp sc)
                                              (.childCons zeroB (.childCons succB .childNil))) = none :=
                                          (if_neg hZero).trans (dif_neg hSucc)
                                        rw [key] at hfire; nomatch hfire
          · by_cases hNatRec : gen = .gen_natRec
            · subst hNatRec
              cases childrenStep with
              | cons scrutStep tailStep => cases tailStep with
                | cons _zeroStep tail2 => cases tail2 with
                  | cons _succStep tailNil => cases tailNil with
                    | nil =>
                        cases ihChildren with
                        | cons ihScrut ihTail => cases ihTail with
                          | cons ihZero ihTail2 => cases ihTail2 with
                            | cons ihSucc ihNil => cases ihNil with
                              | nil =>
                                  rename_i scrut _scrut' zeroB _zeroB' succB _succB'
                                  cases scrut with
                                  | mkGen sg sp sc =>
                                      by_cases hZero : sg = .gen_natZero
                                      · subst hZero
                                        cases sc with | childNil =>
                                            cases scrutStep with
                                            | cong _ _ csS => cases csS with
                                              | nil => exact ParStep.iotaNatRecZero ihZero
                                      · by_cases hSucc : sg = .gen_natSucc
                                        · subst hSucc
                                          cases sc with | childCons _pred scNil => cases scNil with
                                            | childNil =>
                                                cases scrutStep with
                                                | cong _ _ csS => cases csS with
                                                  | cons _ps rS => cases rS with
                                                    | nil =>
                                                        cases ihScrut with
                                                        | cong _ _ csI => cases csI with
                                                          | cons predDevStep rI => cases rI with
                                                            | nil =>
                                                                exact ParStep.iotaNatRecSucc predDevStep ihZero ihSucc
                                        · have key : RawTerm.fireRootRedex .gen_natRec payload
                                              (.childCons (.mkGen sg sp sc)
                                                (.childCons zeroB (.childCons succB .childNil))) = none :=
                                            (if_neg hZero).trans (dif_neg hSucc)
                                          rw [key] at hfire; nomatch hfire
            · by_cases hListElim : gen = .gen_listElim
              · subst hListElim
                cases childrenStep with
                | cons scrutStep tailStep => cases tailStep with
                  | cons _nilStep tail2 => cases tail2 with
                    | cons _consStep tailNil => cases tailNil with
                      | nil =>
                          cases ihChildren with
                          | cons ihScrut ihTail => cases ihTail with
                            | cons ihNilBranch ihTail2 => cases ihTail2 with
                              | cons ihConsBranch ihNil => cases ihNil with
                                | nil =>
                                    rename_i scrut _scrut' nilB _nilB' consB _consB'
                                    cases scrut with
                                    | mkGen sg sp sc =>
                                        by_cases hNil : sg = .gen_listNil
                                        · subst hNil
                                          cases sc with | childNil =>
                                              cases scrutStep with
                                              | cong _ _ csS => cases csS with
                                                | nil => exact ParStep.iotaListElimNil ihNilBranch
                                        · by_cases hCons : sg = .gen_listCons
                                          · subst hCons
                                            cases sc with | childCons _head scTail => cases scTail with
                                              | childCons _tail scNil => cases scNil with
                                                | childNil =>
                                                    cases scrutStep with
                                                    | cong _ _ csS => cases csS with
                                                      | cons _hs rS => cases rS with
                                                        | cons _ts rS2 => cases rS2 with
                                                          | nil =>
                                                              cases ihScrut with
                                                              | cong _ _ csI => cases csI with
                                                                | cons headDevStep rI => cases rI with
                                                                  | cons tailDevStep rI2 => cases rI2 with
                                                                    | nil =>
                                                                        exact ParStep.iotaListElimCons
                                                                          headDevStep tailDevStep
                                                                          ihNilBranch ihConsBranch
                                          · have key : RawTerm.fireRootRedex .gen_listElim payload
                                                (.childCons (.mkGen sg sp sc)
                                                  (.childCons nilB (.childCons consB .childNil))) = none :=
                                              (if_neg hNil).trans (dif_neg hCons)
                                            rw [key] at hfire; nomatch hfire
              · by_cases hOptionMatch : gen = .gen_optionMatch
                · subst hOptionMatch
                  cases childrenStep with
                  | cons scrutStep tailStep => cases tailStep with
                    | cons _noneStep tail2 => cases tail2 with
                      | cons _someStep tailNil => cases tailNil with
                        | nil =>
                            cases ihChildren with
                            | cons ihScrut ihTail => cases ihTail with
                              | cons ihNoneBranch ihTail2 => cases ihTail2 with
                                | cons ihSomeBranch ihNil => cases ihNil with
                                  | nil =>
                                      rename_i scrut _scrut' noneB _noneB' someB _someB'
                                      cases scrut with
                                      | mkGen sg sp sc =>
                                          by_cases hNone : sg = .gen_optionNone
                                          · subst hNone
                                            cases sc with | childNil =>
                                                cases scrutStep with
                                                | cong _ _ csS => cases csS with
                                                  | nil => exact ParStep.iotaOptionMatchNone ihNoneBranch
                                          · by_cases hSome : sg = .gen_optionSome
                                            · subst hSome
                                              cases sc with | childCons _value scNil => cases scNil with
                                                | childNil =>
                                                    cases scrutStep with
                                                    | cong _ _ csS => cases csS with
                                                      | cons _vs rS => cases rS with
                                                        | nil =>
                                                            cases ihScrut with
                                                            | cong _ _ csI => cases csI with
                                                              | cons valueDevStep rI => cases rI with
                                                                | nil =>
                                                                    exact ParStep.iotaOptionMatchSome
                                                                      ihSomeBranch valueDevStep
                                            · have key : RawTerm.fireRootRedex .gen_optionMatch payload
                                                  (.childCons (.mkGen sg sp sc)
                                                    (.childCons noneB (.childCons someB .childNil))) = none :=
                                                (if_neg hNone).trans (dif_neg hSome)
                                              rw [key] at hfire; nomatch hfire
                · by_cases hEitherMatch : gen = .gen_eitherMatch
                  · subst hEitherMatch
                    cases childrenStep with
                    | cons scrutStep tailStep => cases tailStep with
                      | cons _leftStep tail2 => cases tail2 with
                        | cons _rightStep tailNil => cases tailNil with
                          | nil =>
                              cases ihChildren with
                              | cons ihScrut ihTail => cases ihTail with
                                | cons ihLeftBranch ihTail2 => cases ihTail2 with
                                  | cons ihRightBranch ihNil => cases ihNil with
                                    | nil =>
                                        rename_i scrut _scrut' leftB _leftB' rightB _rightB'
                                        cases scrut with
                                        | mkGen sg sp sc =>
                                            by_cases hInl : sg = .gen_eitherInl
                                            · subst hInl
                                              cases sc with | childCons _value scNil => cases scNil with
                                                | childNil =>
                                                    cases scrutStep with
                                                    | cong _ _ csS => cases csS with
                                                      | cons _vs rS => cases rS with
                                                        | nil =>
                                                            cases ihScrut with
                                                            | cong _ _ csI => cases csI with
                                                              | cons valueDevStep rI => cases rI with
                                                                | nil =>
                                                                    exact ParStep.iotaEitherMatchInl
                                                                      ihLeftBranch valueDevStep
                                            · by_cases hInr : sg = .gen_eitherInr
                                              · subst hInr
                                                cases sc with | childCons _value scNil => cases scNil with
                                                  | childNil =>
                                                      cases scrutStep with
                                                      | cong _ _ csS => cases csS with
                                                        | cons _vs rS => cases rS with
                                                          | nil =>
                                                              cases ihScrut with
                                                              | cong _ _ csI => cases csI with
                                                                | cons valueDevStep rI => cases rI with
                                                                  | nil =>
                                                                      exact ParStep.iotaEitherMatchInr
                                                                        ihRightBranch valueDevStep
                                              · have key : RawTerm.fireRootRedex .gen_eitherMatch payload
                                                    (.childCons (.mkGen sg sp sc)
                                                      (.childCons leftB (.childCons rightB .childNil))) = none :=
                                                  (dif_neg hInl).trans (dif_neg hInr)
                                                rw [key] at hfire; nomatch hfire
                  · by_cases hIdJ : gen = .gen_idJ
                    · subst hIdJ
                      cases childrenStep with
                      | cons _baseStep tailStep => cases tailStep with
                        | cons reflStep tailNil => cases tailNil with
                          | nil =>
                              cases ihChildren with
                              | cons ihBase ihTail => cases ihTail with
                                | cons _ihRefl ihNil => cases ihNil with
                                  | nil =>
                                      rename_i baseCase _baseCase' reflC _reflC'
                                      cases reflC with
                                      | mkGen rg rp rc =>
                                          by_cases hRefl : rg = .gen_refl
                                          · subst hRefl
                                            cases rc with | childCons _witness rcNil => cases rcNil with
                                              | childNil =>
                                                  cases reflStep with
                                                  | cong _ _ csR => cases csR with
                                                    | cons _ws rR => cases rR with
                                                      | nil => exact ParStep.iotaIdJRefl ihBase
                                          · have key : RawTerm.fireRootRedex .gen_idJ payload
                                                (.childCons baseCase
                                                  (.childCons (.mkGen rg rp rc) .childNil)) = none :=
                                              if_neg hRefl
                                            rw [key] at hfire; nomatch hfire
                    · by_cases hIdStrictRec : gen = .gen_idStrictRec
                      · subst hIdStrictRec
                        cases childrenStep with
                        | cons _baseStep tailStep => cases tailStep with
                          | cons reflStep tailNil => cases tailNil with
                            | nil =>
                                cases ihChildren with
                                | cons ihBase ihTail => cases ihTail with
                                  | cons _ihRefl ihNil => cases ihNil with
                                    | nil =>
                                        rename_i baseCase _baseCase' reflC _reflC'
                                        cases reflC with
                                        | mkGen rg rp rc =>
                                            by_cases hRefl : rg = .gen_refl
                                            · subst hRefl
                                              cases rc with | childCons _witness rcNil => cases rcNil with
                                                | childNil =>
                                                    cases reflStep with
                                                    | cong _ _ csR => cases csR with
                                                      | cons _ws rR => cases rR with
                                                        | nil => exact ParStep.iotaIdStrictRecRefl ihBase
                                            · have key : RawTerm.fireRootRedex .gen_idStrictRec payload
                                                  (.childCons baseCase
                                                    (.childCons (.mkGen rg rp rc) .childNil)) = none :=
                                                if_neg hRefl
                                              rw [key] at hfire; nomatch hfire
                      · rw [show RawTerm.fireRootRedex gen payload children = none from by
                            unfold RawTerm.fireRootRedex
                            rw [dif_neg hApp, dif_neg hBoolElim, dif_neg hFst, dif_neg hSnd,
                              dif_neg hNatElim, dif_neg hNatRec, dif_neg hListElim, dif_neg hOptionMatch,
                              dif_neg hEitherMatch, dif_neg hIdJ, dif_neg hIdStrictRec]] at hfire
                        nomatch hfire

end FX1Poly.Core
