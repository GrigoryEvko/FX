import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.ParStepSubstPointwise

namespace FX1Poly.Core

open Foundation

-- Probe: the cong-some helper. gen_app/gen_boolElim/gen_natElim real; rest sorry.
theorem triangleCongFires_probe {scope : Nat} (gen : Generator) (payload : gen.payload scope)
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
        | cons thenStep tail2 => cases tail2 with
          | cons elseStep tailNil => cases tailNil with
            | nil =>
                cases ihChildren with
                | cons ihScrut ihTail => cases ihTail with
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
                                        (.childCons thenB (.childCons elseB .childNil))) = none := by
                                    show (if sg = .gen_boolTrue then some thenB
                                          else if sg = .gen_boolFalse then some elseB else none) = none
                                    rw [if_neg hTrue, if_neg hFalse]
                                  rw [key] at hfire; nomatch hfire
    · by_cases hNatElim : gen = .gen_natElim
      · subst hNatElim
        cases childrenStep with
        | cons scrutStep tailStep => cases tailStep with
          | cons zeroStep tail2 => cases tail2 with
            | cons succStep tailNil => cases tailNil with
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
                                    cases sc with | childCons pred scNil => cases scNil with
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
                                          (.childCons zeroB (.childCons succB .childNil))) = none := by
                                      show (if sg = .gen_natZero then some zeroB
                                            else if h : sg = .gen_natSucc then
                                              (match (h ▸ sc : RawTermChildren
                                                  (Generator.gen_natSucc.binderShifts) scope) with
                                                | .childCons predecessor .childNil =>
                                                    some (.mkGen .gen_app ()
                                                      (.childCons (.mkGen .gen_app ()
                                                        (.childCons succB (.childCons predecessor .childNil)))
                                                        (.childCons (.mkGen .gen_natElim ()
                                                          (.childCons predecessor
                                                            (.childCons zeroB (.childCons succB .childNil))))
                                                          .childNil))))
                                            else none) = none
                                      rw [if_neg hZero, dif_neg hSucc]
                                    rw [key] at hfire; nomatch hfire
      · sorry

end FX1Poly.Core
