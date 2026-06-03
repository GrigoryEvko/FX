import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Core/CompleteDevelopmentParStep
    — every term parallel-reduces to its complete development: `ParStep a (completeDevelopment a)`.

This is the **correctness witness** for the gated complete development (an over-firing `cd` would FAIL
this — `ParStep` is a single parallel step, so a redex created by an inner contraction cannot be fired in
the same step) and the **`b := a` instance** of the Takahashi triangle `ParStep a b → ParStep b (cd a)`.

## Why `RawTerm.rec` (not structural recursion)

`completeDevelopment` dispatches on the 194-constructor `Generator` by `by_cases` (a term-mode match would
need a propext-leaking >100-ctor wildcard), which hides the deep subterms from Lean's structural-recursion
checker — a direct mutual `match` definition fails termination ("failed to eliminate recursive application
completeDevelopment_parStep body").  Routing through the `RawTerm.rec` recursor sidesteps this: the recursor
supplies the children-spine IH (`motive_2 children = ParStepChildren children (cdChildren children)`), and
the firing leaves extract the per-component `ParStep`s from it by `cases` (the inline form of the shipped
`ParStep.*_inv` lemmas — here the developed target is concrete, so `cases` suffices without the existential).

## Proof shape

`cases` on `fireRootRedex gen payload children`:

* `none` — `cd a` is the cong-developed cell; `ParStep.cong gen payload childrenIH` (childrenIH intact).
* `some` — `a` is a syntactic redex; navigate by `by_cases` on the generator (mirroring `fireRootRedex`),
  `cases children` (substitution keeps `childrenIH`/`hfire` synced) + `cases` the scrutinee/function to its
  head, fire the matching `ParStep` constructor with the child IHs (extracting the redex sub-component via
  `cases` on the scrutinee's `ParStep` for β/`fst`/`snd`/`natElimSucc`/`natRecSucc`/`listElimCons`/
  `optionMatchSome`/`eitherMatchInl`/`eitherMatchInr`), and close the non-redex-head leaves by `hfire`
  contradiction (`fireRootRedex … = none` via `dif_neg`/`if_neg`).

## Zero-axiom verification

The proof is `RawTerm.rec` + `cases`/`by_cases` + the `ParStep` firing constructors; the contradiction
leaves are `dif_neg`/`if_neg` keys + `nomatch`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open Foundation


/-- Every term parallel-reduces to its complete development. -/
theorem RawTerm.completeDevelopment_parStep {scope0 : Nat} (term0 : RawTerm scope0) :
    ParStep term0 (RawTerm.completeDevelopment term0) :=
  RawTerm.rec
    (motive_1 := fun {scope} term => ParStep term (RawTerm.completeDevelopment term))
    (motive_2 := fun {binderShifts} {scope} children =>
      ParStepChildren children (RawTerm.completeDevelopmentChildren children))
    (fun {scope} gen payload children childrenIH => by
        show ParStep (.mkGen gen payload children)
          (RawTerm.fireRootRedexOrSelfGated gen payload children
            (RawTerm.completeDevelopmentChildren children))
        unfold RawTerm.fireRootRedexOrSelfGated
        cases hfire : RawTerm.fireRootRedex gen payload children with
        | none => exact ParStep.cong gen payload childrenIH
        | some reduct =>
            by_cases hApp : gen = .gen_app
            · subst hApp
              cases children with
              | childCons func rest => cases rest with | childCons arg rest2 => cases rest2 with
                | childNil =>
                    cases func with
                    | mkGen ig ip ic =>
                        by_cases hLam : ig = .gen_lam
                        · subst hLam
                          cases ic with | childCons body ic2 => cases ic2 with
                            | childNil =>
                                cases childrenIH with | cons funcStep restS => cases restS with
                                  | cons argStep _ =>
                                      cases funcStep with | cong _ _ cs => cases cs with
                                        | cons bodyStep rcs => cases rcs with
                                          | nil => exact ParStep.beta bodyStep argStep
                        · have key : RawTerm.fireRootRedex .gen_app payload
                              (.childCons (.mkGen ig ip ic) (.childCons arg .childNil)) = none := dif_neg hLam
                          rw [key] at hfire; nomatch hfire
            · by_cases hBoolElim : gen = .gen_boolElim
              · subst hBoolElim
                cases children with
                | childCons scrut rest => cases rest with | childCons thenB rest2 => cases rest2 with
                  | childCons elseB rest3 => cases rest3 with | childNil =>
                      cases scrut with
                      | mkGen sg sp sc =>
                          by_cases hTrue : sg = .gen_boolTrue
                          · subst hTrue
                            cases sc with | childNil =>
                                cases childrenIH with | cons _ restS => cases restS with
                                  | cons thenStep _ => exact ParStep.iotaBoolTrue thenStep
                          · by_cases hFalse : sg = .gen_boolFalse
                            · subst hFalse
                              cases sc with | childNil =>
                                  cases childrenIH with | cons _ restS => cases restS with
                                    | cons _ restS2 => cases restS2 with
                                      | cons elseStep _ => exact ParStep.iotaBoolFalse elseStep
                            · have key : RawTerm.fireRootRedex .gen_boolElim payload
                                  (.childCons (.mkGen sg sp sc)
                                    (.childCons thenB (.childCons elseB .childNil))) = none :=
                                (if_neg hTrue).trans (if_neg hFalse)
                              rw [key] at hfire; nomatch hfire
              · by_cases hFst : gen = .gen_fst
                · subst hFst
                  cases children with
                  | childCons pairC rest => cases rest with | childNil =>
                      cases pairC with
                      | mkGen pg pp pc =>
                          by_cases hPair : pg = .gen_pair
                          · subst hPair
                            cases pc with | childCons fv pc2 => cases pc2 with
                              | childCons sv pc3 => cases pc3 with | childNil =>
                                  cases childrenIH with | cons pairStep _ =>
                                      cases pairStep with | cong _ _ cs => cases cs with
                                        | cons fvStep _ => exact ParStep.iotaFstPair fvStep
                          · have key : RawTerm.fireRootRedex .gen_fst payload
                                (.childCons (.mkGen pg pp pc) .childNil) = none := dif_neg hPair
                            rw [key] at hfire; nomatch hfire
                · by_cases hSnd : gen = .gen_snd
                  · subst hSnd
                    cases children with
                    | childCons pairC rest => cases rest with | childNil =>
                        cases pairC with
                        | mkGen pg pp pc =>
                            by_cases hPair : pg = .gen_pair
                            · subst hPair
                              cases pc with | childCons fv pc2 => cases pc2 with
                                | childCons sv pc3 => cases pc3 with | childNil =>
                                    cases childrenIH with | cons pairStep _ =>
                                        cases pairStep with | cong _ _ cs => cases cs with
                                          | cons _ rcs => cases rcs with
                                            | cons svStep _ => exact ParStep.iotaSndPair svStep
                            · have key : RawTerm.fireRootRedex .gen_snd payload
                                  (.childCons (.mkGen pg pp pc) .childNil) = none := dif_neg hPair
                              rw [key] at hfire; nomatch hfire
                  · by_cases hNatElim : gen = .gen_natElim
                    · subst hNatElim
                      cases children with
                      | childCons scrut rest => cases rest with | childCons zeroB rest2 => cases rest2 with
                        | childCons succB rest3 => cases rest3 with | childNil =>
                            cases scrut with
                            | mkGen sg sp sc =>
                                by_cases hZero : sg = .gen_natZero
                                · subst hZero
                                  cases sc with | childNil =>
                                      cases childrenIH with | cons _ restS => cases restS with
                                        | cons zeroStep _ => exact ParStep.iotaNatElimZero zeroStep
                                · by_cases hSucc : sg = .gen_natSucc
                                  · subst hSucc
                                    cases sc with | childCons pred sc2 => cases sc2 with
                                      | childNil =>
                                          cases childrenIH with | cons scrutStep restS => cases restS with
                                            | cons zeroStep restS2 => cases restS2 with
                                              | cons succStep _ =>
                                                  cases scrutStep with | cong _ _ cs => cases cs with
                                                    | cons predStep rcs => cases rcs with
                                                      | nil => exact ParStep.iotaNatElimSucc predStep zeroStep succStep
                                  · have key : RawTerm.fireRootRedex .gen_natElim payload
                                        (.childCons (.mkGen sg sp sc)
                                          (.childCons zeroB (.childCons succB .childNil))) = none :=
                                      (if_neg hZero).trans (dif_neg hSucc)
                                    rw [key] at hfire; nomatch hfire
                    · by_cases hNatRec : gen = .gen_natRec
                      · subst hNatRec
                        cases children with
                        | childCons scrut rest => cases rest with | childCons zeroB rest2 => cases rest2 with
                          | childCons succB rest3 => cases rest3 with | childNil =>
                              cases scrut with
                              | mkGen sg sp sc =>
                                  by_cases hZero : sg = .gen_natZero
                                  · subst hZero
                                    cases sc with | childNil =>
                                        cases childrenIH with | cons _ restS => cases restS with
                                          | cons zeroStep _ => exact ParStep.iotaNatRecZero zeroStep
                                  · by_cases hSucc : sg = .gen_natSucc
                                    · subst hSucc
                                      cases sc with | childCons pred sc2 => cases sc2 with
                                        | childNil =>
                                            cases childrenIH with | cons scrutStep restS => cases restS with
                                              | cons zeroStep restS2 => cases restS2 with
                                                | cons succStep _ =>
                                                    cases scrutStep with | cong _ _ cs => cases cs with
                                                      | cons predStep rcs => cases rcs with
                                                        | nil => exact ParStep.iotaNatRecSucc predStep zeroStep succStep
                                    · have key : RawTerm.fireRootRedex .gen_natRec payload
                                          (.childCons (.mkGen sg sp sc)
                                            (.childCons zeroB (.childCons succB .childNil))) = none :=
                                        (if_neg hZero).trans (dif_neg hSucc)
                                      rw [key] at hfire; nomatch hfire
                      · by_cases hListElim : gen = .gen_listElim
                        · subst hListElim
                          cases children with
                          | childCons scrut rest => cases rest with | childCons nilB rest2 => cases rest2 with
                            | childCons consB rest3 => cases rest3 with | childNil =>
                                cases scrut with
                                | mkGen sg sp sc =>
                                    by_cases hNil : sg = .gen_listNil
                                    · subst hNil
                                      cases sc with | childNil =>
                                          cases childrenIH with | cons _ restS => cases restS with
                                            | cons nilStep _ => exact ParStep.iotaListElimNil nilStep
                                    · by_cases hCons : sg = .gen_listCons
                                      · subst hCons
                                        cases sc with | childCons hv sc2 => cases sc2 with
                                          | childCons tv sc3 => cases sc3 with | childNil =>
                                              cases childrenIH with | cons scrutStep restS => cases restS with
                                                | cons nilStep restS2 => cases restS2 with
                                                  | cons consStep _ =>
                                                      cases scrutStep with | cong _ _ cs => cases cs with
                                                        | cons hvStep rcs => cases rcs with
                                                          | cons tvStep rcs2 => cases rcs2 with
                                                            | nil => exact ParStep.iotaListElimCons hvStep tvStep nilStep consStep
                                      · have key : RawTerm.fireRootRedex .gen_listElim payload
                                            (.childCons (.mkGen sg sp sc)
                                              (.childCons nilB (.childCons consB .childNil))) = none :=
                                          (if_neg hNil).trans (dif_neg hCons)
                                        rw [key] at hfire; nomatch hfire
                        · by_cases hOptionMatch : gen = .gen_optionMatch
                          · subst hOptionMatch
                            cases children with
                            | childCons scrut rest => cases rest with | childCons noneB rest2 => cases rest2 with
                              | childCons someB rest3 => cases rest3 with | childNil =>
                                  cases scrut with
                                  | mkGen sg sp sc =>
                                      by_cases hNone : sg = .gen_optionNone
                                      · subst hNone
                                        cases sc with | childNil =>
                                            cases childrenIH with | cons _ restS => cases restS with
                                              | cons noneStep _ => exact ParStep.iotaOptionMatchNone noneStep
                                      · by_cases hSome : sg = .gen_optionSome
                                        · subst hSome
                                          cases sc with | childCons val sc2 => cases sc2 with
                                            | childNil =>
                                                cases childrenIH with | cons scrutStep restS => cases restS with
                                                  | cons _ restS2 => cases restS2 with
                                                    | cons someStep _ =>
                                                        cases scrutStep with | cong _ _ cs => cases cs with
                                                          | cons valStep rcs => cases rcs with
                                                            | nil => exact ParStep.iotaOptionMatchSome someStep valStep
                                        · have key : RawTerm.fireRootRedex .gen_optionMatch payload
                                              (.childCons (.mkGen sg sp sc)
                                                (.childCons noneB (.childCons someB .childNil))) = none :=
                                            (if_neg hNone).trans (dif_neg hSome)
                                          rw [key] at hfire; nomatch hfire
                          · by_cases hEitherMatch : gen = .gen_eitherMatch
                            · subst hEitherMatch
                              cases children with
                              | childCons scrut rest => cases rest with | childCons leftB rest2 => cases rest2 with
                                | childCons rightB rest3 => cases rest3 with | childNil =>
                                    cases scrut with
                                    | mkGen sg sp sc =>
                                        by_cases hInl : sg = .gen_eitherInl
                                        · subst hInl
                                          cases sc with | childCons val sc2 => cases sc2 with
                                            | childNil =>
                                                cases childrenIH with | cons scrutStep restS => cases restS with
                                                  | cons leftStep _ =>
                                                      cases scrutStep with | cong _ _ cs => cases cs with
                                                        | cons valStep rcs => cases rcs with
                                                          | nil => exact ParStep.iotaEitherMatchInl leftStep valStep
                                        · by_cases hInr : sg = .gen_eitherInr
                                          · subst hInr
                                            cases sc with | childCons val sc2 => cases sc2 with
                                              | childNil =>
                                                  cases childrenIH with | cons scrutStep restS => cases restS with
                                                    | cons _ restS2 => cases restS2 with
                                                      | cons rightStep _ =>
                                                          cases scrutStep with | cong _ _ cs => cases cs with
                                                            | cons valStep rcs => cases rcs with
                                                              | nil => exact ParStep.iotaEitherMatchInr rightStep valStep
                                          · have key : RawTerm.fireRootRedex .gen_eitherMatch payload
                                                (.childCons (.mkGen sg sp sc)
                                                  (.childCons leftB (.childCons rightB .childNil))) = none :=
                                              (dif_neg hInl).trans (dif_neg hInr)
                                            rw [key] at hfire; nomatch hfire
                            · by_cases hIdJ : gen = .gen_idJ
                              · subst hIdJ
                                cases children with
                                | childCons baseC rest => cases rest with | childCons reflC rest2 => cases rest2 with
                                  | childNil =>
                                      cases reflC with
                                      | mkGen rg rp rc =>
                                          by_cases hRefl : rg = .gen_refl
                                          · subst hRefl
                                            cases rc with | childCons witness rc2 => cases rc2 with
                                              | childNil =>
                                                  cases childrenIH with | cons baseStep _ =>
                                                      exact ParStep.iotaIdJRefl baseStep
                                          · have key : RawTerm.fireRootRedex .gen_idJ payload
                                                (.childCons baseC
                                                  (.childCons (.mkGen rg rp rc) .childNil)) = none := if_neg hRefl
                                            rw [key] at hfire; nomatch hfire
                              · by_cases hIdStrictRec : gen = .gen_idStrictRec
                                · subst hIdStrictRec
                                  cases children with
                                  | childCons baseC rest => cases rest with | childCons reflC rest2 => cases rest2 with
                                    | childNil =>
                                        cases reflC with
                                        | mkGen rg rp rc =>
                                            by_cases hRefl : rg = .gen_refl
                                            · subst hRefl
                                              cases rc with | childCons witness rc2 => cases rc2 with
                                                | childNil =>
                                                    cases childrenIH with | cons baseStep _ =>
                                                        exact ParStep.iotaIdStrictRecRefl baseStep
                                            · have key : RawTerm.fireRootRedex .gen_idStrictRec payload
                                                  (.childCons baseC
                                                    (.childCons (.mkGen rg rp rc) .childNil)) = none := if_neg hRefl
                                              rw [key] at hfire; nomatch hfire
                                · -- non-redex generator: fireRootRedex = none, contradicts hfire
                                  rw [show RawTerm.fireRootRedex gen payload children = none from by
                                    unfold RawTerm.fireRootRedex
                                    rw [dif_neg hApp, dif_neg hBoolElim, dif_neg hFst, dif_neg hSnd,
                                      dif_neg hNatElim, dif_neg hNatRec, dif_neg hListElim, dif_neg hOptionMatch,
                                      dif_neg hEitherMatch, dif_neg hIdJ, dif_neg hIdStrictRec]] at hfire
                                  nomatch hfire)
    (fun {scope} => ParStepChildren.nil)
    (fun {scope shift restShifts} childHead childTail headIH tailIH =>
        ParStepChildren.cons headIH tailIH)
    term0

end FX1Poly.Core
