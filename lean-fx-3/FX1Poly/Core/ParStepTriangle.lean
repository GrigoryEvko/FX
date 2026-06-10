import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.ParStepSubstPointwise

/-! # FX1Poly/Core/ParStepTriangle
    — the Takahashi triangle `ParStep a b → ParStep b (completeDevelopment a)` (the raw-confluence headline).

`TakahashiTriangle.lean` reduces the FX raw-confluence diamond to `HasMaximalReduct ParStep` — a function
`completeDevelopment` (shipped in `CompleteDevelopment.lean`) such that EVERY parallel reduct of `a`
further parallel-reduces to `completeDevelopment a`.  This file proves that triangle property.  With it,
`HasMaximalReduct.ofTriangle` gives the `DiamondProperty` of `ParStep`, hence `Confluent ParStep`, hence —
through the shipped `Step ⊆ ParStep ⊆ StepStar` sandwich (`ParallelReduction.lean`) and
`StepStar.hasConfluence_of_parallelDiamond` — UNCONDITIONAL raw confluence (the prize strong normalization
cannot supply, since raw β+ι is not SN).

## Structure

The triangle is proved by induction on the `ParStep a b` derivation (`ParStep.rec`, so termination is
free — no structural recursion over the hidden-behind-`by_cases` `completeDevelopment`).  Two motives:

* `motive_1 a b _ := ParStep b (completeDevelopment a)`;
* `motive_2 cs cs' _ := ParStepChildren cs' (completeDevelopmentChildren cs)`.

The arms:

* **β** — `ParStep.subst0_diagonal`: `subst0 body' arg'` parallel-reduces to `subst0 (cd body) (cd arg)`
  from the body/arg IHs, and that equals `cd (app (lam body) arg)` by `cd_app_lam_eq` (defeq).
* **10 branch-selection ι** (`boolTrue`/`boolFalse`/`fst`/`snd`/`natElimZero`/`natRecZero`/`listElimNil`/
  `optionMatchNone`/`idJRefl`/`idStrictRecRefl`) — the reduct IS the single reduced sub-term, and
  `cd (redex)` is definitionally that sub-term's `cd` (the `cd_<redex>_eq` rfl-equations), so the arm IS
  its own IH (`exact ih`).
* **6 recursive/substituting ι** (`optionMatchSome`/`eitherMatchInl`/`eitherMatchInr`/`natElimSucc`/
  `natRecSucc`/`listElimCons`) — the reduct is an app-chain over the reduced components; `cd (redex)` is
  definitionally the same app-chain over the developed components, so the arm assembles by nested
  `ParStep.cong` over the component IHs.
* **cong** — split on whether the original children form a syntactic redex (`fireRootRedex`):
  `none` is the pure congruence (`ParStep.cong` of the children IH); `some` delegates to
  `ParStep.triangleCongFires`, which inverts the cong-reduced children to reconstruct the firing.
* **children** — `nil`/`cons` rebuild the pointwise spine from the per-child IHs.

`ParStep.triangleCongFires` is the cong-`some` workhorse: given a children parallel step
`children ⇒ children'` whose source `children` form a syntactic root redex, and the children IH
`children' ⇒ completeDevelopmentChildren children`, it proves the cong-reduced cell `mkGen gen p children'`
fires to `fireRootRedexOrSelf gen p (completeDevelopmentChildren children)` in one parallel step.  It
dispatches on the 11 redex generators (`by_cases`, propext-clean over the 194-constructor table), inverts
the relevant scrutinee/function child's parallel step to learn the post-cong head shape, extracts the
component development steps from the children IH, and fires the matching `ParStep` β/ι constructor — whose
reduct is definitionally `fireRootRedexOrSelf`'s output.  The non-firing branches reuse the exact
`dif_neg`/`if_neg`-keyed contradiction discharges of `fireRootRedex_sound`.

## Zero-axiom verification

`ParStep.rec` + `cases` on the (propext-clean, indexed) `ParStep`/`ParStepChildren` derivations,
`ParStep.subst0_diagonal`, `ParStep.cong`, the `cd_<redex>_eq` defeq, and the `fireRootRedex` `dif_neg`/
`if_neg` contradiction keys.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **The cong-`some` firing reconstruction.**  When the source children `children` of a `cong` step form
a syntactic root redex (`fireRootRedex … = some _`), the cong-reduced cell `mkGen gen payload children'`
parallel-reduces in one step to the developed-children firing
`fireRootRedexOrSelf gen payload (completeDevelopmentChildren children)`.  This is the heart of the
Takahashi triangle's `cong` arm: it dispatches on the redex generator, inverts the children's parallel
steps to learn the post-cong head shape, extracts the per-component development steps from the children
IH, and fires the matching `ParStep` β/ι constructor (whose contractum is definitionally the
`fireRootRedexOrSelf` output).  The non-firing generator branches reuse `fireRootRedex_sound`'s exact
`dif_neg`/`if_neg` contradiction keys. -/
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
                          cases ic with | childCons domainAnn icTail => cases icTail with
                            | childCons body icNil => cases icNil with
                              | childNil =>
                                  cases funcStep with
                                  | cong _ _ csF => cases csF with
                                    | cons _ds rF0 => cases rF0 with
                                      | cons _bs rF => cases rF with
                                        | nil =>
                                            cases ihFunc with
                                            | cong _ _ csI => cases csI with
                                              | cons domainDevStep rI0 => cases rI0 with
                                                | cons bodyDevStep rI => cases rI with
                                                  | nil => exact ParStep.beta domainDevStep bodyDevStep ihArg
                        · have key : RawTerm.fireRootRedex .gen_app payload
                              (.childCons (.mkGen ig ip ic) (.childCons _arg .childNil)) = none :=
                            dif_neg hLam
                          rw [key] at hfire; nomatch hfire
  · by_cases hBoolElim : gen = .gen_boolElim
    · subst hBoolElim
      cases childrenStep with
      | cons _motiveStep tailStep => cases tailStep with
        | cons _thenStep tail2 => cases tail2 with
          | cons _elseStep tail3 => cases tail3 with
            | cons scrutStep tailNil => cases tailNil with
              | nil =>
                  cases ihChildren with
                  | cons ihMotive ihTail => cases ihTail with
                    | cons ihThen ihTail2 => cases ihTail2 with
                      | cons ihElse ihTail3 => cases ihTail3 with
                        | cons _ihScrut ihNil => cases ihNil with
                          | nil =>
                              rename_i motive _motive' thenB _thenB' elseB _elseB' scrut _scrut'
                              cases scrut with
                              | mkGen sg sp sc =>
                                  by_cases hTrue : sg = .gen_boolTrue
                                  · subst hTrue
                                    cases sc with | childNil =>
                                        cases scrutStep with
                                        | cong _ _ csS => cases csS with
                                          | nil => exact ParStep.iotaBoolTrue ihMotive ihThen
                                  · by_cases hFalse : sg = .gen_boolFalse
                                    · subst hFalse
                                      cases sc with | childNil =>
                                          cases scrutStep with
                                          | cong _ _ csS => cases csS with
                                            | nil => exact ParStep.iotaBoolFalse ihMotive ihElse
                                    · have key : RawTerm.fireRootRedex .gen_boolElim payload
                                          (.childCons motive (.childCons thenB (.childCons elseB
                                            (.childCons (.mkGen sg sp sc) .childNil)))) = none :=
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
                            dsimp only [RawTerm.fireRootRedex]
                            rw [dif_neg hApp, dif_neg hBoolElim, dif_neg hFst, dif_neg hSnd,
                              dif_neg hNatElim, dif_neg hNatRec, dif_neg hListElim, dif_neg hOptionMatch,
                              dif_neg hEitherMatch, dif_neg hIdJ, dif_neg hIdStrictRec]] at hfire
                        nomatch hfire

/-- **The Takahashi triangle.**  Every parallel reduct `b` of `a` further parallel-reduces to the complete
development `completeDevelopment a` — the maximal-reduct property that discharges the `ParStep` diamond and
hence raw confluence.  Proved by induction on the `ParStep a b` derivation: the β / branch-selection
ι arms close by the IHs through the `cd_<redex>_eq` defeq, the recursive ι arms by nested `ParStep.cong`,
and the `cong` arm splits on `fireRootRedex` — pure congruence when the source is not a redex, else
`ParStep.triangleCongFires`. -/
theorem ParStep.triangle {scope : Nat} {a b : RawTerm scope} :
    ParStep a b → ParStep b (RawTerm.completeDevelopment a) :=
  ParStep.rec
    (motive_1 := fun {_scope} a b _ => ParStep b (RawTerm.completeDevelopment a))
    (motive_2 := fun {_binderShifts} {_scope} cs cs' _ =>
      ParStepChildren cs' (RawTerm.completeDevelopmentChildren cs))
    (fun {_scope} {_domainAnn _domainAnn' _body _body' _arg _arg'}
        _domainStep _bodyStep _argStep _ihDomain ihBody ihArg =>
        ParStep.subst0_diagonal ihBody ihArg)
    (fun {_scope} gen payload {_children _children'} childrenStep ih => by
        show ParStep (.mkGen gen payload _children')
          (RawTerm.fireRootRedexOrSelfGated gen payload _children
            (RawTerm.completeDevelopmentChildren _children))
        dsimp only [RawTerm.fireRootRedexOrSelfGated]
        cases hfire : RawTerm.fireRootRedex gen payload _children with
        | none => exact ParStep.cong gen payload ih
        | some reduct => exact ParStep.triangleCongFires gen payload childrenStep ih hfire)
    (fun {_scope} {_motive _motive' _thenBranch _thenBranch' _elseBranch}
        _motiveStep _thenStep _ihMotive ihThen => ihThen)
    (fun {_scope} {_motive _motive' _thenBranch _elseBranch _elseBranch'}
        _motiveStep _elseStep _ihMotive ihElse => ihElse)
    (fun {_scope} {_firstValue _firstValue' _secondValue} _step ih => ih)
    (fun {_scope} {_firstValue _secondValue _secondValue'} _step ih => ih)
    (fun {_scope} {_zeroBranch _zeroBranch' _succBranch} _step ih => ih)
    (fun {_scope} {_zeroBranch _zeroBranch' _succBranch} _step ih => ih)
    (fun {_scope} {_nilBranch _nilBranch' _consBranch} _step ih => ih)
    (fun {_scope} {_noneBranch _noneBranch' _someBranch} _step ih => ih)
    (fun {_scope} {_value _value' _noneBranch _someBranch _someBranch'} _someStep _valueStep ihSome ihValue =>
        ParStep.cong .gen_app () (.cons ihSome (.cons ihValue .nil)))
    (fun {_scope} {_value _value' _leftBranch _leftBranch' _rightBranch} _leftStep _valueStep ihLeft ihValue =>
        ParStep.cong .gen_app () (.cons ihLeft (.cons ihValue .nil)))
    (fun {_scope} {_value _value' _leftBranch _rightBranch _rightBranch'} _rightStep _valueStep ihRight ihValue =>
        ParStep.cong .gen_app () (.cons ihRight (.cons ihValue .nil)))
    (fun {_scope} {_predecessor _predecessor' _zeroBranch _zeroBranch' _succBranch _succBranch'}
        _predStep _zeroStep _succStep ihPred ihZero ihSucc =>
        ParStep.cong .gen_app ()
          (.cons (ParStep.cong .gen_app () (.cons ihSucc (.cons ihPred .nil)))
            (.cons (ParStep.cong .gen_natElim ()
              (.cons ihPred (.cons ihZero (.cons ihSucc .nil)))) .nil)))
    (fun {_scope} {_predecessor _predecessor' _zeroBranch _zeroBranch' _succBranch _succBranch'}
        _predStep _zeroStep _succStep ihPred ihZero ihSucc =>
        ParStep.cong .gen_app ()
          (.cons (ParStep.cong .gen_app () (.cons ihSucc (.cons ihPred .nil)))
            (.cons (ParStep.cong .gen_natRec ()
              (.cons ihPred (.cons ihZero (.cons ihSucc .nil)))) .nil)))
    (fun {_scope} {_headVal _headVal' _tailVal _tailVal' _nilBranch _nilBranch' _consBranch _consBranch'}
        _headStep _tailStep _nilStep _consStep ihHead ihTail ihNil ihCons =>
        ParStep.cong .gen_app ()
          (.cons (ParStep.cong .gen_app ()
            (.cons (ParStep.cong .gen_app () (.cons ihCons (.cons ihHead .nil)))
              (.cons ihTail .nil)))
            (.cons (ParStep.cong .gen_listElim ()
              (.cons ihTail (.cons ihNil (.cons ihCons .nil)))) .nil)))
    (fun {_scope} {_baseCase _baseCase' _rawWitness} _step ih => ih)
    (fun {_scope} {_baseCase _baseCase' _rawWitness} _step ih => ih)
    (fun {_scope} => ParStepChildren.nil)
    (fun {_scope _shift _restShifts} {_childHead _childHead' _childTail _childTail'}
        _headStep _tailStep ihHead ihTail => ParStepChildren.cons ihHead ihTail)

end FX1Poly.Core
