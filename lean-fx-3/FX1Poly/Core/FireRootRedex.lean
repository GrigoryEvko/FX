import FX1Poly.Core.RawTermNF
import FX1Poly.Core.Step

/-! # FX1Poly/Core/FireRootRedex
    — the computable root-redex firing function: the COMPUTATIONAL counterpart of `hasRootStepSource`.

`RootStepDispatch.lean`'s `hasRootStepSource_exists_step` proves a root redex *takes* a `Step`, but the
reduct is bound existentially — it cannot be extracted to a `RawTerm` without choice.  This file ships the
FUNCTION `RawTerm.fireRootRedex` that computes the reduct directly: `some reduct` exactly when the term is a
root redex (a β-redex or one of the inductive-eliminator ι-redexes), `none` otherwise.  Its soundness
(`fireRootRedex_sound`: `= some reduct → Step …`) is the computable companion the weak-normalization
normalizer FUNCTION (eval/quote) needs to turn the existential `exists_normalForm_of_isStronglyNormalizing`
into a real `RawTerm`-valued normalizer, which in turn makes
`Conv.decidableOfNormalForms_of_isStronglyNormalizing` parameter-free.

## Propext-clean construction recipe (the lean-fx-3 indexed-children trap)

A naive `match generator with … | _ => none` over the 194-constructor `Generator` enum leaks `propext`
(the ">100-constructor wildcard" trap), and a partial `match` on the index-dependent `RawTermChildren`
spine leaks it too.  The clean recipe — validated to keep this whole file zero-axiom — is:

* dispatch on the generator with a `dite`-chain over `generator = .gen_Xxx` (`DecidableEq Generator`), never
  a `match` with a wildcard;
* transport the children to the now-concrete `binderShifts` with `generatorEq ▸ children`;
* fully destructure the concrete-index spine (no wildcard — the index forces a single shape);
* test the scrutinee child's head generator with a nested `dite`, transporting its children likewise.

The `DecidableEq`-derived equality proofs reduce to `rfl` for equal constructors, so every concrete firing
reduces definitionally — `fireRootRedex .gen_app … (lam body · arg) = some (subst0 body arg)` holds by
`rfl`, which is what makes the soundness proof's `rfl`-keys and `dif_neg`-terms go through.

## Zero-axiom verification

The function is `dite`/`▸`/full-spine-`match`; the soundness proof is `by_cases` on `DecidableEq Generator`,
`match` spine destructuring, `rfl`-keyed `injection` for firing cases, and `dif_neg`-term + `nomatch` for the
non-firing cases.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Computable root-redex firing.**  Returns `some reduct` exactly when `mkGen generator payload children`
is a root redex (β or an inductive-eliminator ι), producing the same reduct the matching `Step` constructor
names; `none` otherwise.  Dispatches via `DecidableEq Generator` `dite`-chains (propext-clean over the
194-constructor table). -/
def RawTerm.fireRootRedex {scope : Nat} (generator : Generator)
    (_payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    Option (RawTerm scope) :=
  if hApp : generator = .gen_app then
    match (hApp ▸ children : RawTermChildren (Generator.gen_app.binderShifts) scope) with
    | .childCons functionChild (.childCons argChild .childNil) =>
        match functionChild with
        | .mkGen innerGenerator _innerPayload innerChildren =>
            if hLam : innerGenerator = .gen_lam then
              match (hLam ▸ innerChildren : RawTermChildren (Generator.gen_lam.binderShifts) scope) with
              | .childCons _domainAnn (.childCons body .childNil) =>
                  some (RawTerm.subst0 body argChild)
            else none
  else if hBoolElim : generator = .gen_boolElim then
    match (hBoolElim ▸ children : RawTermChildren (Generator.gen_boolElim.binderShifts) scope) with
    | .childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload _scrutineeChildren =>
            if scrutineeGenerator = .gen_boolTrue then some thenBranch
            else if scrutineeGenerator = .gen_boolFalse then some elseBranch
            else none
  else if hFst : generator = .gen_fst then
    match (hFst ▸ children : RawTermChildren (Generator.gen_fst.binderShifts) scope) with
    | .childCons pairChild .childNil =>
        match pairChild with
        | .mkGen pairGenerator _pairPayload pairChildren =>
            if hPair : pairGenerator = .gen_pair then
              match (hPair ▸ pairChildren : RawTermChildren (Generator.gen_pair.binderShifts) scope) with
              | .childCons firstValue (.childCons _secondValue .childNil) => some firstValue
            else none
  else if hSnd : generator = .gen_snd then
    match (hSnd ▸ children : RawTermChildren (Generator.gen_snd.binderShifts) scope) with
    | .childCons pairChild .childNil =>
        match pairChild with
        | .mkGen pairGenerator _pairPayload pairChildren =>
            if hPair : pairGenerator = .gen_pair then
              match (hPair ▸ pairChildren : RawTermChildren (Generator.gen_pair.binderShifts) scope) with
              | .childCons _firstValue (.childCons secondValue .childNil) => some secondValue
            else none
  else if hNatElim : generator = .gen_natElim then
    match (hNatElim ▸ children : RawTermChildren (Generator.gen_natElim.binderShifts) scope) with
    | .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload scrutineeChildren =>
            if scrutineeGenerator = .gen_natZero then some zeroBranch
            else if hSucc : scrutineeGenerator = .gen_natSucc then
              match (hSucc ▸ scrutineeChildren :
                  RawTermChildren (Generator.gen_natSucc.binderShifts) scope) with
              | .childCons predecessor .childNil =>
                  some (.mkGen .gen_app ()
                    (.childCons
                      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
                      (.childCons
                        (.mkGen .gen_natElim ()
                          (.childCons predecessor
                            (.childCons zeroBranch (.childCons succBranch .childNil))))
                        .childNil)))
            else none
  else if hNatRec : generator = .gen_natRec then
    match (hNatRec ▸ children : RawTermChildren (Generator.gen_natRec.binderShifts) scope) with
    | .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload scrutineeChildren =>
            if scrutineeGenerator = .gen_natZero then some zeroBranch
            else if hSucc : scrutineeGenerator = .gen_natSucc then
              match (hSucc ▸ scrutineeChildren :
                  RawTermChildren (Generator.gen_natSucc.binderShifts) scope) with
              | .childCons predecessor .childNil =>
                  some (.mkGen .gen_app ()
                    (.childCons
                      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
                      (.childCons
                        (.mkGen .gen_natRec ()
                          (.childCons predecessor
                            (.childCons zeroBranch (.childCons succBranch .childNil))))
                        .childNil)))
            else none
  else if hListElim : generator = .gen_listElim then
    match (hListElim ▸ children : RawTermChildren (Generator.gen_listElim.binderShifts) scope) with
    | .childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload scrutineeChildren =>
            if scrutineeGenerator = .gen_listNil then some nilBranch
            else if hCons : scrutineeGenerator = .gen_listCons then
              match (hCons ▸ scrutineeChildren :
                  RawTermChildren (Generator.gen_listCons.binderShifts) scope) with
              | .childCons headValue (.childCons tailValue .childNil) =>
                  some (.mkGen .gen_app ()
                    (.childCons
                      (.mkGen .gen_app ()
                        (.childCons
                          (.mkGen .gen_app () (.childCons consBranch (.childCons headValue .childNil)))
                          (.childCons tailValue .childNil)))
                      (.childCons
                        (.mkGen .gen_listElim ()
                          (.childCons tailValue (.childCons nilBranch (.childCons consBranch .childNil))))
                        .childNil)))
            else none
  else if hOptionMatch : generator = .gen_optionMatch then
    match (hOptionMatch ▸ children :
        RawTermChildren (Generator.gen_optionMatch.binderShifts) scope) with
    | .childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload scrutineeChildren =>
            if scrutineeGenerator = .gen_optionNone then some noneBranch
            else if hSome : scrutineeGenerator = .gen_optionSome then
              match (hSome ▸ scrutineeChildren :
                  RawTermChildren (Generator.gen_optionSome.binderShifts) scope) with
              | .childCons value .childNil =>
                  some (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)))
            else none
  else if hEitherMatch : generator = .gen_eitherMatch then
    match (hEitherMatch ▸ children :
        RawTermChildren (Generator.gen_eitherMatch.binderShifts) scope) with
    | .childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload scrutineeChildren =>
            if hInl : scrutineeGenerator = .gen_eitherInl then
              match (hInl ▸ scrutineeChildren :
                  RawTermChildren (Generator.gen_eitherInl.binderShifts) scope) with
              | .childCons value .childNil =>
                  some (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)))
            else if hInr : scrutineeGenerator = .gen_eitherInr then
              match (hInr ▸ scrutineeChildren :
                  RawTermChildren (Generator.gen_eitherInr.binderShifts) scope) with
              | .childCons value .childNil =>
                  some (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)))
            else none
  else if hIdJ : generator = .gen_idJ then
    match (hIdJ ▸ children : RawTermChildren (Generator.gen_idJ.binderShifts) scope) with
    | .childCons baseCase (.childCons reflChild .childNil) =>
        match reflChild with
        | .mkGen reflGenerator _reflPayload _reflChildren =>
            if reflGenerator = .gen_refl then some baseCase else none
  else if hIdStrictRec : generator = .gen_idStrictRec then
    match (hIdStrictRec ▸ children :
        RawTermChildren (Generator.gen_idStrictRec.binderShifts) scope) with
    | .childCons baseCase (.childCons reflChild .childNil) =>
        match reflChild with
        | .mkGen reflGenerator _reflPayload _reflChildren =>
            if reflGenerator = .gen_refl then some baseCase else none
  else none

/-- **Soundness of root-redex firing.**  Whenever `fireRootRedex` returns `some reduct`, the term genuinely
takes that `Step` — the computable companion of `hasRootStepSource_exists_step`, but exhibiting the reduct as
a concrete `RawTerm` rather than an existential witness.  One firing case per `Step` β/ι constructor; each is
a `rfl`-keyed `injection` (the concrete firing reduces definitionally) followed by the matching constructor,
and each non-firing branch closes via a `dif_neg`/`if_neg` term and `nomatch`. -/
theorem RawTerm.fireRootRedex_sound {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fired : RawTerm.fireRootRedex generator payload children = some reduct) :
    Step (.mkGen generator payload children) reduct := by
  by_cases hApp : generator = .gen_app
  · subst hApp
    match children with
    | .childCons functionChild (.childCons argChild .childNil) =>
        match functionChild with
        | .mkGen innerGenerator innerPayload innerChildren =>
            by_cases hLam : innerGenerator = .gen_lam
            · subst hLam
              match innerChildren with
              | .childCons domainAnn (.childCons body .childNil) =>
                  have key : RawTerm.fireRootRedex .gen_app payload
                      (.childCons
                        (.mkGen .gen_lam innerPayload
                          (.childCons domainAnn (.childCons body .childNil)))
                        (.childCons argChild .childNil)) =
                      some (RawTerm.subst0 body argChild) := rfl
                  rw [key] at fired; injection fired with reductEq; rw [← reductEq]; exact Step.beta
            · have key : RawTerm.fireRootRedex .gen_app payload
                  (.childCons (.mkGen innerGenerator innerPayload innerChildren)
                    (.childCons argChild .childNil)) = none := dif_neg hLam
              rw [key] at fired; nomatch fired
  · by_cases hBoolElim : generator = .gen_boolElim
    · subst hBoolElim
      match children with
      | .childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)) =>
          match scrutinee with
          | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
              by_cases hTrue : scrutineeGenerator = .gen_boolTrue
              · subst hTrue
                match scrutineeChildren with
                | .childNil =>
                    have key : RawTerm.fireRootRedex .gen_boolElim payload
                        (.childCons (.mkGen .gen_boolTrue scrutineePayload .childNil)
                          (.childCons thenBranch (.childCons elseBranch .childNil))) =
                        some thenBranch := rfl
                    rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                    exact Step.iotaBoolTrue
              · by_cases hFalse : scrutineeGenerator = .gen_boolFalse
                · subst hFalse
                  match scrutineeChildren with
                  | .childNil =>
                      have key : RawTerm.fireRootRedex .gen_boolElim payload
                          (.childCons (.mkGen .gen_boolFalse scrutineePayload .childNil)
                            (.childCons thenBranch (.childCons elseBranch .childNil))) =
                          some elseBranch := rfl
                      rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                      exact Step.iotaBoolFalse
                · have key : RawTerm.fireRootRedex .gen_boolElim payload
                      (.childCons (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)
                        (.childCons thenBranch (.childCons elseBranch .childNil))) = none :=
                    (if_neg hTrue).trans (if_neg hFalse)
                  rw [key] at fired; nomatch fired
    · by_cases hFst : generator = .gen_fst
      · subst hFst
        match children with
        | .childCons pairChild .childNil =>
            match pairChild with
            | .mkGen pairGenerator pairPayload pairChildren =>
                by_cases hPair : pairGenerator = .gen_pair
                · subst hPair
                  match pairChildren with
                  | .childCons firstValue (.childCons secondValue .childNil) =>
                      have key : RawTerm.fireRootRedex .gen_fst payload
                          (.childCons (.mkGen .gen_pair pairPayload
                            (.childCons firstValue (.childCons secondValue .childNil)))
                            .childNil) = some firstValue := rfl
                      rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                      exact Step.iotaFstPair
                · have key : RawTerm.fireRootRedex .gen_fst payload
                      (.childCons (.mkGen pairGenerator pairPayload pairChildren) .childNil) = none :=
                    dif_neg hPair
                  rw [key] at fired; nomatch fired
      · by_cases hSnd : generator = .gen_snd
        · subst hSnd
          match children with
          | .childCons pairChild .childNil =>
              match pairChild with
              | .mkGen pairGenerator pairPayload pairChildren =>
                  by_cases hPair : pairGenerator = .gen_pair
                  · subst hPair
                    match pairChildren with
                    | .childCons firstValue (.childCons secondValue .childNil) =>
                        have key : RawTerm.fireRootRedex .gen_snd payload
                            (.childCons (.mkGen .gen_pair pairPayload
                              (.childCons firstValue (.childCons secondValue .childNil)))
                              .childNil) = some secondValue := rfl
                        rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                        exact Step.iotaSndPair
                  · have key : RawTerm.fireRootRedex .gen_snd payload
                        (.childCons (.mkGen pairGenerator pairPayload pairChildren) .childNil) = none :=
                      dif_neg hPair
                    rw [key] at fired; nomatch fired
        · by_cases hNatElim : generator = .gen_natElim
          · subst hNatElim
            match children with
            | .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
                match scrutinee with
                | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
                    by_cases hZero : scrutineeGenerator = .gen_natZero
                    · subst hZero
                      match scrutineeChildren with
                      | .childNil =>
                          have key : RawTerm.fireRootRedex .gen_natElim payload
                              (.childCons (.mkGen .gen_natZero scrutineePayload .childNil)
                                (.childCons zeroBranch (.childCons succBranch .childNil))) =
                              some zeroBranch := rfl
                          rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                          exact Step.iotaNatElimZero
                    · by_cases hSucc : scrutineeGenerator = .gen_natSucc
                      · subst hSucc
                        match scrutineeChildren with
                        | .childCons predecessor .childNil =>
                            have key : RawTerm.fireRootRedex .gen_natElim payload
                                (.childCons (.mkGen .gen_natSucc scrutineePayload
                                  (.childCons predecessor .childNil))
                                  (.childCons zeroBranch (.childCons succBranch .childNil))) =
                                some (.mkGen .gen_app ()
                                  (.childCons
                                    (.mkGen .gen_app ()
                                      (.childCons succBranch (.childCons predecessor .childNil)))
                                    (.childCons
                                      (.mkGen .gen_natElim ()
                                        (.childCons predecessor
                                          (.childCons zeroBranch (.childCons succBranch .childNil))))
                                      .childNil))) := rfl
                            rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                            exact Step.iotaNatElimSucc
                      · have key : RawTerm.fireRootRedex .gen_natElim payload
                            (.childCons (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)
                              (.childCons zeroBranch (.childCons succBranch .childNil))) = none :=
                          (if_neg hZero).trans (dif_neg hSucc)
                        rw [key] at fired; nomatch fired
          · by_cases hNatRec : generator = .gen_natRec
            · subst hNatRec
              match children with
              | .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
                  match scrutinee with
                  | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
                      by_cases hZero : scrutineeGenerator = .gen_natZero
                      · subst hZero
                        match scrutineeChildren with
                        | .childNil =>
                            have key : RawTerm.fireRootRedex .gen_natRec payload
                                (.childCons (.mkGen .gen_natZero scrutineePayload .childNil)
                                  (.childCons zeroBranch (.childCons succBranch .childNil))) =
                                some zeroBranch := rfl
                            rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                            exact Step.iotaNatRecZero
                      · by_cases hSucc : scrutineeGenerator = .gen_natSucc
                        · subst hSucc
                          match scrutineeChildren with
                          | .childCons predecessor .childNil =>
                              have key : RawTerm.fireRootRedex .gen_natRec payload
                                  (.childCons (.mkGen .gen_natSucc scrutineePayload
                                    (.childCons predecessor .childNil))
                                    (.childCons zeroBranch (.childCons succBranch .childNil))) =
                                  some (.mkGen .gen_app ()
                                    (.childCons
                                      (.mkGen .gen_app ()
                                        (.childCons succBranch (.childCons predecessor .childNil)))
                                      (.childCons
                                        (.mkGen .gen_natRec ()
                                          (.childCons predecessor
                                            (.childCons zeroBranch (.childCons succBranch .childNil))))
                                        .childNil))) := rfl
                              rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                              exact Step.iotaNatRecSucc
                        · have key : RawTerm.fireRootRedex .gen_natRec payload
                              (.childCons (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)
                                (.childCons zeroBranch (.childCons succBranch .childNil))) = none :=
                            (if_neg hZero).trans (dif_neg hSucc)
                          rw [key] at fired; nomatch fired
            · by_cases hListElim : generator = .gen_listElim
              · subst hListElim
                match children with
                | .childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)) =>
                    match scrutinee with
                    | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
                        by_cases hNil : scrutineeGenerator = .gen_listNil
                        · subst hNil
                          match scrutineeChildren with
                          | .childNil =>
                              have key : RawTerm.fireRootRedex .gen_listElim payload
                                  (.childCons (.mkGen .gen_listNil scrutineePayload .childNil)
                                    (.childCons nilBranch (.childCons consBranch .childNil))) =
                                  some nilBranch := rfl
                              rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                              exact Step.iotaListElimNil
                        · by_cases hCons : scrutineeGenerator = .gen_listCons
                          · subst hCons
                            match scrutineeChildren with
                            | .childCons headValue (.childCons tailValue .childNil) =>
                                have key : RawTerm.fireRootRedex .gen_listElim payload
                                    (.childCons (.mkGen .gen_listCons scrutineePayload
                                      (.childCons headValue (.childCons tailValue .childNil)))
                                      (.childCons nilBranch (.childCons consBranch .childNil))) =
                                    some (.mkGen .gen_app ()
                                      (.childCons
                                        (.mkGen .gen_app ()
                                          (.childCons
                                            (.mkGen .gen_app ()
                                              (.childCons consBranch (.childCons headValue .childNil)))
                                            (.childCons tailValue .childNil)))
                                        (.childCons
                                          (.mkGen .gen_listElim ()
                                            (.childCons tailValue
                                              (.childCons nilBranch (.childCons consBranch .childNil))))
                                          .childNil))) := rfl
                                rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                                exact Step.iotaListElimCons
                          · have key : RawTerm.fireRootRedex .gen_listElim payload
                                (.childCons (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)
                                  (.childCons nilBranch (.childCons consBranch .childNil))) = none :=
                              (if_neg hNil).trans (dif_neg hCons)
                            rw [key] at fired; nomatch fired
              · by_cases hOptionMatch : generator = .gen_optionMatch
                · subst hOptionMatch
                  match children with
                  | .childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)) =>
                      match scrutinee with
                      | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
                          by_cases hNone : scrutineeGenerator = .gen_optionNone
                          · subst hNone
                            match scrutineeChildren with
                            | .childNil =>
                                have key : RawTerm.fireRootRedex .gen_optionMatch payload
                                    (.childCons (.mkGen .gen_optionNone scrutineePayload .childNil)
                                      (.childCons noneBranch (.childCons someBranch .childNil))) =
                                    some noneBranch := rfl
                                rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                                exact Step.iotaOptionMatchNone
                          · by_cases hSome : scrutineeGenerator = .gen_optionSome
                            · subst hSome
                              match scrutineeChildren with
                              | .childCons value .childNil =>
                                  have key : RawTerm.fireRootRedex .gen_optionMatch payload
                                      (.childCons (.mkGen .gen_optionSome scrutineePayload
                                        (.childCons value .childNil))
                                        (.childCons noneBranch (.childCons someBranch .childNil))) =
                                      some (.mkGen .gen_app ()
                                        (.childCons someBranch (.childCons value .childNil))) := rfl
                                  rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                                  exact Step.iotaOptionMatchSome
                            · have key : RawTerm.fireRootRedex .gen_optionMatch payload
                                  (.childCons (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)
                                    (.childCons noneBranch (.childCons someBranch .childNil))) = none :=
                                (if_neg hNone).trans (dif_neg hSome)
                              rw [key] at fired; nomatch fired
                · by_cases hEitherMatch : generator = .gen_eitherMatch
                  · subst hEitherMatch
                    match children with
                    | .childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)) =>
                        match scrutinee with
                        | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
                            by_cases hInl : scrutineeGenerator = .gen_eitherInl
                            · subst hInl
                              match scrutineeChildren with
                              | .childCons value .childNil =>
                                  have key : RawTerm.fireRootRedex .gen_eitherMatch payload
                                      (.childCons (.mkGen .gen_eitherInl scrutineePayload
                                        (.childCons value .childNil))
                                        (.childCons leftBranch (.childCons rightBranch .childNil))) =
                                      some (.mkGen .gen_app ()
                                        (.childCons leftBranch (.childCons value .childNil))) := rfl
                                  rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                                  exact Step.iotaEitherMatchInl
                            · by_cases hInr : scrutineeGenerator = .gen_eitherInr
                              · subst hInr
                                match scrutineeChildren with
                                | .childCons value .childNil =>
                                    have key : RawTerm.fireRootRedex .gen_eitherMatch payload
                                        (.childCons (.mkGen .gen_eitherInr scrutineePayload
                                          (.childCons value .childNil))
                                          (.childCons leftBranch (.childCons rightBranch .childNil))) =
                                        some (.mkGen .gen_app ()
                                          (.childCons rightBranch (.childCons value .childNil))) := rfl
                                    rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                                    exact Step.iotaEitherMatchInr
                              · have key : RawTerm.fireRootRedex .gen_eitherMatch payload
                                    (.childCons
                                      (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)
                                      (.childCons leftBranch (.childCons rightBranch .childNil))) = none :=
                                  (dif_neg hInl).trans (dif_neg hInr)
                                rw [key] at fired; nomatch fired
                  · by_cases hIdJ : generator = .gen_idJ
                    · subst hIdJ
                      match children with
                      | .childCons baseCase (.childCons reflChild .childNil) =>
                          match reflChild with
                          | .mkGen reflGenerator reflPayload reflChildren =>
                              by_cases hRefl : reflGenerator = .gen_refl
                              · subst hRefl
                                match reflChildren with
                                | .childCons witness .childNil =>
                                    have key : RawTerm.fireRootRedex .gen_idJ payload
                                        (.childCons baseCase
                                          (.childCons (.mkGen .gen_refl reflPayload
                                            (.childCons witness .childNil)) .childNil)) =
                                        some baseCase := rfl
                                    rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                                    exact Step.iotaIdJRefl
                              · have key : RawTerm.fireRootRedex .gen_idJ payload
                                    (.childCons baseCase
                                      (.childCons (.mkGen reflGenerator reflPayload reflChildren)
                                        .childNil)) = none := if_neg hRefl
                                rw [key] at fired; nomatch fired
                    · by_cases hIdStrictRec : generator = .gen_idStrictRec
                      · subst hIdStrictRec
                        match children with
                        | .childCons baseCase (.childCons reflChild .childNil) =>
                            match reflChild with
                            | .mkGen reflGenerator reflPayload reflChildren =>
                                by_cases hRefl : reflGenerator = .gen_refl
                                · subst hRefl
                                  match reflChildren with
                                  | .childCons witness .childNil =>
                                      have key : RawTerm.fireRootRedex .gen_idStrictRec payload
                                          (.childCons baseCase
                                            (.childCons (.mkGen .gen_refl reflPayload
                                              (.childCons witness .childNil)) .childNil)) =
                                          some baseCase := rfl
                                      rw [key] at fired; injection fired with reductEq; rw [← reductEq]
                                      exact Step.iotaIdStrictRecRefl
                                · have key : RawTerm.fireRootRedex .gen_idStrictRec payload
                                      (.childCons baseCase
                                        (.childCons (.mkGen reflGenerator reflPayload reflChildren)
                                          .childNil)) = none := if_neg hRefl
                                  rw [key] at fired; nomatch fired
                      · -- generator is none of the redex generators: fireRootRedex returns none.
                        rw [show RawTerm.fireRootRedex generator payload children = none from by
                          unfold RawTerm.fireRootRedex
                          rw [dif_neg hApp, dif_neg hBoolElim, dif_neg hFst, dif_neg hSnd,
                            dif_neg hNatElim, dif_neg hNatRec, dif_neg hListElim, dif_neg hOptionMatch,
                            dif_neg hEitherMatch, dif_neg hIdJ, dif_neg hIdStrictRec]] at fired
                        nomatch fired

end FX1Poly.Core
