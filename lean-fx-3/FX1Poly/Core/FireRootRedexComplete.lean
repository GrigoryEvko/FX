import FX1Poly.Core.FireRootRedex
import FX1Poly.Core.RedexExtraction

/-! # FX1Poly/Core/FireRootRedexComplete
    — completeness of root-redex firing: `fireRootRedex` fires on EXACTLY the root redexes `hasRootStepSource`
      detects.

`FireRootRedex.lean` shipped the firing function plus SOUNDNESS (`fireRootRedex_sound`: a firing is a real
`Step`).  This file ships COMPLETENESS: whenever the boolean root-redex detector `hasRootStepSource` reports
a redex, `fireRootRedex` actually fires (`isSome`).  Together with soundness this pins `fireRootRedex` to
agree with `hasRootStepSource` exactly.

The contrapositive `fireRootRedex_eq_none_imp_hasRootStepSource_false` is the piece the `reduceOnce`
completeness (`reduceOnce = none → isStepNormalForm`) needs: when no root redex fires, the root-redex
detector is false, which is one of the two conjuncts of structural normality.

## Proof shape

`hasRootStepSource (mkGen g p c)` and `fireRootRedex g p c` are parallel `DecidableEq Generator` dite-chains
over the same 11 redex generators (app / boolElim / fst / snd / natElim / natRec / listElim / optionMatch /
eitherMatch / idJ / idStrictRec).  For each, `by_cases` on the generator reduces `hasRootStepSource` (defeq,
the `castToGenerator … rfl` cast collapses) to the per-redex `hasXxxRoot` source-check — an `||` of
`isXxxSource` detectors.  The existing `RedexExtraction` source-inversions (`isLamSource_eq_lam`,
`isBoolTrueSource_eq_boolTrue`, …) turn each true detector into the concrete redex shape, on which
`fireRootRedex` fires by `rfl`.  The non-redex `else` reduces `hasRootStepSource` to `false`, contradicting
the hypothesis.  Multi-shape generators (`||` of two detectors) `cases` on the first detector; the
`false || b ≡ b` defeq retypes the residual.

## Zero-axiom verification

`by_cases` on `DecidableEq Generator`, `match` spine destructuring, the propext-free source-inversions,
`rfl` firings, `dif_neg` rewrites for the `else`, and `nomatch`.  The `||`-split uses `cases` + defeq-retype
(never `rw [Bool.or_eq_true]`, which would leak propext).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Completeness of root-redex firing.**  If `hasRootStepSource` detects a root redex, `fireRootRedex`
fires — so the firer's domain is exactly the detector's truth set. -/
theorem RawTerm.hasRootStepSource_imp_fireRootRedex_isSome {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (detected : RawTerm.hasRootStepSource (.mkGen generator payload children) = true) :
    (RawTerm.fireRootRedex generator payload children).isSome = true := by
  by_cases hApp : generator = .gen_app
  · subst hApp
    match children with
    | .childCons functionChild (.childCons _argChild .childNil) =>
        have srcTrue : RawTerm.isLamSource functionChild = true := detected
        obtain ⟨domainAnn, body, hBody⟩ := isLamSource_eq_lam srcTrue
        subst hBody; rfl
  · by_cases hBoolElim : generator = .gen_boolElim
    · subst hBoolElim
      -- Phase-Z spine: (motive, then, else, scrutinee); the scrutinee is the LAST child.
      match children with
      | .childCons _motive
          (.childCons _thenBranch (.childCons _elseBranch (.childCons scrutinee .childNil))) =>
          have srcTrue :
              (RawTerm.isBoolTrueSource scrutinee || RawTerm.isBoolFalseSource scrutinee) = true := detected
          cases hTrue : RawTerm.isBoolTrueSource scrutinee with
          | true => have hEq := isBoolTrueSource_eq_boolTrue hTrue; subst hEq; rfl
          | false =>
              rw [hTrue] at srcTrue
              replace srcTrue : RawTerm.isBoolFalseSource scrutinee = true := srcTrue
              have hEq := isBoolFalseSource_eq_boolFalse srcTrue; subst hEq; rfl
    · by_cases hFst : generator = .gen_fst
      · subst hFst
        match children with
        | .childCons pairChild .childNil =>
            have srcTrue : RawTerm.isPairSource pairChild = true := detected
            obtain ⟨firstValue, secondValue, hPair⟩ := isPairSource_eq_pair srcTrue
            subst hPair; rfl
      · by_cases hSnd : generator = .gen_snd
        · subst hSnd
          match children with
          | .childCons pairChild .childNil =>
              have srcTrue : RawTerm.isPairSource pairChild = true := detected
              obtain ⟨firstValue, secondValue, hPair⟩ := isPairSource_eq_pair srcTrue
              subst hPair; rfl
        · by_cases hNatElim : generator = .gen_natElim
          · subst hNatElim
            -- Phase-Z spine: (motive, zero, succ, scrutinee); the scrutinee is the LAST child.
            match children with
            | .childCons _motive
                (.childCons _zeroBranch (.childCons _succBranch (.childCons scrutinee .childNil))) =>
                have srcTrue :
                    (RawTerm.isNatZeroSource scrutinee || RawTerm.isNatSuccSource scrutinee) = true :=
                  detected
                cases hZero : RawTerm.isNatZeroSource scrutinee with
                | true => have hEq := isNatZeroSource_eq_natZero hZero; subst hEq; rfl
                | false =>
                    rw [hZero] at srcTrue
                    replace srcTrue : RawTerm.isNatSuccSource scrutinee = true := srcTrue
                    obtain ⟨predecessor, hSucc⟩ := isNatSuccSource_eq_natSucc srcTrue
                    subst hSucc; rfl
          · by_cases hNatRec : generator = .gen_natRec
            · subst hNatRec
              -- Phase-Z spine: (motive, zero, succ, scrutinee); the scrutinee is the LAST child.
              match children with
              | .childCons _motive
                  (.childCons _zeroBranch (.childCons _succBranch (.childCons scrutinee .childNil))) =>
                  have srcTrue :
                      (RawTerm.isNatZeroSource scrutinee || RawTerm.isNatSuccSource scrutinee) = true :=
                    detected
                  cases hZero : RawTerm.isNatZeroSource scrutinee with
                  | true => have hEq := isNatZeroSource_eq_natZero hZero; subst hEq; rfl
                  | false =>
                      rw [hZero] at srcTrue
                      replace srcTrue : RawTerm.isNatSuccSource scrutinee = true := srcTrue
                      obtain ⟨predecessor, hSucc⟩ := isNatSuccSource_eq_natSucc srcTrue
                      subst hSucc; rfl
            · by_cases hListElim : generator = .gen_listElim
              · subst hListElim
                -- Phase-Z spine: (motive, nil, cons, scrutinee); the scrutinee is the LAST child.
                match children with
                | .childCons _motive
                    (.childCons _nilBranch (.childCons _consBranch (.childCons scrutinee .childNil))) =>
                    have srcTrue :
                        (RawTerm.isListNilSource scrutinee || RawTerm.isListConsSource scrutinee) = true :=
                      detected
                    cases hNil : RawTerm.isListNilSource scrutinee with
                    | true => have hEq := isListNilSource_eq_listNil hNil; subst hEq; rfl
                    | false =>
                        rw [hNil] at srcTrue
                        replace srcTrue : RawTerm.isListConsSource scrutinee = true := srcTrue
                        obtain ⟨headValue, tailValue, hCons⟩ := isListConsSource_eq_listCons srcTrue
                        subst hCons; rfl
              · by_cases hOptionMatch : generator = .gen_optionMatch
                · subst hOptionMatch
                  -- Phase-Z spine: (motive, none, some, scrutinee); the scrutinee is the LAST child.
                  match children with
                  | .childCons _motive
                      (.childCons _noneBranch (.childCons _someBranch (.childCons scrutinee .childNil))) =>
                      have srcTrue :
                          (RawTerm.isOptionNoneSource scrutinee ||
                            RawTerm.isOptionSomeSource scrutinee) = true := detected
                      cases hNone : RawTerm.isOptionNoneSource scrutinee with
                      | true => have hEq := isOptionNoneSource_eq_optionNone hNone; subst hEq; rfl
                      | false =>
                          rw [hNone] at srcTrue
                          replace srcTrue : RawTerm.isOptionSomeSource scrutinee = true := srcTrue
                          obtain ⟨value, hSome⟩ := isOptionSomeSource_eq_optionSome srcTrue
                          subst hSome; rfl
                · by_cases hEitherMatch : generator = .gen_eitherMatch
                  · subst hEitherMatch
                    -- Phase-Z spine: (motive, left, right, scrutinee); the scrutinee is the LAST child.
                    match children with
                    | .childCons _motive
                        (.childCons _leftBranch (.childCons _rightBranch (.childCons scrutinee .childNil))) =>
                        have srcTrue :
                            (RawTerm.isEitherInlSource scrutinee ||
                              RawTerm.isEitherInrSource scrutinee) = true := detected
                        cases hInl : RawTerm.isEitherInlSource scrutinee with
                        | true =>
                            obtain ⟨value, hEq⟩ := isEitherInlSource_eq_eitherInl hInl; subst hEq; rfl
                        | false =>
                            rw [hInl] at srcTrue
                            replace srcTrue : RawTerm.isEitherInrSource scrutinee = true := srcTrue
                            obtain ⟨value, hEq⟩ := isEitherInrSource_eq_eitherInr srcTrue; subst hEq; rfl
                  · by_cases hIdJ : generator = .gen_idJ
                    · subst hIdJ
                      match children with
                      | .childCons _baseCase (.childCons witnessChild .childNil) =>
                          have srcTrue : RawTerm.isReflSource witnessChild = true := detected
                          obtain ⟨rawWitness, hRefl⟩ := isReflSource_eq_refl srcTrue
                          subst hRefl; rfl
                    · by_cases hIdStrictRec : generator = .gen_idStrictRec
                      · subst hIdStrictRec
                        match children with
                        | .childCons _baseCase (.childCons witnessChild .childNil) =>
                            have srcTrue : RawTerm.isReflSource witnessChild = true := detected
                            obtain ⟨rawWitness, hRefl⟩ := isReflSource_eq_refl srcTrue
                            subst hRefl; rfl
                      · -- generator is none of the 11 redex generators: hasRootStepSource is false.
                        dsimp only [RawTerm.hasRootStepSource] at detected
                        rw [dif_neg hApp, dif_neg hBoolElim, dif_neg hFst, dif_neg hSnd,
                          dif_neg hNatElim, dif_neg hNatRec, dif_neg hListElim, dif_neg hOptionMatch,
                          dif_neg hEitherMatch, dif_neg hIdJ, dif_neg hIdStrictRec] at detected
                        nomatch detected

/-- **Contrapositive: no firing implies no detected redex.**  When `fireRootRedex` returns `none`, the
root-redex detector `hasRootStepSource` is `false` — the root half of structural normality.  This is the
ingredient `reduceOnce` completeness (`reduceOnce = none → isStepNormalForm`) consumes. -/
theorem RawTerm.fireRootRedex_eq_none_imp_hasRootStepSource_false {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (notFired : RawTerm.fireRootRedex generator payload children = none) :
    RawTerm.hasRootStepSource (.mkGen generator payload children) = false := by
  cases hDetected : RawTerm.hasRootStepSource (.mkGen generator payload children) with
  | false => rfl
  | true =>
      have isSome := RawTerm.hasRootStepSource_imp_fireRootRedex_isSome hDetected
      rw [notFired] at isSome
      nomatch isSome

end FX1Poly.Core
