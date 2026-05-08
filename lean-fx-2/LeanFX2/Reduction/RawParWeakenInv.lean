import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Foundation.RawPartialRename

/-! # Reduction/RawParWeakenInv — par-step weaken-image preservation

The headline lemma:

```
theorem RawStep.par.weaken_inv : par X.weaken Y → ∃ Y', Y = Y'.weaken
```

is proved through the more general `rename_inj_inv`: for any
injective renaming `rho`, a parallel reduction starting from a
renamed source `sourceTerm.rename rho` lands in another renamed
target `targetInner.rename rho`.  Specializing to the canonical
weaken renaming via `RawRenaming.weaken_injective` recovers the
headline lemma.

## Proof shape

Outer induction on `sourceTerm` (67 ctors), inner inversion on
`parStep`.  Most ctors have only `refl` or one cong rule; a few
(app, fst, snd, modElim, glueElim, refineElim, recordProj,
codataDest, pathApp, idJ, idStrictRec, plus the elim/match family)
also have beta/iota rules whose contractum requires the
`subst0_rename_commute` reshape and a shape-inversion helper to
expose the redex pattern after renaming.

## Zero-axiom

* No wildcards in match (per `feedback_lean_zero_axiom_match.md`).
* `cases` on indexed-inductive `RawStep.par` with a fixed `RawTerm`
  source ctor at a definite scope is propext-clean
  (single-Nat-indexed inductive — see
  `feedback_lean_match_arity_axioms.md`).
* Binder recursion threads `rho.lift` whose injectivity is
  established by `RawRenaming.lift_injective`.
-/

namespace LeanFX2

/-- `RawRenaming.weaken` is injective: `weaken a = weaken b → a = b`.

Used by `weaken_inv` to specialize the general `rename_inj_inv` to
the weaken case.  Standalone-useful. -/
theorem RawRenaming.weaken_injective {scope : Nat} :
    ∀ (a b : Fin scope), RawRenaming.weaken a = RawRenaming.weaken b → a = b := by
  intro a b h
  cases a with
  | mk aVal aLt =>
    cases b with
    | mk bVal bLt =>
      simp only [RawRenaming.weaken, Fin.succ] at h
      have hValSucc : aVal + 1 = bVal + 1 := Fin.mk.inj h
      have hVal : aVal = bVal := Nat.succ.inj hValSucc
      cases hVal
      rfl

/-- Lifting an injective renaming preserves injectivity:
if `rho` is injective on `Fin sourceScope`, then `rho.lift` is
injective on `Fin (sourceScope + 1)`.

Used by `rename_inj_inv` to recurse on binder cases: the body of
`lam`, `pathLam`, `piTyCode`, `sigmaTyCode` lives at scope+1 and we
need an injective renaming there. -/
theorem RawRenaming.lift_injective {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (rhoInj : ∀ a b, rho a = rho b → a = b) :
    ∀ a b, rho.lift a = rho.lift b → a = b := by
  intro a b h
  cases a with
  | mk aVal aLt =>
    cases b with
    | mk bVal bLt =>
      cases aVal with
      | zero =>
        cases bVal with
        | zero => rfl
        | succ bPred =>
            simp only [RawRenaming.lift, Fin.succ] at h
            cases h
      | succ aPred =>
        cases bVal with
        | zero =>
            simp only [RawRenaming.lift, Fin.succ] at h
            cases h
        | succ bPred =>
            have aPredLt : aPred < sourceScope := Nat.lt_of_succ_lt_succ aLt
            have bPredLt : bPred < sourceScope := Nat.lt_of_succ_lt_succ bLt
            simp only [RawRenaming.lift, Fin.succ] at h
            have hValSucc : (rho ⟨aPred, aPredLt⟩).val + 1 = (rho ⟨bPred, bPredLt⟩).val + 1 :=
              Fin.mk.inj h
            have hVal : (rho ⟨aPred, aPredLt⟩).val = (rho ⟨bPred, bPredLt⟩).val :=
              Nat.succ.inj hValSucc
            have hRho : rho ⟨aPred, aPredLt⟩ = rho ⟨bPred, bPredLt⟩ :=
              Fin.eq_of_val_eq hVal
            have hPred := rhoInj _ _ hRho
            have : aPred = bPred := Fin.mk.inj hPred
            cases this
            rfl

/-! ## Rename-shape inversion helpers.

For each canonical RawTerm ctor C that appears in some redex/Deep
par rule, we need: if t.rename rho = C args, then t = C args' for
some args' whose rename equals args.  These are mechanical 67-way
cases t enumerations where all non-C ctors are dismissed via
simp only [RawTerm.rename]; nomatch h. -/

/-- Shape inversion for `boolTrue`. -/
private theorem RawTerm.rename_eq_boolTrue_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    (h : term.rename rho = (RawTerm.boolTrue : RawTerm targetScope)) :
    term = RawTerm.boolTrue := by
  cases term with
  | boolTrue =>
    rfl
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `boolFalse`. -/
private theorem RawTerm.rename_eq_boolFalse_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    (h : term.rename rho = (RawTerm.boolFalse : RawTerm targetScope)) :
    term = RawTerm.boolFalse := by
  cases term with
  | boolFalse =>
    rfl
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `natZero`. -/
private theorem RawTerm.rename_eq_natZero_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    (h : term.rename rho = (RawTerm.natZero : RawTerm targetScope)) :
    term = RawTerm.natZero := by
  cases term with
  | natZero =>
    rfl
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `listNil`. -/
private theorem RawTerm.rename_eq_listNil_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    (h : term.rename rho = (RawTerm.listNil : RawTerm targetScope)) :
    term = RawTerm.listNil := by
  cases term with
  | listNil =>
    rfl
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `optionNone`. -/
private theorem RawTerm.rename_eq_optionNone_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    (h : term.rename rho = (RawTerm.optionNone : RawTerm targetScope)) :
    term = RawTerm.optionNone := by
  cases term with
  | optionNone =>
    rfl
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `interval0`. -/
private theorem RawTerm.rename_eq_interval0_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    (h : term.rename rho = (RawTerm.interval0 : RawTerm targetScope)) :
    term = RawTerm.interval0 := by
  cases term with
  | interval0 =>
    rfl
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `interval1`. -/
private theorem RawTerm.rename_eq_interval1_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    (h : term.rename rho = (RawTerm.interval1 : RawTerm targetScope)) :
    term = RawTerm.interval1 := by
  cases term with
  | interval1 =>
    rfl
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `natSucc`. -/
private theorem RawTerm.rename_eq_natSucc_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.natSucc target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.natSucc inner ∧ target = inner.rename rho := by
  cases term with
  | natSucc inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `optionSome`. -/
private theorem RawTerm.rename_eq_optionSome_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.optionSome target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.optionSome inner ∧ target = inner.rename rho := by
  cases term with
  | optionSome inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `eitherInl`. -/
private theorem RawTerm.rename_eq_eitherInl_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.eitherInl target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.eitherInl inner ∧ target = inner.rename rho := by
  cases term with
  | eitherInl inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `eitherInr`. -/
private theorem RawTerm.rename_eq_eitherInr_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.eitherInr target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.eitherInr inner ∧ target = inner.rename rho := by
  cases term with
  | eitherInr inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `refl`. -/
private theorem RawTerm.rename_eq_refl_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.refl target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.refl inner ∧ target = inner.rename rho := by
  cases term with
  | refl inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `modIntro`. -/
private theorem RawTerm.rename_eq_modIntro_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.modIntro target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.modIntro inner ∧ target = inner.rename rho := by
  cases term with
  | modIntro inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `idStrictRefl`. -/
private theorem RawTerm.rename_eq_idStrictRefl_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.idStrictRefl target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.idStrictRefl inner ∧ target = inner.rename rho := by
  cases term with
  | idStrictRefl inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `recordIntro`. -/
private theorem RawTerm.rename_eq_recordIntro_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.recordIntro target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.recordIntro inner ∧ target = inner.rename rho := by
  cases term with
  | recordIntro inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `pathLam` (binder). -/
private theorem RawTerm.rename_eq_pathLam_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm (targetScope + 1)}
    (h : term.rename rho = RawTerm.pathLam target) :
    ∃ inner : RawTerm (sourceScope + 1),
      term = RawTerm.pathLam inner ∧ target = inner.rename rho.lift := by
  cases term with
  | pathLam inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho.lift = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `pair`. -/
private theorem RawTerm.rename_eq_pair_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {target1 target2 : RawTerm targetScope}
    (h : term.rename rho = RawTerm.pair target1 target2) :
    ∃ inner1 inner2 : RawTerm sourceScope,
      term = RawTerm.pair inner1 inner2 ∧
        target1 = inner1.rename rho ∧ target2 = inner2.rename rho := by
  cases term with
  | pair inner1 inner2 =>
    refine ⟨inner1, inner2, rfl, ?_, ?_⟩
    · simp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · simp only [RawTerm.rename] at h
      injection h with _ _ h2; exact h2.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `listCons`. -/
private theorem RawTerm.rename_eq_listCons_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {target1 target2 : RawTerm targetScope}
    (h : term.rename rho = RawTerm.listCons target1 target2) :
    ∃ inner1 inner2 : RawTerm sourceScope,
      term = RawTerm.listCons inner1 inner2 ∧
        target1 = inner1.rename rho ∧ target2 = inner2.rename rho := by
  cases term with
  | listCons inner1 inner2 =>
    refine ⟨inner1, inner2, rfl, ?_, ?_⟩
    · simp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · simp only [RawTerm.rename] at h
      injection h with _ _ h2; exact h2.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `glueIntro`. -/
private theorem RawTerm.rename_eq_glueIntro_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {target1 target2 : RawTerm targetScope}
    (h : term.rename rho = RawTerm.glueIntro target1 target2) :
    ∃ inner1 inner2 : RawTerm sourceScope,
      term = RawTerm.glueIntro inner1 inner2 ∧
        target1 = inner1.rename rho ∧ target2 = inner2.rename rho := by
  cases term with
  | glueIntro inner1 inner2 =>
    refine ⟨inner1, inner2, rfl, ?_, ?_⟩
    · simp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · simp only [RawTerm.rename] at h
      injection h with _ _ h2; exact h2.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `refineIntro`. -/
private theorem RawTerm.rename_eq_refineIntro_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {target1 target2 : RawTerm targetScope}
    (h : term.rename rho = RawTerm.refineIntro target1 target2) :
    ∃ inner1 inner2 : RawTerm sourceScope,
      term = RawTerm.refineIntro inner1 inner2 ∧
        target1 = inner1.rename rho ∧ target2 = inner2.rename rho := by
  cases term with
  | refineIntro inner1 inner2 =>
    refine ⟨inner1, inner2, rfl, ?_, ?_⟩
    · simp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · simp only [RawTerm.rename] at h
      injection h with _ _ h2; exact h2.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `codataUnfold`. -/
private theorem RawTerm.rename_eq_codataUnfold_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {target1 target2 : RawTerm targetScope}
    (h : term.rename rho = RawTerm.codataUnfold target1 target2) :
    ∃ inner1 inner2 : RawTerm sourceScope,
      term = RawTerm.codataUnfold inner1 inner2 ∧
        target1 = inner1.rename rho ∧ target2 = inner2.rename rho := by
  cases term with
  | codataUnfold inner1 inner2 =>
    refine ⟨inner1, inner2, rfl, ?_, ?_⟩
    · simp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · simp only [RawTerm.rename] at h
      injection h with _ _ h2; exact h2.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | lam _ => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `lam` (binder). -/
private theorem RawTerm.rename_eq_lam_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm (targetScope + 1)}
    (h : term.rename rho = RawTerm.lam target) :
    ∃ inner : RawTerm (sourceScope + 1),
      term = RawTerm.lam inner ∧ target = inner.rename rho.lift := by
  cases term with
  | lam inner =>
    refine ⟨inner, rfl, ?_⟩
    simp only [RawTerm.rename] at h
    have : inner.rename rho.lift = target := by injection h
    exact this.symm
  | var _ => simp only [RawTerm.rename] at h; nomatch h
  | unit => simp only [RawTerm.rename] at h; nomatch h
  | app _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pair _ _ => simp only [RawTerm.rename] at h; nomatch h
  | fst _ => simp only [RawTerm.rename] at h; nomatch h
  | snd _ => simp only [RawTerm.rename] at h; nomatch h
  | boolTrue => simp only [RawTerm.rename] at h; nomatch h
  | boolFalse => simp only [RawTerm.rename] at h; nomatch h
  | boolElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natZero => simp only [RawTerm.rename] at h; nomatch h
  | natSucc _ => simp only [RawTerm.rename] at h; nomatch h
  | natElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | natRec _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listNil => simp only [RawTerm.rename] at h; nomatch h
  | listCons _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listElim _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | optionNone => simp only [RawTerm.rename] at h; nomatch h
  | optionSome _ => simp only [RawTerm.rename] at h; nomatch h
  | optionMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInl _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherInr _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherMatch _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refl _ => simp only [RawTerm.rename] at h; nomatch h
  | idJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | modIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | modElim _ => simp only [RawTerm.rename] at h; nomatch h
  | subsume _ => simp only [RawTerm.rename] at h; nomatch h
  | interval0 => simp only [RawTerm.rename] at h; nomatch h
  | interval1 => simp only [RawTerm.rename] at h; nomatch h
  | intervalOpp _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalMeet _ _ => simp only [RawTerm.rename] at h; nomatch h
  | intervalJoin _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathLam _ => simp only [RawTerm.rename] at h; nomatch h
  | pathApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | glueElim _ => simp only [RawTerm.rename] at h; nomatch h
  | transp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | hcomp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqJ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqFunext _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRefl _ => simp only [RawTerm.rename] at h; nomatch h
  | idStrictRec _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApp _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineIntro _ _ => simp only [RawTerm.rename] at h; nomatch h
  | refineElim _ => simp only [RawTerm.rename] at h; nomatch h
  | recordIntro _ => simp only [RawTerm.rename] at h; nomatch h
  | recordProj _ => simp only [RawTerm.rename] at h; nomatch h
  | codataUnfold _ _ => simp only [RawTerm.rename] at h; nomatch h
  | codataDest _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionSend _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sessionRecv _ => simp only [RawTerm.rename] at h; nomatch h
  | effectPerform _ _ => simp only [RawTerm.rename] at h; nomatch h
  | universeCode _ => simp only [RawTerm.rename] at h; nomatch h
  | arrowCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | piTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sigmaTyCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | productCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | sumCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | listCode _ => simp only [RawTerm.rename] at h; nomatch h
  | optionCode _ => simp only [RawTerm.rename] at h; nomatch h
  | eitherCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idCode _ _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCode _ _ => simp only [RawTerm.rename] at h; nomatch h
  | cumulUpMarker _ => simp only [RawTerm.rename] at h; nomatch h

/-! ## Headline: par-step preserves the image of an injective renaming.

If `RawStep.par (sourceTerm.rename rho) targetAfter` and `rho` is
injective, then `targetAfter = targetInner.rename rho` for some
`targetInner : RawTerm sourceScope`.  Proved by structural induction
on `sourceTerm` (67 ctors).  Specialized below to the canonical
weaken case via `RawRenaming.weaken_injective`. -/

theorem RawStep.par.rename_inj_inv :
    ∀ {sourceScope : Nat} (sourceTerm : RawTerm sourceScope)
      {targetScope : Nat} (rho : RawRenaming sourceScope targetScope),
      (∀ a b, rho a = rho b → a = b) →
      ∀ {targetAfter : RawTerm targetScope},
      RawStep.par (sourceTerm.rename rho) targetAfter →
      ∃ targetInner : RawTerm sourceScope,
        targetAfter = targetInner.rename rho := by
  intro sourceScope sourceTerm
  induction sourceTerm with
  -- ============== Atom ctors (refl-only) ==============
  | var position =>
    intro _ rho _ _ parStep
    change RawStep.par (RawTerm.var (rho position)) _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.var position, rfl⟩
  | unit =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.unit _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.unit, rfl⟩
  | boolTrue =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.boolTrue _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.boolTrue, rfl⟩
  | boolFalse =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.boolFalse _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.boolFalse, rfl⟩
  | natZero =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.natZero _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.natZero, rfl⟩
  | listNil =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.listNil _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.listNil, rfl⟩
  | optionNone =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.optionNone _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.optionNone, rfl⟩
  | interval0 =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.interval0 _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.interval0, rfl⟩
  | interval1 =>
    intro _ _ _ _ parStep
    change RawStep.par RawTerm.interval1 _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.interval1, rfl⟩
  | universeCode innerLevel =>
    intro _ _ _ _ parStep
    change RawStep.par (RawTerm.universeCode innerLevel) _ at parStep
    cases parStep
    case refl _ => exact ⟨RawTerm.universeCode innerLevel, rfl⟩
  -- ============== Single-subterm cong (no redex) ==============
  | natSucc predecessor predIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.natSucc (predecessor.rename rho)) _ at parStep
    obtain ⟨predTarget, hTarget, predStep⟩ := RawStep.par.natSucc_inv parStep
    obtain ⟨predInner, hPredInner⟩ := predIH rho rhoInj predStep
    refine ⟨RawTerm.natSucc predInner, ?_⟩
    rw [hTarget, hPredInner]; rfl
  | optionSome valueTerm valueIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.optionSome (valueTerm.rename rho)) _ at parStep
    obtain ⟨valueTarget, hTarget, valueStep⟩ := RawStep.par.optionSome_inv parStep
    obtain ⟨valueInner, hValueInner⟩ := valueIH rho rhoInj valueStep
    refine ⟨RawTerm.optionSome valueInner, ?_⟩
    rw [hTarget, hValueInner]; rfl
  | eitherInl valueTerm valueIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.eitherInl (valueTerm.rename rho)) _ at parStep
    obtain ⟨valueTarget, hTarget, valueStep⟩ := RawStep.par.eitherInl_inv parStep
    obtain ⟨valueInner, hValueInner⟩ := valueIH rho rhoInj valueStep
    refine ⟨RawTerm.eitherInl valueInner, ?_⟩
    rw [hTarget, hValueInner]; rfl
  | eitherInr valueTerm valueIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.eitherInr (valueTerm.rename rho)) _ at parStep
    obtain ⟨valueTarget, hTarget, valueStep⟩ := RawStep.par.eitherInr_inv parStep
    obtain ⟨valueInner, hValueInner⟩ := valueIH rho rhoInj valueStep
    refine ⟨RawTerm.eitherInr valueInner, ?_⟩
    rw [hTarget, hValueInner]; rfl
  | refl rawWitness witnessIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.refl (rawWitness.rename rho)) _ at parStep
    obtain ⟨witnessTarget, hTarget, witnessStep⟩ := RawStep.par.refl_inv parStep
    obtain ⟨witnessInner, hWitnessInner⟩ := witnessIH rho rhoInj witnessStep
    refine ⟨RawTerm.refl witnessInner, ?_⟩
    rw [hTarget, hWitnessInner]; rfl
  | modIntro inner innerIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.modIntro (inner.rename rho)) _ at parStep
    obtain ⟨innerTarget, hTarget, innerStep⟩ := RawStep.par.modIntro_inv parStep
    obtain ⟨innerInner, hInnerInner⟩ := innerIH rho rhoInj innerStep
    refine ⟨RawTerm.modIntro innerInner, ?_⟩
    rw [hTarget, hInnerInner]; rfl
  | subsume inner innerIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.subsume (inner.rename rho)) _ at parStep
    obtain ⟨innerTarget, hTarget, innerStep⟩ := RawStep.par.subsume_inv parStep
    obtain ⟨innerInner, hInnerInner⟩ := innerIH rho rhoInj innerStep
    refine ⟨RawTerm.subsume innerInner, ?_⟩
    rw [hTarget, hInnerInner]; rfl
  | intervalOpp intervalTerm intervalIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.intervalOpp (intervalTerm.rename rho)) _ at parStep
    obtain ⟨intervalTarget, hTarget, intervalStep⟩ :=
      RawStep.par.intervalOpp_inv parStep
    obtain ⟨intervalInner, hIntervalInner⟩ := intervalIH rho rhoInj intervalStep
    refine ⟨RawTerm.intervalOpp intervalInner, ?_⟩
    rw [hTarget, hIntervalInner]; rfl
  | oeqRefl witness witnessIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.oeqRefl (witness.rename rho)) _ at parStep
    obtain ⟨witnessTarget, hTarget, witnessStep⟩ := RawStep.par.oeqRefl_inv parStep
    obtain ⟨witnessInner, hWitnessInner⟩ := witnessIH rho rhoInj witnessStep
    refine ⟨RawTerm.oeqRefl witnessInner, ?_⟩
    rw [hTarget, hWitnessInner]; rfl
  | oeqFunext pointwiseEquality pointwiseIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par
      (RawTerm.oeqFunext (pointwiseEquality.rename rho)) _ at parStep
    obtain ⟨pointwiseTarget, hTarget, pointwiseStep⟩ :=
      RawStep.par.oeqFunext_inv parStep
    obtain ⟨pointwiseInner, hPointwiseInner⟩ :=
      pointwiseIH rho rhoInj pointwiseStep
    refine ⟨RawTerm.oeqFunext pointwiseInner, ?_⟩
    rw [hTarget, hPointwiseInner]; rfl
  | idStrictRefl witness witnessIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.idStrictRefl (witness.rename rho)) _ at parStep
    obtain ⟨witnessTarget, hTarget, witnessStep⟩ :=
      RawStep.par.idStrictRefl_inv parStep
    obtain ⟨witnessInner, hWitnessInner⟩ := witnessIH rho rhoInj witnessStep
    refine ⟨RawTerm.idStrictRefl witnessInner, ?_⟩
    rw [hTarget, hWitnessInner]; rfl
  | recordIntro firstField firstIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.recordIntro (firstField.rename rho)) _ at parStep
    obtain ⟨firstTarget, hTarget, firstStep⟩ := RawStep.par.recordIntro_inv parStep
    obtain ⟨firstInner, hFirstInner⟩ := firstIH rho rhoInj firstStep
    refine ⟨RawTerm.recordIntro firstInner, ?_⟩
    rw [hTarget, hFirstInner]; rfl
  | sessionRecv channel channelIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.sessionRecv (channel.rename rho)) _ at parStep
    obtain ⟨channelTarget, hTarget, channelStep⟩ :=
      RawStep.par.sessionRecv_inv parStep
    obtain ⟨channelInner, hChannelInner⟩ := channelIH rho rhoInj channelStep
    refine ⟨RawTerm.sessionRecv channelInner, ?_⟩
    rw [hTarget, hChannelInner]; rfl
  | listCode elementCode elementIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.listCode (elementCode.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.listCode elementCode, rfl⟩
    | listCodeCong elementStep =>
      obtain ⟨elementInner, hElementInner⟩ := elementIH rho rhoInj elementStep
      refine ⟨RawTerm.listCode elementInner, ?_⟩
      rw [hElementInner]; rfl
  | optionCode elementCode elementIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.optionCode (elementCode.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.optionCode elementCode, rfl⟩
    | optionCodeCong elementStep =>
      obtain ⟨elementInner, hElementInner⟩ := elementIH rho rhoInj elementStep
      refine ⟨RawTerm.optionCode elementInner, ?_⟩
      rw [hElementInner]; rfl
  | cumulUpMarker innerCodeRaw innerIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par
      (RawTerm.cumulUpMarker (innerCodeRaw.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.cumulUpMarker innerCodeRaw, rfl⟩
    | cumulUpMarkerCong innerStep =>
      obtain ⟨innerInner, hInnerInner⟩ := innerIH rho rhoInj innerStep
      refine ⟨RawTerm.cumulUpMarker innerInner, ?_⟩
      rw [hInnerInner]; rfl
  -- ============== Two-subterm cong (no redex parent) ==============
  | pair firstValue secondValue firstIH secondIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par
      (RawTerm.pair (firstValue.rename rho) (secondValue.rename rho)) _ at parStep
    obtain ⟨firstTarget, secondTarget, hTarget, firstStep, secondStep⟩ :=
      RawStep.par.pair_inv parStep
    obtain ⟨firstInner, hFirstInner⟩ := firstIH rho rhoInj firstStep
    obtain ⟨secondInner, hSecondInner⟩ := secondIH rho rhoInj secondStep
    refine ⟨RawTerm.pair firstInner secondInner, ?_⟩
    rw [hTarget, hFirstInner, hSecondInner]; rfl
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.intervalMeet (leftInterval.rename rho)
      (rightInterval.rename rho)) _ at parStep
    obtain ⟨leftTarget, rightTarget, hTarget, leftStep, rightStep⟩ :=
      RawStep.par.intervalMeet_inv parStep
    obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
    obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
    refine ⟨RawTerm.intervalMeet leftInner rightInner, ?_⟩
    rw [hTarget, hLeftInner, hRightInner]; rfl
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.intervalJoin (leftInterval.rename rho)
      (rightInterval.rename rho)) _ at parStep
    obtain ⟨leftTarget, rightTarget, hTarget, leftStep, rightStep⟩ :=
      RawStep.par.intervalJoin_inv parStep
    obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
    obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
    refine ⟨RawTerm.intervalJoin leftInner rightInner, ?_⟩
    rw [hTarget, hLeftInner, hRightInner]; rfl
  | transp path source pathIH sourceIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.transp (path.rename rho)
      (source.rename rho)) _ at parStep
    obtain ⟨pathTarget, sourceTarget, hTarget, pathStep, sourceStep⟩ :=
      RawStep.par.transp_inv parStep
    obtain ⟨pathInner, hPathInner⟩ := pathIH rho rhoInj pathStep
    obtain ⟨sourceInner, hSourceInner⟩ := sourceIH rho rhoInj sourceStep
    refine ⟨RawTerm.transp pathInner sourceInner, ?_⟩
    rw [hTarget, hPathInner, hSourceInner]; rfl
  | hcomp sides cap sidesIH capIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.hcomp (sides.rename rho)
      (cap.rename rho)) _ at parStep
    obtain ⟨sidesTarget, capTarget, hTarget, sidesStep, capStep⟩ :=
      RawStep.par.hcomp_inv parStep
    obtain ⟨sidesInner, hSidesInner⟩ := sidesIH rho rhoInj sidesStep
    obtain ⟨capInner, hCapInner⟩ := capIH rho rhoInj capStep
    refine ⟨RawTerm.hcomp sidesInner capInner, ?_⟩
    rw [hTarget, hSidesInner, hCapInner]; rfl
  | oeqJ baseCase witness baseIH witnessIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.oeqJ (baseCase.rename rho)
      (witness.rename rho)) _ at parStep
    obtain ⟨baseTarget, witnessTarget, hTarget, baseStep, witnessStep⟩ :=
      RawStep.par.oeqJ_inv parStep
    obtain ⟨baseInner, hBaseInner⟩ := baseIH rho rhoInj baseStep
    obtain ⟨witnessInner, hWitnessInner⟩ := witnessIH rho rhoInj witnessStep
    refine ⟨RawTerm.oeqJ baseInner witnessInner, ?_⟩
    rw [hTarget, hBaseInner, hWitnessInner]; rfl
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.equivIntro (forwardFn.rename rho)
      (backwardFn.rename rho)) _ at parStep
    obtain ⟨forwardTarget, backwardTarget, hTarget, forwardStep, backwardStep⟩ :=
      RawStep.par.equivIntro_inv parStep
    obtain ⟨forwardInner, hForwardInner⟩ := forwardIH rho rhoInj forwardStep
    obtain ⟨backwardInner, hBackwardInner⟩ := backwardIH rho rhoInj backwardStep
    refine ⟨RawTerm.equivIntro forwardInner backwardInner, ?_⟩
    rw [hTarget, hForwardInner, hBackwardInner]; rfl
  | equivApp equivTerm argument equivIH argIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.equivApp (equivTerm.rename rho)
      (argument.rename rho)) _ at parStep
    obtain ⟨equivTarget, argTarget, hTarget, equivStep, argStep⟩ :=
      RawStep.par.equivApp_inv parStep
    obtain ⟨equivInner, hEquivInner⟩ := equivIH rho rhoInj equivStep
    obtain ⟨argInner, hArgInner⟩ := argIH rho rhoInj argStep
    refine ⟨RawTerm.equivApp equivInner argInner, ?_⟩
    rw [hTarget, hEquivInner, hArgInner]; rfl
  | codataUnfold initialState transition stateIH transitionIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.codataUnfold (initialState.rename rho)
      (transition.rename rho)) _ at parStep
    obtain ⟨stateTarget, transitionTarget, hTarget, stateStep, transitionStep⟩ :=
      RawStep.par.codataUnfold_inv parStep
    obtain ⟨stateInner, hStateInner⟩ := stateIH rho rhoInj stateStep
    obtain ⟨transitionInner, hTransitionInner⟩ :=
      transitionIH rho rhoInj transitionStep
    refine ⟨RawTerm.codataUnfold stateInner transitionInner, ?_⟩
    rw [hTarget, hStateInner, hTransitionInner]; rfl
  | sessionSend channel payload channelIH payloadIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.sessionSend (channel.rename rho)
      (payload.rename rho)) _ at parStep
    obtain ⟨channelTarget, payloadTarget, hTarget, channelStep, payloadStep⟩ :=
      RawStep.par.sessionSend_inv parStep
    obtain ⟨channelInner, hChannelInner⟩ := channelIH rho rhoInj channelStep
    obtain ⟨payloadInner, hPayloadInner⟩ := payloadIH rho rhoInj payloadStep
    refine ⟨RawTerm.sessionSend channelInner payloadInner, ?_⟩
    rw [hTarget, hChannelInner, hPayloadInner]; rfl
  | effectPerform operationTag arguments tagIH argsIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.effectPerform (operationTag.rename rho)
      (arguments.rename rho)) _ at parStep
    obtain ⟨tagTarget, argsTarget, hTarget, tagStep, argsStep⟩ :=
      RawStep.par.effectPerform_inv parStep
    obtain ⟨tagInner, hTagInner⟩ := tagIH rho rhoInj tagStep
    obtain ⟨argsInner, hArgsInner⟩ := argsIH rho rhoInj argsStep
    refine ⟨RawTerm.effectPerform tagInner argsInner, ?_⟩
    rw [hTarget, hTagInner, hArgsInner]; rfl
  | glueIntro baseValue partialValue baseIH partialIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.glueIntro (baseValue.rename rho)
      (partialValue.rename rho)) _ at parStep
    obtain ⟨baseTarget, partialTarget, hTarget, baseStep, partialStep⟩ :=
      RawStep.par.glueIntro_inv parStep
    obtain ⟨baseInner, hBaseInner⟩ := baseIH rho rhoInj baseStep
    obtain ⟨partialInner, hPartialInner⟩ := partialIH rho rhoInj partialStep
    refine ⟨RawTerm.glueIntro baseInner partialInner, ?_⟩
    rw [hTarget, hBaseInner, hPartialInner]; rfl
  -- Two-subterm CUMUL-2.1 cong cases (no inv lemma in RawParInversion):
  | arrowCode domainCode codomainCode domainIH codomainIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.arrowCode (domainCode.rename rho)
      (codomainCode.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.arrowCode domainCode codomainCode, rfl⟩
    | arrowCodeCong domainStep codomainStep =>
      obtain ⟨domainInner, hDomainInner⟩ := domainIH rho rhoInj domainStep
      obtain ⟨codomainInner, hCodomainInner⟩ := codomainIH rho rhoInj codomainStep
      refine ⟨RawTerm.arrowCode domainInner codomainInner, ?_⟩
      rw [hDomainInner, hCodomainInner]; rfl
  | productCode firstCode secondCode firstIH secondIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.productCode (firstCode.rename rho)
      (secondCode.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.productCode firstCode secondCode, rfl⟩
    | productCodeCong firstStep secondStep =>
      obtain ⟨firstInner, hFirstInner⟩ := firstIH rho rhoInj firstStep
      obtain ⟨secondInner, hSecondInner⟩ := secondIH rho rhoInj secondStep
      refine ⟨RawTerm.productCode firstInner secondInner, ?_⟩
      rw [hFirstInner, hSecondInner]; rfl
  | sumCode leftCode rightCode leftIH rightIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.sumCode (leftCode.rename rho)
      (rightCode.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.sumCode leftCode rightCode, rfl⟩
    | sumCodeCong leftStep rightStep =>
      obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
      obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
      refine ⟨RawTerm.sumCode leftInner rightInner, ?_⟩
      rw [hLeftInner, hRightInner]; rfl
  | eitherCode leftCode rightCode leftIH rightIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.eitherCode (leftCode.rename rho)
      (rightCode.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.eitherCode leftCode rightCode, rfl⟩
    | eitherCodeCong leftStep rightStep =>
      obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
      obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
      refine ⟨RawTerm.eitherCode leftInner rightInner, ?_⟩
      rw [hLeftInner, hRightInner]; rfl
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.equivCode (leftTypeCode.rename rho)
      (rightTypeCode.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.equivCode leftTypeCode rightTypeCode, rfl⟩
    | equivCodeCong leftStep rightStep =>
      obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
      obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
      refine ⟨RawTerm.equivCode leftInner rightInner, ?_⟩
      rw [hLeftInner, hRightInner]; rfl
  -- Three-subterm cong (no redex):
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.idCode (typeCode.rename rho)
      (leftRaw.rename rho) (rightRaw.rename rho)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.idCode typeCode leftRaw rightRaw, rfl⟩
    | idCodeCong typeStep leftStep rightStep =>
      obtain ⟨typeInner, hTypeInner⟩ := typeIH rho rhoInj typeStep
      obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
      obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
      refine ⟨RawTerm.idCode typeInner leftInner rightInner, ?_⟩
      rw [hTypeInner, hLeftInner, hRightInner]; rfl
  -- ============== Binder cong (lift IH to scope+1) ==============
  | lam body bodyIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.lam (body.rename rho.lift)) _ at parStep
    obtain ⟨bodyTarget, hTarget, bodyStep⟩ := RawStep.par.lam_inv parStep
    have liftInj := RawRenaming.lift_injective rho rhoInj
    obtain ⟨bodyInner, hBodyInner⟩ := bodyIH rho.lift liftInj bodyStep
    refine ⟨RawTerm.lam bodyInner, ?_⟩
    rw [hTarget, hBodyInner]; rfl
  | pathLam body bodyIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.pathLam (body.rename rho.lift)) _ at parStep
    obtain ⟨bodyTarget, hTarget, bodyStep⟩ := RawStep.par.pathLam_inv parStep
    have liftInj := RawRenaming.lift_injective rho rhoInj
    obtain ⟨bodyInner, hBodyInner⟩ := bodyIH rho.lift liftInj bodyStep
    refine ⟨RawTerm.pathLam bodyInner, ?_⟩
    rw [hTarget, hBodyInner]; rfl
  | piTyCode domainCode codomainCode domainIH codomainIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.piTyCode (domainCode.rename rho)
      (codomainCode.rename rho.lift)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.piTyCode domainCode codomainCode, rfl⟩
    | piTyCodeCong domainStep codomainStep =>
      have liftInj := RawRenaming.lift_injective rho rhoInj
      obtain ⟨domainInner, hDomainInner⟩ := domainIH rho rhoInj domainStep
      obtain ⟨codomainInner, hCodomainInner⟩ :=
        codomainIH rho.lift liftInj codomainStep
      refine ⟨RawTerm.piTyCode domainInner codomainInner, ?_⟩
      rw [hDomainInner, hCodomainInner]; rfl
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.sigmaTyCode (domainCode.rename rho)
      (codomainCode.rename rho.lift)) _ at parStep
    cases parStep with
    | refl _ => exact ⟨RawTerm.sigmaTyCode domainCode codomainCode, rfl⟩
    | sigmaTyCodeCong domainStep codomainStep =>
      have liftInj := RawRenaming.lift_injective rho rhoInj
      obtain ⟨domainInner, hDomainInner⟩ := domainIH rho rhoInj domainStep
      obtain ⟨codomainInner, hCodomainInner⟩ :=
        codomainIH rho.lift liftInj codomainStep
      refine ⟨RawTerm.sigmaTyCode domainInner codomainInner, ?_⟩
      rw [hDomainInner, hCodomainInner]; rfl
  -- 2-subterm cong (used internally by redex parents but no redex itself):
  | listCons headTerm tailTerm headIH tailIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.listCons (headTerm.rename rho)
      (tailTerm.rename rho)) _ at parStep
    obtain ⟨headTarget, tailTarget, hTarget, headStep, tailStep⟩ :=
      RawStep.par.listCons_inv parStep
    obtain ⟨headInner, hHeadInner⟩ := headIH rho rhoInj headStep
    obtain ⟨tailInner, hTailInner⟩ := tailIH rho rhoInj tailStep
    refine ⟨RawTerm.listCons headInner tailInner, ?_⟩
    rw [hTarget, hHeadInner, hTailInner]; rfl
  | refineIntro rawValue predicateProof valueIH proofIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.refineIntro (rawValue.rename rho)
      (predicateProof.rename rho)) _ at parStep
    obtain ⟨valueTarget, proofTarget, hTarget, valueStep, proofStep⟩ :=
      RawStep.par.refineIntro_inv parStep
    obtain ⟨valueInner, hValueInner⟩ := valueIH rho rhoInj valueStep
    obtain ⟨proofInner, hProofInner⟩ := proofIH rho rhoInj proofStep
    refine ⟨RawTerm.refineIntro valueInner proofInner, ?_⟩
    rw [hTarget, hValueInner, hProofInner]; rfl
  -- ============== Redex parents ==============
  | app fn arg fnIH argIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par
      (RawTerm.app (fn.rename rho) (arg.rename rho)) _ at parStep
    rcases RawStep.par.app_inv parStep with
      ⟨functionTarget, argumentTarget, hTarget, fnStep, argStep⟩ |
      ⟨bodyTarget, argumentTarget, hTarget, fnStep, argStep⟩
    · -- cong-app
      obtain ⟨fnInner, hFnInner⟩ := fnIH rho rhoInj fnStep
      obtain ⟨argInner, hArgInner⟩ := argIH rho rhoInj argStep
      refine ⟨RawTerm.app fnInner argInner, ?_⟩
      rw [hTarget, hFnInner, hArgInner]; rfl
    · -- β-app: fn par-reduces to lam bodyTarget
      obtain ⟨lamRenamed, hLamRenamed⟩ := fnIH rho rhoInj fnStep
      obtain ⟨lamBody, _, hBodyEq⟩ :=
        RawTerm.rename_eq_lam_imp rho hLamRenamed.symm
      obtain ⟨argInner, hArgInner⟩ := argIH rho rhoInj argStep
      refine ⟨lamBody.subst0 argInner, ?_⟩
      rw [hTarget, hBodyEq, hArgInner]
      rw [RawTerm.subst0_rename_commute]
  | fst pairTerm pairIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.fst (pairTerm.rename rho)) _ at parStep
    rcases RawStep.par.fst_inv parStep with
      ⟨pairTarget, hTarget, pairStep⟩ |
      ⟨firstTarget, secondTarget, hTarget, pairStep⟩
    · -- cong
      obtain ⟨pairInner, hPairInner⟩ := pairIH rho rhoInj pairStep
      refine ⟨RawTerm.fst pairInner, ?_⟩
      rw [hTarget, hPairInner]; rfl
    · -- β-fst
      obtain ⟨pairRenamed, hPairRenamed⟩ := pairIH rho rhoInj pairStep
      obtain ⟨first, second, _, hFirst, _⟩ :=
        RawTerm.rename_eq_pair_imp rho hPairRenamed.symm
      refine ⟨first, ?_⟩
      rw [hTarget, hFirst]
  | snd pairTerm pairIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.snd (pairTerm.rename rho)) _ at parStep
    rcases RawStep.par.snd_inv parStep with
      ⟨pairTarget, hTarget, pairStep⟩ |
      ⟨firstTarget, secondTarget, hTarget, pairStep⟩
    · -- cong
      obtain ⟨pairInner, hPairInner⟩ := pairIH rho rhoInj pairStep
      refine ⟨RawTerm.snd pairInner, ?_⟩
      rw [hTarget, hPairInner]; rfl
    · -- β-snd
      obtain ⟨pairRenamed, hPairRenamed⟩ := pairIH rho rhoInj pairStep
      obtain ⟨first, second, _, _, hSecond⟩ :=
        RawTerm.rename_eq_pair_imp rho hPairRenamed.symm
      refine ⟨second, ?_⟩
      rw [hTarget, hSecond]
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.boolElim (scrutinee.rename rho)
      (thenBranch.rename rho) (elseBranch.rename rho)) _ at parStep
    rcases RawStep.par.boolElim_inv parStep with
      ⟨scrutineeTarget, thenTarget, elseTarget, hTarget,
       scrutineeStep, thenStep, elseStep⟩ |
      ⟨thenTarget, hTarget, scrutineeStep, thenStep⟩ |
      ⟨elseTarget, hTarget, scrutineeStep, elseStep⟩
    · -- cong
      obtain ⟨scrutineeInner, hScrutineeInner⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨thenInner, hThenInner⟩ := thenIH rho rhoInj thenStep
      obtain ⟨elseInner, hElseInner⟩ := elseIH rho rhoInj elseStep
      refine ⟨RawTerm.boolElim scrutineeInner thenInner elseInner, ?_⟩
      rw [hTarget, hScrutineeInner, hThenInner, hElseInner]; rfl
    · -- iotaTrue
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      have := RawTerm.rename_eq_boolTrue_imp rho hScrut.symm
      obtain ⟨thenInner, hThenInner⟩ := thenIH rho rhoInj thenStep
      refine ⟨thenInner, ?_⟩
      rw [hTarget, hThenInner]
    · -- iotaFalse
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      have := RawTerm.rename_eq_boolFalse_imp rho hScrut.symm
      obtain ⟨elseInner, hElseInner⟩ := elseIH rho rhoInj elseStep
      refine ⟨elseInner, ?_⟩
      rw [hTarget, hElseInner]
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.natElim (scrutinee.rename rho)
      (zeroBranch.rename rho) (succBranch.rename rho)) _ at parStep
    rcases RawStep.par.natElim_inv parStep with
      ⟨scrutineeTarget, zeroTarget, succTarget, hTarget,
       scrutineeStep, zeroStep, succStep⟩ |
      ⟨zeroTarget, hTarget, scrutineeStep, zeroStep⟩ |
      ⟨predRaw, succTarget, hTarget, scrutineeStep, succStep⟩
    · -- cong
      obtain ⟨scrutineeInner, hScrutineeInner⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨zeroInner, hZeroInner⟩ := zeroIH rho rhoInj zeroStep
      obtain ⟨succInner, hSuccInner⟩ := succIH rho rhoInj succStep
      refine ⟨RawTerm.natElim scrutineeInner zeroInner succInner, ?_⟩
      rw [hTarget, hScrutineeInner, hZeroInner, hSuccInner]; rfl
    · -- iotaZero
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      have := RawTerm.rename_eq_natZero_imp rho hScrut.symm
      obtain ⟨zeroInner, hZeroInner⟩ := zeroIH rho rhoInj zeroStep
      refine ⟨zeroInner, ?_⟩
      rw [hTarget, hZeroInner]
    · -- iotaSucc: scrutinee → natSucc predRaw, succBranch → succTarget
      -- target = app succTarget predRaw, where predRaw : RawTerm targetScope
      obtain ⟨scrutRenamed, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨predInner, _, hPredEq⟩ := RawTerm.rename_eq_natSucc_imp rho hScrut.symm
      obtain ⟨succInner, hSuccInner⟩ := succIH rho rhoInj succStep
      refine ⟨RawTerm.app succInner predInner, ?_⟩
      rw [hTarget, hSuccInner, hPredEq]; rfl
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.natRec (scrutinee.rename rho)
      (zeroBranch.rename rho) (succBranch.rename rho)) _ at parStep
    rcases RawStep.par.natRec_inv parStep with
      ⟨scrutineeTarget, zeroTarget, succTarget, hTarget,
       scrutineeStep, zeroStep, succStep⟩ |
      ⟨zeroTarget, hTarget, scrutineeStep, zeroStep⟩ |
      ⟨predRaw, zeroTarget, succTarget, hTarget,
       scrutineeStep, zeroStep, succStep⟩
    · -- cong
      obtain ⟨scrutineeInner, hScrutineeInner⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨zeroInner, hZeroInner⟩ := zeroIH rho rhoInj zeroStep
      obtain ⟨succInner, hSuccInner⟩ := succIH rho rhoInj succStep
      refine ⟨RawTerm.natRec scrutineeInner zeroInner succInner, ?_⟩
      rw [hTarget, hScrutineeInner, hZeroInner, hSuccInner]; rfl
    · -- iotaZero
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      have := RawTerm.rename_eq_natZero_imp rho hScrut.symm
      obtain ⟨zeroInner, hZeroInner⟩ := zeroIH rho rhoInj zeroStep
      refine ⟨zeroInner, ?_⟩
      rw [hTarget, hZeroInner]
    · -- iotaSucc: target = app (app succTarget predRaw) (natRec predRaw zeroTarget succTarget)
      obtain ⟨scrutRenamed, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨predInner, _, hPredEq⟩ := RawTerm.rename_eq_natSucc_imp rho hScrut.symm
      obtain ⟨zeroInner, hZeroInner⟩ := zeroIH rho rhoInj zeroStep
      obtain ⟨succInner, hSuccInner⟩ := succIH rho rhoInj succStep
      refine ⟨RawTerm.app (RawTerm.app succInner predInner)
                          (RawTerm.natRec predInner zeroInner succInner), ?_⟩
      rw [hTarget, hSuccInner, hPredEq, hZeroInner]; rfl
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.listElim (scrutinee.rename rho)
      (nilBranch.rename rho) (consBranch.rename rho)) _ at parStep
    rcases RawStep.par.listElim_inv parStep with
      ⟨scrutineeTarget, nilTarget, consTarget, hTarget,
       scrutineeStep, nilStep, consStep⟩ |
      ⟨nilTarget, hTarget, scrutineeStep, nilStep⟩ |
      ⟨headRaw, tailRaw, consTarget, hTarget, scrutineeStep, consStep⟩
    · -- cong
      obtain ⟨scrutineeInner, hScrutineeInner⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨nilInner, hNilInner⟩ := nilIH rho rhoInj nilStep
      obtain ⟨consInner, hConsInner⟩ := consIH rho rhoInj consStep
      refine ⟨RawTerm.listElim scrutineeInner nilInner consInner, ?_⟩
      rw [hTarget, hScrutineeInner, hNilInner, hConsInner]; rfl
    · -- iotaNil
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      have := RawTerm.rename_eq_listNil_imp rho hScrut.symm
      obtain ⟨nilInner, hNilInner⟩ := nilIH rho rhoInj nilStep
      refine ⟨nilInner, ?_⟩
      rw [hTarget, hNilInner]
    · -- iotaCons
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨headInner, tailInner, _, hHeadEq, hTailEq⟩ :=
        RawTerm.rename_eq_listCons_imp rho hScrut.symm
      obtain ⟨consInner, hConsInner⟩ := consIH rho rhoInj consStep
      refine ⟨RawTerm.app (RawTerm.app consInner headInner) tailInner, ?_⟩
      rw [hTarget, hConsInner, hHeadEq, hTailEq]; rfl
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.optionMatch (scrutinee.rename rho)
      (noneBranch.rename rho) (someBranch.rename rho)) _ at parStep
    rcases RawStep.par.optionMatch_inv parStep with
      ⟨scrutineeTarget, noneTarget, someTarget, hTarget,
       scrutineeStep, noneStep, someStep⟩ |
      ⟨noneTarget, hTarget, scrutineeStep, noneStep⟩ |
      ⟨valueRaw, someTarget, hTarget, scrutineeStep, someStep⟩
    · -- cong
      obtain ⟨scrutineeInner, hScrutineeInner⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨noneInner, hNoneInner⟩ := noneIH rho rhoInj noneStep
      obtain ⟨someInner, hSomeInner⟩ := someIH rho rhoInj someStep
      refine ⟨RawTerm.optionMatch scrutineeInner noneInner someInner, ?_⟩
      rw [hTarget, hScrutineeInner, hNoneInner, hSomeInner]; rfl
    · -- iotaNone
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      have := RawTerm.rename_eq_optionNone_imp rho hScrut.symm
      obtain ⟨noneInner, hNoneInner⟩ := noneIH rho rhoInj noneStep
      refine ⟨noneInner, ?_⟩
      rw [hTarget, hNoneInner]
    · -- iotaSome
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨valueInner, _, hValueEq⟩ :=
        RawTerm.rename_eq_optionSome_imp rho hScrut.symm
      obtain ⟨someInner, hSomeInner⟩ := someIH rho rhoInj someStep
      refine ⟨RawTerm.app someInner valueInner, ?_⟩
      rw [hTarget, hSomeInner, hValueEq]; rfl
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.eitherMatch (scrutinee.rename rho)
      (leftBranch.rename rho) (rightBranch.rename rho)) _ at parStep
    rcases RawStep.par.eitherMatch_inv parStep with
      ⟨scrutineeTarget, leftTarget, rightTarget, hTarget,
       scrutineeStep, leftStep, rightStep⟩ |
      ⟨valueRaw, leftTarget, hTarget, scrutineeStep, leftStep⟩ |
      ⟨valueRaw, rightTarget, hTarget, scrutineeStep, rightStep⟩
    · -- cong
      obtain ⟨scrutineeInner, hScrutineeInner⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
      obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
      refine ⟨RawTerm.eitherMatch scrutineeInner leftInner rightInner, ?_⟩
      rw [hTarget, hScrutineeInner, hLeftInner, hRightInner]; rfl
    · -- iotaInl
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨valueInner, _, hValueEq⟩ :=
        RawTerm.rename_eq_eitherInl_imp rho hScrut.symm
      obtain ⟨leftInner, hLeftInner⟩ := leftIH rho rhoInj leftStep
      refine ⟨RawTerm.app leftInner valueInner, ?_⟩
      rw [hTarget, hLeftInner, hValueEq]; rfl
    · -- iotaInr
      obtain ⟨_, hScrut⟩ := scrutineeIH rho rhoInj scrutineeStep
      obtain ⟨valueInner, _, hValueEq⟩ :=
        RawTerm.rename_eq_eitherInr_imp rho hScrut.symm
      obtain ⟨rightInner, hRightInner⟩ := rightIH rho rhoInj rightStep
      refine ⟨RawTerm.app rightInner valueInner, ?_⟩
      rw [hTarget, hRightInner, hValueEq]; rfl
  | idJ baseCase witness baseIH witnessIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.idJ (baseCase.rename rho)
      (witness.rename rho)) _ at parStep
    rcases RawStep.par.idJ_inv parStep with
      ⟨baseTarget, witnessTarget, hTarget, baseStep, witnessStep⟩ |
      ⟨witnessRaw, baseTarget, hTarget, witnessStep, baseStep⟩
    · -- cong
      obtain ⟨baseInner, hBaseInner⟩ := baseIH rho rhoInj baseStep
      obtain ⟨witnessInner, hWitnessInner⟩ := witnessIH rho rhoInj witnessStep
      refine ⟨RawTerm.idJ baseInner witnessInner, ?_⟩
      rw [hTarget, hBaseInner, hWitnessInner]; rfl
    · -- iotaIdJRefl: witness → refl _, target = baseTarget
      obtain ⟨_, hWitnessRenamed⟩ := witnessIH rho rhoInj witnessStep
      have := RawTerm.rename_eq_refl_imp rho hWitnessRenamed.symm
      obtain ⟨baseInner, hBaseInner⟩ := baseIH rho rhoInj baseStep
      refine ⟨baseInner, ?_⟩
      rw [hTarget, hBaseInner]
  | idStrictRec baseCase witness baseIH witnessIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.idStrictRec (baseCase.rename rho)
      (witness.rename rho)) _ at parStep
    rcases RawStep.par.idStrictRec_inv parStep with
      ⟨baseTarget, witnessTarget, hTarget, baseStep, witnessStep⟩ |
      ⟨reflRawArgument, baseTarget, hTarget, witnessStep, baseStep⟩
    · -- cong
      obtain ⟨baseInner, hBaseInner⟩ := baseIH rho rhoInj baseStep
      obtain ⟨witnessInner, hWitnessInner⟩ := witnessIH rho rhoInj witnessStep
      refine ⟨RawTerm.idStrictRec baseInner witnessInner, ?_⟩
      rw [hTarget, hBaseInner, hWitnessInner]; rfl
    · -- ι: witness par-reduces to idStrictRefl _, target = baseTarget
      obtain ⟨_, hWitnessRenamed⟩ := witnessIH rho rhoInj witnessStep
      have := RawTerm.rename_eq_idStrictRefl_imp rho hWitnessRenamed.symm
      obtain ⟨baseInner, hBaseInner⟩ := baseIH rho rhoInj baseStep
      refine ⟨baseInner, ?_⟩
      rw [hTarget, hBaseInner]
  | modElim inner innerIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.modElim (inner.rename rho)) _ at parStep
    rcases RawStep.par.modElim_inv parStep with
      ⟨innerTarget, hTarget, innerStep⟩ |
      ⟨payloadTarget, hTarget, innerStep⟩
    · -- cong
      obtain ⟨innerInner, hInnerInner⟩ := innerIH rho rhoInj innerStep
      refine ⟨RawTerm.modElim innerInner, ?_⟩
      rw [hTarget, hInnerInner]; rfl
    · -- β: inner par-reduces to modIntro payloadTarget
      obtain ⟨innerRenamed, hInnerRenamed⟩ := innerIH rho rhoInj innerStep
      obtain ⟨payloadInner, _, hPayloadEq⟩ :=
        RawTerm.rename_eq_modIntro_imp rho hInnerRenamed.symm
      refine ⟨payloadInner, ?_⟩
      rw [hTarget, hPayloadEq]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.pathApp (pathTerm.rename rho)
      (intervalArg.rename rho)) _ at parStep
    rcases RawStep.par.pathApp_inv parStep with
      ⟨pathTarget, intervalTarget, hTarget, pathStep, intervalStep⟩ |
      ⟨bodyTarget, intervalTarget, hTarget, pathStep, intervalStep⟩
    · -- cong
      obtain ⟨pathInner, hPathInner⟩ := pathIH rho rhoInj pathStep
      obtain ⟨intervalInner, hIntervalInner⟩ := intervalIH rho rhoInj intervalStep
      refine ⟨RawTerm.pathApp pathInner intervalInner, ?_⟩
      rw [hTarget, hPathInner, hIntervalInner]; rfl
    · -- β-pathApp: pathTerm par-reduces to pathLam bodyTarget
      obtain ⟨pathRenamed, hPathRenamed⟩ := pathIH rho rhoInj pathStep
      obtain ⟨pathBody, _, hBodyEq⟩ :=
        RawTerm.rename_eq_pathLam_imp rho hPathRenamed.symm
      obtain ⟨intervalInner, hIntervalInner⟩ := intervalIH rho rhoInj intervalStep
      refine ⟨pathBody.subst0 intervalInner, ?_⟩
      rw [hTarget, hBodyEq, hIntervalInner]
      rw [RawTerm.subst0_rename_commute]
  | glueElim gluedValue gluedIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.glueElim (gluedValue.rename rho)) _ at parStep
    rcases RawStep.par.glueElim_inv parStep with
      ⟨gluedTarget, hTarget, gluedStep⟩ |
      ⟨baseTarget, partialTarget, hTarget, gluedStep⟩
    · -- cong
      obtain ⟨gluedInner, hGluedInner⟩ := gluedIH rho rhoInj gluedStep
      refine ⟨RawTerm.glueElim gluedInner, ?_⟩
      rw [hTarget, hGluedInner]; rfl
    · -- β: gluedValue par-reduces to glueIntro baseTarget partialTarget
      obtain ⟨gluedRenamed, hGluedRenamed⟩ := gluedIH rho rhoInj gluedStep
      obtain ⟨baseInner, partialInner, _, hBaseEq, _⟩ :=
        RawTerm.rename_eq_glueIntro_imp rho hGluedRenamed.symm
      refine ⟨baseInner, ?_⟩
      rw [hTarget, hBaseEq]
  | refineElim refinedValue refinedIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.refineElim (refinedValue.rename rho)) _ at parStep
    rcases RawStep.par.refineElim_inv parStep with
      ⟨refinedTarget, hTarget, refinedStep⟩ |
      ⟨valueTarget, proofTarget, hTarget, refinedStep⟩
    · -- cong
      obtain ⟨refinedInner, hRefinedInner⟩ := refinedIH rho rhoInj refinedStep
      refine ⟨RawTerm.refineElim refinedInner, ?_⟩
      rw [hTarget, hRefinedInner]; rfl
    · -- β: refinedValue par-reduces to refineIntro valueTarget proofTarget
      obtain ⟨refinedRenamed, hRefinedRenamed⟩ := refinedIH rho rhoInj refinedStep
      obtain ⟨valueInner, proofInner, _, hValueEq, _⟩ :=
        RawTerm.rename_eq_refineIntro_imp rho hRefinedRenamed.symm
      refine ⟨valueInner, ?_⟩
      rw [hTarget, hValueEq]
  | recordProj recordValue recordIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.recordProj (recordValue.rename rho)) _ at parStep
    rcases RawStep.par.recordProj_inv parStep with
      ⟨recordTarget, hTarget, recordStep⟩ |
      ⟨firstTarget, hTarget, recordStep⟩
    · -- cong
      obtain ⟨recordInner, hRecordInner⟩ := recordIH rho rhoInj recordStep
      refine ⟨RawTerm.recordProj recordInner, ?_⟩
      rw [hTarget, hRecordInner]; rfl
    · -- β: recordValue par-reduces to recordIntro firstTarget
      obtain ⟨recordRenamed, hRecordRenamed⟩ := recordIH rho rhoInj recordStep
      obtain ⟨firstInner, _, hFirstEq⟩ :=
        RawTerm.rename_eq_recordIntro_imp rho hRecordRenamed.symm
      refine ⟨firstInner, ?_⟩
      rw [hTarget, hFirstEq]
  | codataDest codataValue codataIH =>
    intro _ rho rhoInj _ parStep
    change RawStep.par (RawTerm.codataDest (codataValue.rename rho)) _ at parStep
    rcases RawStep.par.codataDest_inv parStep with
      ⟨codataTarget, hTarget, codataStep⟩ |
      ⟨stateTarget, transitionTarget, hTarget, codataStep⟩
    · -- cong
      obtain ⟨codataInner, hCodataInner⟩ := codataIH rho rhoInj codataStep
      refine ⟨RawTerm.codataDest codataInner, ?_⟩
      rw [hTarget, hCodataInner]; rfl
    · -- β: codataValue par-reduces to codataUnfold stateTarget transitionTarget
      -- target = app transitionTarget stateTarget
      obtain ⟨codataRenamed, hCodataRenamed⟩ := codataIH rho rhoInj codataStep
      obtain ⟨stateInner, transitionInner, _, hStateEq, hTransitionEq⟩ :=
        RawTerm.rename_eq_codataUnfold_imp rho hCodataRenamed.symm
      refine ⟨RawTerm.app transitionInner stateInner, ?_⟩
      rw [hTarget, hStateEq, hTransitionEq]; rfl

/-- Specialization to the canonical weaken renaming. -/
theorem RawStep.par.weaken_inv {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetAfter : RawTerm (scope + 1)}
    (parStep : RawStep.par sourceTerm.weaken targetAfter) :
    ∃ targetInner : RawTerm scope, targetAfter = targetInner.weaken :=
  RawStep.par.rename_inj_inv sourceTerm RawRenaming.weaken
    RawRenaming.weaken_injective parStep

end LeanFX2
