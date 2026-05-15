import LeanFX2.Reduction.RawParWeakenInv.Foundation

/-! # Reduction/RawParWeakenInv/AtomShape1 — rename-shape inversion for atom ctors (part 1)

Mechanical 67-way `cases t` shape inversions for the simpler atom
ctors (`boolTrue`, `boolFalse`, `natZero`, `listNil`, `optionNone`,
`interval0`, `interval1`).  All non-target ctors are dismissed via
`simp only [RawTerm.rename]; nomatch h`.

## Root status

Private kernel theorems with bodies, zero-axiom. -/

namespace LeanFX2

/-! ## Rename-shape inversion helpers.

For each canonical RawTerm ctor C that appears in some redex/Deep
par rule, we need: if t.rename rho = C args, then t = C args' for
some args' whose rename equals args.  These are mechanical 67-way
cases t enumerations where all non-C ctors are dismissed via
simp only [RawTerm.rename]; nomatch h. -/

/-- Shape inversion for `boolTrue`. -/
theorem RawTerm.rename_eq_boolTrue_imp {sourceScope targetScope : Nat}
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `boolFalse`. -/
theorem RawTerm.rename_eq_boolFalse_imp {sourceScope targetScope : Nat}
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `natZero`. -/
theorem RawTerm.rename_eq_natZero_imp {sourceScope targetScope : Nat}
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `listNil`. -/
theorem RawTerm.rename_eq_listNil_imp {sourceScope targetScope : Nat}
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `optionNone`. -/
theorem RawTerm.rename_eq_optionNone_imp {sourceScope targetScope : Nat}
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `interval0`. -/
theorem RawTerm.rename_eq_interval0_imp {sourceScope targetScope : Nat}
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `interval1`. -/
theorem RawTerm.rename_eq_interval1_imp {sourceScope targetScope : Nat}
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h


end LeanFX2
