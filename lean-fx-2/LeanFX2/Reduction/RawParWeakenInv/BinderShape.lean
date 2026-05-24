import LeanFX2.Reduction.RawParWeakenInv.Foundation

/-! # BinderShape — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # Reduction/RawParWeakenInv/BinderShape — rename-shape inversion for compound and binder ctors

Shape inversions for compound/binder ctors: `modIntro`, `idStrictRefl`,
`recordIntro`, `pathLam` (binder), `pair`, `listCons`, `glueIntro`,
`refineIntro`, `codataUnfold`, `lam` (binder).  Binder cases thread
`rho.lift` through the inverted argument.

## Root status

Private kernel theorems with bodies, zero-axiom. -/

namespace LeanFX2

/-- Shape inversion for `modIntro`. -/
theorem RawTerm.rename_eq_modIntro_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.modIntro target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.modIntro inner ∧ target = inner.rename rho := by
  cases term with
  | modIntro inner =>
    refine ⟨inner, rfl, ?_⟩
    dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `idStrictRefl`. -/
theorem RawTerm.rename_eq_idStrictRefl_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.idStrictRefl target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.idStrictRefl inner ∧ target = inner.rename rho := by
  cases term with
  | idStrictRefl inner =>
    refine ⟨inner, rfl, ?_⟩
    dsimp only [RawTerm.rename] at h
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `recordIntro`. -/
theorem RawTerm.rename_eq_recordIntro_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.recordIntro target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.recordIntro inner ∧ target = inner.rename rho := by
  cases term with
  | recordIntro inner =>
    refine ⟨inner, rfl, ?_⟩
    dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `pathLam` (binder). -/
theorem RawTerm.rename_eq_pathLam_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm (targetScope + 1)}
    (h : term.rename rho = RawTerm.pathLam target) :
    ∃ inner : RawTerm (sourceScope + 1),
      term = RawTerm.pathLam inner ∧ target = inner.rename rho.lift := by
  cases term with
  | pathLam inner =>
    refine ⟨inner, rfl, ?_⟩
    dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `pair`. -/
theorem RawTerm.rename_eq_pair_imp {sourceScope targetScope : Nat}
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
    · dsimp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `listCons`. -/
theorem RawTerm.rename_eq_listCons_imp {sourceScope targetScope : Nat}
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
    · dsimp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `listCode` (unary type code).  Reserved for
future `transp.transpListBeta` arm reactivation when the D2.5.7.1 raw
cascade is fully shipped with cd_lemma dispatch. -/
theorem RawTerm.rename_eq_listCode_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.listCode target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.listCode inner ∧ target = inner.rename rho := by
  cases term with
  | listCode inner =>
    refine ⟨inner, rfl, ?_⟩
    dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `glueIntro`. -/
theorem RawTerm.rename_eq_glueIntro_imp {sourceScope targetScope : Nat}
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
    · dsimp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `refineIntro`. -/
theorem RawTerm.rename_eq_refineIntro_imp {sourceScope targetScope : Nat}
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
    · dsimp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · dsimp only [RawTerm.rename] at h
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
  | transpFill _ _ _ => simp only [RawTerm.rename] at h; nomatch h
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
  | uaToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-- Shape inversion for `codataUnfold`. -/
theorem RawTerm.rename_eq_codataUnfold_imp {sourceScope targetScope : Nat}
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
    · dsimp only [RawTerm.rename] at h
      injection h with _ h1; exact h1.symm
    · dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `lam` (binder). -/
theorem RawTerm.rename_eq_lam_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm (targetScope + 1)}
    (h : term.rename rho = RawTerm.lam target) :
    ∃ inner : RawTerm (sourceScope + 1),
      term = RawTerm.lam inner ∧ target = inner.rename rho.lift := by
  cases term with
  | lam inner =>
    refine ⟨inner, rfl, ?_⟩
    dsimp only [RawTerm.rename] at h
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

/-- Shape inversion for `piTyCode`.  Used by the shallow `transpPiBeta`
arm of `rename_inj_inv` to extract the source-side codomain inner
from a renamed-image `piTyCode (innerDomain.weaken) codomainCode`.

The codomain of `piTyCode` lives at `scope + 1` (one binder
deeper); rename through `rho.lift` is therefore required. -/
theorem RawTerm.rename_eq_piTyCode_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {domTarget : RawTerm targetScope}
    {codTarget : RawTerm (targetScope + 1)}
    (h : term.rename rho = RawTerm.piTyCode domTarget codTarget) :
    ∃ (domInner : RawTerm sourceScope)
      (codInner : RawTerm (sourceScope + 1)),
      term = RawTerm.piTyCode domInner codInner ∧
      domTarget = domInner.rename rho ∧
      codTarget = codInner.rename rho.lift := by
  cases term with
  | piTyCode domInner codInner =>
    dsimp only [RawTerm.rename] at h
    cases h
    exact ⟨domInner, codInner, rfl, rfl, rfl⟩
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

/-- Shape inversion for `transp` (D2.5.5 Phase B step 4, this commit).

If `term.rename rho = RawTerm.transp pathTarget sourceTarget`, then
`term = RawTerm.transp innerPath innerSource` for some `innerPath` and
`innerSource` at the source scope, with the renamings agreeing on both
arguments.

Load-bearing for the par-step-induction refactor of
`RawStep.par.rename_inj_inv`: each par ctor whose LHS unifies with
`transp _ _` (refl / `transp` cong / `transpReflBeta(Deep)` /
`uaBeta(Deep)` / `transpCompose(Deep)` / `transpPiBeta(Deep)`) needs
to recover `term`'s shape from `hMatch : sourceTerm.rename rho =
<ctor-LHS>`.  This helper does the recovery in one step, matching the
existing pattern of `rename_eq_pair_imp` / `rename_eq_listCons_imp`
for binary same-scope ctors.

Mirrors the structure used by `rename_eq_pair_imp` (line 361 above):
one real case unpacks both arguments via `injection`; 66 sibling ctors
discharge via `simp only [RawTerm.rename]; nomatch h` since their
renamed heads differ from `transp`.

Zero-axiom under the documented Match-Compiler propext recipes
(`feedback_lean_match_propext_recipe.md`); full ctor enumeration with
`nomatch` arms avoids wildcard-pattern propext leaks. -/
theorem RawTerm.rename_eq_transp_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {pathTarget sourceTarget : RawTerm targetScope}
    (h : term.rename rho = RawTerm.transp pathTarget sourceTarget) :
    ∃ innerPath innerSource : RawTerm sourceScope,
      term = RawTerm.transp innerPath innerSource ∧
        pathTarget = innerPath.rename rho ∧
        sourceTarget = innerSource.rename rho := by
  cases term with
  | transp innerPath innerSource =>
    refine ⟨innerPath, innerSource, rfl, ?_, ?_⟩
    · dsimp only [RawTerm.rename] at h
      injection h with _ hPath; exact hPath.symm
    · dsimp only [RawTerm.rename] at h
      injection h with _ _ hSource; exact hSource.symm
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

-/
