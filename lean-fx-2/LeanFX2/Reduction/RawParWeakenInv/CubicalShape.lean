import LeanFX2.Reduction.RawParWeakenInv.Foundation

/-! # Reduction/RawParWeakenInv/CubicalShape — D3.6 cubical shape inversions

Shape-inversion helpers feeding the `transp` arm of
`rename_inj_inv` for the cubical β rules: `uaToEquiv`,
`pathCompose`, `idToEquiv`, `oeqTrans`, and `equivCompose`.  Each
mechanically enumerates the 67 `RawTerm` ctors and dismisses
non-matching cases via `simp only [RawTerm.rename]; nomatch h`.

## Root status

Private kernel theorems with bodies, zero-axiom. -/

namespace LeanFX2

/-! ## D3.6-S1 shape inversion for `uaToEquiv`.

Used by the `transp` arm of `rename_inj_inv` to invert `path.rename
rho = uaToEquiv proofRawSource` (the LHS path-shape produced by
`uaBeta`) into a structurally-decomposed `path = uaToEquiv proofInner`
with `proofInner.rename rho = proofRawSource`. -/
theorem RawTerm.rename_eq_uaToEquiv_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.uaToEquiv target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.uaToEquiv inner ∧ target = inner.rename rho := by
  cases term with
  | uaToEquiv inner =>
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
  | equivApply _ _ => simp only [RawTerm.rename] at h; nomatch h
  | pathCompose _ _ => simp only [RawTerm.rename] at h; nomatch h
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-! ## D3.6-S3 shape inversion for `pathCompose`.

Used by the `transp` arm of `rename_inj_inv` to invert
`path.rename rho = pathCompose leftRawSource rightRawSource` (the LHS
path-shape produced by `transpCompose`) into a structurally-decomposed
`path = pathCompose leftInner rightInner` with
`leftInner.rename rho = leftRawSource` and
`rightInner.rename rho = rightRawSource`. -/
theorem RawTerm.rename_eq_pathCompose_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {leftTarget rightTarget : RawTerm targetScope}
    (h : term.rename rho = RawTerm.pathCompose leftTarget rightTarget) :
    ∃ leftInner rightInner : RawTerm sourceScope,
      term = RawTerm.pathCompose leftInner rightInner ∧
      leftTarget = leftInner.rename rho ∧
      rightTarget = rightInner.rename rho := by
  cases term with
  | pathCompose leftInner rightInner =>
    simp only [RawTerm.rename] at h
    -- h : RawTerm.pathCompose (leftInner.rename rho) (rightInner.rename rho)
    --   = RawTerm.pathCompose leftTarget rightTarget
    -- Use RawTerm.pathCompose.injEq if available, else cases on h.
    cases h
    exact ⟨leftInner, rightInner, rfl, rfl, rfl⟩
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
  | idToEquiv _ => simp only [RawTerm.rename] at h; nomatch h
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-! ## D3.6-S4 shape inversion for `idToEquiv`.

Used by the `idToEquiv` arm of `rename_inj_inv` to invert
`proof.rename rho = idToEquiv proofRawSource` into a structurally-
decomposed `proof = idToEquiv proofInner` with
`proofInner.rename rho = proofRawSource`. -/
theorem RawTerm.rename_eq_idToEquiv_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} {target : RawTerm targetScope}
    (h : term.rename rho = RawTerm.idToEquiv target) :
    ∃ inner : RawTerm sourceScope,
      term = RawTerm.idToEquiv inner ∧ target = inner.rename rho := by
  cases term with
  | idToEquiv inner =>
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
  | oeqTrans _ _ => simp only [RawTerm.rename] at h; nomatch h
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-! ## D3.6-S5 shape inversion for `oeqTrans`.

Used by the `oeqTrans` arm of `rename_inj_inv` to invert
`proof.rename rho = oeqTrans firstTarget secondTarget` into a
structurally-decomposed `proof = oeqTrans firstInner secondInner`. -/
theorem RawTerm.rename_eq_oeqTrans_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {firstTarget secondTarget : RawTerm targetScope}
    (h : term.rename rho = RawTerm.oeqTrans firstTarget secondTarget) :
    ∃ firstInner secondInner : RawTerm sourceScope,
      term = RawTerm.oeqTrans firstInner secondInner ∧
      firstTarget = firstInner.rename rho ∧
      secondTarget = secondInner.rename rho := by
  cases term with
  | oeqTrans firstInner secondInner =>
    simp only [RawTerm.rename] at h
    cases h
    exact ⟨firstInner, secondInner, rfl, rfl, rfl⟩
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
  | equivCompose _ _ => simp only [RawTerm.rename] at h; nomatch h

/-! ## D3.6-S5 shape inversion for `equivCompose`.

Used by the `equivCompose` arm of `rename_inj_inv` to invert
`proof.rename rho = equivCompose firstTarget secondTarget` into a
structurally-decomposed `proof = equivCompose firstInner secondInner`. -/
theorem RawTerm.rename_eq_equivCompose_imp {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope}
    {firstTarget secondTarget : RawTerm targetScope}
    (h : term.rename rho = RawTerm.equivCompose firstTarget secondTarget) :
    ∃ firstInner secondInner : RawTerm sourceScope,
      term = RawTerm.equivCompose firstInner secondInner ∧
      firstTarget = firstInner.rename rho ∧
      secondTarget = secondInner.rename rho := by
  cases term with
  | equivCompose firstInner secondInner =>
    simp only [RawTerm.rename] at h
    cases h
    exact ⟨firstInner, secondInner, rfl, rfl, rfl⟩
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


end LeanFX2
