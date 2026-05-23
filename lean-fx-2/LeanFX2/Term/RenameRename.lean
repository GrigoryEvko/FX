import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose
import LeanFX2.Term.RenamePointwiseHEq

/-! # LeanFX2.Term.RenameRename  (typed-Term rename functoriality)

`Term.rename` is functorial: renaming a renamed term equals renaming by the
composite renaming.  Both sides land in the same final target context, so the
per-constructor `*_HEq_congr` lemmas (which live in a single context) apply
directly; the structure mirrors the RcS / ScR fusion engines arm-for-arm.

  rename tr2 (rename tr1 t)  ≅  rename (compose tr1 tr2) t

The result is HEq-valued: the LHS carries type `(someType.rename rho1).rename rho2`
and raw `(raw.rename rho1).rename rho2`, while the RHS carries
`someType.rename (compose rho1 rho2)` and `raw.rename (compose rho1 rho2)`, bridged
by `Ty.rename_compose` / `RawTerm.rename_compose`.

`TermRenaming` is a `Prop`, so the engine never names a specific proof for the
composite — `TermRenaming.compose firstTermRenaming secondTermRenaming` supplies
one and proof-irrelevance makes `Term.rename` insensitive to the choice.  This is
the missing substrate for the three binder arms of `Term.subst_rename_commute`
(ScR engine): their var(k+1) entry case reduces to `rename (tr.lift X) (weaken X t)`
which, since `weaken X t = rename (weakenStep) t`, is exactly this functoriality.

Cast-arm discipline: where `Term.rename tr1` (and again `tr2`) introduces a `▸`
cast (lam / lamPi / appPi / pair / snd / boolElim / pathLam / funextRefl /
equivIntroHet / oeqFunext), the chain peels the inner cast through the outer
rename (`rename_type_eq_cast_heq` / `_symm`), peels the outer rename's own cast
(`type_eq_cast_heq`), bridges the bare ctor cores via `*_HEq_congr` + the child
IHs, then re-applies the composite-side cast.  Pure HEq.trans chains — NO bare
`simp` / `unfold` in any arm. -/

namespace LeanFX2

/-- Lifted-binder raw rename functoriality: renaming a body raw under two lifted
renamings equals renaming by the lifted composite.  The lambda
`fun position => rho2.lift (rho1.lift position)` agrees with
`(RawRenaming.compose rho1 rho2).lift` pointwise (rfl per de Bruijn position), so
the bridge is `RawTerm.rename_compose` followed by `RawTerm.rename_pointwise` —
no `funext`. -/
theorem RawTerm.rename_compose_lift
    {sourceScope middleScope targetScope : Nat}
    (rho1 : RawRenaming sourceScope middleScope)
    (rho2 : RawRenaming middleScope targetScope)
    (raw : RawTerm (sourceScope + 1)) :
    (raw.rename rho1.lift).rename rho2.lift =
      raw.rename (RawRenaming.compose rho1 rho2).lift :=
  (RawTerm.rename_compose rho1.lift rho2.lift raw).trans
    (RawTerm.rename_pointwise
      (fun position => by
        cases position with
        | mk val isLt =>
          cases val with
          | zero => rfl
          | succ k => rfl)
      raw)

/-- Lifted-binder type rename functoriality (mirror of `RawTerm.rename_compose_lift`
at the `Ty` layer): renaming a `scope+1` type under two lifted renamings equals
renaming by the lifted composite. -/
theorem Ty.rename_compose_lift {level : Nat}
    {sourceScope middleScope targetScope : Nat}
    (rho1 : RawRenaming sourceScope middleScope)
    (rho2 : RawRenaming middleScope targetScope)
    (someType : Ty level (sourceScope + 1)) :
    (someType.rename rho1.lift).rename rho2.lift =
      someType.rename (RawRenaming.compose rho1 rho2).lift :=
  (Ty.rename_compose rho1.lift rho2.lift someType).trans
    (Ty.rename_pointwise
      (fun position => by
        cases position with
        | mk val isLt =>
          cases val with
          | zero => rfl
          | succ k => rfl)
      someType)

/-- `Term.rename` is functorial up to heterogeneous equality.  The composite
typed renaming is `TermRenaming.compose firstTermRenaming secondTermRenaming`. -/
theorem Term.rename_rename
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho1 : RawRenaming sourceScope middleScope}
    {rho2 : RawRenaming middleScope targetScope}
    (firstTermRenaming : TermRenaming sourceCtx middleCtx rho1)
    (secondTermRenaming : TermRenaming middleCtx targetCtx rho2) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
      (someTerm : Term sourceCtx someType raw),
        HEq (Term.rename secondTermRenaming (Term.rename firstTermRenaming someTerm))
            (Term.rename
              (TermRenaming.compose firstTermRenaming secondTermRenaming) someTerm)
  | _, _, .var position =>
      -- Both sides collapse to `var (rho2 (rho1 position))` (= `var (compose p)`)
      -- via `rename_var_HEq`: push the inner var-rename through the outer rename,
      -- then the outer var-rename, then undo the composite var-rename.
      HEq.trans
        (Term.rename_heq_of_eq secondTermRenaming
          (firstTermRenaming position).symm
          (by rfl)
          (Term.rename_var_HEq firstTermRenaming position))
        (HEq.trans
          (Term.rename_var_HEq secondTermRenaming (rho1 position))
          (Term.rename_var_HEq
            (TermRenaming.compose firstTermRenaming secondTermRenaming)
            position).symm)
  | _, _, .unit => HEq.refl _
  | _, _, .boolTrue => HEq.refl _
  | _, _, .boolFalse => HEq.refl _
  | _, _, .natZero => HEq.refl _
  | _, _, .app fnTerm argTerm =>
      Term.app_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming fnTerm)
        (Term.rename_rename firstTermRenaming secondTermRenaming argTerm)
  | _, _, .natSucc predecessor =>
      Term.natSucc_HEq_congr
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_rename firstTermRenaming secondTermRenaming zeroBranch)
        (Term.rename_rename firstTermRenaming secondTermRenaming succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_rename firstTermRenaming secondTermRenaming zeroBranch)
        (Term.rename_rename firstTermRenaming secondTermRenaming succBranch)
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming headTerm)
        (Term.rename_rename firstTermRenaming secondTermRenaming tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_rename firstTermRenaming secondTermRenaming nilBranch)
        (Term.rename_rename firstTermRenaming secondTermRenaming consBranch)
  | _, _, .optionSome valueTerm =>
      Term.optionSome_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_rename firstTermRenaming secondTermRenaming noneBranch)
        (Term.rename_rename firstTermRenaming secondTermRenaming someBranch)
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_rename firstTermRenaming secondTermRenaming leftBranch)
        (Term.rename_rename firstTermRenaming secondTermRenaming rightBranch)
  | _, _, .recordIntro firstField =>
      Term.recordIntro_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming firstField)
  | _, _, .recordProj recordValue =>
      Term.recordProj_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming recordValue)
  | _, _, .codataDest codataValue =>
      Term.codataDest_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming codataValue)
  | _, _, .equivApp equivTerm argumentTerm =>
      Term.equivApp_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming equivTerm)
        (Term.rename_rename firstTermRenaming secondTermRenaming argumentTerm)
  | _, _, .codataUnfold initialState transition =>
      Term.codataUnfold_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming initialState)
        (Term.rename_rename firstTermRenaming secondTermRenaming transition)
  | _, _, .listNil =>
      Term.listNil_HEq_congr (Ty.rename_compose rho1 rho2 _)
  | _, _, .optionNone =>
      Term.optionNone_HEq_congr (Ty.rename_compose rho1 rho2 _)
  | _, _, .interval0 => HEq.refl _
  | _, _, .interval1 => HEq.refl _
  | _, _, .intervalOpp innerValue =>
      Term.intervalOpp_HEq_congr
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming innerValue)
  | _, _, .intervalMeet leftValue rightValue =>
      Term.intervalMeet_HEq_congr
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming leftValue)
        (Term.rename_rename firstTermRenaming secondTermRenaming rightValue)
  | _, _, .intervalJoin leftValue rightValue =>
      Term.intervalJoin_HEq_congr
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming leftValue)
        (Term.rename_rename firstTermRenaming secondTermRenaming rightValue)
  | _, _, .sessionRecv channel =>
      Term.sessionRecv_HEq_congr
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming channel)
  | _, _, .sessionSend _ channel payload =>
      Term.sessionSend_HEq_congr
        (RawTerm.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming channel)
        (Term.rename_rename firstTermRenaming secondTermRenaming payload)
  | _, _, .universeCode _ _ _ _ => HEq.refl _
  | _, _, .arrowCode outerLevel levelLe _ _ =>
      Term.arrowCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .productCode outerLevel levelLe _ _ =>
      Term.productCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .sumCode outerLevel levelLe _ _ =>
      Term.sumCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .listCode outerLevel levelLe _ =>
      Term.listCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .optionCode outerLevel levelLe _ =>
      Term.optionCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .eitherCode outerLevel levelLe _ _ =>
      Term.eitherCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .idCode outerLevel levelLe _ _ _ =>
      Term.idCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .equivCode outerLevel levelLe _ _ =>
      Term.equivCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .refl _ _ =>
      Term.refl_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .idJ baseCase witness =>
      Term.idJ_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming baseCase)
        (Term.rename_rename firstTermRenaming secondTermRenaming witness)
  | _, _, .oeqRefl _ _ =>
      Term.oeqRefl_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .oeqJ baseCase witness =>
      Term.oeqJ_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming baseCase)
        (Term.rename_rename firstTermRenaming secondTermRenaming witness)
  | _, _, .idStrictRefl modeIsStrict _ _ =>
      Term.idStrictRefl_HEq_congr modeIsStrict
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .idStrictRec modeIsStrict baseCase witness =>
      Term.idStrictRec_HEq_congr modeIsStrict
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming baseCase)
        (Term.rename_rename firstTermRenaming secondTermRenaming witness)
  | _, _, .modIntro inner =>
      Term.modIntro_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming inner)
  | _, _, .modElim inner =>
      Term.modElim_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming inner)
  | _, _, .subsume inner =>
      Term.subsume_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming inner)
  | _, _, .cumulUp _ _ _ _ _ typeCode =>
      Term.cumulUp_HEq_congr
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming typeCode)
  | _, _, .equivReflId _ =>
      Term.equivReflId_HEq_congr (Ty.rename_compose rho1 rho2 _)
  | _, _, .equivReflIdAtId _ _ _ _ =>
      Term.equivReflIdAtId_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
  | _, _, .uaToEquiv _ _ _ _ _ _ proof =>
      Term.uaToEquiv_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming proof)
  | _, _, .equivApply equivTerm argumentTerm =>
      Term.equivApply_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming equivTerm)
        (Term.rename_rename firstTermRenaming secondTermRenaming argumentTerm)
  | _, _, .pathApp modeIsUnivalent pathTerm intervalTerm =>
      Term.pathApp_HEq_congr modeIsUnivalent
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming pathTerm)
        (Term.rename_rename firstTermRenaming secondTermRenaming intervalTerm)
  | _, _, .glueIntro modeIsUnivalent _ _ baseValue partialValue =>
      Term.glueIntro_HEq_congr modeIsUnivalent
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming baseValue)
        (Term.rename_rename firstTermRenaming secondTermRenaming partialValue)
  | _, _, .glueElim modeIsUnivalent gluedValue =>
      Term.glueElim_HEq_congr modeIsUnivalent
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming gluedValue)
  | _, _, .transp modeIsUnivalent universeLevel universeLevelLt _ _ _ _ typePath sourceValue =>
      Term.transp_HEq_congr modeIsUnivalent universeLevel universeLevelLt
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming typePath)
        (Term.rename_rename firstTermRenaming secondTermRenaming sourceValue)
  | _, _, .hcomp modeIsUnivalent sidesValue capValue =>
      Term.hcomp_HEq_congr modeIsUnivalent
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming sidesValue)
        (Term.rename_rename firstTermRenaming secondTermRenaming capValue)
  | _, _, .hcompPath modeIsUnivalent _ _ sidesPath capValue =>
      Term.hcompPath_HEq_congr modeIsUnivalent
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming sidesPath)
        (Term.rename_rename firstTermRenaming secondTermRenaming capValue)
  | _, _, .uaIntroHet innerLevel innerLevelLt _ _ equivWitness =>
      Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming equivWitness)
  | _, _, .funextReflAtId _ _ _ =>
      Term.funextReflAtId_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose_lift rho1 rho2 _)
  | _, _, .funextIntroHet _ _ _ _ =>
      Term.funextIntroHet_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose_lift rho1 rho2 _)
        (RawTerm.rename_compose_lift rho1 rho2 _)
  | _, _, .refineElim refinedValue =>
      Term.refineElim_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose_lift rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming refinedValue)
  | _, _, .refineIntro _ baseValue predicateProof =>
      Term.refineIntro_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose_lift rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming baseValue)
        (Term.rename_rename firstTermRenaming secondTermRenaming predicateProof)
  | _, _, .piTyCode outerLevel levelLe _ _ =>
      Term.piTyCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose_lift rho1 rho2 _)
  | _, _, .sigmaTyCode outerLevel levelLe _ _ =>
      Term.sigmaTyCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose_lift rho1 rho2 _)
  -- Σ first projection: structural (no cast in `Term.rename`).
  | _, _, .fst pairTerm =>
      Term.fst_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose_lift rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming pairTerm)
  -- Bool eliminator: result carries OUTER `subst0_rename_commute.symm ▸`, and the two
  -- branches each carry an inner `subst0_rename_commute ▸` (at boolTrue / boolFalse).
  -- Both renames transport the casts; double-peel the outer, push-and-peel each branch.
  | _, _, .boolElim (motiveType := motiveType) (scrutineeRaw := scrutineeRaw)
              (thenRaw := thenRaw) (elseRaw := elseRaw)
              scrutinee thenBranch elseBranch =>
      let composeRenaming :=
        TermRenaming.compose firstTermRenaming secondTermRenaming
      -- Pin the inner-rename branch casts (motiveType lifted by rho1) with explicit types.
      let firstThen :
          Term middleCtx ((motiveType.rename rho1.lift).subst0 Ty.bool RawTerm.boolTrue)
            (thenRaw.rename rho1) :=
        Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho1 ▸
          Term.rename firstTermRenaming thenBranch
      let firstElse :
          Term middleCtx ((motiveType.rename rho1.lift).subst0 Ty.bool RawTerm.boolFalse)
            (elseRaw.rename rho1) :=
        Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho1 ▸
          Term.rename firstTermRenaming elseBranch
      let composeThen :
          Term targetCtx
            ((motiveType.rename (RawRenaming.compose rho1 rho2).lift).subst0 Ty.bool
              RawTerm.boolTrue)
            (thenRaw.rename (RawRenaming.compose rho1 rho2)) :=
        Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
            (RawRenaming.compose rho1 rho2) ▸
          Term.rename composeRenaming thenBranch
      let composeElse :
          Term targetCtx
            ((motiveType.rename (RawRenaming.compose rho1 rho2).lift).subst0 Ty.bool
              RawTerm.boolFalse)
            (elseRaw.rename (RawRenaming.compose rho1 rho2)) :=
        Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
            (RawRenaming.compose rho1 rho2) ▸
          Term.rename composeRenaming elseBranch
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq secondTermRenaming
          (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho1)
          (targetTerm :=
            Term.boolElim (motiveType := motiveType.rename rho1.lift)
              (Term.rename firstTermRenaming scrutinee) firstThen firstElse))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho2)
              (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho1)))
          (HEq.trans
            (Term.type_eq_symm_cast_heq
              (Ty.subst0_rename_commute (motiveType.rename rho1.lift) Ty.bool
                (scrutineeRaw.rename rho1) rho2))
            (HEq.trans
              (Term.boolElim_HEq_congr
                (Ty.rename_compose_lift rho1 rho2 motiveType)
                (RawTerm.rename_compose rho1 rho2 scrutineeRaw)
                (RawTerm.rename_compose rho1 rho2 thenRaw)
                (RawTerm.rename_compose rho1 rho2 elseRaw)
                (Term.rename_rename firstTermRenaming secondTermRenaming scrutinee)
                (HEq.trans
                  (Term.type_eq_cast_heq
                    (Ty.subst0_rename_commute (motiveType.rename rho1.lift) Ty.bool
                      RawTerm.boolTrue rho2)
                    (Term.rename secondTermRenaming firstThen))
                  (HEq.trans
                    (Term.rename_type_eq_cast_heq secondTermRenaming
                      (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho1)
                      (Term.rename firstTermRenaming thenBranch))
                    (HEq.trans
                      (Term.type_eq_cast_heq
                        (congrArg (fun someType => Ty.rename someType rho2)
                          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho1))
                        (Term.rename secondTermRenaming
                          (Term.rename firstTermRenaming thenBranch)))
                      (HEq.trans
                        (Term.rename_rename firstTermRenaming secondTermRenaming thenBranch)
                        (Term.type_eq_cast_heq
                          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
                            (RawRenaming.compose rho1 rho2))
                          (Term.rename composeRenaming thenBranch)).symm))))
                (HEq.trans
                  (Term.type_eq_cast_heq
                    (Ty.subst0_rename_commute (motiveType.rename rho1.lift) Ty.bool
                      RawTerm.boolFalse rho2)
                    (Term.rename secondTermRenaming firstElse))
                  (HEq.trans
                    (Term.rename_type_eq_cast_heq secondTermRenaming
                      (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho1)
                      (Term.rename firstTermRenaming elseBranch))
                    (HEq.trans
                      (Term.type_eq_cast_heq
                        (congrArg (fun someType => Ty.rename someType rho2)
                          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho1))
                        (Term.rename secondTermRenaming
                          (Term.rename firstTermRenaming elseBranch)))
                      (HEq.trans
                        (Term.rename_rename firstTermRenaming secondTermRenaming elseBranch)
                        (Term.type_eq_cast_heq
                          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
                            (RawRenaming.compose rho1 rho2))
                          (Term.rename composeRenaming elseBranch)).symm)))))
              (Term.type_eq_symm_cast_heq
                (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw
                  (RawRenaming.compose rho1 rho2))
                (targetTerm :=
                  Term.boolElim
                    (motiveType := motiveType.rename (RawRenaming.compose rho1 rho2).lift)
                    (Term.rename composeRenaming scrutinee) composeThen composeElse)).symm)))
  -- Non-dep arrow binder.  The body IH recurses under the two lifts and lands at
  -- `compose (rho1.lift) (rho2.lift)`; `rename_pointwise_HEq` + `rename_targetCtx_cast_HEq`
  -- realign it to `(compose rho1 rho2).lift` (pointwise-equal raws, propositionally-equal
  -- target context).  Outer `weaken_rename_commute` casts peeled on both sides.
  | _, _, .lam (domainType := domainType) (codomainType := codomainType)
              (bodyRaw := bodyRaw) body =>
      let composeRenaming :=
        TermRenaming.compose firstTermRenaming secondTermRenaming
      let domainComposeEq := Ty.rename_compose rho1 rho2 domainType
      let targetCtxEq := congrArg (Ctx.cons targetCtx) domainComposeEq.symm
      let bodyIH :=
        Term.rename_rename (firstTermRenaming.lift domainType)
          (secondTermRenaming.lift (domainType.rename rho1)) body
      let bodyRealign :=
        Term.rename_pointwise_HEq
          (fun position => by
            cases position with
            | mk val isLt =>
              cases val with
              | zero => rfl
              | succ k => rfl)
          (TermRenaming.compose (firstTermRenaming.lift domainType)
            (secondTermRenaming.lift (domainType.rename rho1)))
          (targetCtxEq ▸ composeRenaming.lift domainType) body
      let bodyUncast :=
        Term.rename_targetCtx_cast_HEq targetCtxEq
          (composeRenaming.lift domainType) body
      Term.lam_HEq_congr domainComposeEq
        (Ty.rename_compose rho1 rho2 codomainType)
        (RawTerm.rename_compose_lift rho1 rho2 bodyRaw)
        (HEq.trans
          (Term.type_eq_cast_heq
            (Ty.weaken_rename_commute rho2 (codomainType.rename rho1))
            (Term.rename (secondTermRenaming.lift (domainType.rename rho1))
              (Ty.weaken_rename_commute rho1 codomainType ▸
                Term.rename (firstTermRenaming.lift domainType) body)))
          (HEq.trans
            (Term.rename_type_eq_cast_heq (secondTermRenaming.lift (domainType.rename rho1))
              (Ty.weaken_rename_commute rho1 codomainType)
              (Term.rename (firstTermRenaming.lift domainType) body))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho2.lift)
                  (Ty.weaken_rename_commute rho1 codomainType))
                (Term.rename (secondTermRenaming.lift (domainType.rename rho1))
                  (Term.rename (firstTermRenaming.lift domainType) body)))
              (HEq.trans bodyIH
                (HEq.trans (HEq.trans bodyRealign bodyUncast)
                  (Term.type_eq_cast_heq
                    (Ty.weaken_rename_commute (RawRenaming.compose rho1 rho2) codomainType)
                    (Term.rename (composeRenaming.lift domainType) body)).symm)))))
  -- Dep Π binder.  Body type is `codomainType` directly (no weaken), so no outer cast;
  -- the body IH + realignment is exactly the body HEq.
  | _, _, .lamPi (domainType := domainType) (codomainType := codomainType)
                (bodyRaw := bodyRaw) body =>
      let composeRenaming :=
        TermRenaming.compose firstTermRenaming secondTermRenaming
      let domainComposeEq := Ty.rename_compose rho1 rho2 domainType
      let targetCtxEq := congrArg (Ctx.cons targetCtx) domainComposeEq.symm
      let bodyIH :=
        Term.rename_rename (firstTermRenaming.lift domainType)
          (secondTermRenaming.lift (domainType.rename rho1)) body
      let bodyRealign :=
        Term.rename_pointwise_HEq
          (fun position => by
            cases position with
            | mk val isLt =>
              cases val with
              | zero => rfl
              | succ k => rfl)
          (TermRenaming.compose (firstTermRenaming.lift domainType)
            (secondTermRenaming.lift (domainType.rename rho1)))
          (targetCtxEq ▸ composeRenaming.lift domainType) body
      let bodyUncast :=
        Term.rename_targetCtx_cast_HEq targetCtxEq
          (composeRenaming.lift domainType) body
      Term.lamPi_HEq_congr domainComposeEq
        (Ty.rename_compose_lift rho1 rho2 codomainType)
        (RawTerm.rename_compose_lift rho1 rho2 bodyRaw)
        (HEq.trans bodyIH (HEq.trans bodyRealign bodyUncast))
  -- Σ second projection: outer `subst0_rename_commute.symm ▸` cast in each rename.  The
  -- inner cast transports through the outer rename; peel both, bridge bare `snd` cores,
  -- re-apply the composite cast.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
              (pairRaw := pairRaw) pairTerm =>
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq secondTermRenaming
          (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRaw) rho1))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho2)
              (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRaw) rho1)))
          (HEq.trans
            (Term.type_eq_symm_cast_heq
              (Ty.subst0_rename_commute (secondType.rename rho1.lift)
                (firstType.rename rho1) ((RawTerm.fst pairRaw).rename rho1) rho2))
            (HEq.trans
              (Term.snd_HEq_congr
                (Ty.rename_compose rho1 rho2 _)
                (Ty.rename_compose_lift rho1 rho2 _)
                (RawTerm.rename_compose rho1 rho2 _)
                (Term.rename_rename firstTermRenaming secondTermRenaming pairTerm))
              (Term.type_eq_symm_cast_heq
                (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRaw)
                  (RawRenaming.compose rho1 rho2))).symm)))
  -- Dep Π application: same outer-`subst0_rename_commute.symm ▸` double-peel as `snd`.
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                (argumentRaw := argumentRaw) fn arg =>
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq secondTermRenaming
          (Ty.subst0_rename_commute codomainType domainType argumentRaw rho1))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho2)
              (Ty.subst0_rename_commute codomainType domainType argumentRaw rho1)))
          (HEq.trans
            (Term.type_eq_symm_cast_heq
              (Ty.subst0_rename_commute (codomainType.rename rho1.lift)
                (domainType.rename rho1) (argumentRaw.rename rho1) rho2))
            (HEq.trans
              (Term.appPi_HEq_congr
                (Ty.rename_compose rho1 rho2 _)
                (Ty.rename_compose_lift rho1 rho2 _)
                (RawTerm.rename_compose rho1 rho2 _)
                (RawTerm.rename_compose rho1 rho2 _)
                (Term.rename_rename firstTermRenaming secondTermRenaming fn)
                (Term.rename_rename firstTermRenaming secondTermRenaming arg))
              (Term.type_eq_symm_cast_heq
                (Ty.subst0_rename_commute codomainType domainType argumentRaw
                  (RawRenaming.compose rho1 rho2))).symm)))
  -- Σ pair: NO outer cast; the SECOND component carries a FORWARD `subst0_rename_commute ▸`
  -- cast in each rename.  Push the inner cast through the outer rename, peel, IH, re-cast.
  | _, _, .pair (secondType := secondType) (firstType := firstType)
              (firstRaw := firstRaw) firstValue secondValue =>
      Term.pair_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose_lift rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming firstValue)
        (HEq.trans
          (Term.type_eq_cast_heq
            (Ty.subst0_rename_commute (secondType.rename rho1.lift) (firstType.rename rho1)
              (firstRaw.rename rho1) rho2)
            (Term.rename secondTermRenaming
              (Ty.subst0_rename_commute secondType firstType firstRaw rho1 ▸
                Term.rename firstTermRenaming secondValue)))
          (HEq.trans
            (Term.rename_type_eq_cast_heq secondTermRenaming
              (Ty.subst0_rename_commute secondType firstType firstRaw rho1)
              (Term.rename firstTermRenaming secondValue))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho2)
                  (Ty.subst0_rename_commute secondType firstType firstRaw rho1))
                (Term.rename secondTermRenaming (Term.rename firstTermRenaming secondValue)))
              (HEq.trans
                (Term.rename_rename firstTermRenaming secondTermRenaming secondValue)
                (Term.type_eq_cast_heq
                  (Ty.subst0_rename_commute secondType firstType firstRaw
                    (RawRenaming.compose rho1 rho2))
                  (Term.rename (TermRenaming.compose firstTermRenaming secondTermRenaming)
                    secondValue)).symm))))
  -- Path binder: lifts by the CLOSED `Ty.interval`, so the two lifted target contexts
  -- coincide definitionally — no targetCtx cast.  Body IH realigned by pointwise bridge
  -- only; outer `weaken_rename_commute` casts peeled on both sides.
  | _, _, .pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body =>
      let composeRenaming :=
        TermRenaming.compose firstTermRenaming secondTermRenaming
      let bodyIH :=
        Term.rename_rename (firstTermRenaming.lift Ty.interval)
          (secondTermRenaming.lift Ty.interval) body
      let bodyRealign :=
        Term.rename_pointwise_HEq
          (fun position => by
            cases position with
            | mk val isLt =>
              cases val with
              | zero => rfl
              | succ k => rfl)
          (TermRenaming.compose (firstTermRenaming.lift Ty.interval)
            (secondTermRenaming.lift Ty.interval))
          (composeRenaming.lift Ty.interval) body
      Term.pathLam_HEq_congr modeIsUnivalent
        (Ty.rename_compose rho1 rho2 carrierType)
        (RawTerm.rename_compose rho1 rho2 leftEndpoint)
        (RawTerm.rename_compose rho1 rho2 rightEndpoint)
        (RawTerm.rename_compose_lift rho1 rho2 _)
        (HEq.trans
          (Term.type_eq_cast_heq
            (Ty.weaken_rename_commute rho2 (carrierType.rename rho1))
            (Term.rename (secondTermRenaming.lift Ty.interval)
              (Ty.weaken_rename_commute rho1 carrierType ▸
                Term.rename (firstTermRenaming.lift Ty.interval) body)))
          (HEq.trans
            (Term.rename_type_eq_cast_heq (secondTermRenaming.lift Ty.interval)
              (Ty.weaken_rename_commute rho1 carrierType)
              (Term.rename (firstTermRenaming.lift Ty.interval) body))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho2.lift)
                  (Ty.weaken_rename_commute rho1 carrierType))
                (Term.rename (secondTermRenaming.lift Ty.interval)
                  (Term.rename (firstTermRenaming.lift Ty.interval) body)))
              (HEq.trans bodyIH
                (HEq.trans bodyRealign
                  (Term.type_eq_cast_heq
                    (Ty.weaken_rename_commute (RawRenaming.compose rho1 rho2) carrierType)
                    (Term.rename (composeRenaming.lift Ty.interval) body)).symm)))))
  -- Funext-refl witness: outer `funextReflType_rename.symm ▸` cast in each rename.
  | _, _, .funextRefl domainType codomainType applyRaw =>
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq secondTermRenaming
          (funextReflType_rename rho1 domainType codomainType applyRaw)
          (targetTerm := Term.funextRefl (domainType.rename rho1) (codomainType.rename rho1)
            (applyRaw.rename rho1.lift)))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho2)
              (funextReflType_rename rho1 domainType codomainType applyRaw)))
          (HEq.trans
            (Term.type_eq_symm_cast_heq
              (funextReflType_rename rho2 (domainType.rename rho1) (codomainType.rename rho1)
                (applyRaw.rename rho1.lift)))
            (HEq.trans
              (Term.funextRefl_HEq_congr
                (Ty.rename_compose rho1 rho2 _)
                (Ty.rename_compose rho1 rho2 _)
                (RawTerm.rename_compose_lift rho1 rho2 _))
              (Term.type_eq_symm_cast_heq
                (funextReflType_rename (RawRenaming.compose rho1 rho2)
                  domainType codomainType applyRaw)).symm)))
  -- Observational funext: the pointwiseProof child carries a FORWARD
  -- `oeqFunextPointwiseType_rename ▸` cast in each rename; push through, peel, IH, re-cast.
  | _, _, .oeqFunext (pointwiseRaw := pointwiseRaw) domainType codomainType
              leftFunctionRaw rightFunctionRaw pointwiseProof =>
      let firstPointwise :
          Term middleCtx
            (oeqFunextPointwiseType (domainType.rename rho1) (codomainType.rename rho1)
              (leftFunctionRaw.rename rho1) (rightFunctionRaw.rename rho1))
            (pointwiseRaw.rename rho1) :=
        oeqFunextPointwiseType_rename rho1 domainType codomainType
            leftFunctionRaw rightFunctionRaw ▸
          Term.rename firstTermRenaming pointwiseProof
      Term.oeqFunext_HEq_congr
        (Ty.rename_compose rho1 rho2 _)
        (Ty.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (HEq.trans
          (Term.type_eq_cast_heq
            (oeqFunextPointwiseType_rename rho2 (domainType.rename rho1)
              (codomainType.rename rho1) (leftFunctionRaw.rename rho1)
              (rightFunctionRaw.rename rho1))
            (Term.rename secondTermRenaming firstPointwise))
          (HEq.trans
            (Term.rename_type_eq_cast_heq secondTermRenaming
              (oeqFunextPointwiseType_rename rho1 domainType codomainType
                leftFunctionRaw rightFunctionRaw)
              (Term.rename firstTermRenaming pointwiseProof))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho2)
                  (oeqFunextPointwiseType_rename rho1 domainType codomainType
                    leftFunctionRaw rightFunctionRaw))
                (Term.rename secondTermRenaming (Term.rename firstTermRenaming pointwiseProof)))
              (HEq.trans
                (Term.rename_rename firstTermRenaming secondTermRenaming pointwiseProof)
                (Term.type_eq_cast_heq
                  (oeqFunextPointwiseType_rename (RawRenaming.compose rho1 rho2)
                    domainType codomainType leftFunctionRaw rightFunctionRaw)
                  (Term.rename (TermRenaming.compose firstTermRenaming secondTermRenaming)
                    pointwiseProof)).symm))))
  -- Heterogeneous equivalence-intro: leftInv / rightInv each carry a FORWARD
  -- `equivIntroHet{Left,Right}InverseType_rename ▸` cast in each rename.
  | _, _, .equivIntroHet (carrierA := carrierA) (carrierB := carrierB)
              (forwardRaw := forwardRaw) (backwardRaw := backwardRaw)
              (leftInvRaw := leftInvRaw) (rightInvRaw := rightInvRaw)
              forward backward leftInv rightInv =>
      let firstLeftInv :
          Term middleCtx
            (equivIntroHetLeftInverseType (carrierA.rename rho1)
              (forwardRaw.rename rho1) (backwardRaw.rename rho1))
            (leftInvRaw.rename rho1) :=
        equivIntroHetLeftInverseType_rename rho1 carrierA forwardRaw backwardRaw ▸
          Term.rename firstTermRenaming leftInv
      let firstRightInv :
          Term middleCtx
            (equivIntroHetRightInverseType (carrierB.rename rho1)
              (forwardRaw.rename rho1) (backwardRaw.rename rho1))
            (rightInvRaw.rename rho1) :=
        equivIntroHetRightInverseType_rename rho1 carrierB forwardRaw backwardRaw ▸
          Term.rename firstTermRenaming rightInv
      Term.equivIntroHet_HEq_congr
        (Ty.rename_compose rho1 rho2 carrierA)
        (Ty.rename_compose rho1 rho2 carrierB)
        (RawTerm.rename_compose rho1 rho2 forwardRaw)
        (RawTerm.rename_compose rho1 rho2 backwardRaw)
        (RawTerm.rename_compose rho1 rho2 leftInvRaw)
        (RawTerm.rename_compose rho1 rho2 rightInvRaw)
        (Term.rename_rename firstTermRenaming secondTermRenaming forward)
        (Term.rename_rename firstTermRenaming secondTermRenaming backward)
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetLeftInverseType_rename rho2 (carrierA.rename rho1)
              (forwardRaw.rename rho1) (backwardRaw.rename rho1))
            (Term.rename secondTermRenaming firstLeftInv))
          (HEq.trans
            (Term.rename_type_eq_cast_heq secondTermRenaming
              (equivIntroHetLeftInverseType_rename rho1 carrierA forwardRaw backwardRaw)
              (Term.rename firstTermRenaming leftInv))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho2)
                  (equivIntroHetLeftInverseType_rename rho1 carrierA forwardRaw backwardRaw))
                (Term.rename secondTermRenaming (Term.rename firstTermRenaming leftInv)))
              (HEq.trans
                (Term.rename_rename firstTermRenaming secondTermRenaming leftInv)
                (Term.type_eq_cast_heq
                  (equivIntroHetLeftInverseType_rename (RawRenaming.compose rho1 rho2)
                    carrierA forwardRaw backwardRaw)
                  (Term.rename (TermRenaming.compose firstTermRenaming secondTermRenaming)
                    leftInv)).symm))))
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetRightInverseType_rename rho2 (carrierB.rename rho1)
              (forwardRaw.rename rho1) (backwardRaw.rename rho1))
            (Term.rename secondTermRenaming firstRightInv))
          (HEq.trans
            (Term.rename_type_eq_cast_heq secondTermRenaming
              (equivIntroHetRightInverseType_rename rho1 carrierB forwardRaw backwardRaw)
              (Term.rename firstTermRenaming rightInv))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho2)
                  (equivIntroHetRightInverseType_rename rho1 carrierB forwardRaw backwardRaw))
                (Term.rename secondTermRenaming (Term.rename firstTermRenaming rightInv)))
              (HEq.trans
                (Term.rename_rename firstTermRenaming secondTermRenaming rightInv)
                (Term.type_eq_cast_heq
                  (equivIntroHetRightInverseType_rename (RawRenaming.compose rho1 rho2)
                    carrierB forwardRaw backwardRaw)
                  (Term.rename (TermRenaming.compose firstTermRenaming secondTermRenaming)
                    rightInv)).symm))))
  -- Effect perform: `Term.rename` maps the operationSignature (and CanPerform) by
  -- renaming each carrier; the two renames carry DIFFERENT signatures bridged by the
  -- composite signature equation (no funext; proof-irrelevant CanPerform).
  | _, _, .effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTag arguments =>
      Term.effectPerform_HEq_congr_subst
        (by
          show ((operationSignature.map (fun carrierType => carrierType.rename rho1)).map
                (fun carrierType => carrierType.rename rho2))
            = operationSignature.map
                (fun carrierType => carrierType.rename (RawRenaming.compose rho1 rho2))
          show Effects.OperationSignature.mk operationSignature.effectLabel
                ((operationSignature.argumentCarrier.rename rho1).rename rho2)
                ((operationSignature.resultCarrier.rename rho1).rename rho2)
              = Effects.OperationSignature.mk operationSignature.effectLabel
                (operationSignature.argumentCarrier.rename
                  (RawRenaming.compose rho1 rho2))
                (operationSignature.resultCarrier.rename
                  (RawRenaming.compose rho1 rho2))
          rw [Ty.rename_compose rho1 rho2 operationSignature.argumentCarrier,
              Ty.rename_compose rho1 rho2 operationSignature.resultCarrier])
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (RawTerm.rename_compose rho1 rho2 _)
        (Term.rename_rename firstTermRenaming secondTermRenaming operationTag)
        (Term.rename_rename firstTermRenaming secondTermRenaming arguments)

end LeanFX2
