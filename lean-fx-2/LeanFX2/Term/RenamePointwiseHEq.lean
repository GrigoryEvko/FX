import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose
import LeanFX2.Term.SubstPointwiseHEq

/-! # LeanFX2.Term.RenamePointwiseHEq  (rename-pointwise heterogeneous bridge)

Rename analogue of `Term.subst_pointwise_HEq`.  `TermRenaming` is a `Prop`, so
`Term.rename` depends only on the underlying `RawRenaming`; this bridge says that
two renamings over *pointwise-equal* raw renamings (living in propositionally-equal
target contexts) rename every term heterogeneously-equally:

  (∀ p, rho1 p = rho2 p) → HEq (rename tr1 t) (rename tr2 t)

Index witnesses come from `Ty.rename_pointwise` / `RawTerm.rename_pointwise`; the
binder arms recurse under one lift, where `RawRenaming.lift_pointwise` propagates
the pointwise hypothesis and the divergent lifted target context is reconciled by
`Term.rename_targetCtx_cast_HEq`.  Pure HEq.trans chains — NO bare `simp`/`unfold`.

This closes the binder arms of `Term.rename_rename` (functoriality), where the body
IH lands at `compose rho1.lift rho2.lift` and must realign to
`(compose rho1 rho2).lift` (pointwise-equal raws). -/

namespace LeanFX2

/-- Casting a typed renaming's target context by an equality leaves the rename
result heterogeneously unchanged.  `TermRenaming` is a Prop, so only the context
index matters. -/
theorem Term.rename_targetCtx_cast_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx1 targetCtx2 : Ctx mode level targetScope}
    (targetCtxEq : targetCtx1 = targetCtx2)
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx1 rho)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (someTerm : Term sourceCtx someType raw) :
    HEq (Term.rename (targetCtxEq ▸ termRenaming) someTerm)
        (Term.rename termRenaming someTerm) := by
  cases targetCtxEq
  exact HEq.rfl

/-- `Term.rename` respects pointwise heterogeneous equality of raw renamings.
Two renamings over pointwise-equal raw renamings rename every term
heterogeneously-equally.  The binder arms recurse under one lift and reconcile the
divergent lifted target context via `rename_targetCtx_cast_HEq`. -/
theorem Term.rename_pointwise_HEq
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho1 rho2 : RawRenaming sourceScope targetScope}
    (renamingEq : ∀ position, rho1 position = rho2 position)
    (firstTermRenaming : TermRenaming sourceCtx targetCtx rho1)
    (secondTermRenaming : TermRenaming sourceCtx targetCtx rho2) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
      (someTerm : Term sourceCtx someType raw),
        HEq (Term.rename firstTermRenaming someTerm)
            (Term.rename secondTermRenaming someTerm)
  | _, _, .var position =>
      HEq.trans
        (Term.rename_var_HEq firstTermRenaming position)
        (HEq.trans
          (by rw [renamingEq position])
          (Term.rename_var_HEq secondTermRenaming position).symm)
  | _, _, .unit => HEq.refl _
  | _, _, .app fnTerm argTerm =>
      Term.app_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming fnTerm)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming argTerm)
  -- Non-dep arrow binder: rename lifts each renaming by `domainType`, landing in
  -- `targetCtx.cons (domainType.rename rhoᵢ)` — divergent contexts.  Cast the second
  -- lift back onto the first's target, run the lifted-renaming IH on `body`, peel the
  -- outer `weaken_rename_commute` casts on both sides.
  | _, _, .lam (domainType := domainType) (codomainType := codomainType)
              (bodyRaw := bodyRaw) body =>
      let domainEq := Ty.rename_pointwise renamingEq domainType
      let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEq.symm
      let coreLifted :=
        Term.rename_pointwise_HEq (RawRenaming.lift_pointwise renamingEq)
          (firstTermRenaming.lift domainType)
          (targetCtxEq ▸ secondTermRenaming.lift domainType) body
      let coreUncast :=
        Term.rename_targetCtx_cast_HEq targetCtxEq
          (secondTermRenaming.lift domainType) body
      Term.lam_HEq_congr domainEq
        (Ty.rename_pointwise renamingEq codomainType)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) bodyRaw)
        (HEq.trans
          (Term.type_eq_cast_heq (Ty.weaken_rename_commute rho1 codomainType)
            (Term.rename (firstTermRenaming.lift domainType) body))
          (HEq.trans (HEq.trans coreLifted coreUncast)
            (Term.type_eq_cast_heq (Ty.weaken_rename_commute rho2 codomainType)
              (Term.rename (secondTermRenaming.lift domainType) body)).symm))
  | _, _, .lamPi (domainType := domainType) (codomainType := codomainType)
                (bodyRaw := bodyRaw) body =>
      let domainEq := Ty.rename_pointwise renamingEq domainType
      let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEq.symm
      let coreLifted :=
        Term.rename_pointwise_HEq (RawRenaming.lift_pointwise renamingEq)
          (firstTermRenaming.lift domainType)
          (targetCtxEq ▸ secondTermRenaming.lift domainType) body
      let coreUncast :=
        Term.rename_targetCtx_cast_HEq targetCtxEq
          (secondTermRenaming.lift domainType) body
      Term.lamPi_HEq_congr domainEq
        (Ty.rename_pointwise (RawRenaming.lift_pointwise renamingEq) codomainType)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) bodyRaw)
        (HEq.trans coreLifted coreUncast)
  | _, _, .fst pairTerm =>
      Term.fst_HEq_congr (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming pairTerm)
  | _, _, .snd (secondType := secondType) (firstType := firstType)
              (pairRaw := pairRaw) pairTerm =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRaw) rho1))
        (HEq.trans
          (Term.snd_HEq_congr (Ty.rename_pointwise renamingEq _)
            (Ty.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
            (RawTerm.rename_pointwise renamingEq _)
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming
              pairTerm))
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRaw) rho2)).symm)
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                (argumentRaw := argumentRaw) fn arg =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.subst0_rename_commute codomainType domainType argumentRaw rho1))
        (HEq.trans
          (Term.appPi_HEq_congr (Ty.rename_pointwise renamingEq _)
            (Ty.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
            (RawTerm.rename_pointwise renamingEq _)
            (RawTerm.rename_pointwise renamingEq _)
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming fn)
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming arg))
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_rename_commute codomainType domainType argumentRaw rho2)).symm)
  | _, _, .pair (secondType := secondType) (firstType := firstType)
              (firstRaw := firstRaw) fv sv =>
      Term.pair_HEq_congr (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming fv)
        (HEq.trans
          (Term.type_eq_cast_heq
            (Ty.subst0_rename_commute secondType firstType firstRaw rho1)
            (Term.rename firstTermRenaming sv))
          (HEq.trans
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming sv)
            (Term.type_eq_cast_heq
              (Ty.subst0_rename_commute secondType firstType firstRaw rho2)
              (Term.rename secondTermRenaming sv)).symm))
  | _, _, .boolTrue => HEq.refl _
  | _, _, .boolFalse => HEq.refl _
  | _, _, .natZero => HEq.refl _
  | _, _, .natSucc predecessor =>
      Term.natSucc_HEq_congr
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming zeroBranch)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming zeroBranch)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming succBranch)
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming headTerm)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming nilBranch)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming consBranch)
  | _, _, .optionSome valueTerm =>
      Term.optionSome_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming noneBranch)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming someBranch)
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming scrutinee)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming leftBranch)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming rightBranch)
  | _, _, .recordIntro firstField =>
      Term.recordIntro_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming firstField)
  | _, _, .recordProj recordValue =>
      Term.recordProj_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming recordValue)
  | _, _, .codataDest codataValue =>
      Term.codataDest_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming codataValue)
  | _, _, .equivApp equivTerm argumentTerm =>
      Term.equivApp_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming equivTerm)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming argumentTerm)
  | _, _, .codataUnfold initialState transition =>
      Term.codataUnfold_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming initialState)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming transition)
  | _, _, .listNil =>
      Term.listNil_HEq_congr (Ty.rename_pointwise renamingEq _)
  | _, _, .optionNone =>
      Term.optionNone_HEq_congr (Ty.rename_pointwise renamingEq _)
  | _, _, .interval0 => HEq.refl _
  | _, _, .interval1 => HEq.refl _
  | _, _, .intervalOpp innerValue =>
      Term.intervalOpp_HEq_congr
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming innerValue)
  | _, _, .intervalMeet leftValue rightValue =>
      Term.intervalMeet_HEq_congr
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming leftValue)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming rightValue)
  | _, _, .intervalJoin leftValue rightValue =>
      Term.intervalJoin_HEq_congr
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming leftValue)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming rightValue)
  | _, _, .sessionRecv channel =>
      Term.sessionRecv_HEq_congr
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming channel)
  | _, _, .sessionSend _ channel payload =>
      Term.sessionSend_HEq_congr
        (RawTerm.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming channel)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming payload)
  | _, _, .universeCode _ _ _ _ => HEq.refl _
  | _, _, .arrowCode outerLevel levelLe _ _ =>
      Term.arrowCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .productCode outerLevel levelLe _ _ =>
      Term.productCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .sumCode outerLevel levelLe _ _ =>
      Term.sumCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .listCode outerLevel levelLe _ =>
      Term.listCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .optionCode outerLevel levelLe _ =>
      Term.optionCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .eitherCode outerLevel levelLe _ _ =>
      Term.eitherCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .idCode outerLevel levelLe _ _ _ =>
      Term.idCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .equivCode outerLevel levelLe _ _ =>
      Term.equivCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .refl _ _ =>
      Term.refl_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .idJ baseCase witness =>
      Term.idJ_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming baseCase)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming witness)
  | _, _, .oeqRefl _ _ =>
      Term.oeqRefl_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .oeqJ baseCase witness =>
      Term.oeqJ_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming baseCase)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming witness)
  | _, _, .idStrictRefl modeIsStrict _ _ =>
      Term.idStrictRefl_HEq_congr modeIsStrict
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .idStrictRec modeIsStrict baseCase witness =>
      Term.idStrictRec_HEq_congr modeIsStrict
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming baseCase)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming witness)
  | _, _, .modIntro inner =>
      Term.modIntro_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming inner)
  | _, _, .modElim inner =>
      Term.modElim_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming inner)
  | _, _, .subsume inner =>
      Term.subsume_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming inner)
  | _, _, .cumulUp _ _ _ _ _ typeCode =>
      Term.cumulUp_HEq_congr
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming typeCode)
  | _, _, .equivReflId _ =>
      Term.equivReflId_HEq_congr (Ty.rename_pointwise renamingEq _)
  | _, _, .equivReflIdAtId _ _ _ _ =>
      Term.equivReflIdAtId_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
  | _, _, .uaToEquiv _ _ _ _ _ _ proof =>
      Term.uaToEquiv_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming proof)
  | _, _, .equivApply equivTerm argumentTerm =>
      Term.equivApply_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming equivTerm)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming argumentTerm)
  | _, _, .pathApp modeIsUnivalent pathTerm intervalTerm =>
      Term.pathApp_HEq_congr modeIsUnivalent
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming pathTerm)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming intervalTerm)
  | _, _, .glueIntro modeIsUnivalent _ _ baseValue partialValue =>
      Term.glueIntro_HEq_congr modeIsUnivalent
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming baseValue)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming partialValue)
  | _, _, .glueElim modeIsUnivalent gluedValue =>
      Term.glueElim_HEq_congr modeIsUnivalent
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming gluedValue)
  | _, _, .transp modeIsUnivalent universeLevel universeLevelLt _ _ _ _ typePath sourceValue =>
      Term.transp_HEq_congr modeIsUnivalent universeLevel universeLevelLt
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming typePath)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming sourceValue)
  | _, _, .hcomp modeIsUnivalent sidesValue capValue =>
      Term.hcomp_HEq_congr modeIsUnivalent
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming sidesValue)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming capValue)
  | _, _, .hcompPath modeIsUnivalent _ _ sidesPath capValue =>
      Term.hcompPath_HEq_congr modeIsUnivalent
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming sidesPath)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming capValue)
  -- Path binder: lifts by the CLOSED `Ty.interval`, so the two lifted target contexts
  -- coincide definitionally — no targetCtx cast needed; recurse directly under the lift.
  | _, _, .pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body =>
      Term.pathLam_HEq_congr modeIsUnivalent
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
        (HEq.trans
          (Term.type_eq_cast_heq (Ty.weaken_rename_commute rho1 carrierType)
            (Term.rename (firstTermRenaming.lift Ty.interval) body))
          (HEq.trans
            (Term.rename_pointwise_HEq (RawRenaming.lift_pointwise renamingEq)
              (firstTermRenaming.lift Ty.interval)
              (secondTermRenaming.lift Ty.interval) body)
            (Term.type_eq_cast_heq (Ty.weaken_rename_commute rho2 carrierType)
              (Term.rename (secondTermRenaming.lift Ty.interval) body)).symm))
  | _, _, .uaIntroHet innerLevel innerLevelLt _ _ equivWitness =>
      Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming equivWitness)
  | _, _, .funextReflAtId _ _ _ =>
      Term.funextReflAtId_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
  | _, _, .funextIntroHet _ _ _ _ =>
      Term.funextIntroHet_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
  | _, _, .refineElim refinedValue =>
      Term.refineElim_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming refinedValue)
  | _, _, .refineIntro _ baseValue predicateProof =>
      Term.refineIntro_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming baseValue)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming predicateProof)
  | _, _, .piTyCode outerLevel levelLe _ _ =>
      Term.piTyCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
  | _, _, .sigmaTyCode outerLevel levelLe _ _ =>
      Term.sigmaTyCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
  | _, _, .funextRefl domainType codomainType applyRaw =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (funextReflType_rename rho1 domainType codomainType applyRaw))
        (HEq.trans
          (Term.funextRefl_HEq_congr
            (Ty.rename_pointwise renamingEq _)
            (Ty.rename_pointwise renamingEq _)
            (RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _))
          (Term.type_eq_symm_cast_heq
            (funextReflType_rename rho2 domainType codomainType applyRaw)).symm)
  | _, _, .oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
              pointwiseProof =>
      Term.oeqFunext_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (HEq.trans
          (Term.type_eq_cast_heq
            (oeqFunextPointwiseType_rename rho1 domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            (Term.rename firstTermRenaming pointwiseProof))
          (HEq.trans
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming
              pointwiseProof)
            (Term.type_eq_cast_heq
              (oeqFunextPointwiseType_rename rho2 domainType codomainType
                leftFunctionRaw rightFunctionRaw)
              (Term.rename secondTermRenaming pointwiseProof)).symm))
  | _, _, .equivIntroHet (carrierA := carrierA) (carrierB := carrierB)
              (forwardRaw := forwardRaw) (backwardRaw := backwardRaw)
              forward backward leftInv rightInv =>
      Term.equivIntroHet_HEq_congr
        (Ty.rename_pointwise renamingEq _)
        (Ty.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming forward)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming backward)
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetLeftInverseType_rename rho1 carrierA forwardRaw backwardRaw)
            (Term.rename firstTermRenaming leftInv))
          (HEq.trans
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming leftInv)
            (Term.type_eq_cast_heq
              (equivIntroHetLeftInverseType_rename rho2 carrierA forwardRaw backwardRaw)
              (Term.rename secondTermRenaming leftInv)).symm))
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetRightInverseType_rename rho1 carrierB forwardRaw backwardRaw)
            (Term.rename firstTermRenaming rightInv))
          (HEq.trans
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming rightInv)
            (Term.type_eq_cast_heq
              (equivIntroHetRightInverseType_rename rho2 carrierB forwardRaw backwardRaw)
              (Term.rename secondTermRenaming rightInv)).symm))
  -- Bool eliminator: result carries OUTER `subst0_rename_commute.symm ▸`, and the two
  -- branches each carry an inner `subst0_rename_commute ▸` (at boolTrue / boolFalse).
  | _, _, .boolElim (motiveType := motiveType) (scrutineeRaw := scrutineeRaw)
              scrutinee thenBranch elseBranch =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho1))
        (HEq.trans
          (Term.boolElim_HEq_congr
            (Ty.rename_pointwise (RawRenaming.lift_pointwise renamingEq) _)
            (RawTerm.rename_pointwise renamingEq _)
            (RawTerm.rename_pointwise renamingEq _)
            (RawTerm.rename_pointwise renamingEq _)
            (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming
              scrutinee)
            (HEq.trans
              (Term.type_eq_cast_heq
                (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho1)
                (Term.rename firstTermRenaming thenBranch))
              (HEq.trans
                (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming
                  thenBranch)
                (Term.type_eq_cast_heq
                  (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho2)
                  (Term.rename secondTermRenaming thenBranch)).symm))
            (HEq.trans
              (Term.type_eq_cast_heq
                (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho1)
                (Term.rename firstTermRenaming elseBranch))
              (HEq.trans
                (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming
                  elseBranch)
                (Term.type_eq_cast_heq
                  (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho2)
                  (Term.rename secondTermRenaming elseBranch)).symm)))
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho2)).symm)
  | _, _, .effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTag arguments =>
      Term.effectPerform_HEq_congr_subst
        (by
          show operationSignature.map (fun carrierType => carrierType.rename rho1)
            = operationSignature.map (fun carrierType => carrierType.rename rho2)
          show Effects.OperationSignature.mk operationSignature.effectLabel
                (operationSignature.argumentCarrier.rename rho1)
                (operationSignature.resultCarrier.rename rho1)
              = Effects.OperationSignature.mk operationSignature.effectLabel
                (operationSignature.argumentCarrier.rename rho2)
                (operationSignature.resultCarrier.rename rho2)
          rw [Ty.rename_pointwise renamingEq operationSignature.argumentCarrier,
              Ty.rename_pointwise renamingEq operationSignature.resultCarrier])
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (RawTerm.rename_pointwise renamingEq _)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming operationTag)
        (Term.rename_pointwise_HEq renamingEq firstTermRenaming secondTermRenaming arguments)

end LeanFX2
