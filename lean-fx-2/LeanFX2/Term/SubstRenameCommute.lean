import LeanFX2.Term.SubstRenameCommute.Support
import LeanFX2.Term.SubstRenameCommute.Binders
import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT

/-! # LeanFX2.Term.SubstRenameCommute  (strength-T8 ScR engine — WIP dispatcher)

Typed term-level subst/rename FUSION (ScR direction): renaming a substituted term
equals substituting by the output-renamed substitution.  The MIRROR of the shipped
RcS engine `Term.rename_subst_commute`; both are required to derive T8
(`Term.subst0_rename_commute`, #1964) and thence the 34 subst0 arms of #2027.

  rename ρ (subst σ t)  ≅  subst (renameOutput σ ρ) t

`Subst.renameOutput σ ρ` renames each substitution entry's output by ρ.  HEq-valued
(intrinsic typing: both the Ty index — bridged by `Ty.subst_rename_commute` — and the
raw index differ).  78-arm structural induction mirroring the RcS engine.

## Status: COMPLETE — all 78 constructor arms shipped zero-axiom.  The three binder arms
(`lamPi` / `lam` / `pathLam`) dispatch to `SubstRenameCommute/Binders.lean`, whose body
realignment uses `TermSubst.renameOutput_lift_entry_HEq`.  Its var(k+1) case reduces to a
Term-level rename/weaken commute `rename (tr.lift X) (weaken X t) ≅ weaken (X.rename rho)
(rename tr t)` (`Term.rename_weaken_commute`), derived from typed-Term rename functoriality
`Term.rename_rename` (`LeanFX2/Term/RenameRename.lean`).  The RcS binder NEVER needed this —
`subst` ABSORBS the lift cast, whereas `rename` TRANSPORTS it, exposing the `rename`-of-
`weaken` that functoriality discharges. -/

namespace LeanFX2

theorem Term.subst_rename_commute
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
      (someTerm : Term sourceCtx someType raw),
        HEq (Term.rename termRenaming (Term.subst termSubst someTerm))
            (Term.subst (TermSubst.renameOutput termSubst termRenaming) someTerm)
  | _, _, .var position =>
      -- `subst termSubst (var p)` is the entry `termSubst p`; `renameOutput`'s entry is
      -- exactly `rename termRenaming (termSubst p)` up to the type cast, so the per-position
      -- HEq closes the arm directly.
      (TermSubst.renameOutput_position_HEq termSubst termRenaming position).symm
  | _, _, .unit => HEq.refl _
  | _, _, .boolTrue => HEq.refl _
  | _, _, .boolFalse => HEq.refl _
  | _, _, .natZero => HEq.refl _
  | _, _, .app fnTerm argTerm =>
      Term.app_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming fnTerm)
        (Term.subst_rename_commute termSubst termRenaming argTerm)
  | _, _, .natSucc predecessor =>
      Term.natSucc_HEq_congr
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming scrutinee)
        (Term.subst_rename_commute termSubst termRenaming zeroBranch)
        (Term.subst_rename_commute termSubst termRenaming succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming scrutinee)
        (Term.subst_rename_commute termSubst termRenaming zeroBranch)
        (Term.subst_rename_commute termSubst termRenaming succBranch)
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming headTerm)
        (Term.subst_rename_commute termSubst termRenaming tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming scrutinee)
        (Term.subst_rename_commute termSubst termRenaming nilBranch)
        (Term.subst_rename_commute termSubst termRenaming consBranch)
  | _, _, .optionSome valueTerm =>
      Term.optionSome_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming scrutinee)
        (Term.subst_rename_commute termSubst termRenaming noneBranch)
        (Term.subst_rename_commute termSubst termRenaming someBranch)
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming scrutinee)
        (Term.subst_rename_commute termSubst termRenaming leftBranch)
        (Term.subst_rename_commute termSubst termRenaming rightBranch)
  | _, _, .recordIntro firstField =>
      Term.recordIntro_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming firstField)
  | _, _, .recordProj recordValue =>
      Term.recordProj_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming recordValue)
  | _, _, .codataDest codataValue =>
      Term.codataDest_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming codataValue)
  | _, _, .equivApp equivTerm argumentTerm =>
      Term.equivApp_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming equivTerm)
        (Term.subst_rename_commute termSubst termRenaming argumentTerm)
  | _, _, .codataUnfold initialState transition =>
      Term.codataUnfold_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming initialState)
        (Term.subst_rename_commute termSubst termRenaming transition)
  | _, _, .listNil =>
      Term.listNil_HEq_congr (Ty.subst_rename_commute sigma rho _)
  | _, _, .optionNone =>
      Term.optionNone_HEq_congr (Ty.subst_rename_commute sigma rho _)
  | _, _, .interval0 => HEq.refl _
  | _, _, .interval1 => HEq.refl _
  | _, _, .intervalOpp innerValue =>
      Term.intervalOpp_HEq_congr
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming innerValue)
  | _, _, .intervalMeet leftValue rightValue =>
      Term.intervalMeet_HEq_congr
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming leftValue)
        (Term.subst_rename_commute termSubst termRenaming rightValue)
  | _, _, .intervalJoin leftValue rightValue =>
      Term.intervalJoin_HEq_congr
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming leftValue)
        (Term.subst_rename_commute termSubst termRenaming rightValue)
  | _, _, .sessionRecv channel =>
      Term.sessionRecv_HEq_congr
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming channel)
  | _, _, .sessionSend _ channel payload =>
      Term.sessionSend_HEq_congr
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming channel)
        (Term.subst_rename_commute termSubst termRenaming payload)
  | _, _, .universeCode _ _ _ _ => HEq.refl _
  | _, _, .arrowCode outerLevel levelLe _ _ =>
      Term.arrowCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .productCode outerLevel levelLe _ _ =>
      Term.productCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .sumCode outerLevel levelLe _ _ =>
      Term.sumCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .listCode outerLevel levelLe _ =>
      Term.listCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .optionCode outerLevel levelLe _ =>
      Term.optionCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .eitherCode outerLevel levelLe _ _ =>
      Term.eitherCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .idCode outerLevel levelLe _ _ _ =>
      Term.idCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .equivCode outerLevel levelLe _ _ =>
      Term.equivCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .refl _ _ =>
      Term.refl_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .idJ baseCase witness =>
      Term.idJ_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming baseCase)
        (Term.subst_rename_commute termSubst termRenaming witness)
  | _, _, .oeqRefl _ _ =>
      Term.oeqRefl_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .oeqJ baseCase witness =>
      Term.oeqJ_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming baseCase)
        (Term.subst_rename_commute termSubst termRenaming witness)
  | _, _, .idStrictRefl modeIsStrict _ _ =>
      Term.idStrictRefl_HEq_congr modeIsStrict
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .idStrictRec modeIsStrict baseCase witness =>
      Term.idStrictRec_HEq_congr modeIsStrict
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming baseCase)
        (Term.subst_rename_commute termSubst termRenaming witness)
  | _, _, .modIntro inner =>
      Term.modIntro_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming inner)
  | _, _, .modElim inner =>
      Term.modElim_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming inner)
  | _, _, .subsume inner =>
      Term.subsume_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming inner)
  | _, _, .cumulUp _ _ _ _ _ typeCode =>
      Term.cumulUp_HEq_congr
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming typeCode)
  | _, _, .equivReflId _ =>
      Term.equivReflId_HEq_congr (Ty.subst_rename_commute sigma rho _)
  | _, _, .equivReflIdAtId _ _ _ _ =>
      Term.equivReflIdAtId_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
  | _, _, .uaToEquiv _ _ _ _ _ _ proof =>
      Term.uaToEquiv_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming proof)
  | _, _, .equivApply equivTerm argumentTerm =>
      Term.equivApply_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming equivTerm)
        (Term.subst_rename_commute termSubst termRenaming argumentTerm)
  | _, _, .fst pairTerm =>
      Term.fst_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute_lift sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming pairTerm)
  | _, _, .pathApp modeIsUnivalent pathTerm intervalTerm =>
      Term.pathApp_HEq_congr modeIsUnivalent
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming pathTerm)
        (Term.subst_rename_commute termSubst termRenaming intervalTerm)
  | _, _, .glueIntro modeIsUnivalent _ _ baseValue partialValue =>
      Term.glueIntro_HEq_congr modeIsUnivalent
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming baseValue)
        (Term.subst_rename_commute termSubst termRenaming partialValue)
  | _, _, .glueElim modeIsUnivalent gluedValue =>
      Term.glueElim_HEq_congr modeIsUnivalent
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming gluedValue)
  | _, _, .transp modeIsUnivalent universeLevel universeLevelLt _ _ _ _ typePath sourceValue =>
      Term.transp_HEq_congr modeIsUnivalent universeLevel universeLevelLt
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming typePath)
        (Term.subst_rename_commute termSubst termRenaming sourceValue)
  | _, _, .hcomp modeIsUnivalent sidesValue capValue =>
      Term.hcomp_HEq_congr modeIsUnivalent
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming sidesValue)
        (Term.subst_rename_commute termSubst termRenaming capValue)
  | _, _, .hcompPath modeIsUnivalent _ _ sidesPath capValue =>
      Term.hcompPath_HEq_congr modeIsUnivalent
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming sidesPath)
        (Term.subst_rename_commute termSubst termRenaming capValue)
  | _, _, .uaIntroHet innerLevel innerLevelLt _ _ equivWitness =>
      Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming equivWitness)
  | _, _, .refineElim refinedValue =>
      Term.refineElim_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute_lift sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming refinedValue)
  | _, _, .refineIntro _ baseValue predicateProof =>
      Term.refineIntro_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute_lift sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming baseValue)
        (Term.subst_rename_commute termSubst termRenaming predicateProof)
  | _, _, .piTyCode outerLevel levelLe _ _ =>
      Term.piTyCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute_lift sigma rho _)
  | _, _, .sigmaTyCode outerLevel levelLe _ _ =>
      Term.sigmaTyCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute_lift sigma rho _)
  | _, _, .funextReflAtId _ _ _ =>
      Term.funextReflAtId_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute_lift sigma rho _)
  | _, _, .funextIntroHet _ _ _ _ =>
      Term.funextIntroHet_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute_lift sigma rho _)
        (RawTerm.subst_rename_commute_lift sigma rho _)
  -- Effect perform: subst maps the operation signature by `subst σ`, then rename maps the
  -- result by `rename ρ`, so the two sides carry DIFFERENT signatures bridged by the ScR
  -- `map_subst_rename_commute`.  `effectPerform_HEq_congr_subst` is direction-agnostic (it
  -- takes a signature `Eq` and absorbs the permission witnesses by proof irrelevance).
  | _, _, .effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTag arguments =>
      Term.effectPerform_HEq_congr_subst
        (Effects.OperationSignature.map_subst_rename_commute sigma rho
          operationSignature)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming operationTag)
        (Term.subst_rename_commute termSubst termRenaming arguments)
  -- Σ second projection (cast-carrying, MIRROR of the RcS arm).  In ScR the outer op is
  -- `rename`, which TRANSPORTS the inner `subst`'s `subst0_subst_commute` cast (rather than
  -- absorbing it), and `rename` on the bare `snd` re-introduces a `subst0_rename_commute`
  -- cast — a 5-step peel: (A) push the inner subst cast through rename (`rename_type_eq_cast_heq`);
  -- (B) peel the resulting renamed cast (`type_eq_cast_heq`); (C) peel the rename-arm's own
  -- `subst0_rename_commute` cast; (D) bridge the bare `snd` cores via `snd_HEq_congr` + the
  -- pair IH; (E) re-apply the RHS `subst (renameOutput)` cast.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
               (pairRaw := pairRaw) pairTerm =>
      HEq.trans
        (Term.rename_type_eq_cast_heq termRenaming
          (Ty.subst0_subst_commute secondType firstType (RawTerm.fst pairRaw) sigma).symm
          (Term.snd (Term.subst termSubst pairTerm)))
        (HEq.trans
          (Term.type_eq_cast_heq
            (congrArg (fun someType => Ty.rename someType rho)
              (Ty.subst0_subst_commute secondType firstType (RawTerm.fst pairRaw) sigma).symm)
            (Term.rename termRenaming (Term.snd (Term.subst termSubst pairTerm))))
          (HEq.trans
            (Term.type_eq_cast_heq
              (Ty.subst0_rename_commute (secondType.subst sigma.lift) (firstType.subst sigma)
                (RawTerm.fst (pairRaw.subst sigma.forRaw)) rho).symm
              (Term.snd (Term.rename termRenaming (Term.subst termSubst pairTerm))))
            (HEq.trans
              (Term.snd_HEq_congr
                (Ty.subst_rename_commute sigma rho _)
                (Ty.subst_rename_commute_lift sigma rho _)
                (RawTerm.subst_rename_commute sigma.forRaw rho _)
                (Term.subst_rename_commute termSubst termRenaming pairTerm))
              (Term.type_eq_cast_heq
                (Ty.subst0_subst_commute secondType firstType (RawTerm.fst pairRaw)
                  (Subst.renameOutput sigma rho)).symm
                (Term.snd (Term.subst (TermSubst.renameOutput termSubst termRenaming)
                  pairTerm))).symm)))
  -- Dep Π application: same 5-step outer-`subst0`-cast peel as `snd` (β-redex result type
  -- is `codomainType.subst0 domainType argumentRaw`).
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                (argumentRaw := argumentRaw) fn arg =>
      HEq.trans
        (Term.rename_type_eq_cast_heq termRenaming
          (Ty.subst0_subst_commute codomainType domainType argumentRaw sigma).symm
          (Term.appPi (Term.subst termSubst fn) (Term.subst termSubst arg)))
        (HEq.trans
          (Term.type_eq_cast_heq
            (congrArg (fun someType => Ty.rename someType rho)
              (Ty.subst0_subst_commute codomainType domainType argumentRaw sigma).symm)
            (Term.rename termRenaming
              (Term.appPi (Term.subst termSubst fn) (Term.subst termSubst arg))))
          (HEq.trans
            (Term.type_eq_cast_heq
              (Ty.subst0_rename_commute (codomainType.subst sigma.lift)
                (domainType.subst sigma) (argumentRaw.subst sigma.forRaw) rho).symm
              (Term.appPi (Term.rename termRenaming (Term.subst termSubst fn))
                (Term.rename termRenaming (Term.subst termSubst arg))))
            (HEq.trans
              (Term.appPi_HEq_congr
                (Ty.subst_rename_commute sigma rho _)
                (Ty.subst_rename_commute_lift sigma rho _)
                (RawTerm.subst_rename_commute sigma.forRaw rho _)
                (RawTerm.subst_rename_commute sigma.forRaw rho _)
                (Term.subst_rename_commute termSubst termRenaming fn)
                (Term.subst_rename_commute termSubst termRenaming arg))
              (Term.type_eq_cast_heq
                (Ty.subst0_subst_commute codomainType domainType argumentRaw
                  (Subst.renameOutput sigma rho)).symm
                (Term.appPi
                  (Term.subst (TermSubst.renameOutput termSubst termRenaming) fn)
                  (Term.subst (TermSubst.renameOutput termSubst termRenaming) arg))).symm)))
  -- Σ pair: NO outer cast (result is the plain `sigmaTy`); the SECOND component carries a
  -- FORWARD `subst0_*_commute ▸` cast in BOTH subst and rename.  `pair_HEq_congr` takes the
  -- first child as the plain IH; the second child is a 5-step forward chain: peel the
  -- rename-arm `subst0_rename_commute` cast, push the subst-arm `subst0_subst_commute` cast
  -- through rename + peel the renamed cast, the IH, then re-apply the RHS `renameOutput` cast.
  | _, _, .pair (secondType := secondType) (firstType := firstType)
                (firstRaw := firstRaw) firstValue secondValue =>
      Term.pair_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute_lift sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (Term.subst_rename_commute termSubst termRenaming firstValue)
        (HEq.trans
          (Term.type_eq_cast_heq
            (Ty.subst0_rename_commute (secondType.subst sigma.lift) (firstType.subst sigma)
              (firstRaw.subst sigma.forRaw) rho)
            (Term.rename termRenaming
              (Ty.subst0_subst_commute secondType firstType firstRaw sigma ▸
                Term.subst termSubst secondValue)))
          (HEq.trans
            (Term.rename_type_eq_cast_heq termRenaming
              (Ty.subst0_subst_commute secondType firstType firstRaw sigma)
              (Term.subst termSubst secondValue))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho)
                  (Ty.subst0_subst_commute secondType firstType firstRaw sigma))
                (Term.rename termRenaming (Term.subst termSubst secondValue)))
              (HEq.trans
                (Term.subst_rename_commute termSubst termRenaming secondValue)
                (Term.type_eq_cast_heq
                  (Ty.subst0_subst_commute secondType firstType firstRaw
                    (Subst.renameOutput sigma rho))
                  (Term.subst (TermSubst.renameOutput termSubst termRenaming)
                    secondValue)).symm))))
  -- Observational funext: `pair`-shape forward double-peel on the `pointwiseProof` child
  -- (forward `oeqFunextPointwiseType_*` cast in BOTH subst and rename, NO outer cast).  The
  -- five congr index witnesses are plain fusions; the child is the pair-second-component chain.
  | _, _, .oeqFunext domainType codomainType
              leftFunctionRaw rightFunctionRaw pointwiseProof =>
      Term.oeqFunext_HEq_congr
        (Ty.subst_rename_commute sigma rho _)
        (Ty.subst_rename_commute sigma rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (RawTerm.subst_rename_commute sigma.forRaw rho _)
        (HEq.trans
          (Term.type_eq_cast_heq
            (oeqFunextPointwiseType_rename rho (domainType.subst sigma)
              (codomainType.subst sigma) (leftFunctionRaw.subst sigma.forRaw)
              (rightFunctionRaw.subst sigma.forRaw))
            (Term.rename termRenaming
              (oeqFunextPointwiseType_subst sigma domainType codomainType
                leftFunctionRaw rightFunctionRaw ▸
                Term.subst termSubst pointwiseProof)))
          (HEq.trans
            (Term.rename_type_eq_cast_heq termRenaming
              (oeqFunextPointwiseType_subst sigma domainType codomainType
                leftFunctionRaw rightFunctionRaw)
              (Term.subst termSubst pointwiseProof))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho)
                  (oeqFunextPointwiseType_subst sigma domainType codomainType
                    leftFunctionRaw rightFunctionRaw))
                (Term.rename termRenaming (Term.subst termSubst pointwiseProof)))
              (HEq.trans
                (Term.subst_rename_commute termSubst termRenaming pointwiseProof)
                (Term.type_eq_cast_heq
                  (oeqFunextPointwiseType_subst (Subst.renameOutput sigma rho)
                    domainType codomainType leftFunctionRaw rightFunctionRaw)
                  (Term.subst (TermSubst.renameOutput termSubst termRenaming)
                    pointwiseProof)).symm))))
  -- Heterogeneous equivalence-intro: `pair`-shape twice — leftInv (carrierA) and rightInv
  -- (carrierB) each carry a FORWARD `equivIntroHet{Left,Right}InverseType_*` cast in both ops;
  -- forward/backward are plain IH children, no outer cast.
  | _, _, .equivIntroHet (carrierA := carrierA) (carrierB := carrierB)
              (forwardRaw := forwardRaw) (backwardRaw := backwardRaw)
              (leftInvRaw := leftInvRaw) (rightInvRaw := rightInvRaw)
              forward backward leftInv rightInv =>
      Term.equivIntroHet_HEq_congr
        (Ty.subst_rename_commute sigma rho carrierA)
        (Ty.subst_rename_commute sigma rho carrierB)
        (RawTerm.subst_rename_commute sigma.forRaw rho forwardRaw)
        (RawTerm.subst_rename_commute sigma.forRaw rho backwardRaw)
        (RawTerm.subst_rename_commute sigma.forRaw rho leftInvRaw)
        (RawTerm.subst_rename_commute sigma.forRaw rho rightInvRaw)
        (Term.subst_rename_commute termSubst termRenaming forward)
        (Term.subst_rename_commute termSubst termRenaming backward)
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetLeftInverseType_rename rho (carrierA.subst sigma)
              (forwardRaw.subst sigma.forRaw) (backwardRaw.subst sigma.forRaw))
            (Term.rename termRenaming
              (equivIntroHetLeftInverseType_subst sigma carrierA forwardRaw backwardRaw ▸
                Term.subst termSubst leftInv :
                Term middleCtx
                  (equivIntroHetLeftInverseType (carrierA.subst sigma)
                    (forwardRaw.subst sigma.forRaw) (backwardRaw.subst sigma.forRaw))
                  (leftInvRaw.subst sigma.forRaw))))
          (HEq.trans
            (Term.rename_type_eq_cast_heq termRenaming
              (equivIntroHetLeftInverseType_subst sigma carrierA forwardRaw backwardRaw)
              (Term.subst termSubst leftInv))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho)
                  (equivIntroHetLeftInverseType_subst sigma carrierA forwardRaw backwardRaw))
                (Term.rename termRenaming (Term.subst termSubst leftInv)))
              (HEq.trans
                (Term.subst_rename_commute termSubst termRenaming leftInv)
                (Term.type_eq_cast_heq
                  (equivIntroHetLeftInverseType_subst (Subst.renameOutput sigma rho)
                    carrierA forwardRaw backwardRaw)
                  (Term.subst (TermSubst.renameOutput termSubst termRenaming)
                    leftInv)).symm))))
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetRightInverseType_rename rho (carrierB.subst sigma)
              (forwardRaw.subst sigma.forRaw) (backwardRaw.subst sigma.forRaw))
            (Term.rename termRenaming
              (equivIntroHetRightInverseType_subst sigma carrierB forwardRaw backwardRaw ▸
                Term.subst termSubst rightInv :
                Term middleCtx
                  (equivIntroHetRightInverseType (carrierB.subst sigma)
                    (forwardRaw.subst sigma.forRaw) (backwardRaw.subst sigma.forRaw))
                  (rightInvRaw.subst sigma.forRaw))))
          (HEq.trans
            (Term.rename_type_eq_cast_heq termRenaming
              (equivIntroHetRightInverseType_subst sigma carrierB forwardRaw backwardRaw)
              (Term.subst termSubst rightInv))
            (HEq.trans
              (Term.type_eq_cast_heq
                (congrArg (fun someType => Ty.rename someType rho)
                  (equivIntroHetRightInverseType_subst sigma carrierB forwardRaw backwardRaw))
                (Term.rename termRenaming (Term.subst termSubst rightInv)))
              (HEq.trans
                (Term.subst_rename_commute termSubst termRenaming rightInv)
                (Term.type_eq_cast_heq
                  (equivIntroHetRightInverseType_subst (Subst.renameOutput sigma rho)
                    carrierB forwardRaw backwardRaw)
                  (Term.subst (TermSubst.renameOutput termSubst termRenaming)
                    rightInv)).symm))))
  -- Funext-refl witness: `snd`-shape OUTER `.symm ▸` cast via `funextReflType_{subst,rename}`
  -- (NO Term child).  The 5-step outer peel: (A) push the inner subst `.symm` cast through
  -- rename; (B) peel the renamed cast; (C) peel the rename arm's own `.symm` cast on the bare
  -- funextRefl; (D) bridge index witnesses via `funextRefl_HEq_congr` (applyRaw scope+1 → `_lift`);
  -- (E) re-apply the RHS `funextReflType_subst` cast.
  | _, _, .funextRefl domainType codomainType applyRaw =>
      HEq.trans
        (Term.rename_type_eq_cast_heq termRenaming
          (funextReflType_subst sigma domainType codomainType applyRaw).symm
          (Term.funextRefl (domainType.subst sigma) (codomainType.subst sigma)
            (applyRaw.subst sigma.forRaw.lift)))
        (HEq.trans
          (Term.type_eq_cast_heq
            (congrArg (fun someType => Ty.rename someType rho)
              (funextReflType_subst sigma domainType codomainType applyRaw).symm)
            (Term.rename termRenaming
              (Term.funextRefl (domainType.subst sigma) (codomainType.subst sigma)
                (applyRaw.subst sigma.forRaw.lift))))
          (HEq.trans
            (Term.type_eq_cast_heq
              (funextReflType_rename rho (domainType.subst sigma) (codomainType.subst sigma)
                (applyRaw.subst sigma.forRaw.lift)).symm
              (Term.funextRefl _ _ _))
            (HEq.trans
              (Term.funextRefl_HEq_congr
                (Ty.subst_rename_commute sigma rho _)
                (Ty.subst_rename_commute sigma rho _)
                (RawTerm.subst_rename_commute_lift sigma rho _))
              (Term.type_eq_cast_heq
                (funextReflType_subst (Subst.renameOutput sigma rho)
                  domainType codomainType applyRaw).symm
                (Term.funextRefl _ _ _)).symm)))
  -- Bool eliminator: OUTER `.symm ▸ subst0_subst_commute … scrutineeRaw` peel (snd-shape) around
  -- `boolElim_HEq_congr`; scrutinee is a plain IH; then/else are forward double-peels (pair-shape).
  -- The four cast-wrapped branches (subst-arm `substThen`/`substElse`, renameOutput-arm
  -- `renameOutputThen`/`renameOutputElse`) are `let`-bound with explicit types so the `▸` motives
  -- are pinned once (otherwise the inner `boolElim` ctor leaves the branch terms as metavars).
  | _, _, .boolElim (motiveType := motiveType) (scrutineeRaw := scrutineeRaw)
                    (thenRaw := thenRaw) (elseRaw := elseRaw)
                    scrutinee thenBranch elseBranch =>
      let substThen :
          Term middleCtx ((motiveType.subst sigma.lift).subst0 Ty.bool RawTerm.boolTrue)
            (thenRaw.subst sigma.forRaw) :=
        Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue sigma ▸
          Term.subst termSubst thenBranch
      let substElse :
          Term middleCtx ((motiveType.subst sigma.lift).subst0 Ty.bool RawTerm.boolFalse)
            (elseRaw.subst sigma.forRaw) :=
        Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse sigma ▸
          Term.subst termSubst elseBranch
      let renameOutputThen :
          Term targetCtx
            ((motiveType.subst (Subst.renameOutput sigma rho).lift).subst0 Ty.bool
              RawTerm.boolTrue)
            (thenRaw.subst (Subst.renameOutput sigma rho).forRaw) :=
        Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
            (Subst.renameOutput sigma rho) ▸
          Term.subst (TermSubst.renameOutput termSubst termRenaming) thenBranch
      let renameOutputElse :
          Term targetCtx
            ((motiveType.subst (Subst.renameOutput sigma rho).lift).subst0 Ty.bool
              RawTerm.boolFalse)
            (elseRaw.subst (Subst.renameOutput sigma rho).forRaw) :=
        Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
            (Subst.renameOutput sigma rho) ▸
          Term.subst (TermSubst.renameOutput termSubst termRenaming) elseBranch
      let renamedThen :
          Term targetCtx
            (((motiveType.subst sigma.lift).rename rho.lift).subst0 Ty.bool RawTerm.boolTrue)
            ((thenRaw.subst sigma.forRaw).rename rho) :=
        Ty.subst0_rename_commute (motiveType.subst sigma.lift) Ty.bool RawTerm.boolTrue rho ▸
          Term.rename termRenaming substThen
      let renamedElse :
          Term targetCtx
            (((motiveType.subst sigma.lift).rename rho.lift).subst0 Ty.bool RawTerm.boolFalse)
            ((elseRaw.subst sigma.forRaw).rename rho) :=
        Ty.subst0_rename_commute (motiveType.subst sigma.lift) Ty.bool RawTerm.boolFalse rho ▸
          Term.rename termRenaming substElse
      HEq.trans
        (Term.rename_type_eq_cast_heq termRenaming
          (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw sigma).symm
          (Term.boolElim (motiveType := motiveType.subst sigma.lift)
            (Term.subst termSubst scrutinee) substThen substElse))
        (HEq.trans
          (Term.type_eq_cast_heq
            (congrArg (fun someType => Ty.rename someType rho)
              (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw sigma).symm)
            (Term.rename termRenaming
              (Term.boolElim (motiveType := motiveType.subst sigma.lift)
                (Term.subst termSubst scrutinee) substThen substElse)))
          (HEq.trans
            (Term.type_eq_cast_heq
              (Ty.subst0_rename_commute (motiveType.subst sigma.lift) Ty.bool
                (scrutineeRaw.subst sigma.forRaw) rho).symm
              (Term.boolElim (motiveType := (motiveType.subst sigma.lift).rename rho.lift)
                (Term.rename termRenaming (Term.subst termSubst scrutinee))
                renamedThen renamedElse))
            (HEq.trans
              (Term.boolElim_HEq_congr
                (Ty.subst_rename_commute_lift sigma rho _)
                (RawTerm.subst_rename_commute sigma.forRaw rho scrutineeRaw)
                (RawTerm.subst_rename_commute sigma.forRaw rho thenRaw)
                (RawTerm.subst_rename_commute sigma.forRaw rho elseRaw)
                (Term.subst_rename_commute termSubst termRenaming scrutinee)
                (HEq.trans
                  (Term.type_eq_cast_heq
                    (Ty.subst0_rename_commute (motiveType.subst sigma.lift) Ty.bool
                      RawTerm.boolTrue rho)
                    (Term.rename termRenaming substThen))
                  (HEq.trans
                    (Term.rename_type_eq_cast_heq termRenaming
                      (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue sigma)
                      (Term.subst termSubst thenBranch))
                    (HEq.trans
                      (Term.type_eq_cast_heq
                        (congrArg (fun someType => Ty.rename someType rho)
                          (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue sigma))
                        (Term.rename termRenaming (Term.subst termSubst thenBranch)))
                      (HEq.trans
                        (Term.subst_rename_commute termSubst termRenaming thenBranch)
                        (Term.type_eq_cast_heq
                          (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
                            (Subst.renameOutput sigma rho))
                          (Term.subst (TermSubst.renameOutput termSubst termRenaming)
                            thenBranch)).symm))))
                (HEq.trans
                  (Term.type_eq_cast_heq
                    (Ty.subst0_rename_commute (motiveType.subst sigma.lift) Ty.bool
                      RawTerm.boolFalse rho)
                    (Term.rename termRenaming substElse))
                  (HEq.trans
                    (Term.rename_type_eq_cast_heq termRenaming
                      (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse sigma)
                      (Term.subst termSubst elseBranch))
                    (HEq.trans
                      (Term.type_eq_cast_heq
                        (congrArg (fun someType => Ty.rename someType rho)
                          (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse sigma))
                        (Term.rename termRenaming (Term.subst termSubst elseBranch)))
                      (HEq.trans
                        (Term.subst_rename_commute termSubst termRenaming elseBranch)
                        (Term.type_eq_cast_heq
                          (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
                            (Subst.renameOutput sigma rho))
                          (Term.subst (TermSubst.renameOutput termSubst termRenaming)
                            elseBranch)).symm)))))
              (Term.type_eq_cast_heq
                (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw
                  (Subst.renameOutput sigma rho)).symm
                (Term.boolElim
                  (motiveType := motiveType.subst (Subst.renameOutput sigma rho).lift)
                  (Term.subst (TermSubst.renameOutput termSubst termRenaming) scrutinee)
                  renameOutputThen renameOutputElse)).symm)))
  -- Binder arms dispatch to the standalone fusion lemmas in
  -- `SubstRenameCommute/Binders.lean` (parallelizable; the recursion supplies the body
  -- fusion HEq).  The lifted renaming weakens by `domainType.subst sigma` (the subst-side
  -- domain), mirroring the RcS engine.
  | _, _, .lamPi (domainType := domainType) body =>
      Term.subst_rename_commute_lamPi termSubst termRenaming body
        (Term.subst_rename_commute (termSubst.lift domainType)
          (termRenaming.lift (domainType.subst sigma)) body)
  | _, _, .lam (domainType := domainType) body =>
      Term.subst_rename_commute_lam termSubst termRenaming body
        (Term.subst_rename_commute (termSubst.lift domainType)
          (termRenaming.lift (domainType.subst sigma)) body)
  | _, _, .pathLam modeIsUnivalent _ _ _ body =>
      Term.subst_rename_commute_pathLam termSubst termRenaming modeIsUnivalent body
        (Term.subst_rename_commute (termSubst.lift Ty.interval)
          (termRenaming.lift (Ty.interval.subst sigma)) body)

end LeanFX2

