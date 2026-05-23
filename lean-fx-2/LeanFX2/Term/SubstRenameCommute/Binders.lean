import LeanFX2.Term.SubstRenameCommute.Support
import LeanFX2.Term.RenameOutputLiftEntryHEq

/-! # LeanFX2.Term.SubstRenameCommute.Binders  (strength-T8 ScR dispatcher arms)

Standalone per-constructor subst/rename fusion lemmas for the three binder
constructors (`lamPi` / `lam` / `pathLam`) of the ScR engine
`Term.subst_rename_commute`.  Each takes the body's fusion HEq as an explicit
hypothesis (`bodyFusion`) rather than recursing, so this file does NOT depend on the
recursive driver and elaborates in parallel with the other arm families under
`lake -j`.  The mirror of `RenameSubstCommute/Binders.lean` (RcS).

The dispatcher driver supplies `bodyFusion` by recursing
(`Term.subst_rename_commute (termSubst.lift _) (termRenaming.lift _) body`) and
routes the binder arms here.

Shared shape (all three): the body fusion lands at
`renameOutput (σ.lift)(ρ.lift)`; `Term.subst_pointwise_HEq` realigns it to
`(renameOutput σ ρ).lift` across the divergent target contexts, with the entry HEq
from `renameOutput_lift_entry_HEq` + `targetCtx_cast_entry_HEq` and the context cast
peeled by `subst_targetCtx_cast_HEq`.  `lam` / `pathLam` add the outer
`weaken_subst_commute` (subst side) / `weaken_rename_commute` (rename transport) cast
peel (codomain at base scope); `pathLam` binds the closed `Ty.interval`. -/

namespace LeanFX2

/-- Dependent Π-lambda fusion arm (ScR). -/
theorem Term.subst_rename_commute_lamPi
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (bodyFusion :
      HEq (Term.rename (termRenaming.lift (domainType.subst sigma))
              (Term.subst (termSubst.lift domainType) body))
          (Term.subst (TermSubst.renameOutput (termSubst.lift domainType)
              (termRenaming.lift (domainType.subst sigma))) body)) :
    HEq (Term.rename termRenaming (Term.subst termSubst (Term.lamPi body)))
        (Term.subst (TermSubst.renameOutput termSubst termRenaming)
          (Term.lamPi body)) :=
  let domainEqTy := Ty.subst_rename_commute sigma rho domainType
  let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEqTy.symm
  let secondTermSubst :=
    (TermSubst.renameOutput termSubst termRenaming).lift domainType
  let entryHEqAligned := fun position =>
    HEq.trans
      (TermSubst.renameOutput_lift_entry_HEq termSubst termRenaming
        domainType position)
      (TermSubst.targetCtx_cast_entry_HEq targetCtxEq secondTermSubst
        position).symm
  Term.lamPi_HEq_congr
    domainEqTy
    (Ty.subst_rename_commute_lift sigma rho codomainType)
    (RawTerm.subst_rename_commute_lift sigma rho bodyRaw)
    (HEq.trans
      bodyFusion
      (HEq.trans
        (Term.subst_pointwise_HEq
          (Subst.renameOutput_lift_forTy_pointwise sigma rho)
          (Subst.renameOutput_lift_forRaw_pointwise sigma rho)
          entryHEqAligned body)
        (Term.subst_targetCtx_cast_HEq targetCtxEq secondTermSubst body)))

/-- Non-dependent arrow-lambda fusion arm (ScR). -/
theorem Term.subst_rename_commute_lam
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw)
    (bodyFusion :
      HEq (Term.rename (termRenaming.lift (domainType.subst sigma))
              (Term.subst (termSubst.lift domainType) body))
          (Term.subst (TermSubst.renameOutput (termSubst.lift domainType)
              (termRenaming.lift (domainType.subst sigma))) body)) :
    HEq (Term.rename termRenaming (Term.subst termSubst (Term.lam body)))
        (Term.subst (TermSubst.renameOutput termSubst termRenaming)
          (Term.lam body)) :=
  let domainEqTy := Ty.subst_rename_commute sigma rho domainType
  let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEqTy.symm
  let secondTermSubst :=
    (TermSubst.renameOutput termSubst termRenaming).lift domainType
  let entryHEqAligned := fun position =>
    HEq.trans
      (TermSubst.renameOutput_lift_entry_HEq termSubst termRenaming
        domainType position)
      (TermSubst.targetCtx_cast_entry_HEq targetCtxEq secondTermSubst
        position).symm
  Term.lam_HEq_congr
    domainEqTy
    (Ty.subst_rename_commute sigma rho codomainType)
    (RawTerm.subst_rename_commute_lift sigma rho bodyRaw)
    (HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_rename_commute rho (codomainType.subst sigma))
        (Term.rename (termRenaming.lift (domainType.subst sigma))
          (Ty.weaken_subst_commute sigma codomainType ▸
            Term.subst (termSubst.lift domainType) body)))
      (HEq.trans
        (Term.rename_type_eq_cast_heq (termRenaming.lift (domainType.subst sigma))
          (Ty.weaken_subst_commute sigma codomainType)
          (Term.subst (termSubst.lift domainType) body))
        (HEq.trans
          (Term.type_eq_cast_heq
            (congrArg (fun someType => Ty.rename someType rho.lift)
              (Ty.weaken_subst_commute sigma codomainType))
            (Term.rename (termRenaming.lift (domainType.subst sigma))
              (Term.subst (termSubst.lift domainType) body)))
          (HEq.trans
            bodyFusion
            (HEq.trans
              (Term.subst_pointwise_HEq
                (Subst.renameOutput_lift_forTy_pointwise sigma rho)
                (Subst.renameOutput_lift_forRaw_pointwise sigma rho)
                entryHEqAligned body)
              (HEq.trans
                (Term.subst_targetCtx_cast_HEq targetCtxEq secondTermSubst body)
                (Term.type_eq_cast_heq
                  (Ty.weaken_subst_commute (Subst.renameOutput sigma rho) codomainType)
                  (Term.subst secondTermSubst body)).symm))))))

/-- Path-lambda fusion arm (ScR).  Binds the closed type `Ty.interval`. -/
theorem Term.subst_rename_commute_pathLam
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyFusion :
      HEq (Term.rename (termRenaming.lift (Ty.interval.subst sigma))
              (Term.subst (termSubst.lift Ty.interval) body))
          (Term.subst (TermSubst.renameOutput (termSubst.lift Ty.interval)
              (termRenaming.lift (Ty.interval.subst sigma))) body)) :
    HEq (Term.rename termRenaming
          (Term.subst termSubst
            (Term.pathLam modeIsUnivalent carrierType leftEndpoint
              rightEndpoint body)))
        (Term.subst (TermSubst.renameOutput termSubst termRenaming)
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint
            rightEndpoint body)) :=
  let domainEqTy := Ty.subst_rename_commute sigma rho Ty.interval
  let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEqTy.symm
  let secondTermSubst :=
    (TermSubst.renameOutput termSubst termRenaming).lift Ty.interval
  let entryHEqAligned := fun position =>
    HEq.trans
      (TermSubst.renameOutput_lift_entry_HEq termSubst termRenaming
        Ty.interval position)
      (TermSubst.targetCtx_cast_entry_HEq targetCtxEq secondTermSubst
        position).symm
  Term.pathLam_HEq_congr
    modeIsUnivalent
    (Ty.subst_rename_commute sigma rho carrierType)
    (RawTerm.subst_rename_commute sigma.forRaw rho leftEndpoint)
    (RawTerm.subst_rename_commute sigma.forRaw rho rightEndpoint)
    (RawTerm.subst_rename_commute_lift sigma rho bodyRaw)
    (HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_rename_commute rho (carrierType.subst sigma))
        (Term.rename (termRenaming.lift (Ty.interval.subst sigma))
          (Ty.weaken_subst_commute sigma carrierType ▸
            Term.subst (termSubst.lift Ty.interval) body)))
      (HEq.trans
        (Term.rename_type_eq_cast_heq (termRenaming.lift (Ty.interval.subst sigma))
          (Ty.weaken_subst_commute sigma carrierType)
          (Term.subst (termSubst.lift Ty.interval) body))
        (HEq.trans
          (Term.type_eq_cast_heq
            (congrArg (fun someType => Ty.rename someType rho.lift)
              (Ty.weaken_subst_commute sigma carrierType))
            (Term.rename (termRenaming.lift (Ty.interval.subst sigma))
              (Term.subst (termSubst.lift Ty.interval) body)))
          (HEq.trans
            bodyFusion
            (HEq.trans
              (Term.subst_pointwise_HEq
                (Subst.renameOutput_lift_forTy_pointwise sigma rho)
                (Subst.renameOutput_lift_forRaw_pointwise sigma rho)
                entryHEqAligned body)
              (HEq.trans
                (Term.subst_targetCtx_cast_HEq targetCtxEq secondTermSubst body)
                (Term.type_eq_cast_heq
                  (Ty.weaken_subst_commute (Subst.renameOutput sigma rho) carrierType)
                  (Term.subst secondTermSubst body)).symm))))))

end LeanFX2
