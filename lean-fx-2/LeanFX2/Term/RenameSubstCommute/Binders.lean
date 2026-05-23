import LeanFX2.Term.RenameSubstCommute.Support

/-! # LeanFX2.Term.RenameSubstCommute.Binders  (strength-T8 dispatcher arms)

Standalone per-constructor rename/subst fusion lemmas for the three binder
constructors (`lamPi` / `lam` / `pathLam`).  Each takes the body's fusion HEq as
an explicit hypothesis (`bodyFusion`) rather than recursing, so this file does
NOT depend on the recursive driver `Term.rename_subst_commute` and elaborates in
parallel with the other arm families under `lake -j`.

The dispatcher driver supplies `bodyFusion` by recursing
(`Term.rename_subst_commute (termRenaming.lift _) (termSubst.lift _) body`) and
routes the binder arms here.

Shared shape (all three): the body fusion lands at
`precompose (ρ.lift)(σ.lift)`; `Term.subst_pointwise_HEq` realigns it to
`(precompose ρ σ).lift` across the divergent target contexts, with the entry HEq
from `precomposeRenaming_lift_entry_HEq` + `targetCtx_cast_entry_HEq` and the
context cast peeled by `subst_targetCtx_cast_HEq`.  `lam` / `pathLam` add the
outer `weaken` cast peel (codomain at base scope); `pathLam` binds the closed
`Ty.interval` so the two target contexts coincide definitionally. -/

namespace LeanFX2

/-- Dependent Π-lambda fusion arm. -/
theorem Term.rename_subst_commute_lamPi
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (bodyFusion :
      HEq (Term.subst (termSubst.lift (domainType.rename rho))
              (Term.rename (termRenaming.lift domainType) body))
          (Term.subst (TermSubst.precomposeRenaming (termRenaming.lift domainType)
              (termSubst.lift (domainType.rename rho))) body)) :
    HEq (Term.subst termSubst (Term.rename termRenaming (Term.lamPi body)))
        (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
          (Term.lamPi body)) :=
  let domainEqTy := Ty.rename_subst_commute rho sigma domainType
  let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEqTy.symm
  let secondTermSubst :=
    (TermSubst.precomposeRenaming termRenaming termSubst).lift domainType
  let entryHEqAligned := fun position =>
    HEq.trans
      (TermSubst.precomposeRenaming_lift_entry_HEq termRenaming termSubst
        domainType position)
      (TermSubst.targetCtx_cast_entry_HEq targetCtxEq secondTermSubst
        position).symm
  Term.lamPi_HEq_congr
    domainEqTy
    (Ty.rename_subst_commute_lift rho sigma codomainType)
    (RawTerm.rename_subst_commute_lift rho sigma bodyRaw)
    (HEq.trans
      bodyFusion
      (HEq.trans
        (Term.subst_pointwise_HEq
          (Subst.precomposeRenaming_lift_forTy_pointwise rho sigma)
          (Subst.precomposeRenaming_lift_forRaw_pointwise rho sigma)
          entryHEqAligned body)
        (Term.subst_targetCtx_cast_HEq targetCtxEq secondTermSubst body)))

/-- Non-dependent arrow-lambda fusion arm. -/
theorem Term.rename_subst_commute_lam
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma)
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw)
    (bodyFusion :
      HEq (Term.subst (termSubst.lift (domainType.rename rho))
              (Term.rename (termRenaming.lift domainType) body))
          (Term.subst (TermSubst.precomposeRenaming (termRenaming.lift domainType)
              (termSubst.lift (domainType.rename rho))) body)) :
    HEq (Term.subst termSubst (Term.rename termRenaming (Term.lam body)))
        (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
          (Term.lam body)) :=
  let domainEqTy := Ty.rename_subst_commute rho sigma domainType
  let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEqTy.symm
  let secondTermSubst :=
    (TermSubst.precomposeRenaming termRenaming termSubst).lift domainType
  let entryHEqAligned := fun position =>
    HEq.trans
      (TermSubst.precomposeRenaming_lift_entry_HEq termRenaming termSubst
        domainType position)
      (TermSubst.targetCtx_cast_entry_HEq targetCtxEq secondTermSubst
        position).symm
  Term.lam_HEq_congr
    domainEqTy
    (Ty.rename_subst_commute rho sigma codomainType)
    (RawTerm.rename_subst_commute_lift rho sigma bodyRaw)
    (HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute sigma (codomainType.rename rho))
        (Term.subst (termSubst.lift (domainType.rename rho))
          (Ty.weaken_rename_commute rho codomainType ▸
            Term.rename (termRenaming.lift domainType) body)))
      (HEq.trans
        (Term.subst_type_eq_cast_heq (termSubst.lift (domainType.rename rho))
          (Ty.weaken_rename_commute rho codomainType)
          (Term.rename (termRenaming.lift domainType) body))
        (HEq.trans
          bodyFusion
          (HEq.trans
            (Term.subst_pointwise_HEq
              (Subst.precomposeRenaming_lift_forTy_pointwise rho sigma)
              (Subst.precomposeRenaming_lift_forRaw_pointwise rho sigma)
              entryHEqAligned body)
            (HEq.trans
              (Term.subst_targetCtx_cast_HEq targetCtxEq secondTermSubst body)
              (Term.type_eq_cast_heq
                (Ty.weaken_subst_commute (Subst.precomposeRenaming rho sigma)
                  codomainType)
                (Term.subst
                  ((TermSubst.precomposeRenaming termRenaming termSubst).lift
                    domainType)
                  body)).symm)))))

/-- Path-lambda fusion arm.  Binds the closed type `Ty.interval`. -/
theorem Term.rename_subst_commute_pathLam
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyFusion :
      HEq (Term.subst (termSubst.lift Ty.interval)
              (Term.rename (termRenaming.lift Ty.interval) body))
          (Term.subst (TermSubst.precomposeRenaming (termRenaming.lift Ty.interval)
              (termSubst.lift Ty.interval)) body)) :
    HEq (Term.subst termSubst
          (Term.rename termRenaming
            (Term.pathLam modeIsUnivalent carrierType leftEndpoint
              rightEndpoint body)))
        (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint
            rightEndpoint body)) :=
  let domainEqTy := Ty.rename_subst_commute rho sigma Ty.interval
  let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEqTy.symm
  let secondTermSubst :=
    (TermSubst.precomposeRenaming termRenaming termSubst).lift Ty.interval
  let entryHEqAligned := fun position =>
    HEq.trans
      (TermSubst.precomposeRenaming_lift_entry_HEq termRenaming termSubst
        Ty.interval position)
      (TermSubst.targetCtx_cast_entry_HEq targetCtxEq secondTermSubst
        position).symm
  Term.pathLam_HEq_congr
    modeIsUnivalent
    (Ty.rename_subst_commute rho sigma carrierType)
    (RawTerm.rename_subst_commute rho sigma.forRaw leftEndpoint)
    (RawTerm.rename_subst_commute rho sigma.forRaw rightEndpoint)
    (RawTerm.rename_subst_commute_lift rho sigma bodyRaw)
    (HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute sigma (carrierType.rename rho))
        (Term.subst (termSubst.lift Ty.interval)
          (Ty.weaken_rename_commute rho carrierType ▸
            Term.rename (termRenaming.lift Ty.interval) body)))
      (HEq.trans
        (Term.subst_type_eq_cast_heq (termSubst.lift Ty.interval)
          (Ty.weaken_rename_commute rho carrierType)
          (Term.rename (termRenaming.lift Ty.interval) body))
        (HEq.trans
          bodyFusion
          (HEq.trans
            (Term.subst_pointwise_HEq
              (Subst.precomposeRenaming_lift_forTy_pointwise rho sigma)
              (Subst.precomposeRenaming_lift_forRaw_pointwise rho sigma)
              entryHEqAligned body)
            (HEq.trans
              (Term.subst_targetCtx_cast_HEq targetCtxEq secondTermSubst body)
              (Term.type_eq_cast_heq
                (Ty.weaken_subst_commute (Subst.precomposeRenaming rho sigma)
                  carrierType)
                (Term.subst
                  ((TermSubst.precomposeRenaming termRenaming termSubst).lift
                    Ty.interval)
                  body)).symm)))))

end LeanFX2
