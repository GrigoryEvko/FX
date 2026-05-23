import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose
import LeanFX2.Term.SubstPointwiseHEq
import LeanFX2.Term.SubstTargetCtxCast

/-! # LeanFX2.Term.SubstRenameCommute.Support  (strength-T8 ScR-mirror support)

Shared lifted-index fusion helpers for the ScR engine `Term.subst_rename_commute`
(subst-then-rename), the mirror of the RcS engine `Term.rename_subst_commute`.
Where RcS factors through `Subst.precomposeRenaming`, ScR factors through
`Subst.renameOutput` (rename each substitution entry's output).

All zero-axiom: each is a `.trans` of `Ty`/`RawTerm.subst_rename_commute` with a
`renameOutput`-lift pointwise realignment, or a per-field signature congruence. -/

namespace LeanFX2

/-- Lifted-binder type fusion (ScR): substituting-then-renaming a `scope+1` type
under lifted actions equals substituting by the renameOutput composite's lift.
Bridges the codomain index of the `lamPi` arm. -/
theorem Ty.subst_rename_commute_lift {level scope middleScope targetScope : Nat}
    (sigma : Subst level scope middleScope) (rho : RawRenaming middleScope targetScope)
    (someType : Ty level (scope + 1)) :
    (someType.subst sigma.lift).rename rho.lift =
      someType.subst (Subst.renameOutput sigma rho).lift :=
  (Ty.subst_rename_commute sigma.lift rho.lift someType).trans
    (Ty.subst_pointwise
      (Subst.renameOutput_lift_forTy_pointwise sigma rho)
      (Subst.renameOutput_lift_forRaw_pointwise sigma rho) someType)

/-- Lifted-binder raw fusion (ScR): the raw-substitution analogue of
`Ty.subst_rename_commute_lift`, bridging every binder arm's body raw index. -/
theorem RawTerm.subst_rename_commute_lift {level scope middleScope targetScope : Nat}
    (sigma : Subst level scope middleScope) (rho : RawRenaming middleScope targetScope)
    (raw : RawTerm (scope + 1)) :
    (raw.subst sigma.lift.forRaw).rename rho.lift =
      raw.subst (Subst.renameOutput sigma rho).lift.forRaw :=
  (RawTerm.subst_rename_commute sigma.lift.forRaw rho.lift raw).trans
    (RawTerm.subst_pointwise
      (Subst.renameOutput_lift_forRaw_pointwise sigma rho) raw)

/-- Signature-level subst/rename fusion (ScR): mapping an operation signature's
carriers by `subst σ` then `rename ρ` equals mapping by `subst (renameOutput σ ρ)`.
The `effectPerform` arm's signature index is transformed exactly this way. -/
theorem Effects.OperationSignature.map_subst_rename_commute
    {level scope middleScope targetScope : Nat}
    (sigma : Subst level scope middleScope)
    (rho : RawRenaming middleScope targetScope)
    (operation : Effects.OperationSignature (Ty level scope)) :
    (operation.map (fun carrierType => carrierType.subst sigma)).map
        (fun carrierType => carrierType.rename rho)
      = operation.map
          (fun carrierType => carrierType.subst (Subst.renameOutput sigma rho)) := by
  show Effects.OperationSignature.mk operation.effectLabel
        ((operation.argumentCarrier.subst sigma).rename rho)
        ((operation.resultCarrier.subst sigma).rename rho)
      = Effects.OperationSignature.mk operation.effectLabel
        (operation.argumentCarrier.subst (Subst.renameOutput sigma rho))
        (operation.resultCarrier.subst (Subst.renameOutput sigma rho))
  rw [Ty.subst_rename_commute sigma rho operation.argumentCarrier,
      Ty.subst_rename_commute sigma rho operation.resultCarrier]

end LeanFX2
