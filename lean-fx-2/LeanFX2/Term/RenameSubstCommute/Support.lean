import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose
import LeanFX2.Term.PrecomposeLiftEntryHEq
import LeanFX2.Term.SubstPointwiseHEq
import LeanFX2.Term.SubstTargetCtxCast

/-! # LeanFX2.Term.RenameSubstCommute.Support  (strength-T8 dispatcher support)

Shared lifted-index fusion helpers consumed by both the per-constructor arm
files (`RenameSubstCommute/Binders.lean`, …) and the dispatcher driver
(`RenameSubstCommute.lean`).  Factored out so the arm files do not import the
driver (which would cycle) and so each arm file parallelizes against the others
under `lake -j`.

All zero-axiom: each is a `.trans` of `Ty`/`RawTerm.rename_subst_commute` with a
pointwise realignment, or a per-field signature congruence. -/

namespace LeanFX2

/-- Lifted-binder type fusion: renaming-then-substituting a `scope+1` type under
lifted actions equals substituting by the precomposition's lift.  Bridges the
codomain index of the `lamPi` arm. -/
theorem Ty.rename_subst_commute_lift {level scope middleScope targetScope : Nat}
    (rho : RawRenaming scope middleScope) (sigma : Subst level middleScope targetScope)
    (someType : Ty level (scope + 1)) :
    (someType.rename rho.lift).subst sigma.lift =
      someType.subst (Subst.precomposeRenaming rho sigma).lift :=
  (Ty.rename_subst_commute rho.lift sigma.lift someType).trans
    (Ty.subst_pointwise
      (Subst.precomposeRenaming_lift_forTy_pointwise rho sigma)
      (Subst.precomposeRenaming_lift_forRaw_pointwise rho sigma) someType)

/-- Lifted-binder raw fusion: the raw-substitution analogue of
`Ty.rename_subst_commute_lift`, bridging every binder arm's body raw index. -/
theorem RawTerm.rename_subst_commute_lift {level scope middleScope targetScope : Nat}
    (rho : RawRenaming scope middleScope) (sigma : Subst level middleScope targetScope)
    (raw : RawTerm (scope + 1)) :
    (raw.rename rho.lift).subst sigma.lift.forRaw =
      raw.subst (Subst.precomposeRenaming rho sigma).lift.forRaw :=
  (RawTerm.rename_subst_commute rho.lift sigma.lift.forRaw raw).trans
    (RawTerm.subst_pointwise
      (Subst.precomposeRenaming_lift_forRaw_pointwise rho sigma) raw)

/-- Signature-level rename/subst fusion: mapping an operation signature's carriers
by `rename ρ` then `subst σ` equals mapping by `subst (precomposeRenaming ρ σ)`.
The `effectPerform` arm's signature index is transformed exactly this way.  Pure
per-field congruence over the two carrier `Ty` fields — no funext. -/
theorem Effects.OperationSignature.map_rename_subst_commute
    {level scope middleScope targetScope : Nat}
    (rho : RawRenaming scope middleScope)
    (sigma : Subst level middleScope targetScope)
    (operation : Effects.OperationSignature (Ty level scope)) :
    (operation.map (fun carrierType => carrierType.rename rho)).map
        (fun carrierType => carrierType.subst sigma)
      = operation.map
          (fun carrierType =>
            carrierType.subst (Subst.precomposeRenaming rho sigma)) := by
  show Effects.OperationSignature.mk operation.effectLabel
        ((operation.argumentCarrier.rename rho).subst sigma)
        ((operation.resultCarrier.rename rho).subst sigma)
      = Effects.OperationSignature.mk operation.effectLabel
        (operation.argumentCarrier.subst (Subst.precomposeRenaming rho sigma))
        (operation.resultCarrier.subst (Subst.precomposeRenaming rho sigma))
  rw [Ty.rename_subst_commute rho sigma operation.argumentCarrier,
      Ty.rename_subst_commute rho sigma operation.resultCarrier]

end LeanFX2
