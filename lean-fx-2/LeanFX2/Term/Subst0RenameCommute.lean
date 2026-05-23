import LeanFX2.Term.SubstRenameCommute
import LeanFX2.Term.RenameSubstCommute
import LeanFX2.Term.SubstPointwiseHEq

/-! # LeanFX2.Term.Subst0RenameCommute  (strength-T8 headline, #1964)

The two-engine T8 corollary: single-variable substitution commutes with renaming.

  rename ρ (subst0 body arg)  ≅  subst0 (rename ρ.lift body) (rename ρ arg)

This is the typed-Term mirror of `Ty.subst0_rename_commute`.  `subst0 b a =
subst (singleton a) b`, so each side reduces to a `subst`; the ScR engine
`Term.subst_rename_commute` fires on the LHS (rename of subst), the RcS engine
`Term.rename_subst_commute` fires on the RHS (subst of rename), and the residual is
the pointwise equality of the two singleton-derived substitutions
(`renameOutput (singleton arg) ρ` vs `precomposeRenaming ρ.lift (singleton (rename ρ
arg))`) — pure singleton / lift / weaken Fin arithmetic, NO term induction.

Zero-axiom: the entry bridge factors through `renameOutput_position_HEq` /
`precomposeRenaming_position_HEq` and the singleton cast helpers; the body bridge is
`Term.subst_pointwise_HEq` over the two pointwise-equal singleton substitutions. -/

namespace LeanFX2

/-- Per-position bridge for the residual singleton equality.  Renaming the singleton
substitution entry agrees with the renamed-argument singleton entry under the lift,
heterogeneously.  Position 0 hits the (renamed) argument; position k+1 hits the
(renamed) variable.  Pure cast peeling + `rename_var_HEq`. -/
theorem Term.singleton_renameOutput_lift_entry_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {substituent : Ty level sourceScope} {argRaw : RawTerm sourceScope}
    (argTerm : Term sourceCtx substituent argRaw) :
    ∀ position,
      HEq
        (Term.rename termRenaming ((TermSubst.singleton argTerm) position))
        ((TermSubst.singleton (Term.rename termRenaming argTerm)) (rho.lift position))
  | ⟨0, _⟩ =>
      -- Both entries are the (renamed) argument up to the `weaken_subst_singleton` cast.
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq termRenaming
          (Ty.weaken_subst_singleton substituent substituent argRaw)
          (targetTerm := argTerm))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho)
              (Ty.weaken_subst_singleton substituent substituent argRaw)))
          (Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_singleton (substituent.rename rho)
              (substituent.rename rho) (argRaw.rename rho))).symm)
  | ⟨k + 1, h⟩ =>
      -- Both entries are the (renamed) variable `var k` up to the cast.
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq termRenaming
          (Ty.weaken_subst_singleton (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)
            substituent argRaw)
          (targetTerm := Term.var ⟨k, Nat.lt_of_succ_lt_succ h⟩))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho)
              (Ty.weaken_subst_singleton (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)
                substituent argRaw)))
          (HEq.trans
            (Term.rename_var_HEq termRenaming ⟨k, Nat.lt_of_succ_lt_succ h⟩)
            (Term.type_eq_symm_cast_heq
              (Ty.weaken_subst_singleton
                (varType targetCtx (rho ⟨k, Nat.lt_of_succ_lt_succ h⟩))
                (substituent.rename rho) (argRaw.rename rho))).symm))

/-- The two singleton-derived typed substitutions agree heterogeneously on every
position: renaming-the-output of the singleton equals precomposing the lifted renaming
with the renamed-argument singleton.  Factors through the renameOutput / precompose
position bridges + the singleton entry HEq. -/
theorem Term.singleton_renameOutput_precompose_entry_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {substituent : Ty level sourceScope} {argRaw : RawTerm sourceScope}
    (argTerm : Term sourceCtx substituent argRaw)
    (position : Fin (sourceScope + 1)) :
    HEq
      ((TermSubst.renameOutput (TermSubst.singleton argTerm) termRenaming) position)
      ((TermSubst.precomposeRenaming (termRenaming.lift substituent)
          (TermSubst.singleton (Term.rename termRenaming argTerm))) position) :=
  HEq.trans
    (TermSubst.renameOutput_position_HEq (TermSubst.singleton argTerm) termRenaming
      position)
    (HEq.trans
      (Term.singleton_renameOutput_lift_entry_HEq termRenaming argTerm position)
      (TermSubst.precomposeRenaming_position_HEq (termRenaming.lift substituent)
        (TermSubst.singleton (Term.rename termRenaming argTerm)) position).symm)

/-- **T8** (#1964): single-variable substitution commutes with renaming.

  rename ρ (subst0 body arg) ≅ subst0 (rename ρ.lift body) (rename ρ arg)

Two-engine corollary: ScR (`Term.subst_rename_commute`) on the LHS, RcS
(`Term.rename_subst_commute`) on the RHS, joined by the singleton pointwise bridge. -/
theorem Term.subst0_rename_commute
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {substituent : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {argRaw : RawTerm sourceScope} {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyTerm : Term (sourceCtx.cons substituent) codomainType bodyRaw)
    (argTerm : Term sourceCtx substituent argRaw) :
    HEq (Term.rename termRenaming (Term.subst0 bodyTerm argTerm))
        (Term.subst0
          (Term.rename (termRenaming.lift substituent) bodyTerm)
          (Term.rename termRenaming argTerm)) :=
  -- LHS = subst (singleton arg) body, renamed: ScR engine.
  -- RHS = subst0 (rename body) (rename arg) = subst (singleton (rename arg)) (rename body):
  --   RcS engine.  The two intermediate `subst _ body` agree by the singleton pointwise
  --   bridge over `renameOutput (singleton arg) ρ` ≈ `precompose ρ.lift (singleton (rename arg))`.
  HEq.trans
    (Term.subst_rename_commute (TermSubst.singleton argTerm) termRenaming bodyTerm)
    (HEq.trans
      (Term.subst_pointwise_HEq
        (Subst.singleton_rename_commute_forTy_pointwise substituent argRaw rho)
        (Subst.singleton_rename_commute_forRaw_pointwise substituent argRaw rho)
        (Term.singleton_renameOutput_precompose_entry_HEq termRenaming argTerm)
        bodyTerm)
      (Term.rename_subst_commute (termRenaming.lift substituent)
        (TermSubst.singleton (Term.rename termRenaming argTerm)) bodyTerm).symm)

end LeanFX2

