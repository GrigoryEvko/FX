import LeanFX2.Term.RenameRename

/-! # LeanFX2.Term.RenameOutputLiftEntryHEq  (strength-T8 ScR binder entry lemma)

The three binder arms (`lamPi` / `lam` / `pathLam`) of the ScR engine
`Term.subst_rename_commute` push both operands under the bound variable and then
must bridge

  `TermSubst.renameOutput (termSubst.lift _) (termRenaming.lift _)`

against

  `(TermSubst.renameOutput termSubst termRenaming).lift _`.

This is the ScR mirror of `TermSubst.precomposeRenaming_lift_entry_HEq` (RcS).
Where RcS's `subst` ABSORBS the lift cast, ScR's `rename` TRANSPORTS it, so the
var(k+1) case exposes a `rename`-of-`weaken` discharged by the typed-Term
rename/weaken commute `Term.rename_weaken_commute` (itself derived from rename
functoriality `Term.rename_rename`).

Pure HEq.trans chains over the cast helpers + `rename_weaken_commute` — NO `funext`,
NO `simp`/`unfold` in a case split: axiom-clean under the strict gate. -/

namespace LeanFX2

/-- The variable-entry core of the ScR binder bridge: lifting a typed substitution
and renaming its output by the lifted renaming agrees, at every position, with the
lift of the output-renamed substitution. -/
theorem TermSubst.lift_renameOutput_entry_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho)
    (domainType : Ty level sourceScope) :
    ∀ position,
      HEq
        (Term.rename (termRenaming.lift (domainType.subst sigma))
          ((termSubst.lift domainType) position))
        (((TermSubst.renameOutput termSubst termRenaming).lift
            domainType) position)
  | ⟨0, _⟩ =>
      -- var0.  `(termSubst.lift domainType) ⟨0,_⟩` is the cast fresh variable; rename
      -- transports the weaken_subst cast, the renamed cast peels, the bare fresh var
      -- renames to the fresh var, the differing cons-head is bridged by the
      -- subst/rename-commute equation, and the RHS weaken_subst cast is re-applied.
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq
          (termRenaming.lift (domainType.subst sigma))
          (Ty.weaken_subst_commute sigma domainType)
          (targetTerm := Term.var ⟨0, Nat.zero_lt_succ _⟩))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho.lift)
              (Ty.weaken_subst_commute sigma domainType)))
          (HEq.trans
            (Term.rename_var_HEq (termRenaming.lift (domainType.subst sigma))
              ⟨0, Nat.zero_lt_succ _⟩)
            (HEq.trans
              (Term.var_zero_cons_type_eq_heq
                (Ty.subst_rename_commute sigma rho domainType))
              (Term.type_eq_symm_cast_heq
                (Ty.weaken_subst_commute (Subst.renameOutput sigma rho) domainType)).symm)))
  | ⟨k + 1, h⟩ =>
      -- var(k+1).  `(termSubst.lift domainType) ⟨k+1,_⟩` is the cast weakening of
      -- `termSubst ⟨k,_⟩`.  rename transports the weaken_subst cast, the renamed cast
      -- peels, `rename_weaken_commute` turns `rename (tr.lift) (weaken X _)` into
      -- `weaken (X.rename rho) (rename tr _)`, the renamed entry bridges to the
      -- renameOutput entry, the weaken head type aligns via subst/rename-commute, and
      -- the RHS weaken_subst cast is re-applied.
      HEq.trans
        (Term.rename_type_eq_symm_cast_heq
          (termRenaming.lift (domainType.subst sigma))
          (Ty.weaken_subst_commute sigma
            (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))
          (targetTerm := Term.weaken (domainType.subst sigma)
            (termSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩)))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (congrArg (fun someType => Ty.rename someType rho.lift)
              (Ty.weaken_subst_commute sigma
                (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))))
          (HEq.trans
            (Term.rename_weaken_commute termRenaming (domainType.subst sigma)
              (termSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩))
            (HEq.trans
              (Term.weaken_head_type_eq_heq
                (Ty.subst_rename_commute sigma rho domainType)
                (Term.rename termRenaming
                  (termSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩)))
              (HEq.trans
                (Term.weaken_heq_of_eq
                  (domainType.subst (Subst.renameOutput sigma rho))
                  (Ty.subst_rename_commute sigma rho
                    (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))
                  rfl
                  (TermSubst.renameOutput_position_HEq termSubst termRenaming
                    ⟨k, Nat.lt_of_succ_lt_succ h⟩).symm)
                (Term.type_eq_symm_cast_heq
                  (Ty.weaken_subst_commute (Subst.renameOutput sigma rho)
                    (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))).symm))))

/-- Full binder entry equality consumed by the `lam` / `lamPi` / `pathLam` arms of
the ScR engine `Term.subst_rename_commute`: the renameOutput of the lifts equals the
lift of the renameOutput, heterogeneously, at every position. -/
theorem TermSubst.renameOutput_lift_entry_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho)
    (domainType : Ty level sourceScope)
    (position : Fin (sourceScope + 1)) :
    HEq
      ((TermSubst.renameOutput (termSubst.lift domainType)
          (termRenaming.lift (domainType.subst sigma))) position)
      (((TermSubst.renameOutput termSubst termRenaming).lift
          domainType) position) :=
  HEq.trans
    (TermSubst.renameOutput_position_HEq (termSubst.lift domainType)
      (termRenaming.lift (domainType.subst sigma)) position)
    (TermSubst.lift_renameOutput_entry_HEq termSubst termRenaming domainType
      position)

end LeanFX2

