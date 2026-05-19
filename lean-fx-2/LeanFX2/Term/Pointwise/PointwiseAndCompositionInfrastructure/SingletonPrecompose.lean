import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq

/-! # LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose

Semantic slice of typed pointwise substitution and composition infrastructure. -/

namespace LeanFX2

theorem Term.rename_var_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (position : Fin sourceScope) :
    HEq (Term.rename termRenaming (Term.var position))
      (Term.var (context := targetCtx) (rho position)) := by
  simp only [Term.rename]
  exact Term.type_eq_cast_heq
    (typeEq := termRenaming position)
    (sourceTerm := Term.var (context := targetCtx) (rho position))

/-- The cast in `TermSubst.renameOutput` changes only the type index.

This packages the exact `Ty.subst_rename_commute` transport used by
`TermSubst.renameOutput`, so downstream binder-stability proofs can
reason about the renamed substitution entry without unfolding the
definition at every position. -/
theorem TermSubst.renameOutput_position_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho)
    (position : Fin sourceScope) :
    HEq (TermSubst.renameOutput termSubst termRenaming position)
      (Term.rename termRenaming (termSubst position)) := by
  change HEq
    (Ty.subst_rename_commute sigma rho (varType sourceCtx position) ▸
      Term.rename termRenaming (termSubst position))
    (Term.rename termRenaming (termSubst position))
  exact Term.type_eq_cast_heq
    (Ty.subst_rename_commute sigma rho (varType sourceCtx position))
    (Term.rename termRenaming (termSubst position))

/-- The cast in `TermSubst.precomposeRenaming` changes only the type
index.

This is the input-side companion to `TermSubst.renameOutput_position_HEq`:
the raw substituted entry is exactly `termSubst (rho position)`, while
the type index is transported through `Ty.rename_subst_commute` and the
typed renaming lookup equation. -/
theorem TermSubst.precomposeRenaming_position_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma)
    (position : Fin sourceScope) :
    HEq (TermSubst.precomposeRenaming termRenaming termSubst position)
      (termSubst (rho position)) := by
  unfold TermSubst.precomposeRenaming
  exact Term.type_eq_cast_heq
    (by
      show (varType middleCtx (rho position)).subst sigma =
        (varType sourceCtx position).subst
          (Subst.precomposeRenaming rho sigma)
      rw [termRenaming position]
      exact Ty.rename_subst_commute rho sigma
        (varType sourceCtx position))
    (termSubst (rho position))

/-- The underlying type-substitution component of weakening followed
by singleton substitution is pointwise identity. -/
theorem Subst.precompose_weaken_singleton_forTy_pointwise
    {level scope : Nat}
    (newType : Ty level scope)
    (singletonRaw : RawTerm scope) :
    ∀ position,
      (Subst.precomposeRenaming RawRenaming.weaken
        (Subst.singleton newType singletonRaw)).forTy position =
        (@Subst.identity level scope).forTy position
  | ⟨_, _⟩ => rfl

/-- The underlying raw-substitution component of weakening followed
by singleton substitution is pointwise identity. -/
theorem Subst.precompose_weaken_singleton_forRaw_pointwise
    {level scope : Nat}
    (newType : Ty level scope)
    (singletonRaw : RawTerm scope) :
    ∀ position,
      (Subst.precomposeRenaming RawRenaming.weaken
        (Subst.singleton newType singletonRaw)).forRaw position =
        (@Subst.identity level scope).forRaw position
  | ⟨_, _⟩ => rfl

/-- Precomposing weakening with singleton substitution is entrywise the
identity typed substitution.

This is the depth-zero counterpart of
`TermSubst.precompose_lift_weaken_singleton_lift_position_HEq`; together
they are the variable-entry base cases for the general cancel theorem
needed by the M04 lambda route. -/
theorem TermSubst.precompose_weaken_singleton_position_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (position : Fin scope) :
    HEq
      (TermSubst.precomposeRenaming
        (TermRenaming.weakenStep context newType)
        (TermSubst.singleton singletonTerm)
        position)
      (TermSubst.identity context position) := by
  apply HEq.trans
  · exact TermSubst.precomposeRenaming_position_HEq
      (TermRenaming.weakenStep context newType)
      (TermSubst.singleton singletonTerm)
      position
  · rcases position with ⟨positionIndex, positionIsWithinScope⟩
    simp only [RawRenaming.weaken, TermSubst.singleton, TermSubst.identity]
    exact HEq.trans
      (Term.type_eq_symm_cast_heq
        (Ty.weaken_subst_singleton
          (varType context ⟨positionIndex, positionIsWithinScope⟩)
          newType singletonRaw))
      (HEq.symm
        (Term.type_eq_symm_cast_heq
          (context := context)
          (typeEq := Ty.subst_identity
            (varType context ⟨positionIndex, positionIsWithinScope⟩))
          (targetTerm := Term.var
            (context := context)
            ⟨positionIndex, positionIsWithinScope⟩)))

/-- Precomposing weakening with singleton substitution is pointwise the
identity typed substitution.

The underlying `Subst` is definitionally `Subst.identity`; this theorem
turns the entrywise HEq alignment into the ordinary equality consumed by
`Term.subst_pointwise`. -/
theorem TermSubst.precompose_weaken_singleton_pointwise
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    ∀ position,
      TermSubst.precomposeRenaming
        (TermRenaming.weakenStep context newType)
        (TermSubst.singleton singletonTerm)
        position =
      TermSubst.identity context position := by
  intro position
  exact eq_of_heq
    (TermSubst.precompose_weaken_singleton_position_HEq
      singletonTerm position)

/-- Substituting by the weakening/singleton precomposition agrees with
identity substitution on every term.

This is the reusable substitution-level half of the old-entry collapse
needed by `Term.subst_compose_lift_singleton_eq_consSingleton_of_entry`.
The remaining half is the typed factorization from `weaken` followed by
`singleton` into this precomposed substitution. -/
theorem Term.subst_precompose_weaken_singleton_eq_identity
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    {someType : Ty level scope}
    {raw : RawTerm scope}
    (someTerm : Term context someType raw) :
    Term.subst
        (TermSubst.precomposeRenaming
          (TermRenaming.weakenStep context newType)
          (TermSubst.singleton singletonTerm))
        someTerm =
      Term.subst (TermSubst.identity context) someTerm :=
  Term.subst_pointwise
    (TermSubst.precompose_weaken_singleton_pointwise singletonTerm)
    someTerm

/-- Old-entry weaken/singleton collapse from the typed precomposition
factorization.

The beta-contractum bridge needs old substitution entries to collapse
after `Term.weaken` followed by singleton substitution.  This theorem
separates the problem into the real hard part and the already-solved
pointwise identity part:

* `factorHEq` aligns the concrete `weaken`-then-singleton expression
  with substitution by the input-precomposed substitution;
* `Term.subst_precompose_weaken_singleton_eq_identity` then reduces
  that precomposed substitution to identity;
* `identityHEq` erases identity substitution for the specific term.

This keeps the next blocker precise instead of hiding it inside the
`compose_lift_singleton_consSingleton` comparison. -/
theorem Term.weaken_subst_singleton_of_precompose_factor_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    {someType : Ty level scope}
    {raw : RawTerm scope}
    (someTerm : Term context someType raw)
    (factorHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType someTerm))
        (Term.subst
          (TermSubst.precomposeRenaming
            (TermRenaming.weakenStep context newType)
            (TermSubst.singleton singletonTerm))
          someTerm))
    (identityHEq :
      HEq (Term.subst (TermSubst.identity context) someTerm)
        someTerm) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType someTerm))
      someTerm := by
  exact HEq.trans factorHEq
    (HEq.trans
      (by
        rw [Term.subst_precompose_weaken_singleton_eq_identity
          singletonTerm someTerm]
        exact HEq.rfl)
      identityHEq)

/-- The underlying type-substitution component of lifted weakening
followed by lifted singleton is pointwise identity under the original
binder. -/
theorem Subst.precompose_lift_weaken_singleton_lift_forTy_pointwise
    {level scope : Nat}
    (newType : Ty level scope)
    (singletonRaw : RawTerm scope) :
    ∀ position,
      (Subst.precomposeRenaming RawRenaming.weaken.lift
        ((Subst.singleton newType singletonRaw).lift)).forTy position =
        (@Subst.identity level (scope + 1)).forTy position
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- The underlying raw-substitution component of lifted weakening
followed by lifted singleton is pointwise identity under the original
binder. -/
theorem Subst.precompose_lift_weaken_singleton_lift_forRaw_pointwise
    {level scope : Nat}
    (newType : Ty level scope)
    (singletonRaw : RawTerm scope) :
    ∀ position,
      (Subst.precomposeRenaming RawRenaming.weaken.lift
        ((Subst.singleton newType singletonRaw).lift)).forRaw position =
        (@Subst.identity level (scope + 1)).forRaw position
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- Precomposing the lifted weakening renaming with a lifted singleton
substitution is entrywise the identity substitution under the original
binder.

This is the binder-body entry alignment behind
`Term.weaken_subst_singleton_lam_heq`: the raw operation weakens under
an existing binder and then substitutes the inserted outer variable
away, so old and binder-local variables return to their original
positions. -/
theorem TermSubst.precompose_lift_weaken_singleton_lift_position_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType newType : Ty level scope}
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (position : Fin (scope + 1)) :
    HEq
      (TermSubst.precomposeRenaming
        ((TermRenaming.weakenStep context newType).lift domainType)
        ((TermSubst.singleton singletonTerm).lift
          (domainType.rename RawRenaming.weaken))
        position)
      (TermSubst.identity (context.cons domainType) position) := by
  apply HEq.trans
  · exact TermSubst.precomposeRenaming_position_HEq
      ((TermRenaming.weakenStep context newType).lift domainType)
      ((TermSubst.singleton singletonTerm).lift
        (domainType.rename RawRenaming.weaken))
      position
  · rcases position with ⟨positionIndex, positionIsWithinScope⟩
    cases positionIndex with
    | zero =>
        simp only [RawRenaming.lift, TermSubst.lift, TermSubst.identity,
          varType]
        exact HEq.trans
          (Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute
              (Subst.singleton newType singletonRaw)
              (domainType.rename RawRenaming.weaken)))
          (HEq.trans
            (Term.var_zero_cons_type_eq_heq
              (Ty.weaken_subst_singleton domainType newType singletonRaw))
            (HEq.symm
              (Term.type_eq_symm_cast_heq
                (context := context.cons domainType)
                (typeEq := Ty.subst_identity (domainType.weaken))
                (targetTerm := Term.var
                  (context := context.cons domainType)
                  ⟨0, Nat.zero_lt_succ scope⟩))))
    | succ previousIndex =>
        simp only [RawRenaming.lift, RawRenaming.weaken, TermSubst.lift,
          TermSubst.singleton, TermSubst.identity, varType]
        exact HEq.trans
          (Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute
              (Subst.singleton newType singletonRaw)
              (varType (context.cons newType)
                ⟨previousIndex + 1, positionIsWithinScope⟩)))
          (HEq.trans
            (Term.weaken_head_type_eq_heq
              (Ty.weaken_subst_singleton domainType newType singletonRaw)
              ((Ty.weaken_subst_singleton
                (varType context
                  ⟨previousIndex,
                    Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
                newType singletonRaw).symm ▸
                  Term.var
                    ⟨previousIndex,
                      Nat.lt_of_succ_lt_succ positionIsWithinScope⟩))
            (HEq.trans
              (Term.rename_type_eq_cast_heq
                (TermRenaming.weakenStep context domainType)
                (Ty.weaken_subst_singleton
                  (varType context
                    ⟨previousIndex,
                      Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
                  newType singletonRaw).symm
                (Term.var
                  ⟨previousIndex,
                    Nat.lt_of_succ_lt_succ positionIsWithinScope⟩))
              (HEq.trans
                (Term.type_eq_cast_heq
                  (context := context.cons domainType)
                  (typeEq := congrArg
                    (fun someType => Ty.rename someType RawRenaming.weaken)
                    (Ty.weaken_subst_singleton
                      (varType context
                        ⟨previousIndex,
                          Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
                      newType singletonRaw).symm)
                  (sourceTerm :=
                    Term.rename (TermRenaming.weakenStep context domainType)
                      (Term.var
                        ⟨previousIndex,
                          Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)))
                (HEq.trans
                  (Term.rename_var_HEq
                    (TermRenaming.weakenStep context domainType)
                    ⟨previousIndex,
                      Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
                  (HEq.symm
                    (Term.type_eq_symm_cast_heq
                      (context := context.cons domainType)
                      (typeEq := Ty.subst_identity
                        (varType (context.cons domainType)
                          ⟨previousIndex + 1, positionIsWithinScope⟩))
                      (targetTerm := Term.var
                        (context := context.cons domainType)
                        ⟨previousIndex + 1, positionIsWithinScope⟩)))))))

/-- Variable surface case for lifted weaken/singleton precomposition.

This packages `TermSubst.precompose_lift_weaken_singleton_lift_position_HEq`
at the `Term.subst` layer.  It is the base case for the binder-body
rename/substitution cancellation theorem: after weakening under an
existing binder and substituting by the lifted singleton, every variable
in the original binder context returns to itself up to heterogeneous
equality. -/
theorem Term.subst_precompose_lift_weaken_singleton_lift_var_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType newType : Ty level scope}
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (position : Fin (scope + 1)) :
    HEq
      (Term.subst
        (TermSubst.precomposeRenaming
          ((TermRenaming.weakenStep context newType).lift domainType)
          ((TermSubst.singleton singletonTerm).lift
            (domainType.rename RawRenaming.weaken)))
        (Term.var (context := context.cons domainType) position))
      (Term.var (context := context.cons domainType) position) := by
  exact HEq.trans
    (by
      simpa only [Term.subst] using
        TermSubst.precompose_lift_weaken_singleton_lift_position_HEq
          (domainType := domainType) singletonTerm position)
    (by
      simp only [TermSubst.identity]
      exact Term.type_eq_symm_cast_heq
        (context := context.cons domainType)
        (typeEq := Ty.subst_identity
          (varType (context.cons domainType) position))
        (targetTerm := Term.var
          (context := context.cons domainType) position))

/-- A raw-index cast on a typed term is heterogeneously equal to the
original term. -/
theorem Term.raw_eq_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (rawEq : sourceRaw = targetRaw)
    (sourceTerm : Term context someType sourceRaw) :
    HEq (rawEq ▸ sourceTerm) sourceTerm := by
  cases rawEq
  exact HEq.rfl

/-- Combined type/raw casts on a typed term are heterogeneously equal
to the original term. -/
theorem Term.type_raw_eq_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (rawEq : sourceRaw = targetRaw)
    (sourceTerm : Term context sourceType sourceRaw) :
    HEq (rawEq ▸ typeEq ▸ sourceTerm) sourceTerm := by
  cases typeEq
  cases rawEq
  exact HEq.rfl

/-- Substitution ignores a pure type-index cast up to heterogeneous
equality. -/
theorem Term.subst_type_eq_cast_heq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {sourceType targetType : Ty level sourceScope}
    {raw : RawTerm sourceScope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term sourceCtx sourceType raw) :
    HEq (Term.subst termSubst (typeEq ▸ sourceTerm))
      (Term.subst termSubst sourceTerm) := by
  cases typeEq
  exact HEq.rfl

/-- Substitution preserves heterogeneous equality once source indices
are aligned by explicit type/raw equalities. -/
theorem Term.subst_heq_of_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    (typeEq : firstType = secondType)
    (rawEq : firstRaw = secondRaw)
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (termsHEq : HEq firstTerm secondTerm) :
    HEq (Term.subst termSubst firstTerm)
      (Term.subst termSubst secondTerm) := by
  subst typeEq
  subst rawEq
  have termsEq : firstTerm = secondTerm := eq_of_heq termsHEq
  subst termsEq
  rfl

/-- Single-variable substitution preserves heterogeneous equality of
the body once body indices are aligned by explicit type/raw equalities. -/
theorem Term.subst0_body_heq_of_eq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {substituent : Ty level scope}
    {argumentRaw : RawTerm scope}
    {argumentTerm : Term context substituent argumentRaw}
    {firstCodomain secondCodomain : Ty level (scope + 1)}
    {firstBodyRaw secondBodyRaw : RawTerm (scope + 1)}
    (codomainEq : firstCodomain = secondCodomain)
    (bodyRawEq : firstBodyRaw = secondBodyRaw)
    {firstBody :
      Term (context.cons substituent) firstCodomain firstBodyRaw}
    {secondBody :
      Term (context.cons substituent) secondCodomain secondBodyRaw}
    (bodyHEq : HEq firstBody secondBody) :
    HEq (Term.subst0 firstBody argumentTerm)
      (Term.subst0 secondBody argumentTerm) := by
  unfold Term.subst0
  exact Term.subst_heq_of_eq
    (TermSubst.singleton argumentTerm)
    codomainEq bodyRawEq bodyHEq

/-- Variable base case for heterogeneous rename/substitution
cancellation.

If the substitution entry selected by the typed renaming is HEq to the
identity entry, then substituting the renamed variable returns the
original variable.  This is the base case of the stronger
rename-then-substitute cancellation theorem needed by the beta
contractum route. -/
theorem Term.subst_rename_cancel_var_HEq
    {mode : Mode} {level sourceScope middleScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope sourceScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx sourceCtx sigma)
    (entryHEq :
      ∀ position,
        HEq (termSubst (rho position))
          (TermSubst.identity sourceCtx position))
    (position : Fin sourceScope) :
    HEq
      (Term.subst termSubst
        (Term.rename termRenaming
          (Term.var (context := sourceCtx) position)))
      (Term.var (context := sourceCtx) position) := by
  simp only [Term.rename]
  exact HEq.trans
    (Term.subst_type_eq_cast_heq termSubst (termRenaming position)
      (Term.var (context := middleCtx) (rho position)))
    (HEq.trans
      (by simpa only [Term.subst] using entryHEq position)
      (Term.type_eq_symm_cast_heq
        (context := sourceCtx)
        (typeEq := Ty.subst_identity (varType sourceCtx position))
        (targetTerm := Term.var (context := sourceCtx) position)))

end LeanFX2
