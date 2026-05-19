import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose

/-! # LeanFX2.Term.Pointwise.IdentitySubst

Typed identity-substitution erasure helpers for the M04 lambda route.

These lemmas are kept out of `PointwiseAndCompositionInfrastructure`
so the identity-erasure cascade can evolve without forcing every edit
through the large composition-infrastructure module. -/

namespace LeanFX2

private theorem heq_of_eq_local.{universeLevel}
    {SomeType : Sort universeLevel} {firstValue secondValue : SomeType}
    (valuesEq : firstValue = secondValue) :
    HEq firstValue secondValue := by
  cases valuesEq
  exact HEq.rfl

/-! ## Lifted identity entries -/

/-- Fresh entry of lifted identity substitution. -/
theorem TermSubst.identity_lift_zero_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    HEq
      ((TermSubst.identity context).lift newType
        ⟨0, Nat.zero_lt_succ scope⟩)
      (TermSubst.identity (context.cons newType)
        ⟨0, Nat.zero_lt_succ scope⟩) := by
  change HEq
    ((Ty.weaken_subst_commute (@Subst.identity level scope) newType).symm ▸
      (show
        Term
          (context.cons (newType.subst (@Subst.identity level scope)))
          ((newType.subst (@Subst.identity level scope)).weaken)
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) from
        Term.var
          (context := context.cons
            (newType.subst (@Subst.identity level scope)))
          ⟨0, Nat.zero_lt_succ scope⟩))
    ((Ty.subst_identity (newType.weaken)).symm ▸
      (show
        Term (context.cons newType) newType.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) from
        Term.var
          (context := context.cons newType)
          ⟨0, Nat.zero_lt_succ scope⟩))
  exact HEq.trans
    (Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (@Subst.identity level scope) newType))
    (HEq.trans
      (Term.var_zero_cons_type_eq_heq
        (Ty.subst_identity newType))
      (HEq.symm
        (Term.type_eq_symm_cast_heq
          (context := context.cons newType)
          (typeEq := Ty.subst_identity (newType.weaken))
          (targetTerm := Term.var
            (context := context.cons newType)
            ⟨0, Nat.zero_lt_succ scope⟩))))

/-- Old-variable entry of lifted identity substitution. -/
theorem TermSubst.identity_lift_succ_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin scope) :
    HEq
      ((TermSubst.identity context).lift newType (Fin.succ position))
      (TermSubst.identity (context.cons newType) (Fin.succ position)) := by
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  simp only [TermSubst.lift, TermSubst.identity]
  exact HEq.trans
    (Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (@Subst.identity level scope)
        (varType context ⟨positionIndex, positionIsWithinScope⟩)))
    (HEq.trans
      (Term.weaken_head_type_eq_heq
        (Ty.subst_identity newType)
        ((Ty.subst_identity
          (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm ▸
          Term.var ⟨positionIndex, positionIsWithinScope⟩))
      (HEq.trans
        (Term.rename_type_eq_cast_heq
          (TermRenaming.weakenStep context newType)
          (Ty.subst_identity
            (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm
          (Term.var ⟨positionIndex, positionIsWithinScope⟩))
        (HEq.trans
          (Term.type_eq_cast_heq
            (context := context.cons newType)
            (typeEq := congrArg
              (fun someType => Ty.rename someType RawRenaming.weaken)
              (Ty.subst_identity
                (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm)
            (sourceTerm :=
              Term.rename (TermRenaming.weakenStep context newType)
                (Term.var ⟨positionIndex, positionIsWithinScope⟩)))
          (HEq.trans
            (Term.rename_var_HEq
              (TermRenaming.weakenStep context newType)
              ⟨positionIndex, positionIsWithinScope⟩)
            (HEq.symm
              (Term.type_eq_symm_cast_heq
                (context := context.cons newType)
                (typeEq := Ty.subst_identity
                  (varType (context.cons newType)
                    (Fin.succ ⟨positionIndex, positionIsWithinScope⟩)))
                (targetTerm := Term.var
                  (context := context.cons newType)
                  (Fin.succ
                    ⟨positionIndex, positionIsWithinScope⟩))))))))

/-- Lifting identity substitution is pointwise heterogeneously equal
to identity on the extended context. -/
theorem TermSubst.identity_lift_position_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin (scope + 1)) :
    HEq
      ((TermSubst.identity context).lift newType position)
      (TermSubst.identity (context.cons newType) position) := by
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  cases positionIndex with
  | zero =>
      exact TermSubst.identity_lift_zero_HEq
        (context := context) newType
  | succ previousIndex =>
      exact TermSubst.identity_lift_succ_HEq
        (context := context) newType
        ⟨previousIndex,
          Nat.lt_of_succ_lt_succ positionIsWithinScope⟩

/-- Plain weakening of an identity-substitution entry agrees with the
successor entry of the lifted identity substitution. -/
theorem TermSubst.identity_lift_succ_plain_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin scope) :
    HEq
      (Term.weaken newType
        (TermSubst.identity context position))
      ((TermSubst.identity context).lift newType
        (Fin.succ position)) := by
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  simp only [TermSubst.lift]
  exact HEq.trans
    (Term.weaken_head_type_eq_heq
      (context := context)
      (sourceTerm := TermSubst.identity context
        ⟨positionIndex, positionIsWithinScope⟩)
      (Ty.subst_identity newType).symm)
    (HEq.symm
      (Term.type_eq_symm_cast_heq
        (context := context.cons (newType.subst (@Subst.identity level scope)))
        (typeEq := Ty.weaken_subst_commute (@Subst.identity level scope)
          (varType context ⟨positionIndex, positionIsWithinScope⟩))
        (targetTerm := Term.weaken
          (newType.subst (@Subst.identity level scope))
          (TermSubst.identity context
            ⟨positionIndex, positionIsWithinScope⟩))))

/-! ## Identity-like substitutions -/

/-- A typed substitution that behaves like identity up to the casts
introduced by the type and raw substitution indices.

The pointwise `Subst` fields are kept explicit because term-entry HEq
alone is not enough to lift the invariant through binders: the fresh
variable case also needs type/raw substitution to remain identity.

The context HEq is equally load-bearing.  A lifted substitution maps the
fresh variable into `targetCtx.cons (newType.subst sigma)`, while the
identity substitution maps it into `sourceCtx.cons newType`; relating
those two variables requires the old contexts to agree as well as the
new head type. -/
structure TermSubst.IsIdentityLike
    {mode : Mode} {level sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level sourceScope}
    {sigma : Subst level sourceScope sourceScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) : Prop where
  contextHEq :
    HEq targetCtx sourceCtx
  forTyPointwise :
    ∀ position,
      sigma.forTy position = (@Subst.identity level sourceScope).forTy position
  forRawPointwise :
    ∀ position,
      sigma.forRaw position = (@Subst.identity level sourceScope).forRaw position
  entryHEq :
    ∀ position,
      HEq (termSubst position) (TermSubst.identity sourceCtx position)

/-- The literal identity substitution is identity-like. -/
theorem TermSubst.IsIdentityLike.identity
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) :
    TermSubst.IsIdentityLike (TermSubst.identity context) := by
  refine
    { contextHEq := ?_
      forTyPointwise := ?_
      forRawPointwise := ?_
      entryHEq := ?_ }
  · exact HEq.rfl
  · intro position
    rfl
  · intro position
    rfl
  · intro position
    exact HEq.rfl

/-- The context component of an identity-like substitution remains
identity-like after lifting under a binder. -/
theorem TermSubst.IsIdentityLike.lift_contextHEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (newType : Ty level scope) :
    HEq
      (targetCtx.cons (newType.subst sigma))
      (sourceCtx.cons newType) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  have newTypeSubstEq : newType.subst sigma = newType := by
    exact Eq.trans
      (Ty.subst_pointwise
        substitutionIsIdentityLike.forTyPointwise
        substitutionIsIdentityLike.forRawPointwise
        newType)
      (Ty.subst_identity newType)
  exact heq_of_eq_local (congrArg (fun headType => Ctx.cons targetCtx headType)
    newTypeSubstEq)

/-- The type-substitution field of an identity-like substitution remains
pointwise identity after lifting under a binder. -/
theorem TermSubst.IsIdentityLike.lift_forTyPointwise
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    ∀ position,
      sigma.lift.forTy position =
        (@Subst.identity level (scope + 1)).forTy position
  | ⟨0, _⟩ => rfl
  | ⟨positionIndex + 1, positionIsWithinScope⟩ => by
      change
        (sigma.forTy
          ⟨positionIndex,
            Nat.lt_of_succ_lt_succ positionIsWithinScope⟩).weaken =
          Ty.tyVar ⟨positionIndex + 1, positionIsWithinScope⟩
      rw [substitutionIsIdentityLike.forTyPointwise
        ⟨positionIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩]
      rfl

/-- The raw-substitution field of an identity-like substitution remains
pointwise identity after lifting under a binder. -/
theorem TermSubst.IsIdentityLike.lift_forRawPointwise
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    ∀ position,
      sigma.lift.forRaw position =
        (@Subst.identity level (scope + 1)).forRaw position
  | ⟨0, _⟩ => rfl
  | ⟨positionIndex + 1, positionIsWithinScope⟩ => by
      change
        (sigma.forRaw
          ⟨positionIndex,
            Nat.lt_of_succ_lt_succ positionIsWithinScope⟩).rename
            RawRenaming.weaken =
          RawTerm.var ⟨positionIndex + 1, positionIsWithinScope⟩
      rw [substitutionIsIdentityLike.forRawPointwise
        ⟨positionIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩]
      rfl

/-- The term-entry component of an identity-like substitution remains
identity-like after lifting under a binder. -/
theorem TermSubst.IsIdentityLike.lift_entryHEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (newType : Ty level scope) :
    ∀ position,
      HEq
        (termSubst.lift newType position)
        (TermSubst.identity (sourceCtx.cons newType) position)
  | ⟨0, _⟩ => by
      have contextsEq : targetCtx = sourceCtx :=
        eq_of_heq substitutionIsIdentityLike.contextHEq
      subst contextsEq
      have newTypeSubstEq : newType.subst sigma = newType := by
        exact Eq.trans
          (Ty.subst_pointwise
            substitutionIsIdentityLike.forTyPointwise
            substitutionIsIdentityLike.forRawPointwise
            newType)
          (Ty.subst_identity newType)
      simp only [TermSubst.lift, TermSubst.identity]
      exact HEq.trans
        (Term.type_eq_symm_cast_heq
          (context := targetCtx.cons (newType.subst sigma))
          (typeEq := Ty.weaken_subst_commute sigma newType)
          (targetTerm := Term.var
            (context := targetCtx.cons (newType.subst sigma))
            ⟨0, Nat.zero_lt_succ scope⟩))
        (HEq.trans
          (Term.var_zero_cons_type_eq_heq
            (context := targetCtx)
            newTypeSubstEq)
          (HEq.symm
            (Term.type_eq_symm_cast_heq
              (context := targetCtx.cons newType)
              (typeEq := Ty.subst_identity (newType.weaken))
              (targetTerm := Term.var
                (context := targetCtx.cons newType)
                ⟨0, Nat.zero_lt_succ scope⟩))))
  | ⟨positionIndex + 1, positionIsWithinScope⟩ => by
      let oldPosition : Fin scope :=
        ⟨positionIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
      have contextsEq : targetCtx = sourceCtx :=
        eq_of_heq substitutionIsIdentityLike.contextHEq
      subst contextsEq
      have newTypeSubstEq : newType.subst sigma = newType := by
        exact Eq.trans
          (Ty.subst_pointwise
            substitutionIsIdentityLike.forTyPointwise
            substitutionIsIdentityLike.forRawPointwise
            newType)
          (Ty.subst_identity newType)
      have oldTypeSubstEq :
          (varType targetCtx oldPosition).subst sigma =
            (varType targetCtx oldPosition).subst
              (@Subst.identity level scope) :=
        Ty.subst_pointwise
          substitutionIsIdentityLike.forTyPointwise
          substitutionIsIdentityLike.forRawPointwise
          (varType targetCtx oldPosition)
      have oldRawSubstEq :
          sigma.forRaw oldPosition =
            (@Subst.identity level scope).forRaw oldPosition :=
        substitutionIsIdentityLike.forRawPointwise oldPosition
      simp only [TermSubst.lift]
      exact HEq.trans
        (Term.type_eq_symm_cast_heq
          (context := targetCtx.cons (newType.subst sigma))
          (typeEq := Ty.weaken_subst_commute sigma
            (varType targetCtx oldPosition))
          (targetTerm := Term.weaken (newType.subst sigma)
            (termSubst oldPosition)))
        (HEq.trans
          (Term.weaken_head_type_eq_heq
            (context := targetCtx)
            (sourceTerm := termSubst oldPosition)
            newTypeSubstEq)
          (HEq.trans
            (Term.weaken_heq_of_eq
              (context := targetCtx)
              newType
              oldTypeSubstEq
              oldRawSubstEq
              (substitutionIsIdentityLike.entryHEq oldPosition))
            (HEq.trans
              (TermSubst.identity_lift_succ_plain_HEq
                (context := targetCtx)
                newType oldPosition)
              (TermSubst.identity_lift_succ_HEq
                (context := targetCtx)
                newType oldPosition))))

/-- Identity-like substitutions remain identity-like after lifting under
a binder. -/
theorem TermSubst.IsIdentityLike.lift
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (newType : Ty level scope) :
    TermSubst.IsIdentityLike (termSubst.lift newType) := by
  refine
    { contextHEq := ?_
      forTyPointwise := ?_
      forRawPointwise := ?_
      entryHEq := ?_ }
  · exact substitutionIsIdentityLike.lift_contextHEq newType
  · exact substitutionIsIdentityLike.lift_forTyPointwise
  · exact substitutionIsIdentityLike.lift_forRawPointwise
  · exact substitutionIsIdentityLike.lift_entryHEq newType

/-- An identity-like typed substitution acts as identity on types. -/
theorem TermSubst.IsIdentityLike.tySubst_eq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (someType : Ty level scope) :
    someType.subst sigma = someType :=
  Eq.trans
    (Ty.subst_pointwise
      substitutionIsIdentityLike.forTyPointwise
      substitutionIsIdentityLike.forRawPointwise
      someType)
    (Ty.subst_identity someType)

/-- An identity-like typed substitution acts as identity on raw terms. -/
theorem TermSubst.IsIdentityLike.rawSubst_eq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (raw : RawTerm scope) :
    raw.subst sigma.forRaw = raw :=
  Eq.trans
    (RawTerm.subst_pointwise
      substitutionIsIdentityLike.forRawPointwise
      raw)
    (RawTerm.subst_identity raw)

end LeanFX2
