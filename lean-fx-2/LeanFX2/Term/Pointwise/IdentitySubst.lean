import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

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

/-! ## Identity-like substitution at binder introductions -/

/-- Lambda introduction case for an identity-like substitution.

This is the binder-facing form used by the eventual whole-term
identity-like erasure induction: the caller supplies the body erasure
under the lifted substitution. -/
theorem Term.subst_identityLike_lam_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw)
    (bodyHEq :
      HEq (Term.subst (termSubst.lift domainType) body) body) :
    HEq
      (Term.subst termSubst (Term.lam body))
      (Term.lam body) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  have liftedSubstitutionIsIdentityLike :=
    substitutionIsIdentityLike.lift domainType
  have bodyRawEq :
      bodyRaw.subst sigma.forRaw.lift = bodyRaw :=
    liftedSubstitutionIsIdentityLike.rawSubst_eq bodyRaw
  have bodyCastHEq :
      HEq
        ((Ty.weaken_subst_commute sigma codomainType) ▸
          Term.subst (termSubst.lift domainType) body)
        body :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute sigma codomainType)
        (Term.subst (termSubst.lift domainType) body))
      bodyHEq
  exact Term.lam_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq domainType)
    (substitutionIsIdentityLike.tySubst_eq codomainType)
    bodyRawEq
    bodyCastHEq

/-- Dependent lambda introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_lamPi_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (bodyHEq :
      HEq (Term.subst (termSubst.lift domainType) body) body) :
    HEq
      (Term.subst termSubst (Term.lamPi body))
      (Term.lamPi body) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  have liftedSubstitutionIsIdentityLike :=
    substitutionIsIdentityLike.lift domainType
  exact Term.lamPi_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq domainType)
    (liftedSubstitutionIsIdentityLike.tySubst_eq codomainType)
    (liftedSubstitutionIsIdentityLike.rawSubst_eq bodyRaw)
    bodyHEq

/-- Cubical path-lambda introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_pathLam_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyHEq :
      HEq (Term.subst (termSubst.lift Ty.interval) body) body) :
    HEq
      (Term.subst termSubst
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint body))
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint
        rightEndpoint body) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  have liftedSubstitutionIsIdentityLike :=
    substitutionIsIdentityLike.lift Ty.interval
  have bodyCastHEq :
      HEq
        ((Ty.weaken_subst_commute sigma carrierType) ▸
          Term.subst (termSubst.lift Ty.interval) body)
        body :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute sigma carrierType)
        (Term.subst (termSubst.lift Ty.interval) body))
      bodyHEq
  exact Term.pathLam_HEq_congr
    modeIsUnivalent
    (substitutionIsIdentityLike.tySubst_eq carrierType)
    (substitutionIsIdentityLike.rawSubst_eq leftEndpoint)
    (substitutionIsIdentityLike.rawSubst_eq rightEndpoint)
    (liftedSubstitutionIsIdentityLike.rawSubst_eq bodyRaw)
    bodyCastHEq

/-! ## Identity-like substitution at the term surface -/

/-- Variable case for an identity-like substitution. -/
theorem Term.subst_identityLike_var_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (position : Fin scope) :
    HEq
      (Term.subst termSubst
        (Term.var (context := sourceCtx) position))
      (Term.var (context := sourceCtx) position) := by
  simp only [Term.subst]
  exact HEq.trans
    (substitutionIsIdentityLike.entryHEq position)
    (Term.type_eq_symm_cast_heq
      (context := sourceCtx)
      (typeEq := Ty.subst_identity (varType sourceCtx position))
      (targetTerm := Term.var (context := sourceCtx) position))

/-- Unit case for an identity-like substitution. -/
theorem Term.subst_identityLike_unit_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.unit (context := sourceCtx)))
      (Term.unit (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Boolean true case for an identity-like substitution. -/
theorem Term.subst_identityLike_boolTrue_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.boolTrue (context := sourceCtx)))
      (Term.boolTrue (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Boolean false case for an identity-like substitution. -/
theorem Term.subst_identityLike_boolFalse_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.boolFalse (context := sourceCtx)))
      (Term.boolFalse (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Natural zero case for an identity-like substitution. -/
theorem Term.subst_identityLike_natZero_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.natZero (context := sourceCtx)))
      (Term.natZero (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Left interval endpoint case for an identity-like substitution. -/
theorem Term.subst_identityLike_interval0_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.interval0 (context := sourceCtx)))
      (Term.interval0 (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Right interval endpoint case for an identity-like substitution. -/
theorem Term.subst_identityLike_interval1_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.interval1 (context := sourceCtx)))
      (Term.interval1 (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Empty list case for an identity-like substitution. -/
theorem Term.subst_identityLike_listNil_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope} :
    HEq
      (Term.subst termSubst
        (Term.listNil (context := sourceCtx) (elementType := elementType)))
      (Term.listNil (context := sourceCtx) (elementType := elementType)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.listNil_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)

/-- Empty option case for an identity-like substitution. -/
theorem Term.subst_identityLike_optionNone_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope} :
    HEq
      (Term.subst termSubst
        (Term.optionNone (context := sourceCtx) (elementType := elementType)))
      (Term.optionNone (context := sourceCtx) (elementType := elementType)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.optionNone_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)

/-- Natural successor case for an identity-like substitution. -/
theorem Term.subst_identityLike_natSucc_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {predecessorRaw : RawTerm scope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorHEq :
      HEq (Term.subst termSubst predecessor) predecessor) :
    HEq
      (Term.subst termSubst (Term.natSucc predecessor))
      (Term.natSucc predecessor) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.natSucc_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq predecessorRaw)
    predecessorHEq

/-- List cons case for an identity-like substitution. -/
theorem Term.subst_identityLike_listCons_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term sourceCtx elementType headRaw)
    (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headHEq :
      HEq (Term.subst termSubst headTerm) headTerm)
    (tailHEq :
      HEq (Term.subst termSubst tailTerm) tailTerm) :
    HEq
      (Term.subst termSubst (Term.listCons headTerm tailTerm))
      (Term.listCons headTerm tailTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.listCons_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)
    (substitutionIsIdentityLike.rawSubst_eq headRaw)
    (substitutionIsIdentityLike.rawSubst_eq tailRaw)
    headHEq tailHEq

/-- Option some case for an identity-like substitution. -/
theorem Term.subst_identityLike_optionSome_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueHEq :
      HEq (Term.subst termSubst valueTerm) valueTerm) :
    HEq
      (Term.subst termSubst (Term.optionSome valueTerm))
      (Term.optionSome valueTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.optionSome_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)
    (substitutionIsIdentityLike.rawSubst_eq valueRaw)
    valueHEq

/-- Either-left injection case for an identity-like substitution. -/
theorem Term.subst_identityLike_eitherInl_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueHEq :
      HEq (Term.subst termSubst valueTerm) valueTerm) :
    HEq
      (Term.subst termSubst
        (Term.eitherInl (rightType := rightType) valueTerm))
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.eitherInl_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq leftType)
    (substitutionIsIdentityLike.tySubst_eq rightType)
    (substitutionIsIdentityLike.rawSubst_eq valueRaw)
    valueHEq

/-- Either-right injection case for an identity-like substitution. -/
theorem Term.subst_identityLike_eitherInr_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueHEq :
      HEq (Term.subst termSubst valueTerm) valueTerm) :
    HEq
      (Term.subst termSubst
        (Term.eitherInr (leftType := leftType) valueTerm))
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.eitherInr_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq leftType)
    (substitutionIsIdentityLike.tySubst_eq rightType)
    (substitutionIsIdentityLike.rawSubst_eq valueRaw)
    valueHEq

/-- Interval negation case for an identity-like substitution. -/
theorem Term.subst_identityLike_intervalOpp_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerRaw : RawTerm scope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerValue) innerValue) :
    HEq
      (Term.subst termSubst (Term.intervalOpp innerValue))
      (Term.intervalOpp innerValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.intervalOpp_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

/-- Interval meet case for an identity-like substitution. -/
theorem Term.subst_identityLike_intervalMeet_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst termSubst leftValue) leftValue)
    (rightHEq :
      HEq (Term.subst termSubst rightValue) rightValue) :
    HEq
      (Term.subst termSubst (Term.intervalMeet leftValue rightValue))
      (Term.intervalMeet leftValue rightValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.intervalMeet_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq leftRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightRaw)
    leftHEq rightHEq

/-- Interval join case for an identity-like substitution. -/
theorem Term.subst_identityLike_intervalJoin_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst termSubst leftValue) leftValue)
    (rightHEq :
      HEq (Term.subst termSubst rightValue) rightValue) :
    HEq
      (Term.subst termSubst (Term.intervalJoin leftValue rightValue))
      (Term.intervalJoin leftValue rightValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.intervalJoin_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq leftRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightRaw)
    leftHEq rightHEq

/-- Modal introduction wrapper case for an identity-like substitution. -/
theorem Term.subst_identityLike_modIntro_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerTerm) innerTerm) :
    HEq
      (Term.subst termSubst (Term.modIntro innerTerm))
      (Term.modIntro innerTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.modIntro_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq innerType)
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

/-- Modal elimination wrapper case for an identity-like substitution. -/
theorem Term.subst_identityLike_modElim_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerTerm) innerTerm) :
    HEq
      (Term.subst termSubst (Term.modElim innerTerm))
      (Term.modElim innerTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.modElim_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq innerType)
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

/-- Modal subsumption wrapper case for an identity-like substitution. -/
theorem Term.subst_identityLike_subsume_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerTerm) innerTerm) :
    HEq
      (Term.subst termSubst (Term.subsume innerTerm))
      (Term.subsume innerTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.subsume_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq innerType)
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

/-- Application case for an identity-like substitution. -/
theorem Term.subst_identityLike_app_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionHEq :
      HEq (Term.subst termSubst functionTerm) functionTerm)
    (argumentHEq :
      HEq (Term.subst termSubst argumentTerm) argumentTerm) :
    HEq
      (Term.subst termSubst (Term.app functionTerm argumentTerm))
      (Term.app functionTerm argumentTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.app_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq domainType)
    (substitutionIsIdentityLike.tySubst_eq codomainType)
    (substitutionIsIdentityLike.rawSubst_eq functionRaw)
    (substitutionIsIdentityLike.rawSubst_eq argumentRaw)
    functionHEq argumentHEq

/-! ## Lifted identity at the term surface -/

/-- Variable surface case for ordinary identity substitution. -/
theorem Term.subst_identity_var_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (position : Fin scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.var (context := context) position))
      (Term.var (context := context) position) := by
  simp only [Term.subst, TermSubst.identity]
  exact Term.type_eq_symm_cast_heq
    (context := context)
    (typeEq := Ty.subst_identity (varType context position))
    (targetTerm := Term.var (context := context) position)

/-- Variable surface case for lifted identity substitution. -/
theorem Term.subst_identity_lift_var_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin (scope + 1)) :
    HEq
      (Term.subst ((TermSubst.identity context).lift newType)
        (Term.var (context := context.cons newType) position))
      (Term.var (context := context.cons newType) position) := by
  simp only [Term.subst]
  exact HEq.trans
    (TermSubst.identity_lift_position_HEq
      (context := context) newType position)
    (Term.type_eq_symm_cast_heq
      (context := context.cons newType)
      (typeEq := Ty.subst_identity
        (varType (context.cons newType) position))
      (targetTerm := Term.var
        (context := context.cons newType) position))

/-! ## Nullary value cases -/

/-- Unit value case for ordinary identity substitution. -/
theorem Term.subst_identity_unit_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.unit (context := context)))
      (Term.unit (context := context)) := by
  rfl

/-! ## Binder cases -/

/-- Lambda case for ordinary identity substitution.

The recursive premise is intentionally stated for the lifted identity
substitution, matching the actual `Term.subst` binder arm. -/
theorem Term.subst_identity_lam_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType.weaken bodyRaw)
    (bodyHEq :
      HEq (Term.subst ((TermSubst.identity context).lift domainType) body)
        body) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.lam (codomainType := codomainType) body))
      (Term.lam (codomainType := codomainType) body) := by
  simp only [Term.subst]
  have bodyRawIdentity :
      bodyRaw.subst (@Subst.identity level scope).forRaw.lift = bodyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) bodyRaw]
    exact RawTerm.subst_identity bodyRaw
  have bodyCastHEq :
      HEq
        ((Ty.weaken_subst_commute Subst.identity codomainType) ▸
          Term.subst ((TermSubst.identity context).lift domainType) body)
        body :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute Subst.identity codomainType)
        (Term.subst ((TermSubst.identity context).lift domainType) body))
      bodyHEq
  exact Term.lam_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    bodyRawIdentity
    bodyCastHEq

/-- Dependent lambda case for ordinary identity substitution.

The recursive premise is intentionally stated for the lifted identity
substitution, matching the actual `Term.subst` binder arm. -/
theorem Term.subst_identity_lamPi_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType bodyRaw)
    (bodyHEq :
      HEq (Term.subst ((TermSubst.identity context).lift domainType) body)
        body) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.lamPi (domainType := domainType) body))
      (Term.lamPi (domainType := domainType) body) := by
  simp only [Term.subst]
  have codomainIdentity :
      codomainType.subst (@Subst.identity level scope).lift = codomainType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      codomainType]
    exact Ty.subst_identity codomainType
  have bodyRawIdentity :
      bodyRaw.subst (@Subst.identity level scope).forRaw.lift = bodyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) bodyRaw]
    exact RawTerm.subst_identity bodyRaw
  exact Term.lamPi_HEq_congr
    (Ty.subst_identity domainType)
    codomainIdentity
    bodyRawIdentity
    bodyHEq

/-- Path lambda case for ordinary identity substitution.

The recursive premise is intentionally stated for the lifted interval
identity substitution, matching the actual `Term.subst` binder arm. -/
theorem Term.subst_identity_pathLam_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyHEq :
      HEq (Term.subst ((TermSubst.identity context).lift Ty.interval) body)
        body) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
          body))
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
        body) := by
  simp only [Term.subst]
  have bodyRawIdentity :
      bodyRaw.subst (@Subst.identity level scope).forRaw.lift = bodyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) bodyRaw]
    exact RawTerm.subst_identity bodyRaw
  have bodyCastHEq :
      HEq
        ((Ty.weaken_subst_commute Subst.identity carrierType) ▸
          Term.subst ((TermSubst.identity context).lift Ty.interval) body)
        body :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute Subst.identity carrierType)
        (Term.subst ((TermSubst.identity context).lift Ty.interval) body))
      bodyHEq
  exact Term.pathLam_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity carrierType)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    bodyRawIdentity
    bodyCastHEq

/-- Boolean true case for ordinary identity substitution. -/
theorem Term.subst_identity_boolTrue_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolTrue (context := context)))
      (Term.boolTrue (context := context)) := by
  rfl

/-- Boolean false case for ordinary identity substitution. -/
theorem Term.subst_identity_boolFalse_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolFalse (context := context)))
      (Term.boolFalse (context := context)) := by
  rfl

/-- Natural zero case for ordinary identity substitution. -/
theorem Term.subst_identity_natZero_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natZero (context := context)))
      (Term.natZero (context := context)) := by
  rfl

/-- Left interval endpoint case for ordinary identity substitution. -/
theorem Term.subst_identity_interval0_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.interval0 (context := context)))
      (Term.interval0 (context := context)) := by
  rfl

/-- Right interval endpoint case for ordinary identity substitution. -/
theorem Term.subst_identity_interval1_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.interval1 (context := context)))
      (Term.interval1 (context := context)) := by
  rfl

/-- Empty list case for ordinary identity substitution. -/
theorem Term.subst_identity_listNil_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listNil (context := context) (elementType := elementType)))
      (Term.listNil (context := context) (elementType := elementType)) := by
  simp only [Term.subst]
  exact Term.listNil_HEq_congr (Ty.subst_identity elementType)

/-- Empty option case for ordinary identity substitution. -/
theorem Term.subst_identity_optionNone_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionNone (context := context) (elementType := elementType)))
      (Term.optionNone (context := context) (elementType := elementType)) := by
  simp only [Term.subst]
  exact Term.optionNone_HEq_congr (Ty.subst_identity elementType)

/-! ## Recursive value cases -/

/-- Natural successor case for ordinary identity substitution. -/
theorem Term.subst_identity_natSucc_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (predecessorHEq :
      HEq (Term.subst (TermSubst.identity context) predecessor)
        predecessor) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natSucc predecessor))
      (Term.natSucc predecessor) := by
  simp only [Term.subst]
  exact Term.natSucc_HEq_congr
    (RawTerm.subst_identity predecessorRaw) predecessorHEq

/-- List cons case for ordinary identity substitution. -/
theorem Term.subst_identity_listCons_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headHEq :
      HEq (Term.subst (TermSubst.identity context) headTerm)
        headTerm)
    (tailHEq :
      HEq (Term.subst (TermSubst.identity context) tailTerm)
        tailTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listCons headTerm tailTerm))
      (Term.listCons headTerm tailTerm) := by
  simp only [Term.subst]
  exact Term.listCons_HEq_congr
    (Ty.subst_identity elementType)
    (RawTerm.subst_identity headRaw)
    (RawTerm.subst_identity tailRaw)
    headHEq tailHEq

/-- Option some case for ordinary identity substitution. -/
theorem Term.subst_identity_optionSome_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (valueHEq :
      HEq (Term.subst (TermSubst.identity context) valueTerm)
        valueTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionSome valueTerm))
      (Term.optionSome valueTerm) := by
  simp only [Term.subst]
  exact Term.optionSome_HEq_congr
    (Ty.subst_identity elementType)
    (RawTerm.subst_identity valueRaw)
    valueHEq

/-- Either-left injection case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherInl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (valueHEq :
      HEq (Term.subst (TermSubst.identity context) valueTerm)
        valueTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherInl (rightType := rightType) valueTerm))
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  simp only [Term.subst]
  exact Term.eitherInl_HEq_congr
    (Ty.subst_identity leftType)
    (Ty.subst_identity rightType)
    (RawTerm.subst_identity valueRaw)
    valueHEq

/-- Either-right injection case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherInr_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (valueHEq :
      HEq (Term.subst (TermSubst.identity context) valueTerm)
        valueTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherInr (leftType := leftType) valueTerm))
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  simp only [Term.subst]
  exact Term.eitherInr_HEq_congr
    (Ty.subst_identity leftType)
    (Ty.subst_identity rightType)
    (RawTerm.subst_identity valueRaw)
    valueHEq

/-- Interval negation case for ordinary identity substitution. -/
theorem Term.subst_identity_intervalOpp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerValue)
        innerValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.intervalOpp innerValue))
      (Term.intervalOpp innerValue) := by
  simp only [Term.subst]
  exact Term.intervalOpp_HEq_congr
    (RawTerm.subst_identity innerRaw) innerHEq

/-- Interval meet case for ordinary identity substitution. -/
theorem Term.subst_identity_intervalMeet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst (TermSubst.identity context) leftValue)
        leftValue)
    (rightHEq :
      HEq (Term.subst (TermSubst.identity context) rightValue)
        rightValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.intervalMeet leftValue rightValue))
      (Term.intervalMeet leftValue rightValue) := by
  simp only [Term.subst]
  exact Term.intervalMeet_HEq_congr
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)
    leftHEq rightHEq

/-- Interval join case for ordinary identity substitution. -/
theorem Term.subst_identity_intervalJoin_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst (TermSubst.identity context) leftValue)
        leftValue)
    (rightHEq :
      HEq (Term.subst (TermSubst.identity context) rightValue)
        rightValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.intervalJoin leftValue rightValue))
      (Term.intervalJoin leftValue rightValue) := by
  simp only [Term.subst]
  exact Term.intervalJoin_HEq_congr
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)
    leftHEq rightHEq

/-- Modal introduction wrapper case for ordinary identity substitution. -/
theorem Term.subst_identity_modIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerTerm)
        innerTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.modIntro innerTerm))
      (Term.modIntro innerTerm) := by
  simp only [Term.subst]
  exact Term.modIntro_HEq_congr
    (Ty.subst_identity innerType)
    (RawTerm.subst_identity innerRaw)
    innerHEq

/-- Modal elimination wrapper case for ordinary identity substitution. -/
theorem Term.subst_identity_modElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerTerm)
        innerTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.modElim innerTerm))
      (Term.modElim innerTerm) := by
  simp only [Term.subst]
  exact Term.modElim_HEq_congr
    (Ty.subst_identity innerType)
    (RawTerm.subst_identity innerRaw)
    innerHEq

/-- Modal subsumption wrapper case for ordinary identity substitution. -/
theorem Term.subst_identity_subsume_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerTerm)
        innerTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.subsume innerTerm))
      (Term.subsume innerTerm) := by
  simp only [Term.subst]
  exact Term.subsume_HEq_congr
    (Ty.subst_identity innerType)
    (RawTerm.subst_identity innerRaw)
    innerHEq

/-! ## Non-dependent eliminator cases -/

/-- Application case for ordinary identity substitution. -/
theorem Term.subst_identity_app_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionHEq :
      HEq (Term.subst (TermSubst.identity context) functionTerm)
        functionTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.app functionTerm argumentTerm))
      (Term.app functionTerm argumentTerm) := by
  simp only [Term.subst]
  exact Term.app_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (RawTerm.subst_identity functionRaw)
    (RawTerm.subst_identity argumentRaw)
    functionHEq argumentHEq

/-- Dependent function application case for ordinary identity substitution. -/
theorem Term.subst_identity_appPi_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionHEq :
      HEq (Term.subst (TermSubst.identity context) functionTerm)
        functionTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.appPi functionTerm argumentTerm))
      (Term.appPi functionTerm argumentTerm) := by
  simp only [Term.subst]
  have codomainIdentity :
      codomainType.subst (@Subst.identity level scope).lift = codomainType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      codomainType]
    exact Ty.subst_identity codomainType
  have appPiWithoutCastHEq :
      HEq
        (Term.appPi
          (Term.subst (TermSubst.identity context) functionTerm)
          (Term.subst (TermSubst.identity context) argumentTerm))
        (Term.appPi functionTerm argumentTerm) :=
    Term.appPi_HEq_congr
      (Ty.subst_identity domainType)
      codomainIdentity
      (RawTerm.subst_identity functionRaw)
      (RawTerm.subst_identity argumentRaw)
      functionHEq argumentHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute codomainType domainType argumentRaw
          Subst.identity).symm ▸
          Term.appPi
            (Term.subst (TermSubst.identity context) functionTerm)
            (Term.subst (TermSubst.identity context) argumentTerm))
        (Term.appPi
          (Term.subst (TermSubst.identity context) functionTerm)
          (Term.subst (TermSubst.identity context) argumentTerm)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute codomainType domainType argumentRaw
        Subst.identity).symm
      (Term.appPi
        (Term.subst (TermSubst.identity context) functionTerm)
        (Term.subst (TermSubst.identity context) argumentTerm))
  exact HEq.trans resultCastHEq appPiWithoutCastHEq

/-- Sigma pair introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_pair_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw)
    (firstHEq :
      HEq (Term.subst (TermSubst.identity context) firstValue) firstValue)
    (secondHEq :
      HEq (Term.subst (TermSubst.identity context) secondValue)
        secondValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.pair (secondType := secondType) firstValue secondValue))
      (Term.pair (secondType := secondType) firstValue secondValue) := by
  simp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst (@Subst.identity level scope).lift = secondType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      secondType]
    exact Ty.subst_identity secondType
  have secondCastHEq :
      HEq
        ((Ty.subst0_subst_commute secondType firstType firstRaw
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) secondValue)
        secondValue :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute secondType firstType firstRaw
          Subst.identity)
        (Term.subst (TermSubst.identity context) secondValue))
      secondHEq
  exact Term.pair_HEq_congr
    (Ty.subst_identity firstType)
    secondTypeIdentity
    (RawTerm.subst_identity firstRaw)
    (RawTerm.subst_identity secondRaw)
    firstHEq secondCastHEq

/-- Sigma first projection case for ordinary identity substitution. -/
theorem Term.subst_identity_fst_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq (Term.subst (TermSubst.identity context) pairTerm) pairTerm) :
    HEq
      (Term.subst (TermSubst.identity context) (Term.fst pairTerm))
      (Term.fst pairTerm) := by
  simp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst (@Subst.identity level scope).lift = secondType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      secondType]
    exact Ty.subst_identity secondType
  exact Term.fst_HEq_congr
    (Ty.subst_identity firstType)
    secondTypeIdentity
    (RawTerm.subst_identity pairRaw)
    pairHEq

/-- Sigma second projection case for ordinary identity substitution. -/
theorem Term.subst_identity_snd_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq (Term.subst (TermSubst.identity context) pairTerm) pairTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.snd (secondType := secondType) pairTerm))
      (Term.snd (secondType := secondType) pairTerm) := by
  simp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst (@Subst.identity level scope).lift = secondType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      secondType]
    exact Ty.subst_identity secondType
  have sndWithoutCastHEq :
      HEq
        (Term.snd
          (Term.subst (TermSubst.identity context) pairTerm))
        (Term.snd (secondType := secondType) pairTerm) :=
    Term.snd_HEq_congr
      (Ty.subst_identity firstType)
      secondTypeIdentity
      (RawTerm.subst_identity pairRaw)
      pairHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute secondType firstType
          (RawTerm.fst pairRaw) Subst.identity).symm ▸
          Term.snd (Term.subst (TermSubst.identity context) pairTerm))
        (Term.snd (Term.subst (TermSubst.identity context) pairTerm)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute secondType firstType
        (RawTerm.fst pairRaw) Subst.identity).symm
      (Term.snd (Term.subst (TermSubst.identity context) pairTerm))
  exact HEq.trans resultCastHEq sndWithoutCastHEq

/-- Dependent boolean eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_boolElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee) scrutinee)
    (thenHEq :
      HEq (Term.subst (TermSubst.identity context) thenBranch) thenBranch)
    (elseHEq :
      HEq (Term.subst (TermSubst.identity context) elseBranch) elseBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolElim scrutinee thenBranch elseBranch))
      (Term.boolElim scrutinee thenBranch elseBranch) := by
  simp only [Term.subst]
  have motiveIdentity :
      motiveType.subst (@Subst.identity level scope).lift = motiveType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      motiveType]
    exact Ty.subst_identity motiveType
  have thenCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) thenBranch)
        thenBranch :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          Subst.identity)
        (Term.subst (TermSubst.identity context) thenBranch))
      thenHEq
  have elseCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) elseBranch)
        elseBranch :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          Subst.identity)
        (Term.subst (TermSubst.identity context) elseBranch))
      elseHEq
  have boolElimWithoutCastHEq :
      HEq
        (Term.boolElim
          (motiveType := motiveType.subst (@Subst.identity level scope).lift)
          (Term.subst (TermSubst.identity context) scrutinee)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) thenBranch)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) elseBranch))
        (Term.boolElim scrutinee thenBranch elseBranch) :=
    Term.boolElim_HEq_congr
      motiveIdentity
      (RawTerm.subst_identity scrutineeRaw)
      (RawTerm.subst_identity thenRaw)
      (RawTerm.subst_identity elseRaw)
      scrutineeHEq thenCastHEq elseCastHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw
          Subst.identity).symm ▸
          Term.boolElim
            (motiveType := motiveType.subst
              (@Subst.identity level scope).lift)
            (Term.subst (TermSubst.identity context) scrutinee)
            ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
              Subst.identity) ▸
              Term.subst (TermSubst.identity context) thenBranch)
            ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
              Subst.identity) ▸
              Term.subst (TermSubst.identity context) elseBranch))
        (Term.boolElim
          (motiveType := motiveType.subst (@Subst.identity level scope).lift)
          (Term.subst (TermSubst.identity context) scrutinee)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) thenBranch)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) elseBranch)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw
        Subst.identity).symm
      (Term.boolElim
        (motiveType := motiveType.subst (@Subst.identity level scope).lift)
        (Term.subst (TermSubst.identity context) scrutinee)
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) thenBranch)
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) elseBranch))
  exact HEq.trans resultCastHEq boolElimWithoutCastHEq

/-- Natural eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_natElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (zeroHEq :
      HEq (Term.subst (TermSubst.identity context) zeroBranch)
        zeroBranch)
    (succHEq :
      HEq (Term.subst (TermSubst.identity context) succBranch)
        succBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natElim scrutinee zeroBranch succBranch))
      (Term.natElim scrutinee zeroBranch succBranch) := by
  simp only [Term.subst]
  exact Term.natElim_HEq_congr
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity zeroRaw)
    (RawTerm.subst_identity succRaw)
    scrutineeHEq zeroHEq succHEq

/-- Primitive natural recursor case for ordinary identity substitution. -/
theorem Term.subst_identity_natRec_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (zeroHEq :
      HEq (Term.subst (TermSubst.identity context) zeroBranch)
        zeroBranch)
    (succHEq :
      HEq (Term.subst (TermSubst.identity context) succBranch)
        succBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natRec scrutinee zeroBranch succBranch))
      (Term.natRec scrutinee zeroBranch succBranch) := by
  simp only [Term.subst]
  exact Term.natRec_HEq_congr
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity zeroRaw)
    (RawTerm.subst_identity succRaw)
    scrutineeHEq zeroHEq succHEq

/-- List eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_listElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context
      (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
      consRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (nilHEq :
      HEq (Term.subst (TermSubst.identity context) nilBranch)
        nilBranch)
    (consHEq :
      HEq (Term.subst (TermSubst.identity context) consBranch)
        consBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listElim scrutinee nilBranch consBranch))
      (Term.listElim scrutinee nilBranch consBranch) := by
  simp only [Term.subst]
  exact Term.listElim_HEq_congr
    (Ty.subst_identity elementType)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity nilRaw)
    (RawTerm.subst_identity consRaw)
    scrutineeHEq nilHEq consHEq

/-- Option match case for ordinary identity substitution. -/
theorem Term.subst_identity_optionMatch_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (noneHEq :
      HEq (Term.subst (TermSubst.identity context) noneBranch)
        noneBranch)
    (someHEq :
      HEq (Term.subst (TermSubst.identity context) someBranch)
        someBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionMatch scrutinee noneBranch someBranch))
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  simp only [Term.subst]
  exact Term.optionMatch_HEq_congr
    (Ty.subst_identity elementType)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity noneRaw)
    (RawTerm.subst_identity someRaw)
    scrutineeHEq noneHEq someHEq

/-- Either match case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherMatch_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (leftHEq :
      HEq (Term.subst (TermSubst.identity context) leftBranch)
        leftBranch)
    (rightHEq :
      HEq (Term.subst (TermSubst.identity context) rightBranch)
        rightBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherMatch scrutinee leftBranch rightBranch))
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  simp only [Term.subst]
  exact Term.eitherMatch_HEq_congr
    (Ty.subst_identity leftType)
    (Ty.subst_identity rightType)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)
    scrutineeHEq leftHEq rightHEq

/-! ## Equality-family cases -/

/-- Identity reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_refl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.refl (context := context) carrier rawWitness))
      (Term.refl (context := context) carrier rawWitness) := by
  simp only [Term.subst]
  exact Term.refl_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity rawWitness)

/-- Identity eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_idJ_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst (TermSubst.identity context) baseCase)
        baseCase)
    (witnessHEq :
      HEq (Term.subst (TermSubst.identity context) witness)
        witness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idJ baseCase witness))
      (Term.idJ baseCase witness) := by
  simp only [Term.subst]
  exact Term.idJ_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity witnessRaw)
    baseCaseHEq witnessHEq

/-- Observational equality reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_oeqRefl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.oeqRefl (context := context) carrier rawWitness))
      (Term.oeqRefl (context := context) carrier rawWitness) := by
  simp only [Term.subst]
  exact Term.oeqRefl_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity rawWitness)

/-- Observational equality eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_oeqJ_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst (TermSubst.identity context) baseCase)
        baseCase)
    (witnessHEq :
      HEq (Term.subst (TermSubst.identity context) witness)
        witness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.oeqJ baseCase witness))
      (Term.oeqJ baseCase witness) := by
  simp only [Term.subst]
  exact Term.oeqJ_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity witnessRaw)
    baseCaseHEq witnessHEq

/-- Strict identity reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_idStrictRefl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idStrictRefl (context := context) modeIsStrict carrier
          rawWitness))
      (Term.idStrictRefl (context := context) modeIsStrict carrier
        rawWitness) := by
  simp only [Term.subst]
  exact Term.idStrictRefl_HEq_congr
    modeIsStrict
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity rawWitness)

/-- Strict identity eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_idStrictRec_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context
      (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst (TermSubst.identity context) baseCase)
        baseCase)
    (witnessHEq :
      HEq (Term.subst (TermSubst.identity context) witness)
        witness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idStrictRec modeIsStrict baseCase witness))
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  simp only [Term.subst]
  exact Term.idStrictRec_HEq_congr
    modeIsStrict
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity witnessRaw)
    baseCaseHEq witnessHEq

/-! ## Structural advanced cases -/

/-- Path application case for ordinary identity substitution. -/
theorem Term.subst_identity_pathApp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathHEq :
      HEq (Term.subst (TermSubst.identity context) pathTerm)
        pathTerm)
    (intervalHEq :
      HEq (Term.subst (TermSubst.identity context) intervalTerm)
        intervalTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.pathApp modeIsUnivalent pathTerm intervalTerm))
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  simp only [Term.subst]
  exact Term.pathApp_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity carrierType)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (RawTerm.subst_identity pathRaw)
    (RawTerm.subst_identity intervalRaw)
    pathHEq intervalHEq

/-- Glue introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_glueIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw)
    (baseHEq :
      HEq (Term.subst (TermSubst.identity context) baseValue)
        baseValue)
    (partialHEq :
      HEq (Term.subst (TermSubst.identity context) partialValue)
        partialValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue))
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) := by
  simp only [Term.subst]
  exact Term.glueIntro_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity baseType)
    (RawTerm.subst_identity boundaryWitness)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity partialRaw)
    baseHEq partialHEq

/-- Glue elimination case for ordinary identity substitution. -/
theorem Term.subst_identity_glueElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedHEq :
      HEq (Term.subst (TermSubst.identity context) gluedValue)
        gluedValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.glueElim modeIsUnivalent gluedValue))
      (Term.glueElim modeIsUnivalent gluedValue) := by
  simp only [Term.subst]
  exact Term.glueElim_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity baseType)
    (RawTerm.subst_identity boundaryWitness)
    (RawTerm.subst_identity gluedRaw)
    gluedHEq

/-- Homogeneous composition case for ordinary identity substitution. -/
theorem Term.subst_identity_hcomp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesHEq :
      HEq (Term.subst (TermSubst.identity context) sidesValue)
        sidesValue)
    (capHEq :
      HEq (Term.subst (TermSubst.identity context) capValue)
        capValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.hcomp modeIsUnivalent sidesValue capValue))
      (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  simp only [Term.subst]
  exact Term.hcomp_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity carrierType)
    (RawTerm.subst_identity sidesRaw)
    (RawTerm.subst_identity capRaw)
    sidesHEq capHEq

/-- Record introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_recordIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw)
    (firstFieldHEq :
      HEq (Term.subst (TermSubst.identity context) firstField)
        firstField) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.recordIntro firstField))
      (Term.recordIntro firstField) := by
  simp only [Term.subst]
  exact Term.recordIntro_HEq_congr
    (Ty.subst_identity singleFieldType)
    (RawTerm.subst_identity firstRaw)
    firstFieldHEq

/-- Record projection case for ordinary identity substitution. -/
theorem Term.subst_identity_recordProj_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordHEq :
      HEq (Term.subst (TermSubst.identity context) recordValue)
        recordValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.recordProj recordValue))
      (Term.recordProj recordValue) := by
  simp only [Term.subst]
  exact Term.recordProj_HEq_congr
    (Ty.subst_identity singleFieldType)
    (RawTerm.subst_identity recordRaw)
    recordHEq

/-- Refinement elimination case for ordinary identity substitution. -/
theorem Term.subst_identity_refineElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedHEq :
      HEq (Term.subst (TermSubst.identity context) refinedValue)
        refinedValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.refineElim refinedValue))
      (Term.refineElim refinedValue) := by
  simp only [Term.subst]
  exact Term.refineElim_HEq_congr
    (Ty.subst_identity baseType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) predicate]
      exact RawTerm.subst_identity predicate)
    (RawTerm.subst_identity refinedRaw)
    refinedHEq

/-- Codata unfold case for ordinary identity substitution. -/
theorem Term.subst_identity_codataUnfold_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (initialStateHEq :
      HEq (Term.subst (TermSubst.identity context) initialState)
        initialState)
    (transitionHEq :
      HEq (Term.subst (TermSubst.identity context) transition)
        transition) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.codataUnfold initialState transition))
      (Term.codataUnfold initialState transition) := by
  simp only [Term.subst]
  exact Term.codataUnfold_HEq_congr
    (Ty.subst_identity stateType)
    (Ty.subst_identity outputType)
    (RawTerm.subst_identity stateRaw)
    (RawTerm.subst_identity transitionRaw)
    initialStateHEq transitionHEq

/-- Codata destructor case for ordinary identity substitution. -/
theorem Term.subst_identity_codataDest_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataHEq :
      HEq (Term.subst (TermSubst.identity context) codataValue)
        codataValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.codataDest codataValue))
      (Term.codataDest codataValue) := by
  simp only [Term.subst]
  exact Term.codataDest_HEq_congr
    (Ty.subst_identity stateType)
    (Ty.subst_identity outputType)
    (RawTerm.subst_identity codataRaw)
    codataHEq

/-- Session send case for ordinary identity substitution. -/
theorem Term.subst_identity_sessionSend_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw)
    (channelHEq :
      HEq (Term.subst (TermSubst.identity context) channel)
        channel)
    (payloadHEq :
      HEq (Term.subst (TermSubst.identity context) payload)
        payload) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sessionSend protocolStep channel payload))
      (Term.sessionSend protocolStep channel payload) := by
  simp only [Term.subst]
  exact Term.sessionSend_HEq_congr
    (RawTerm.subst_identity protocolStep)
    (Ty.subst_identity payloadType)
    (RawTerm.subst_identity channelRaw)
    (RawTerm.subst_identity payloadRaw)
    channelHEq payloadHEq

/-- Session receive case for ordinary identity substitution. -/
theorem Term.subst_identity_sessionRecv_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelHEq :
      HEq (Term.subst (TermSubst.identity context) channel)
        channel) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sessionRecv channel))
      (Term.sessionRecv channel) := by
  simp only [Term.subst]
  exact Term.sessionRecv_HEq_congr
    (RawTerm.subst_identity protocolStep)
    (RawTerm.subst_identity channelRaw)
    channelHEq

/-- Direct effect-performance congruence with propositionally equal
operation carriers, scoped to ordinary identity-substitution erasure. -/
private theorem Term.effectPerform_direct_identity_carrier_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (effectLabel : Effects.EffectLabel)
    (rowMember : Effects.EffectRow.Member effectLabel effectRow)
    {argumentCarrier1 argumentCarrier2 resultCarrier1 resultCarrier2 :
      Ty level scope}
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 :
      RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (argumentCarrierEq : argumentCarrier1 = argumentCarrier2)
    (resultCarrierEq : resultCarrier1 = resultCarrier2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context (Ty.effect argumentCarrier1 effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context (Ty.effect argumentCarrier2 effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 : Term context argumentCarrier1 argumentsRaw1}
    {arguments2 : Term context argumentCarrier2 argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow
        { effectLabel := effectLabel
          argumentCarrier := argumentCarrier1
          resultCarrier := resultCarrier1 }
        (Effects.CanPerform.direct rowMember) operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow
        { effectLabel := effectLabel
          argumentCarrier := argumentCarrier2
          resultCarrier := resultCarrier2 }
        (Effects.CanPerform.direct rowMember) operationTag2 arguments2) := by
  subst effectTagEq
  subst argumentCarrierEq
  subst resultCarrierEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

/-- Read-via-write effect-performance congruence with propositionally equal
operation carriers, scoped to ordinary identity-substitution erasure. -/
private theorem Term.effectPerform_readViaWrite_identity_carrier_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (rowMember : Effects.EffectRow.Member Effects.EffectLabel.write
      effectRow)
    {argumentCarrier1 argumentCarrier2 resultCarrier1 resultCarrier2 :
      Ty level scope}
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 :
      RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (argumentCarrierEq : argumentCarrier1 = argumentCarrier2)
    (resultCarrierEq : resultCarrier1 = resultCarrier2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context (Ty.effect argumentCarrier1 effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context (Ty.effect argumentCarrier2 effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 : Term context argumentCarrier1 argumentsRaw1}
    {arguments2 : Term context argumentCarrier2 argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier := argumentCarrier1
          resultCarrier := resultCarrier1 }
        (Effects.CanPerform.readViaWrite argumentCarrier1
          resultCarrier1 rowMember)
        operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier := argumentCarrier2
          resultCarrier := resultCarrier2 }
        (Effects.CanPerform.readViaWrite argumentCarrier2
          resultCarrier2 rowMember)
        operationTag2 arguments2) := by
  subst effectTagEq
  subst argumentCarrierEq
  subst resultCarrierEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

/-- Effect-performance case for ordinary identity substitution. -/
theorem Term.subst_identity_effectPerform_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {effectTag : RawTerm scope}
    {effectRow : Effects.EffectRow}
    {operationSignature : Effects.OperationSignature (Ty level scope)}
    {canPerformOperation :
      Effects.CanPerform effectRow operationSignature}
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw)
    (operationTagHEq :
      HEq (Term.subst (TermSubst.identity context) operationTag)
        operationTag)
    (argumentsHEq :
      HEq (Term.subst (TermSubst.identity context) arguments)
        arguments) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments))
      (Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments) := by
  simp only [Term.subst]
  cases operationSignature with
  | mk effectLabel argumentCarrier resultCarrier =>
    cases canPerformOperation with
    | direct rowMember =>
      simp only [Effects.OperationSignature.map]
      exact Term.effectPerform_direct_identity_carrier_HEq_congr
        effectRow effectLabel rowMember
        (RawTerm.subst_identity effectTag)
        (Ty.subst_identity argumentCarrier)
        (Ty.subst_identity resultCarrier)
        (RawTerm.subst_identity operationRaw)
        (RawTerm.subst_identity argumentsRaw)
        operationTagHEq
        argumentsHEq
    | readViaWrite argumentCarrier resultCarrier rowMember =>
      simp only [Effects.OperationSignature.map]
      exact Term.effectPerform_readViaWrite_identity_carrier_HEq_congr
        effectRow rowMember
        (RawTerm.subst_identity effectTag)
        (Ty.subst_identity argumentCarrier)
        (Ty.subst_identity resultCarrier)
        (RawTerm.subst_identity operationRaw)
        (RawTerm.subst_identity argumentsRaw)
        operationTagHEq
        argumentsHEq

/-- Universe cumulativity marker case for ordinary identity substitution. -/
theorem Term.subst_identity_cumulUp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeHEq :
      HEq (Term.subst (TermSubst.identity context) typeCode)
        typeCode) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.cumulUp lowerLevel higherLevel cumulMonotone
          levelLeLow levelLeHigh typeCode))
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) := by
  simp only [Term.subst]
  exact Term.cumulUp_HEq_congr
    (RawTerm.subst_identity codeRaw)
    typeCodeHEq

/-- Equivalence application case for ordinary identity substitution. -/
theorem Term.subst_identity_equivApp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw)
    (equivHEq :
      HEq (Term.subst (TermSubst.identity context) equivTerm)
        equivTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivApp equivTerm argumentTerm))
      (Term.equivApp equivTerm argumentTerm) := by
  simp only [Term.subst]
  exact Term.equivApp_HEq_congr
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity equivRaw)
    (RawTerm.subst_identity argumentRaw)
    equivHEq argumentHEq

/-- Univalence beta application case for ordinary identity substitution. -/
theorem Term.subst_identity_equivApply_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw)
    (equivHEq :
      HEq (Term.subst (TermSubst.identity context) equivTerm)
        equivTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivApply equivTerm argumentTerm))
      (Term.equivApply equivTerm argumentTerm) := by
  simp only [Term.subst]
  exact Term.equivApply_HEq_congr
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity equivRaw)
    (RawTerm.subst_identity argumentRaw)
    equivHEq argumentHEq

/-! ## Universe code cases -/

/-- Universe-code case for ordinary identity substitution. -/
theorem Term.subst_identity_universeCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.universeCode (context := context) innerLevel outerLevel
          cumulOk levelLe))
      (Term.universeCode (context := context) innerLevel outerLevel
        cumulOk levelLe) := by
  rfl

/-- Arrow type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_arrowCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.arrowCode (context := context) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.arrowCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.subst]
  exact Term.arrowCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity domainCodeRaw)
    (RawTerm.subst_identity codomainCodeRaw)

/-- Pi type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_piTyCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.piTyCode (context := context) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.piTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.subst]
  exact Term.piTyCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity domainCodeRaw)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope)
        codomainCodeRaw]
      exact RawTerm.subst_identity codomainCodeRaw)

/-- Sigma type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_sigmaTyCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sigmaTyCode (context := context) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.sigmaTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.subst]
  exact Term.sigmaTyCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity domainCodeRaw)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope)
        codomainCodeRaw]
      exact RawTerm.subst_identity codomainCodeRaw)

/-- Product type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_productCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.productCode (context := context) outerLevel levelLe
          firstCodeRaw secondCodeRaw))
      (Term.productCode (context := context) outerLevel levelLe
        firstCodeRaw secondCodeRaw) := by
  simp only [Term.subst]
  exact Term.productCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity firstCodeRaw)
    (RawTerm.subst_identity secondCodeRaw)

/-- Sum type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_sumCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sumCode (context := context) outerLevel levelLe
          leftCodeRaw rightCodeRaw))
      (Term.sumCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  simp only [Term.subst]
  exact Term.sumCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity leftCodeRaw)
    (RawTerm.subst_identity rightCodeRaw)

/-- List type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_listCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listCode (context := context) outerLevel levelLe
          elementCodeRaw))
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw) := by
  simp only [Term.subst]
  exact Term.listCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity elementCodeRaw)

/-- Option type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_optionCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionCode (context := context) outerLevel levelLe
          elementCodeRaw))
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw) := by
  simp only [Term.subst]
  exact Term.optionCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity elementCodeRaw)

/-- Either type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherCode (context := context) outerLevel levelLe
          leftCodeRaw rightCodeRaw))
      (Term.eitherCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  simp only [Term.subst]
  exact Term.eitherCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity leftCodeRaw)
    (RawTerm.subst_identity rightCodeRaw)

/-- Identity type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_idCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idCode (context := context) outerLevel levelLe
          typeCodeRaw leftRaw rightRaw))
      (Term.idCode (context := context) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw) := by
  simp only [Term.subst]
  exact Term.idCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity typeCodeRaw)
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)

/-- Equivalence type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_equivCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivCode (context := context) outerLevel levelLe
          leftTypeCodeRaw rightTypeCodeRaw))
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) := by
  simp only [Term.subst]
  exact Term.equivCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity leftTypeCodeRaw)
    (RawTerm.subst_identity rightTypeCodeRaw)

/-! ## HoTT canonical value cases -/

/-- Canonical identity equivalence case for ordinary identity substitution. -/
theorem Term.subst_identity_equivReflId_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivReflId (context := context) carrier))
      (Term.equivReflId (context := context) carrier) := by
  simp only [Term.subst]
  exact Term.equivReflId_HEq_congr (Ty.subst_identity carrier)

/-- Id-typed identity equivalence case for ordinary identity substitution. -/
theorem Term.subst_identity_equivReflIdAtId_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivReflIdAtId (context := context) innerLevel
          innerLevelLt carrier carrierRaw))
      (Term.equivReflIdAtId (context := context) innerLevel
        innerLevelLt carrier carrierRaw) := by
  simp only [Term.subst]
  exact Term.equivReflIdAtId_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity carrierRaw)

/-- Id-typed funext witness case for ordinary identity substitution. -/
theorem Term.subst_identity_funextReflAtId_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.funextReflAtId (context := context)
          domainType codomainType applyRaw))
      (Term.funextReflAtId (context := context)
        domainType codomainType applyRaw) := by
  simp only [Term.subst]
  exact Term.funextReflAtId_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) applyRaw]
      exact RawTerm.subst_identity applyRaw)

/-- Canonical funext reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_funextRefl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.funextRefl (context := context)
          domainType codomainType applyRaw))
      (Term.funextRefl (context := context)
        domainType codomainType applyRaw) := by
  simp only [Term.subst]
  have applyRawIdentity :
      applyRaw.subst (@Subst.identity level scope).forRaw.lift =
        applyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) applyRaw]
    exact RawTerm.subst_identity applyRaw
  have funextWithoutCastHEq :
      HEq
        (Term.funextRefl
          (context := context)
          (domainType.subst Subst.identity)
          (codomainType.subst Subst.identity)
          (applyRaw.subst (@Subst.identity level scope).forRaw.lift))
        (Term.funextRefl (context := context)
          domainType codomainType applyRaw) :=
    Term.funextRefl_HEq_congr
      (Ty.subst_identity domainType)
      (Ty.subst_identity codomainType)
      applyRawIdentity
  have resultCastHEq :
      HEq
        ((funextReflType_subst Subst.identity
          domainType codomainType applyRaw).symm ▸
          Term.funextRefl
            (context := context)
            (domainType.subst Subst.identity)
            (codomainType.subst Subst.identity)
            (applyRaw.subst
              (@Subst.identity level scope).forRaw.lift))
        (Term.funextRefl
          (context := context)
          (domainType.subst Subst.identity)
          (codomainType.subst Subst.identity)
          (applyRaw.subst
            (@Subst.identity level scope).forRaw.lift)) := by
    exact Term.type_eq_cast_heq
      (funextReflType_subst Subst.identity
        domainType codomainType applyRaw).symm
      (Term.funextRefl
        (context := context)
        (domainType.subst Subst.identity)
        (codomainType.subst Subst.identity)
        (applyRaw.subst
          (@Subst.identity level scope).forRaw.lift))
  exact HEq.trans resultCastHEq funextWithoutCastHEq

/-- Observational funext case for ordinary identity substitution. -/
theorem Term.subst_identity_oeqFunext_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    (pointwiseProof :
      Term context
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseHEq :
      HEq (Term.subst (TermSubst.identity context) pointwiseProof)
        pointwiseProof) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.oeqFunext domainType codomainType leftFunctionRaw
          rightFunctionRaw pointwiseProof))
      (Term.oeqFunext domainType codomainType leftFunctionRaw
        rightFunctionRaw pointwiseProof) := by
  simp only [Term.subst]
  have pointwiseCastHEq :
      HEq
        ((oeqFunextPointwiseType_subst Subst.identity domainType codomainType
          leftFunctionRaw rightFunctionRaw) ▸
          Term.subst (TermSubst.identity context) pointwiseProof)
        pointwiseProof :=
    HEq.trans
      (Term.type_eq_cast_heq
        (oeqFunextPointwiseType_subst Subst.identity domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        (Term.subst (TermSubst.identity context) pointwiseProof))
      pointwiseHEq
  exact Term.oeqFunext_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (RawTerm.subst_identity leftFunctionRaw)
    (RawTerm.subst_identity rightFunctionRaw)
    (RawTerm.subst_identity pointwiseRaw)
    pointwiseCastHEq

/-- Cubical transport case for ordinary identity substitution. -/
theorem Term.subst_identity_transp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term context sourceType sourceRaw)
    (typePathHEq :
      HEq (Term.subst (TermSubst.identity context) typePath)
        typePath)
    (sourceValueHEq :
      HEq (Term.subst (TermSubst.identity context) sourceValue)
        sourceValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType sourceTypeRaw targetTypeRaw typePath
          sourceValue))
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw typePath
        sourceValue) := by
  simp only [Term.subst]
  exact Term.transp_HEq_congr
    modeIsUnivalent universeLevel universeLevelLt
    (Ty.subst_identity sourceType)
    (Ty.subst_identity targetType)
    (RawTerm.subst_identity sourceTypeRaw)
    (RawTerm.subst_identity targetTypeRaw)
    (RawTerm.subst_identity pathRaw)
    (RawTerm.subst_identity sourceRaw)
    typePathHEq sourceValueHEq

/-- Refinement introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_refineIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (baseValueHEq :
      HEq (Term.subst (TermSubst.identity context) baseValue)
        baseValue)
    (predicateProofHEq :
      HEq (Term.subst (TermSubst.identity context) predicateProof)
        predicateProof) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.refineIntro predicate baseValue predicateProof))
      (Term.refineIntro predicate baseValue predicateProof) := by
  simp only [Term.subst]
  exact Term.refineIntro_HEq_congr
    (Ty.subst_identity baseType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) predicate]
      exact RawTerm.subst_identity predicate)
    (RawTerm.subst_identity valueRaw)
    (RawTerm.subst_identity proofRaw)
    baseValueHEq predicateProofHEq

/-- Heterogeneous univalence introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_uaIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term context (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessHEq :
      HEq (Term.subst (TermSubst.identity context) equivWitness)
        equivWitness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
          equivWitness))
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness) := by
  simp only [Term.subst]
  exact Term.uaIntroHet_HEq_congr
    innerLevel innerLevelLt
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity carrierARaw)
    (RawTerm.subst_identity carrierBRaw)
    (RawTerm.subst_identity forwardRaw)
    (RawTerm.subst_identity backwardRaw)
    equivWitnessHEq

/-- Heterogeneous equivalence introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_equivIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardHEq :
      HEq (Term.subst (TermSubst.identity context) forward) forward)
    (backwardHEq :
      HEq (Term.subst (TermSubst.identity context) backward) backward)
    (leftInvHEq :
      HEq (Term.subst (TermSubst.identity context) leftInv) leftInv)
    (rightInvHEq :
      HEq (Term.subst (TermSubst.identity context) rightInv) rightInv) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivIntroHet forward backward leftInv rightInv))
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  simp only [Term.subst]
  have leftInvCastHEq :
      HEq
        ((equivIntroHetLeftInverseType_subst Subst.identity
          carrierA forwardRaw backwardRaw) ▸
          Term.subst (TermSubst.identity context) leftInv)
        leftInv :=
    HEq.trans
      (Term.type_eq_cast_heq
        (equivIntroHetLeftInverseType_subst Subst.identity
          carrierA forwardRaw backwardRaw)
        (Term.subst (TermSubst.identity context) leftInv))
      leftInvHEq
  have rightInvCastHEq :
      HEq
        ((equivIntroHetRightInverseType_subst Subst.identity
          carrierB forwardRaw backwardRaw) ▸
          Term.subst (TermSubst.identity context) rightInv)
        rightInv :=
    HEq.trans
      (Term.type_eq_cast_heq
        (equivIntroHetRightInverseType_subst Subst.identity
          carrierB forwardRaw backwardRaw)
        (Term.subst (TermSubst.identity context) rightInv))
      rightInvHEq
  exact Term.equivIntroHet_HEq_congr
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity forwardRaw)
    (RawTerm.subst_identity backwardRaw)
    (RawTerm.subst_identity leftInvRaw)
    (RawTerm.subst_identity rightInvRaw)
    forwardHEq backwardHEq leftInvCastHEq rightInvCastHEq

/-- Heterogeneous funext introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_funextIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.funextIntroHet (context := context)
          domainType codomainType applyARaw applyBRaw))
      (Term.funextIntroHet (context := context)
        domainType codomainType applyARaw applyBRaw) := by
  simp only [Term.subst]
  exact Term.funextIntroHet_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) applyARaw]
      exact RawTerm.subst_identity applyARaw)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) applyBRaw]
      exact RawTerm.subst_identity applyBRaw)

/-- Univalence beta extraction case for ordinary identity substitution. -/
theorem Term.subst_identity_uaToEquiv_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (proof :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofHEq :
      HEq (Term.subst (TermSubst.identity context) proof) proof) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
          leftTyRaw rightTyRaw proof))
      (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
        leftTyRaw rightTyRaw proof) := by
  simp only [Term.subst]
  exact Term.uaToEquiv_HEq_congr
    (Ty.subst_identity leftTy)
    (Ty.subst_identity rightTy)
    (RawTerm.subst_identity leftTyRaw)
    (RawTerm.subst_identity rightTyRaw)
    (RawTerm.subst_identity proofRaw)
    proofHEq

end LeanFX2
