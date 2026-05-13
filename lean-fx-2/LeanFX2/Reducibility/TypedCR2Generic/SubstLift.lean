import LeanFX2.Reducibility.TypedCR2Generic.SubstSingleton

/-! # LeanFX2.Reducibility.TypedCR2Generic.SubstLift

`ReducibleSubst.lift` SN projections plus identity-substitution
strong-normalization bridges (raw + typed).  Used by the
`Term.lam` fundamental theorem case to refine bodies through a
lifted identity substitution.

## Root status

Layer 3 metatheory leaf.  Fourth slice of `TypedCR2Generic`. -/

namespace LeanFX2

/-- **K12.20.U3.lift SN projection**: every entry of a lifted reducible
substitution is strongly normalizing.

This is the CR1 part of `ReducibleSubst.lift`, not the full theorem.
The fresh variable is SN by var-shape CR3; older positions are weakened
images of already-reducible substitution entries, so raw weakening
preserves their SN.  Compound `Reducible` closures remain the separate
world-monotone blocker tracked by #1944. -/
theorem ReducibleSubst.lift_isStronglyNormalizing
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substReducible : ReducibleSubst termSubst)
    (newSourceType : Ty level scope) :
    ∀ (position : Fin (scope + 1)),
      Term.isStronglyNormalizing
        ((termSubst.lift newSourceType) position) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          change RawTerm.isStronglyNormalizing
            (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)
          exact RawTerm.var_isStronglyNormalizing
            ⟨0, Nat.zero_lt_succ targetScope⟩
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
          change Term.isStronglyNormalizing
            ((Ty.weaken_subst_commute sigma
              (varType sourceCtx previousPosition)).symm ▸
                Term.weaken (newSourceType.subst sigma)
                  (termSubst previousPosition))
          exact Term.isStronglyNormalizing_weaken
            (newType := newSourceType.subst sigma)
            (Reducible.isStronglyNormalizing
              (substReducible previousPosition))

/-- **K12.20.U3.lift under renaming stability**: a renaming-stable
reducible substitution lifts under one binder.

This is the first full-reducibility version of `ReducibleSubst.lift`.
The extra stability premise is the honest Kripke/world monotonicity
needed by old variables: after lifting, successor positions are exactly
the old substitution entries weakened into the extended target context.
Fresh position zero is a neutral variable and is reducible by CR3. -/
theorem ReducibleSubst.lift_of_renamingStable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substIsStable : IsRenamingStableReducibleSubst termSubst)
    (newSourceType : Ty level scope) :
    ReducibleSubst (termSubst.lift newSourceType) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_commute sigma newSourceType)
            (Reducible.of_varShape
              ((newSourceType.subst sigma).weaken)
              (Term.var (context := targetCtx.cons (newSourceType.subst sigma))
                ⟨0, Nat.zero_lt_succ targetScope⟩))
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
          change Reducible
            ((varType sourceCtx previousPosition).weaken.subst sigma.lift)
            ((Ty.weaken_subst_commute sigma
              (varType sourceCtx previousPosition)).symm ▸
                Term.weaken (newSourceType.subst sigma)
                  (termSubst previousPosition))
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_commute sigma
              (varType sourceCtx previousPosition))
            (IsRenamingStableReducibleSubst.weaken_position
              substIsStable newSourceType previousPosition)

/-- **K12.27.M04 identity-substitution SN extraction**.

The identity-only M04 route often proves SN for the term after
`TermSubst.identity`, because all fundamental endpoints are stated in
the substitution-parametric shape.  This lemma erases that identity
substitution from the raw index. -/
theorem Term.strong_normalization_of_identity_subst
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    (identityIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity sourceCtx) sourceTerm)) :
    Term.isStronglyNormalizing sourceTerm := by
  change RawTerm.isStronglyNormalizing sourceRaw
  rw [← RawTerm.subst_identity sourceRaw]
  exact identityIsSN

/-- **K12.27.M04 identity-substitution SN extraction**.

The final strong-normalization corollary will apply the fundamental
theorem at `TermSubst.identity`, then erase the identity substitution
from the raw index.  This lemma packages only that last extraction
step: it does not assert the still-pending fundamental theorem. -/
theorem Reducible.strong_normalization_of_identity_reducible
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    (identityReducible :
    Reducible (sourceType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) sourceTerm)) :
    Term.isStronglyNormalizing sourceTerm := by
  have identitySubstIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity sourceCtx) sourceTerm) :=
    Reducible.isStronglyNormalizing identityReducible
  exact Term.strong_normalization_of_identity_subst sourceTerm
    identitySubstIsSN

/-- **K12.27 identity-lift raw bridge**.

For the identity-only M04 route, the lambda body IH is naturally
available under `TermSubst.identity (sourceCtx.cons domainType)`, while
`Term.subst` on a lambda uses `(TermSubst.identity sourceCtx).lift`.
At the raw level those substitutions agree: lifting identity under one
binder is pointwise identity. -/
theorem RawTerm.subst_identity_lift
    {level scope : Nat}
    (sourceRaw : RawTerm (scope + 1)) :
    sourceRaw.subst ((@Subst.identity level scope).forRaw.lift) =
      sourceRaw := by
  rw [RawTerm.subst_pointwise
    (@Subst.identity_lift_forRaw_pointwise level scope) sourceRaw]
  exact RawTerm.subst_identity sourceRaw

/-- Strong normalization survives raw identity substitution. -/
theorem RawTerm.subst_identity_isStronglyNormalizing
    {level scope : Nat} {sourceRaw : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing sourceRaw) :
    RawTerm.isStronglyNormalizing
      (sourceRaw.subst (@Subst.identity level scope).forRaw) := by
  rw [RawTerm.subst_identity sourceRaw]
  exact sourceIsSN

/-- Strong normalization survives the lifted raw identity substitution
under one binder. -/
theorem RawTerm.subst_identity_lift_isStronglyNormalizing
    {level scope : Nat} {sourceRaw : RawTerm (scope + 1)}
    (sourceIsSN : RawTerm.isStronglyNormalizing sourceRaw) :
    RawTerm.isStronglyNormalizing
      (sourceRaw.subst ((@Subst.identity level scope).forRaw.lift)) := by
  rw [RawTerm.subst_identity_lift (level := level) (scope := scope)
    sourceRaw]
  exact sourceIsSN

/-- **K12.27 identity-lift body SN bridge**.

This is the lambda-specific identity-substitution bridge for the
M04-only route.  If the body is reducible under identity in the
extended context, then the body produced by substituting the enclosing
lambda with identity and entering its binder is strongly normalizing.

The result deliberately concludes only SN.  It does not provide generic
world-monotone `Reducible.weaken`; that stronger theorem remains the
full `ReducibleSubst.lift` blocker for non-identity substitutions. -/
theorem Reducible.identity_lift_body_sn_of_identity_reducible
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyIdentityReducible :
      Reducible (codomainType.weaken.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Ty.weaken_subst_commute Subst.identity codomainType ▸
        Term.subst ((TermSubst.identity sourceCtx).lift domainType)
          bodyTerm) := by
  have bodyIdentityIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm) :=
    Reducible.isStronglyNormalizing bodyIdentityReducible
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level scope).forRaw.lift))
  rw [RawTerm.subst_identity_lift (level := level) (scope := scope) bodyRaw]
  change RawTerm.isStronglyNormalizing bodyRaw
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level (scope + 1)).forRaw))
    at bodyIdentityIsSN
  rw [RawTerm.subst_identity bodyRaw] at bodyIdentityIsSN
  exact bodyIdentityIsSN

/-- **K12.27 generic identity-lift body SN bridge**.

This is the binder-generic form of
`identity_lift_body_sn_of_identity_reducible` for binders whose body
type already lives in the extended scope, such as `lamPi`.  The result
is still SN-only and identity-only; it deliberately does not claim
generic `ReducibleSubst.lift`. -/
theorem Reducible.identity_lift_body_sn_of_identity_reducible_at
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {bodyType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (sourceCtx.cons domainType) bodyType bodyRaw}
    (bodyIdentityReducible :
      Reducible (bodyType.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst ((TermSubst.identity sourceCtx).lift domainType)
        bodyTerm) := by
  have bodyIdentityIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm) :=
    Reducible.isStronglyNormalizing bodyIdentityReducible
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level scope).forRaw.lift))
  rw [RawTerm.subst_identity_lift (level := level) (scope := scope) bodyRaw]
  change RawTerm.isStronglyNormalizing bodyRaw
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level (scope + 1)).forRaw))
    at bodyIdentityIsSN
  rw [RawTerm.subst_identity bodyRaw] at bodyIdentityIsSN
  exact bodyIdentityIsSN

end LeanFX2
