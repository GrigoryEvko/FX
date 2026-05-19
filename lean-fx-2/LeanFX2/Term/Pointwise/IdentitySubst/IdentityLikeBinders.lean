import LeanFX2.Term.Pointwise.IdentitySubst.Foundation

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeBinders

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

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

end LeanFX2
