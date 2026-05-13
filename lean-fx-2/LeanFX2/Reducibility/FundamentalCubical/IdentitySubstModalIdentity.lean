import LeanFX2.Reducibility.FundamentalAliases

/-! # LeanFX2.Reducibility.FundamentalCubical.IdentitySubstModalIdentity

Identity-substitution SN endpoints for the modal + J-recursor
family: `modIntro`, `modElim`, `subsume`, `idJ` (at `Ty.id`),
`oeqJ` (at `Ty.oeq`), `idStrictRec` (at `Ty.idStrict`).

## Root status

Layer 3 metatheory leaf.  Fifth slice of `FundamentalCubical`. -/

namespace LeanFX2


/-- **K12.27 identity-substitution modal introduction SN endpoint**.

Layer-1 `modIntro` is type-preserving, so the M04 identity route only
needs SN of the identity-substituted inner term.  This theorem does not
claim a full modal reducibility introduction principle. -/
theorem Reducible.fundamental_identity_modIntro_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIdentityReducible :
      Reducible (innerType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) innerTerm)) :
    Term.isStronglyNormalizing (Term.modIntro innerTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.modIntro innerTerm)
    (Term.modIntro_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIdentityReducible))

/-- **K12.27 identity-substitution modal elimination SN endpoint**.

This is the SN-output identity bridge for the current Layer-1
type-preserving `modElim` constructor.  Full cross-modal eliminator
reducibility remains a separate K12.25/K12.20.U4 problem. -/
theorem Reducible.fundamental_identity_modElim_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIdentityReducible :
      Reducible (innerType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) innerTerm)) :
    Term.isStronglyNormalizing (Term.modElim innerTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.modElim innerTerm)
    (Term.modElim_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIdentityReducible))

/-- **K12.27 identity-substitution modal subsumption SN endpoint**.

`subsume` is also type-preserving in the present Layer-1 kernel, so this
bridge only packages the M04 SN consequence of the child identity
reducibility witness. -/
theorem Reducible.fundamental_identity_subsume_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIdentityReducible :
      Reducible (innerType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) innerTerm)) :
    Term.isStronglyNormalizing (Term.subsume innerTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.subsume innerTerm)
    (Term.subsume_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIdentityReducible))

/-- **K12.27 identity-substitution identity eliminator SN endpoint**. -/
theorem Reducible.fundamental_identity_idJ_at_id_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIdentityReducible :
        Reducible (motiveType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseCase))
    (witnessIdentityReducible :
        Reducible ((Ty.id carrier leftEndpoint rightEndpoint).subst
          Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) witness)) :
    Term.isStronglyNormalizing (Term.idJ baseCase witness) :=
  Term.strong_normalization_of_identity_subst
    (Term.idJ baseCase witness)
    (Reducible.fundamental_idJ_at_id
      (termSubst := TermSubst.identity sourceCtx)
      baseIdentityReducible witnessIdentityReducible)

/-- **K12.27 identity-substitution observational equality eliminator SN
endpoint**. -/
theorem Reducible.fundamental_identity_oeqJ_at_oeq_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessRaw}
    (baseIdentityReducible :
        Reducible (motiveType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseCase))
    (witnessIdentityReducible :
        Reducible ((Ty.oeq carrier leftEndpoint rightEndpoint).subst
          Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) witness)) :
    Term.isStronglyNormalizing (Term.oeqJ baseCase witness) :=
  Term.strong_normalization_of_identity_subst
    (Term.oeqJ baseCase witness)
    (Reducible.fundamental_oeqJ_at_oeq
      (termSubst := TermSubst.identity sourceCtx)
      baseIdentityReducible witnessIdentityReducible)

/-- **K12.27 identity-substitution strict identity eliminator SN
endpoint**. -/
theorem Reducible.fundamental_identity_idStrictRec_at_idStrict_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx
          (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIdentityReducible :
        Reducible (motiveType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseCase))
    (witnessIdentityReducible :
        Reducible
          ((Ty.idStrict carrier leftEndpoint rightEndpoint).subst
            Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) witness)) :
    Term.isStronglyNormalizing
      (Term.idStrictRec modeIsStrict baseCase witness) :=
  Term.strong_normalization_of_identity_subst
    (Term.idStrictRec modeIsStrict baseCase witness)
    (Reducible.fundamental_idStrictRec_at_idStrict
      (termSubst := TermSubst.identity sourceCtx)
      modeIsStrict baseIdentityReducible witnessIdentityReducible)

end LeanFX2
