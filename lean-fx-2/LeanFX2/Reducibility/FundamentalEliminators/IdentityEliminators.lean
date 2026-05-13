import LeanFX2.Reducibility.FundamentalWrappers

/-! # LeanFX2.Reducibility.FundamentalEliminators.IdentityEliminators

Fundamental-theorem cases for J-style eliminators on the three
identity-type families: `idJ` at `Ty.id` (HoTT observational
equality), `oeqJ` at `Ty.oeq` (observational equality in inner
mode), and `idStrictRec` at `Ty.idStrict` (strict equality
recursor).

## Root status

Layer 3 metatheory leaf.  Third slice of `FundamentalEliminators`. -/

namespace LeanFX2


/-! ## K12.23 fundamental HOTT-eliminator cases -/

/-- Fundamental case: `Term.idJ` at `Ty.id` (K12.23.B, SN-output).

The current `Ty.id` reducibility arm stores
SN of the equality witness plus an eliminator closure from any SN
base case to SN of `Term.idJ baseCase witness`.  The motive type is
arbitrary, not a structural sub-type of `Ty.id carrier left right`, so
the conclusion here is exactly `Term.isStronglyNormalizing`, not full
`Reducible motiveType`.
-/
theorem Reducible.fundamental_idJ_at_id_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.id carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.idJ baseCase witness)) :=
  witnessIH.2 (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-- Fundamental case: `Term.oeqJ` at `Ty.oeq` (K12.23.C, SN-output).

Observational equality has the same SN-output eliminator closure shape as
`Ty.id`: SN of the witness plus SN preservation through `oeqJ` for any
SN base case.  The arbitrary motive wall again prevents a full
`Reducible motiveType` conclusion in the current structural-on-`Ty`
candidate.
-/
theorem Reducible.fundamental_oeqJ_at_oeq_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.oeq carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.oeqJ baseCase witness)) :=
  witnessIH.2 (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-- Fundamental case: `Term.idStrictRec` at `Ty.idStrict`
(K12.23.D, SN-output).

Strict identity adds the ambient `mode = Mode.strict` witness to the
same SN-output eliminator closure used by `Ty.id` and `Ty.oeq`.  The result
is SN of the substituted strict recursor, matching the closure stored in
`Reducible (Ty.idStrict ...)`.
-/
theorem Reducible.fundamental_idStrictRec_at_idStrict_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx
          (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible
          ((Ty.idStrict carrier leftEndpoint rightEndpoint).subst sigma)
          (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseCase witness)) :=
  witnessIH.2 modeIsStrict (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

end LeanFX2
