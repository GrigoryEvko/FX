import LeanFX2.Reducibility.FundamentalWrappers

/-! # LeanFX2.Reducibility.FundamentalEliminators.ReflexivityIntroducers

Fundamental-theorem cases for reflexivity introducers on the
three identity-type families: `refl` at `Ty.id`, `oeqRefl` at
`Ty.oeq`, `idStrictRefl` at `Ty.idStrict`.  Each takes an
explicit endpoint SN witness and produces SN of the constructor
application.

## Root status

Layer 3 metatheory leaf.  Fourth slice of `FundamentalEliminators`. -/

namespace LeanFX2


/-! ## K12.26 reflexivity-intro fundamentals with explicit endpoint SN -/

/-- Fundamental case: `Term.refl` at `Ty.id` with an explicit endpoint
SN premise.

`Term.refl` carries a raw endpoint rather than a typed endpoint subterm, so
this lemma does not pretend to be the full structural fundamental-theorem
case.  The caller must provide SN of the substituted endpoint; from there the
weak `Ty.id` closure is discharged by raw refl SN plus generic `idJ` SN.
-/
theorem Reducible.fundamental_refl_at_id_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.id carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.refl carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.refl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.refl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.idJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Fundamental case: `Term.oeqRefl` at `Ty.oeq` with an explicit
endpoint SN premise.  Observational equality has the same weak-J closure
shape as `Ty.id`. -/
theorem Reducible.fundamental_oeqRefl_at_oeq_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.oeq carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.oeqRefl carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqRefl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.oeqRefl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.oeqJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Fundamental case: `Term.idStrictRefl` at `Ty.idStrict` with an
explicit endpoint SN premise.  The strict-mode eliminator closure keeps its
mode equality parameter explicit and otherwise mirrors `Term.refl`. -/
theorem Reducible.fundamental_idStrictRefl_at_idStrict_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.idStrict carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst
        (Term.idStrictRefl modeIsStrict carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.idStrictRefl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.idStrictRefl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun modeIsStrict' {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.idStrictRec_isStronglyNormalizing baseIsSN witnessIsSN⟩


end LeanFX2
