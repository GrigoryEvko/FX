import LeanFX2.Term.Pointwise.IdentitySubst.IdentityEliminators
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityEquality

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

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

end LeanFX2
