import FX1Poly.Typed.HasTypeDescPiAppInversion

/-! Probe: grown var-typing inversion — HasTypeDescPi Γ (variableCell i) classifier → Conv classifier
    (Γ.lookup i). The spine-re-typing prerequisite for the Abel-reflection neutral-app reconstruction. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Formation-engine var inversion: a `variableCell i` typed in the FORMATION engine has its classifier
convertible to the looked-up type (the formation `conv` arm threads `Conv`, so the conclusion is `Conv`, not
equality). -/
theorem HasTypeDesc.invertVarFormationGeneral {profile : PolyProfile} {generalScope : Nat}
    {generalContext : TypingContext profile generalScope}
    {subject classifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject classifier) :
    ∀ {index : Fin generalScope}, subject = variableCell index →
      Conv classifier (generalContext.lookup index) :=
  fun {indexImplicit} =>
    match derivation with
    | .var _context index => fun subjectEq => by
        injection subjectEq with _scopeEq _generatorEq payloadEq _childrenEq
        subst payloadEq
        exact Conv.refl _
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq =>
        Conv.trans converts.sym (HasTypeDesc.invertVarFormationGeneral typedPremise subjectEq)
    | .universeFormation _context _levelExpr _flag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_var)
    | .genFormation _armContext armGenerator _armPayload _armChildren _armLevels _armFlag
        armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorIsVar : armGenerator = Generator.gen_var :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorIsVar
        rw [show typingRuleDescOf Generator.gen_var = none from rfl] at armIsFormation
        nomatch armIsFormation

/-- Grown var inversion: a `variableCell i` typed in the GROWN engine has its classifier convertible to the
looked-up type.  The spine-re-typing prerequisite for the Abel-reflection neutral-app reconstruction. -/
theorem HasTypeDescPi.invertVarGeneral {profile : PolyProfile} {generalScope : Nat}
    {generalContext : TypingContext profile generalScope}
    {subject classifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject classifier) :
    ∀ {index : Fin generalScope}, subject = variableCell index →
      Conv classifier (generalContext.lookup index) :=
  fun {indexImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq =>
        HasTypeDesc.invertVarFormationGeneral formationTyped subjectEq
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq =>
        Conv.trans converts.sym (HasTypeDescPi.invertVarGeneral typedPremise subjectEq)
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_var)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_var)
    | .genFormationPi _armContext armGenerator _armPayload _armChildren _armLevels _armFlag
        armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorIsVar : armGenerator = Generator.gen_var :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorIsVar
        rw [show typingRuleDescOf Generator.gen_var = none from rfl] at armIsFormation
        nomatch armIsFormation

/-- **Grown var inversion (clean corollary).**  A `variableCell index` typed at `classifier` in the grown
engine has `classifier` convertible to the looked-up type `context.lookup index`. -/
theorem HasTypeDescPi.invertVar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {index : Fin scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (variableCell index) classifier) :
    Conv classifier (context.lookup index) :=
  HasTypeDescPi.invertVarGeneral typed rfl

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDesc.invertVarFormationGeneral
#print axioms FX1Poly.Typed.HasTypeDescPi.invertVar
