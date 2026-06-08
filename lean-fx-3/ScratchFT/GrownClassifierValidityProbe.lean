import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Typed.WfContextDescPiValidity
import FX1Poly.Typed.HasTypeDescPiValidity

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- (1) UNCONDITIONAL grown Π-code telescope inversion: uses the Conv-free formation inversion
-- `inversionPiCodeGeneral` (no WfContext) in the ofFormation arm, conv recurses. NO well-formedness.
theorem HasTypeDescPi.inversionPiCodeTelescopeUnconditional {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier) :
    ∀ {payload : Generator.gen_piTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_piTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_piTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescopePi profile (currentDepth := 0) generalContext levels flag children :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope⟩ :=
          HasTypeDesc.inversionPiCodeGeneral formationTyped subjectEq
        exact ⟨levels, flag, telescope.toDescTelescopePi⟩
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped => fun subjectEq =>
        HasTypeDescPi.inversionPiCodeTelescopeUnconditional typedPremise subjectEq
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq : Generator.gen_lam = Generator.gen_piTyCode)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq : Generator.gen_app = Generator.gen_piTyCode)
    | .genFormationPi _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_piTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

-- (2) UNCONDITIONAL grown Π-code component inversion (cases the two-entry telescope).
theorem HasTypeDescPi.inversionPiCodeComponentsUnconditional {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := by
  obtain ⟨levels, flag, telescope⟩ :=
    HasTypeDescPi.inversionPiCodeTelescopeUnconditional typed rfl
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped nilTelescope =>
          cases nilTelescope with
          | nil _ _ => exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

-- (3) UNCONDITIONAL grown dependent-Π-elimination output validity: the eliminator's classifier
-- `subst0 codomainCode argument` is a grown type, needing only the argument typing (no well-formedness).
theorem HasTypeDescPi.piCodeInstantiationIsTypeUnconditional {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {argument : RawTerm scope}
    (piIsType : IsTypeDescPi profile context (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode) :
    IsTypeDescPi profile context (RawTerm.subst0 codomainCode argument) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := piIsType
  obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  exact IsTypeDescPi.substituteUnderBinding ⟨codomainLevel, flag, codomainTyped⟩ argument argumentTyped

-- (4) THE PAYOFF — grown classifier-validity over the GROWN well-formedness WfContextDescPi.
-- ofFormation uses the shipped grown formation classifier-validity; conv reads off the reclassifier
-- typing directly; piIntro/genFormationPi build the universe code; piElim uses (3) unconditionally.
theorem HasTypeDescPi.classifierIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (derivation : HasTypeDescPi profile context subject classifier) :
    IsTypeDescPi profile context classifier :=
  match derivation with
  | .ofFormation formationTyped =>
      formationTyped.classifierIsTypeDescPi wellFormed
  | .conv levelExpr flag _typed _converts reclassifierTyped =>
      ⟨levelExpr, flag, reclassifierTyped⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode _body domainLevel codomainLevel flag
      domainTyped codomainTyped _bodyTyped => by
      refine ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
        HasTypeDescPi.genFormationPi context Generator.gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil))
          [domainLevel, codomainLevel] flag
          { outputType := universeFormerOutput } typingRuleDescOf_piTyCode ?_⟩
      exact DescTelescopePi.cons (currentDepth := 0) context domainCode domainLevel [codomainLevel]
        flag (.childCons codomainCode .childNil) domainTyped
        (DescTelescopePi.cons (context.cons domainCode) codomainCode codomainLevel [] flag
          .childNil codomainTyped (DescTelescopePi.nil _ flag))
  | .piElim functionTyped argumentTyped =>
      HasTypeDescPi.piCodeInstantiationIsTypeUnconditional
        (functionTyped.classifierIsTypeDescPi wellFormed) argumentTyped
  | .genFormationPi context generator _payload _children levels flag rule isFormation _premises => by
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context (lmaxAll levels) flag)⟩

#print axioms HasTypeDescPi.inversionPiCodeTelescopeUnconditional
#print axioms HasTypeDescPi.inversionPiCodeComponentsUnconditional
#print axioms HasTypeDescPi.piCodeInstantiationIsTypeUnconditional
#print axioms HasTypeDescPi.classifierIsTypeDescPi

end FX1Poly.Typed
