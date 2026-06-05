import FX1Poly.Typed.HasTypeDescInversion

/-! # FX1Poly/Typed/HasTypeDescFormerTelescopeInversion — generic former TELESCOPE inversion (GTL-08 probe)

The wall-bearing half of the generic former inversion: recover the children `DescTelescope` for ANY
formation generator (`typingRuleDescOf generator = some rule`), not just the concrete `gen_piTyCode` /
`gen_sigmaTyCode`.  The classifier half (`inversionFormerClassifierGeneric`) is wall-free; this is the
residual that hits the documented dependent-`subst` wall (`subst armGenerator := generator` against a
FREE generator fails Lean's occurs/scope check).  PROBE: try `subst generatorAgree` directly to see the
actual error, then the explicit-`Eq.rec`-motive transport workaround. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Generic former TELESCOPE inversion (probe).**  A typed formation cell's children form a
`DescTelescope`, generic over the formation generator.  The `conv` arm passes through (subject and
children unchanged); the `genFormation` arm extracts the arm's telescope after aligning the generator. -/
theorem HasTypeDesc.inversionFormerTelescopeGeneric {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext)
    {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    ∀ {payload : generator.payload generalScope}
      {children : RawTermChildren generator.binderShifts generalScope},
      subject = RawTerm.mkGen generator payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescope profile (currentDepth := 0) generalContext levels flag children :=
  fun {_payloadImplicit} {_childrenImplicit} =>
    match derivation with
    | .var _armContext _armIndex => fun subjectEq => by
        have rootEq : Generator.gen_var = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        unfold typingRuleDescOf at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma)] at isFormation
        cases isFormation
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped => fun subjectEq =>
        HasTypeDesc.inversionFormerTelescopeGeneric typedPremise wellFormed isFormation subjectEq
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq => by
        have rootEq : Generator.gen_universeCode = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        unfold typingRuleDescOf at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma)] at isFormation
        cases isFormation
    | .genFormation _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = generator :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

end FX1Poly.Typed
