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
        HasTypeDesc.inversionFormerTelescopeGeneric typedPremise isFormation subjectEq
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

/-- **Generic former inversion (FULL: telescope + classifier `Conv`).**  The generic-over-the-formation-
generator analogue of `inversionPiCodeWithConvGeneral` / `inversionSigmaCodeWithConvGeneral`: a typed
formation cell yields BOTH the children `DescTelescope` AND the classifier `Conv` to the canonical
universe code, at CONSISTENT `levels`/`flag` (both read off the SAME `genFormation` arm).  Merges the
classifier (`inversionFormerClassifierGeneric`) and telescope (`inversionFormerTelescopeGeneric`) halves
— the consistency is exactly what `uniquenessAgree`-style consumers (e.g. `HasTypeDesc.uniqueness`) need,
which two separate existential calls would NOT guarantee.  Zero-axiom (same cracked-wall idiom: `subst`
the free generator, then `injection`/`subst_vars`). -/
theorem HasTypeDesc.inversionFormerWithConvGeneric {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier)
    {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    ∀ {payload : generator.payload generalScope}
      {children : RawTermChildren generator.binderShifts generalScope},
      subject = RawTerm.mkGen generator payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescope profile (currentDepth := 0) generalContext levels flag children ∧
          Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) :=
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
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, convToCode⟩ :=
          HasTypeDesc.inversionFormerWithConvGeneric typedPremise isFormation subjectEq
        exact ⟨levels, flag, telescope,
          Conv.trans converts.sym convToCode⟩
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq => by
        have rootEq : Generator.gen_universeCode = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        unfold typingRuleDescOf at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma)] at isFormation
        cases isFormation
    | .genFormation _armContext armGenerator _armPayload armChildren armLevels armFlag
        armRule armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = generator :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        obtain rfl : armRule = { outputType := universeFormerOutput } :=
          formationRuleIsUniverseFormer armIsFormation
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises, Conv.refl _⟩

end FX1Poly.Typed
