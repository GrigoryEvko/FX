import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.GrownFormerClassifierConv

/-! Probe: E2.7 assembly (a) — the TELESCOPE-KEEPING table-generic grown former inversion.  The
merge of the two shipped templates: `invertPiCodeTelescopeWithConvGeneral` (Π-specific, keeps the
telescope) generalized to the abstract (generator, rule) of `formerClassifierConvUniverseGeneric`
(generic, drops the telescope).  One inversion for EVERY formation row, returning both the
premise telescope (the determinism consumer) and the universe-code classifier Conv. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem HasTypeDescPi.invertFormerTelescopeWithConvGeneric {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier)
    {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    ∀ {payload : generator.payload generalScope}
      {children : RawTermChildren generator.binderShifts generalScope},
      subject = RawTerm.mkGen generator payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescopePi profile (currentDepth := 0) generalContext levels flag children ∧
            Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) :=
  fun {_payloadImplicit} {_childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, convToCode⟩ :=
          HasTypeDesc.inversionFormerWithConvGeneric formationTyped isFormation subjectEq
        exact ⟨levels, flag, telescope.toDescTelescopePi, convToCode⟩
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, convToCode⟩ :=
          HasTypeDescPi.invertFormerTelescopeWithConvGeneric typedPremise isFormation subjectEq
        exact ⟨levels, flag, telescope, Conv.trans converts.sym convToCode⟩
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq => by
        have rootEq : Generator.gen_lam = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        unfold typingRuleDescOf at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma),
          if_neg (fun isList => Generator.noConfusion isList)] at isFormation
        cases isFormation
    | .piElim _functionTyped _argumentTyped => fun subjectEq => by
        have rootEq : Generator.gen_app = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        unfold typingRuleDescOf at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma),
          if_neg (fun isList => Generator.noConfusion isList)] at isFormation
        cases isFormation
    | .genFormationPi _armContext armGenerator _armPayload _armChildren armLevels armFlag
        armRule armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = generator :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq with _hScope _hGenerator _hPayload hChildren
        subst hChildren
        refine ⟨armLevels, armFlag, armPremises, ?_⟩
        rw [typingRuleDescOf_outputIsUniverseFormer armIsFormation]
        exact Conv.refl _

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.invertFormerTelescopeWithConvGeneric
