import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.GrownFormerClassifierConv

/-! # Telescope-keeping table-generic grown former inversion

The merge of the two shipped inversion templates: `invertPiCodeTelescopeWithConvGeneral`
(Pi-specific, KEEPS the premise telescope) generalized to the abstract `(generator, rule)`
parameterization of `formerClassifierConvUniverseGeneric` (table-generic, but drops the
telescope).  ONE inversion now serves EVERY formation row — present and future — returning both
the `DescTelescopePi` over the subject's own children (the input to
`DescTelescopePi.universeDeterminismOfChildIH`) and the universe-code classifier `Conv` pin.

Consumers: the normal-subject universe-classification uniqueness master (the former arm inverts
both classifications with this lemma at the SAME children, then negotiates levels/flags via the
telescope determinism), and onward the flag-coherent pair extraction feeding the grown
strengthening master. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Generic grown former inversion, telescope-keeping**: a grown typing of a subject rooted at
ANY generator carrying a formation rule yields a premise telescope over the subject's own
children (at some level list and flag) together with `Conv` of the reached classifier to the
universe former's output code.  Table-generic: the `(generator, rule)` pair is abstract with only
`typingRuleDescOf generator = some rule` demanded, so a new formation row needs no new arm.
Unconditional — no well-formedness premise. -/
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
        dsimp only [typingRuleDescOf] at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma),
          if_neg (fun isList => Generator.noConfusion isList)] at isFormation
        cases isFormation
    | .piElim _functionTyped _argumentTyped => fun subjectEq => by
        have rootEq : Generator.gen_app = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        dsimp only [typingRuleDescOf] at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma),
          if_neg (fun isList => Generator.noConfusion isList)] at isFormation
        cases isFormation
    | .genFormationPi _armContext armGenerator _armPayload armChildren armLevels armFlag
        armRule armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = generator :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq with _hScope _hGenerator _hPayload hChildren
        subst hChildren
        by_cases isNullary : armGenerator = Generator.gen_unitCode
        · subst isNullary
          cases armPremises with
          | nil =>
              refine ⟨[], UniverseFlag.standard, DescTelescopePi.nil _ _, ?_⟩
              rw [typingRuleDescOf_unitCode_outputConstant armIsFormation]
              exact Conv.refl _
        · refine ⟨armLevels, armFlag, armPremises, ?_⟩
          rw [typingRuleDescOf_outputIsUniverseFormer armIsFormation isNullary]
          exact Conv.refl _

end FX1Poly.Typed
