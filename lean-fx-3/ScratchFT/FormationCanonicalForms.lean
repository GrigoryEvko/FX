import FX1Poly.Typed.EmptyTypeValueInversion

/-! Scratch: formation-engine canonical forms (Lemma A) + closed corollary + consistency (Lemma B). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Lemma A (general):** a `HasTypeDesc`-typed subject is a variable, or a Π / Σ / universe-code head. -/
theorem HasTypeDesc.subjectIsVariableOrFormerHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    (∃ index : Fin scope, subject = variableCell index) ∨
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode := by
  refine HasTypeDesc.rec
    (motive_1 := fun {_scope} _context subject _classifier _typed =>
      (∃ index : Fin _scope, subject = variableCell index) ∨
      RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
      RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
      RawTerm.headGenerator subject = Generator.gen_universeCode)
    (motive_2 := fun _context _levels _flag _children _telescope => True)
    ?var ?conv ?universeFormation ?genFormation ?nilTelescope ?consTelescope typed
  · intro _scope _context index
    exact Or.inl ⟨index, rfl⟩
  · intro _scope _context _subject _classifier _reclassifier _levelExpr _flag _typed _converts
      _reclassifierTyped subjectIH _reclassifierIH
    exact subjectIH
  · intro _scope _context levelExpr flag
    exact Or.inr (Or.inr (Or.inr rfl))
  · intro _scope _context generator payload children levels flag rule isFormation premises _premisesIH
    by_cases isPi : generator = Generator.gen_piTyCode
    · exact Or.inr (Or.inl (by subst isPi; rfl))
    · by_cases isSigma : generator = Generator.gen_sigmaTyCode
      · exact Or.inr (Or.inr (Or.inl (by subst isSigma; rfl)))
      · exfalso
        unfold typingRuleDescOf at isFormation
        rw [if_neg isPi, if_neg isSigma] at isFormation
        contradiction
  · intro _baseScope _currentDepth _context _flag
    exact True.intro
  · intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped _headIH _restIH
    exact True.intro

/-- **Lemma A-closed:** at the empty context the variable disjunct is vacuous, so a closed formation-typed
subject's head is Π / Σ / universe. -/
theorem HasTypeDesc.closedSubjectHeadIsFormerOrUniverse {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode := by
  rcases HasTypeDesc.subjectIsVariableOrFormerHead typed with ⟨index, _⟩ | rest
  · exact index.elim0
  · exact rest

end FX1Poly.Typed

-- axiom check
#print axioms FX1Poly.Typed.HasTypeDesc.subjectIsVariableOrFormerHead
#print axioms FX1Poly.Typed.HasTypeDesc.closedSubjectHeadIsFormerOrUniverse
