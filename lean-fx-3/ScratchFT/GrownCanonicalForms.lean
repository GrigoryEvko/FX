import FX1Poly.Typed.PiTypeFunctionInversion
import FX1Poly.Typed.FormationCanonicalForms
import FX1Poly.Core.ExistsStepOfNotNormal

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- subterm-of-normal: a normal application has a normal function child.  A function step would lift to an
application step (head congruence), which a normal application blocks. -/
theorem appNormal_functionNormal {scope : Nat} (functionTerm argument : RawTerm scope)
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument)) :
    RawTerm.isStepNormalForm functionTerm := by
  refine Decidable.byContradiction (fun notNormal => ?_)
  obtain ⟨reduct, functionStep⟩ := exists_step_of_not_isStepNormalForm notNormal
  exact RawTerm.isStepNormalForm_blocks_step normal (appCell reduct argument)
    (Step.cong .gen_app ()
      (StepChildren.here (.childCons argument .childNil : RawTermChildren [0] scope) functionStep))

/-- **Grown closed canonical forms.**  A closed normal grown-typed term is a λ / Π-former / Σ-former /
universe-code.  Stated generally with closedness as `Fin scope → False`. -/
theorem HasTypeDescPi.closedNormalSubjectHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContext context)
    (normal : RawTerm.isStepNormalForm subject)
    (closed : Fin scope → False) :
    RawTerm.headGenerator subject = Generator.gen_lam ∨
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode := by
  refine HasTypeDescPi.rec
    (motive_1 := fun {armScope} armContext armSubject _armClassifier _armTyped =>
      WfContext armContext → RawTerm.isStepNormalForm armSubject → (Fin armScope → False) →
      (RawTerm.headGenerator armSubject = Generator.gen_lam ∨
       RawTerm.headGenerator armSubject = Generator.gen_piTyCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_sigmaTyCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_universeCode))
    (motive_2 := fun _armContext _armLevels _armFlag _armChildren _armTelescope => True)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope
    typed wellFormed normal closed
  · intro _armScope _armContext _armSubject _armClassifier formationTyped armWf _armNormal armClosed
    rcases HasTypeDesc.subjectIsVariableOrFormerHead formationTyped with ⟨index, _⟩ | rest
    · exact (armClosed index).elim
    · exact Or.inr rest
  · intro _armScope _armContext _armSubject _armClassifier _reclassifier _levelExpr _flag _typed
      _converts _reclassifierTyped subjectIH _reclassifierIH armWf armNormal armClosed
    exact subjectIH armWf armNormal armClosed
  · intro _armScope _armContext _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      _domainTyped _codomainTyped _bodyTyped _domainIH _codomainIH _bodyIH _armWf _armNormal _armClosed
    exact Or.inl rfl
  · intro _armScope _armContext functionTerm argument _domainCode _codomainCode functionTyped
      _argumentTyped functionIH _argumentIH armWf armNormal armClosed
    exfalso
    have functionNormal : RawTerm.isStepNormalForm functionTerm :=
      appNormal_functionNormal functionTerm argument armNormal
    rcases functionIH armWf functionNormal armClosed with headLam | headPi | headSigma | headUniverse
    · obtain ⟨body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
      rw [bodyEq] at armNormal
      exact RawTerm.not_isStepNormalForm_beta_smoke body argument armNormal
    · obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
      rw [piEq] at functionTyped
      exact HasTypeDescPi.piFormerNotTypedAtPiType functionTyped armWf
    · obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
      rw [sigmaEq] at functionTyped
      exact HasTypeDescPi.sigmaFormerNotTypedAtPiType functionTyped armWf
    · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
      rw [universeEq] at functionTyped
      exact HasTypeDescPi.universeCodeNotTypedAtPiType functionTyped armWf
  · intro _armScope _armContext generator _payload _children _levels _flag _rule isFormation _premises
      _premisesIH _armWf _armNormal _armClosed
    by_cases isPi : generator = Generator.gen_piTyCode
    · exact Or.inr (Or.inl (by subst isPi; rfl))
    · by_cases isSigma : generator = Generator.gen_sigmaTyCode
      · exact Or.inr (Or.inr (Or.inl (by subst isSigma; rfl)))
      · exfalso
        unfold typingRuleDescOf at isFormation
        rw [if_neg isPi, if_neg isSigma] at isFormation
        contradiction
  · intro _armBaseScope _armCurrentDepth _armContext _armFlag
    exact True.intro
  · intro _armBaseScope _armCurrentDepth _armRestShifts _armContext _armHead _armHeadLevel
      _armRestLevels _armFlag _armRest _armHeadTyped _armRestTyped _armHeadIH _armRestIH
    exact True.intro

/-- **No closed NORMAL term inhabits the empty type.**  Grown normal-form consistency: by the canonical forms
the subject is λ / Π / Σ / universe, each refuted at `emptyTypeCell` by the banked value-case inversions.  No
SR needed; full consistency adds SN (OB-5) + SR to reduce an arbitrary closed `t:Empty` to its normal form. -/
theorem HasTypeDescPi.noClosedNormalTermAtEmptyType {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0)))
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed WfContext.emptyIsWellFormed normal
      (fun emptyIndex => emptyIndex.elim0) with headLam | headPi | headSigma | headUniverse
  · obtain ⟨_body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
    rw [bodyEq] at typed
    exact HasTypeDescPi.lambdaNotTypedAtEmptyType typed
  · obtain ⟨_domain, _codomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
    rw [piEq] at typed
    exact HasTypeDescPi.piFormerNotTypedAtEmptyType typed WfContext.emptyIsWellFormed
  · obtain ⟨_domain, _codomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
    rw [sigmaEq] at typed
    exact HasTypeDescPi.sigmaFormerNotTypedAtEmptyType typed WfContext.emptyIsWellFormed
  · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
    rw [universeEq] at typed
    exact HasTypeDescPi.universeCodeNotTypedAtEmptyType typed WfContext.emptyIsWellFormed

#print axioms FX1Poly.Typed.appNormal_functionNormal
#print axioms FX1Poly.Typed.HasTypeDescPi.closedNormalSubjectHead
#print axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtEmptyType

end FX1Poly.Typed
