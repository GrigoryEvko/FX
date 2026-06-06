import FX1Poly.Typed.PiTypeFunctionInversion
import FX1Poly.Typed.SigmaCodeShape
import FX1Poly.Typed.FormationCanonicalForms
import FX1Poly.Core.ExistsStepOfNotNormal

/-! # FX1Poly/Typed/GrownCanonicalForms — canonical forms for the grown engine `HasTypeDescPi`
    + grown normal-form consistency (SN-050 syntactic route)

`FormationCanonicalForms.lean` proved that a closed FORMATION-typed term is a Π / Σ former or universe code.
The grown engine `HasTypeDescPi` adds λ (`piIntro`) and application (`piElim`).  This file proves the grown
analogue and its empty-type consistency corollary.

## The three results

* `appNormal_functionNormal` — subterm-of-normal: a normal application has a normal function child.  A
  function step would lift to an application step (the head congruence `Step.cong .gen_app () (StepChildren.here
  …)`), which a normal application blocks (`isStepNormalForm_blocks_step`).

* `HasTypeDescPi.closedNormalSubjectHead` — **grown closed canonical forms**: a CLOSED NORMAL grown-typed
  term has head `gen_lam` / `gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode`.  Proved by the propext-free
  mutual recursor with closedness threaded as `Fin scope → False`.  The only hard
  arm is `piElim` (application): the function is closed, normal (by the subterm lemma) and typed at a Π-code, so
  by the IH its head is one of the four shapes — but a λ head makes the application a β-redex (not normal,
  `not_isStepNormalForm_beta_smoke`), and a former / universe-code head is impossible at a Π classifier
  (`PiTypeFunctionInversion`'s `*NotTypedAtPiType`).  So a closed normal application cannot exist — there are no
  neutrals to head it, since the empty context has no variables.

* `HasTypeDescPi.noClosedNormalTermAtEmptyType` — **grown normal-form consistency**: no closed NORMAL term
  inhabits the empty type.  Canonical forms make the subject λ / Π / Σ / universe; each is refuted at
  `emptyTypeCell` by the banked `EmptyTypeValueInversion` value-case inversions.  This needs NO subject
  reduction.  Full SN-050 consistency for an ARBITRARY closed `t : Empty` adds strong normalization (OB-5,
  `#794`) to reach a normal form and subject reduction (the SN-055 dispatcher) to keep it typed at `Empty` — SR
  is the sole remaining gate.

## Zero-axiom verification

`Decidable.byContradiction` (axiom-free for the decidable `isStepNormalForm`) + `Step.cong` congruence +
`isStepNormalForm_blocks_step`; the propext-free `HasTypeDescPi.rec` (trivial `True` telescope motive_2); the
shipped head→shape reconstructions + `subjectIsVariableOrFormerHead` + `not_isStepNormalForm_beta_smoke` + the
`*NotTypedAtPiType` / `*NotTypedAtEmptyType` inversions.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Subterm-of-normal.**  A normal application has a normal function child: a function step lifts to an
application step via the head congruence (`Step.cong .gen_app () (StepChildren.here …)`), which a normal
application blocks. -/
theorem appNormal_functionNormal {scope : Nat} (functionTerm argument : RawTerm scope)
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument)) :
    RawTerm.isStepNormalForm functionTerm := by
  refine Decidable.byContradiction (fun notNormal => ?_)
  obtain ⟨reduct, functionStep⟩ := exists_step_of_not_isStepNormalForm notNormal
  exact RawTerm.isStepNormalForm_blocks_step normal (appCell reduct argument)
    (Step.cong .gen_app ()
      (StepChildren.here (.childCons argument .childNil : RawTermChildren [0] scope) functionStep))

/-- **Grown closed canonical forms.**  A closed normal grown-typed term has head `gen_lam` / `gen_piTyCode` /
`gen_sigmaTyCode` / `gen_universeCode`.  Stated generally with closedness as `Fin scope → False` so the
recursor needs no scope-0 side condition; the `piElim` arm is the crux (a closed normal application is
impossible, killed by β-redex non-normality and the type-former-not-a-Π-member inversions). -/
theorem HasTypeDescPi.closedNormalSubjectHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (normal : RawTerm.isStepNormalForm subject)
    (closed : Fin scope → False) :
    RawTerm.headGenerator subject = Generator.gen_lam ∨
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode := by
  refine HasTypeDescPi.rec
    (motive_1 := fun {armScope} _armContext armSubject _armClassifier _armTyped =>
      RawTerm.isStepNormalForm armSubject → (Fin armScope → False) →
      (RawTerm.headGenerator armSubject = Generator.gen_lam ∨
       RawTerm.headGenerator armSubject = Generator.gen_piTyCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_sigmaTyCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_universeCode))
    (motive_2 := fun _armContext _armLevels _armFlag _armChildren _armTelescope => True)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope
    typed normal closed
  · intro _armScope _armContext _armSubject _armClassifier formationTyped _armNormal armClosed
    rcases HasTypeDesc.subjectIsVariableOrFormerHead formationTyped with ⟨index, _⟩ | rest
    · exact (armClosed index).elim
    · exact Or.inr rest
  · intro _armScope _armContext _armSubject _armClassifier _reclassifier _levelExpr _flag _typed
      _converts _reclassifierTyped subjectIH _reclassifierIH armNormal armClosed
    exact subjectIH armNormal armClosed
  · intro _armScope _armContext _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      _domainTyped _codomainTyped _bodyTyped _domainIH _codomainIH _bodyIH _armNormal _armClosed
    exact Or.inl rfl
  · intro _armScope _armContext functionTerm argument _domainCode _codomainCode functionTyped
      _argumentTyped functionIH _argumentIH armNormal armClosed
    exfalso
    have functionNormal : RawTerm.isStepNormalForm functionTerm :=
      appNormal_functionNormal functionTerm argument armNormal
    rcases functionIH functionNormal armClosed with headLam | headPi | headSigma | headUniverse
    · obtain ⟨body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
      rw [bodyEq] at armNormal
      exact RawTerm.not_isStepNormalForm_beta_smoke body argument armNormal
    · obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
      rw [piEq] at functionTyped
      exact HasTypeDescPi.piFormerNotTypedAtPiType functionTyped
    · obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
      rw [sigmaEq] at functionTyped
      exact HasTypeDescPi.sigmaFormerNotTypedAtPiType functionTyped
    · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
      rw [universeEq] at functionTyped
      exact HasTypeDescPi.universeCodeNotTypedAtPiType functionTyped
  · intro _armScope _armContext generator _payload _children _levels _flag _rule isFormation _premises
      _premisesIH _armNormal _armClosed
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
subject reduction needed; full SN-050 consistency adds SN (OB-5) + SR to reduce an arbitrary closed `t:Empty`
to its normal form. -/
theorem HasTypeDescPi.noClosedNormalTermAtEmptyType {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0)))
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed normal
      (fun emptyIndex => emptyIndex.elim0) with headLam | headPi | headSigma | headUniverse
  · obtain ⟨_body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
    rw [bodyEq] at typed
    exact HasTypeDescPi.lambdaNotTypedAtEmptyType typed
  · obtain ⟨_domain, _codomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
    rw [piEq] at typed
    exact HasTypeDescPi.piFormerNotTypedAtEmptyType typed
  · obtain ⟨_domain, _codomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
    rw [sigmaEq] at typed
    exact HasTypeDescPi.sigmaFormerNotTypedAtEmptyType typed
  · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
    rw [universeEq] at typed
    exact HasTypeDescPi.universeCodeNotTypedAtEmptyType typed

end FX1Poly.Typed
