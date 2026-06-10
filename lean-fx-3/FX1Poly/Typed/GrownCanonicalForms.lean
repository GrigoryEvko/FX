import FX1Poly.Typed.PiTypeFunctionInversion
import FX1Poly.Typed.SigmaCodeShape
import FX1Poly.Typed.FormationCanonicalForms
import FX1Poly.Typed.GrownFormerClassifierConv
import FX1Poly.Typed.OptionCodeShape
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
  term has head `gen_lam` / `gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` / `gen_listCode` /
  `gen_optionCode` / `gen_unitCode`.  Proved by the propext-free mutual recursor with closedness threaded as
  `Fin scope → False`.  The only hard arm is `piElim` (application): the function is closed, normal (by the
  subterm lemma) and typed at a Π-code, so by the IH its head is one of those shapes — but a λ head makes the
  application a β-redex (not normal, `not_isStepNormalForm_beta_smoke`), and a former / universe-code head is
  impossible at a Π classifier (`PiTypeFunctionInversion`'s `*NotTypedAtPiType`, including the nullary
  `unitFormerNotTypedAtPiType`).  So a closed normal application cannot exist — there are no neutrals to head it,
  since the empty context has no variables.

* `HasTypeDescPi.noClosedNormalTermAtEmptyType` — **grown normal-form consistency**: no closed NORMAL term
  inhabits the empty type.  Canonical forms make the subject λ / Π / Σ / universe; each is refuted at
  `emptyTypeCell` by the banked `EmptyTypeValueInversion` value-case inversions.  This needs NO subject
  reduction.  Full consistency for an ARBITRARY closed `t : Empty` adds strong normalization (open SN)
  to reach a normal form and subject reduction (the master dispatcher) to keep it typed at `Empty` — SR
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
`gen_sigmaTyCode` / `gen_universeCode` / `gen_listCode` / `gen_optionCode` / `gen_unitCode`.  Stated generally
with closedness as `Fin scope → False` so the recursor needs no scope-0 side condition; the `piElim` arm is the
crux (a closed normal application is impossible, killed by β-redex non-normality and the
type-former-not-a-Π-member inversions, including the nullary `unitFormerNotTypedAtPiType`). -/
theorem HasTypeDescPi.closedNormalSubjectHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (normal : RawTerm.isStepNormalForm subject)
    (closed : Fin scope → False) :
    RawTerm.headGenerator subject = Generator.gen_lam ∨
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode ∨
    RawTerm.headGenerator subject = Generator.gen_listCode ∨
    RawTerm.headGenerator subject = Generator.gen_optionCode ∨
    RawTerm.headGenerator subject = Generator.gen_unitCode := by
  refine HasTypeDescPi.rec
    (motive_1 := fun {armScope} _armContext armSubject _armClassifier _armTyped =>
      RawTerm.isStepNormalForm armSubject → (Fin armScope → False) →
      (RawTerm.headGenerator armSubject = Generator.gen_lam ∨
       RawTerm.headGenerator armSubject = Generator.gen_piTyCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_sigmaTyCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_universeCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_listCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_optionCode ∨
       RawTerm.headGenerator armSubject = Generator.gen_unitCode))
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
    rcases functionIH functionNormal armClosed with
      headLam | headPi | headSigma | headUniverse | headList | headOption | headUnit
    · obtain ⟨domainAnn, body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
      rw [bodyEq] at armNormal
      exact RawTerm.not_isStepNormalForm_beta_smoke domainAnn body argument armNormal
    · obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
      rw [piEq] at functionTyped
      exact HasTypeDescPi.piFormerNotTypedAtPiType functionTyped
    · obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
      rw [sigmaEq] at functionTyped
      exact HasTypeDescPi.sigmaFormerNotTypedAtPiType functionTyped
    · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
      rw [universeEq] at functionTyped
      exact HasTypeDescPi.universeCodeNotTypedAtPiType functionTyped
    · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
      rw [listEq] at functionTyped
      exact HasTypeDescPi.listFormerNotTypedAtPiType functionTyped
    · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
      rw [optionEq] at functionTyped
      exact HasTypeDescPi.optionFormerNotTypedAtPiType functionTyped
    · have unitEq := eq_unitCodeCell_of_headGenerator headUnit
      rw [unitEq] at functionTyped
      exact HasTypeDescPi.unitFormerNotTypedAtPiType functionTyped
  · intro _armScope _armContext generator _payload _children _levels _flag _rule isFormation _premises
      _premisesIH _armNormal _armClosed
    by_cases isPi : generator = Generator.gen_piTyCode
    · exact Or.inr (Or.inl (by subst isPi; rfl))
    · by_cases isSigma : generator = Generator.gen_sigmaTyCode
      · exact Or.inr (Or.inr (Or.inl (by subst isSigma; rfl)))
      · by_cases isList : generator = Generator.gen_listCode
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by subst isList; rfl)))))
        · by_cases isOption : generator = Generator.gen_optionCode
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by subst isOption; rfl))))))
          · by_cases isUnit : generator = Generator.gen_unitCode
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by subst isUnit; rfl))))))
            · exfalso
              dsimp only [typingRuleDescOf] at isFormation
              rw [if_neg isPi, if_neg isSigma, if_neg isList, if_neg isOption, if_neg isUnit]
                at isFormation
              contradiction
  · intro _armBaseScope _armCurrentDepth _armContext _armFlag
    exact True.intro
  · intro _armBaseScope _armCurrentDepth _armRestShifts _armContext _armHead _armHeadLevel
      _armRestLevels _armFlag _armRest _armHeadTyped _armRestTyped _armHeadIH _armRestIH
    exact True.intro

/-- **No closed NORMAL term inhabits the empty type.**  Grown normal-form consistency: by the canonical forms
the subject is λ / Π / Σ / universe / list / option / unit, each refuted at `emptyTypeCell` by the banked
value-case inversions (the nullary case via `unitFormerNotTypedAtEmptyType`).  No subject reduction needed; full
consistency adds open SN + SR to reduce an arbitrary closed `t:Empty` to its normal form. -/
theorem HasTypeDescPi.noClosedNormalTermAtEmptyType {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0)))
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed normal
      (fun emptyIndex => emptyIndex.elim0) with
      headLam | headPi | headSigma | headUniverse | headList | headOption | headUnit
  · obtain ⟨_domainAnn, _body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
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
  · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
    rw [listEq] at typed
    exact HasTypeDescPi.listFormerNotTypedAtEmptyType typed
  · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
    rw [optionEq] at typed
    exact HasTypeDescPi.optionFormerNotTypedAtEmptyType typed
  · have unitEq := eq_unitCodeCell_of_headGenerator headUnit
    rw [unitEq] at typed
    exact HasTypeDescPi.unitFormerNotTypedAtEmptyType typed

end FX1Poly.Typed
