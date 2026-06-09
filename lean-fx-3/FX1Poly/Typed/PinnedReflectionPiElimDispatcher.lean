import FX1Poly.Typed.PinnedReflectionPiElimCore
import FX1Poly.Typed.GrownWfOpenStronglyNormalizing
import FX1Poly.Typed.GrownOpenProgressByClassifier
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/PinnedReflectionPiElimDispatcher — the whnf dispatcher for the piElim residual

THE structural decomposition of the pinned reflection's one open arm: the FULL
`PinnedReflectionPiElimResidual` reduces to two HEAD-SPECIFIC residuals —

  * `PinnedReflectionPiElimLamResidual` — the function whnf-reduces to a normal λ (the genuinely
    open analysis: the contracted application is covered by no premise IH);
  * `PinnedReflectionPiElimNeutralSpineResidual` — the function whnf-reduces to a normal neutral
    (var-headed spine or stuck eliminator); the bare-VARIABLE instance is ALREADY DISCHARGED by
    `pinnedReflectionPiElimReducesToVarArm`, so the open content is the 11 composite heads.

Pipeline (`pinnedReflectionPiElimResidualOfHeadResiduals`): grown-wf open SN
(`stronglyNormalizingOfWfContextDescPi` — the exact consumer of the motive's target-wf premise)
normalizes the function; `subjectReductionStar` types the normal reduct at the SAME Π classifier;
the wf-free canonical forms split its head.

The wf-free canonical forms (`normalSubjectCanonicalOrNeutralOfTyping` /
`normalFunctionIsLambdaOrNeutralOfTyping`) are copies of the shipped open canonical forms with the
VESTIGIAL `WfContextDesc` premise deleted — the shipped proofs thread it through the motive but no
arm consumes it, and the reflection motive carries the GROWN wf, which cannot supply it.

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- wf-free copy of `openNormalSubjectCanonicalOrNeutral` (its `WfContextDesc` premise is
vestigial — threaded through the motive, consumed by no arm). -/
theorem HasTypeDescPi.normalSubjectCanonicalOrNeutralOfTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (normal : RawTerm.isStepNormalForm subject) :
    RawTerm.IsGrownCanonicalHead subject ∨ IsNeutral subject := by
  refine HasTypeDescPi.rec
    (motive_1 := fun {armScope} armContext armSubject _armClassifier _armTyped =>
      RawTerm.isStepNormalForm armSubject →
      (RawTerm.IsGrownCanonicalHead armSubject ∨ IsNeutral armSubject))
    (motive_2 := fun _armContext _armLevels _armFlag _armChildren _armTelescope => True)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope
    typed normal
  · intro _armScope _armContext _armSubject _armClassifier formationTyped _armNormal
    rcases HasTypeDesc.subjectIsVariableOrFormerHead formationTyped with ⟨index, subjectEq⟩ | rest
    · rw [subjectEq]
      exact Or.inr (IsNeutral.var index)
    · exact Or.inl (Or.inr rest)
  · intro _armScope _armContext _armSubject _armClassifier _reclassifier _levelExpr _flag _typed
      _converts _reclassifierTyped subjectIH _reclassifierIH armNormal
    exact subjectIH armNormal
  · intro _armScope _armContext _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      _domainTyped _codomainTyped _bodyTyped _domainIH _codomainIH _bodyIH _armNormal
    exact Or.inl (Or.inl rfl)
  · intro _armScope _armContext functionTerm argument _domainCode _codomainCode functionTyped
      _argumentTyped functionIH _argumentIH armNormal
    have functionNormal : RawTerm.isStepNormalForm functionTerm :=
      appNormal_functionNormal functionTerm argument armNormal
    rcases functionIH functionNormal with
        (headLam | headPi | headSigma | headUniverse | headList | headOption) | functionNeutral
    · exfalso
      obtain ⟨body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
      rw [bodyEq] at armNormal
      exact RawTerm.not_isStepNormalForm_beta_smoke body argument armNormal
    · exfalso
      obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
      rw [piEq] at functionTyped
      exact HasTypeDescPi.piFormerNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
      rw [sigmaEq] at functionTyped
      exact HasTypeDescPi.sigmaFormerNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
      rw [universeEq] at functionTyped
      exact HasTypeDescPi.universeCodeNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
      rw [listEq] at functionTyped
      exact HasTypeDescPi.listFormerNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
      rw [optionEq] at functionTyped
      exact HasTypeDescPi.optionFormerNotTypedAtPiType functionTyped
    · exact Or.inr (IsNeutral.app functionNeutral)
  · intro _armScope _armContext generator _payload _children _levels _flag _rule isFormation
      _premises _premisesIH _armNormal
    by_cases isPi : generator = Generator.gen_piTyCode
    · exact Or.inl (Or.inr (Or.inl (by subst isPi; rfl)))
    · by_cases isSigma : generator = Generator.gen_sigmaTyCode
      · exact Or.inl (Or.inr (Or.inr (Or.inl (by subst isSigma; rfl))))
      · by_cases isList : generator = Generator.gen_listCode
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by subst isList; rfl))))))
        · by_cases isOption : generator = Generator.gen_optionCode
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by subst isOption; rfl))))))
          · exfalso
            unfold typingRuleDescOf at isFormation
            rw [if_neg isPi, if_neg isSigma, if_neg isList, if_neg isOption] at isFormation
            contradiction
  · intro _armBaseScope _armCurrentDepth _armContext _armFlag
    exact True.intro
  · intro _armBaseScope _armCurrentDepth _armRestShifts _armContext _armHead _armHeadLevel
      _armRestLevels _armFlag _armRest _armHeadTyped _armRestTyped _armHeadIH _armRestIH
    exact True.intro

/-- wf-free copy of `openNormalFunctionIsLambdaOrNeutral`. -/
theorem HasTypeDescPi.normalFunctionIsLambdaOrNeutralOfTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed : HasTypeDescPi profile context subject (piTyCodeCell outerDomain outerCodomain))
    (normal : RawTerm.isStepNormalForm subject) :
    (∃ body : RawTerm (scope + 1), subject = lamCell body) ∨ IsNeutral subject := by
  rcases HasTypeDescPi.normalSubjectCanonicalOrNeutralOfTyping typed normal with
      (headLam | headPi | headSigma | headUniverse | headList | headOption) | neutral
  · exact Or.inl (eq_lamCell_of_headGenerator headLam)
  · obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
    rw [piEq] at typed
    exact (HasTypeDescPi.piFormerNotTypedAtPiType typed).elim
  · obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
    rw [sigmaEq] at typed
    exact (HasTypeDescPi.sigmaFormerNotTypedAtPiType typed).elim
  · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
    rw [universeEq] at typed
    exact (HasTypeDescPi.universeCodeNotTypedAtPiType typed).elim
  · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
    rw [listEq] at typed
    exact (HasTypeDescPi.listFormerNotTypedAtPiType typed).elim
  · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
    rw [optionEq] at typed
    exact (HasTypeDescPi.optionFormerNotTypedAtPiType typed).elim
  · exact Or.inr neutral

/-- **The λ-headed-after-whnf residual**: the residual conclusion when the function
`StepStar`-reduces to a NORMAL λ — the genuinely open analysis (the contracted application is not
covered by any premise IH). -/
def PinnedReflectionPiElimLamResidual (profile : PolyProfile) : Prop :=
  ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode lamBody : RawTerm (targetScope + 1)},
    HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    HasTypeDescPi profile targetContext argument domainCode →
    StepStar functionTerm (lamCell lamBody) →
    RawTerm.isStepNormalForm (lamCell lamBody) →
    PinnedReflectionConclusion profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    PinnedReflectionConclusion profile targetContext argument domainCode →
    PinnedReflectionConclusion profile targetContext (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument)

/-- **The neutral-spine-after-whnf residual**: the residual conclusion when the function
`StepStar`-reduces to a NORMAL neutral (var-headed application spine or stuck eliminator) — the
spine-recursion analysis (the spine components are reduct subterms not covered by any premise IH).
NOTE: the bare-VARIABLE instance of this residual is ALREADY DISCHARGED
(`pinnedReflectionPiElimReducesToVarArm`); the open content is the 11 composite-neutral heads. -/
def PinnedReflectionPiElimNeutralSpineResidual (profile : PolyProfile) : Prop :=
  ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode reduct : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)},
    HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    HasTypeDescPi profile targetContext argument domainCode →
    StepStar functionTerm reduct →
    IsNeutral reduct →
    RawTerm.isStepNormalForm reduct →
    PinnedReflectionConclusion profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    PinnedReflectionConclusion profile targetContext argument domainCode →
    PinnedReflectionConclusion profile targetContext (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument)

/-- **The whnf dispatcher**: the FULL piElim residual reduces to the two head-specific residuals.
Grown-wf open SN normalizes the function; SR-star types the normal reduct; the wf-free canonical
forms split its head: a λ routes to the λ residual, a neutral routes to the spine residual
(whose bare-variable instance is pre-discharged by `pinnedReflectionPiElimReducesToVarArm`). -/
theorem pinnedReflectionPiElimResidualOfHeadResiduals (profile : PolyProfile)
    (lamResidual : PinnedReflectionPiElimLamResidual profile)
    (neutralSpineResidual : PinnedReflectionPiElimNeutralSpineResidual profile) :
    PinnedReflectionPiElimResidual profile := by
  intro targetScope targetContext functionTerm argument domainCode codomainCode
    functionTyped argumentTyped functionIH argumentIH
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  have functionStronglyNormalizing : StepStar.IsStronglyNormalizing functionTerm :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDescPi targetWellFormed functionTyped
  obtain ⟨reduct, functionReduces, reductNormal⟩ :
      ∃ reduct : RawTerm targetScope,
        StepStar functionTerm reduct ∧ RawTerm.isStepNormalForm reduct :=
    ⟨RawTerm.normalize functionTerm functionStronglyNormalizing,
      RawTerm.normalize_reducesTo functionTerm functionStronglyNormalizing,
      RawTerm.normalize_isStepNormalForm functionTerm functionStronglyNormalizing⟩
  have reductTyped : HasTypeDescPi profile targetContext reduct
      (piTyCodeCell domainCode codomainCode) :=
    HasTypeDescPi.subjectReductionStar targetWellFormed functionTyped functionReduces
  rcases HasTypeDescPi.normalFunctionIsLambdaOrNeutralOfTyping reductTyped reductNormal with
      ⟨lamBody, reductEq⟩ | reductNeutral
  · subst reductEq
    exact lamResidual functionTyped argumentTyped functionReduces reductNormal
      functionIH argumentIH targetWellFormed rho sourceContext rhoInjective condition wellFormed
      subjectInImage pinned pinBaseTyped
  · exact neutralSpineResidual functionTyped argumentTyped functionReduces reductNeutral
      reductNormal functionIH argumentIH targetWellFormed rho sourceContext rhoInjective
      condition wellFormed subjectInImage pinned pinBaseTyped

end FX1Poly.Typed
