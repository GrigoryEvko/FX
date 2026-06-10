import FX1Poly.Typed.GuardedPinnedReflection
import FX1Poly.Typed.PinnedReflectionPiElimCore
import FX1Poly.Typed.GrownOpenProgressByClassifier
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.CellSubstitution

/-! Probe: STR-8b brick i-b — THE PLATEAU INDUCTION.  `∀ bound, ResidualGuarded profile bound` by
structural induction on a budget, with the spine PIN-EXTRACTION (the classifier of a normal
non-λ grown-typed term is pinned) as a derivation-structural helper whose one external call is
the guarded master on the nested argument at a strictly smaller bound (the induction hypothesis).
Harvest: `HasTypeDescPi.pinnedReflectionNormal` — THE PLATEAU MASTER. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Formation-side pin extraction: a formation classifier is pinned — variable classifiers by the
Kripke condition + `lookupIsType`, universe/former classifiers by rename-invariance. -/
theorem pinExtractFormationClassifier {profile : PolyProfile}
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDesc profile targetContext subject classifier)
    {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (condition : ContextReflectsRename profile rho sourceContext targetContext)
    (wellFormed : WfContextDescPi sourceContext)
    {sourceSubject : RawTerm sourceScope}
    (subjectInImage : subject = RawTerm.rename rho sourceSubject) :
    ∃ base : RawTerm sourceScope,
      Conv classifier (RawTerm.rename rho base) ∧
      IsTypeDescPi profile sourceContext base :=
  match derivation with
  | .var _targetContext index => by
      obtain ⟨sourceIndex, hSourceSubject, hIndex⟩ :=
        renameEqVariableCellInversion rho subjectInImage.symm
      subst hIndex
      exact ⟨sourceContext.lookup sourceIndex, condition sourceIndex,
        WfContextDescPi.lookupIsType sourceContext wellFormed sourceIndex⟩
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      let ⟨base, pinConv, baseTyped⟩ :=
        pinExtractFormationClassifier typedPremise rho sourceContext condition
          wellFormed subjectInImage
      ⟨base, converts.sym.trans pinConv, baseTyped⟩
  | .universeFormation _targetContext levelExpr flag => by
      refine ⟨universeCodeCell levelExpr.lsucc flag, ?_, ?_⟩
      · rw [rename_universeCodeCell]
        exact Conv.refl _
      · exact ⟨levelExpr.lsucc.lsucc, flag,
          .ofFormation (.universeFormation sourceContext levelExpr.lsucc flag)⟩
  | .genFormation _targetContext generator payload children levels flag rule
      isFormation _premises => by
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        formationRuleIsUniverseFormer isFormation
      refine ⟨universeCodeCell (lmaxAll levels) flag, ?_, ?_⟩
      · show Conv (universeCodeCell (lmaxAll levels) flag)
          (RawTerm.rename rho (universeCodeCell (lmaxAll levels) flag))
        rw [rename_universeCodeCell]
        exact Conv.refl _
      · exact ⟨(lmaxAll levels).lsucc, flag,
          .ofFormation (.universeFormation sourceContext (lmaxAll levels) flag)⟩

/-- **The spine pin-extraction**: the classifier of a NORMAL, non-λ, in-image grown-typed term is
pinned.  Derivation-structural; the piElim arm pins the nested function recursively, reflects the
nested argument via the guarded master at a strictly smaller bound (the strong-induction supply),
and assembles the instantiated-codomain pin via the substitution lemma. -/
theorem pinExtractNeutralClassifier {profile : PolyProfile} {budget : Nat}
    (residualBelow : ∀ {smallBound : Nat}, smallBound ≤ budget →
      PinnedReflectionPiElimResidualGuarded profile smallBound)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier)
    (subjectNormal : RawTerm.isStepNormalForm subject)
    (hNotLam : ∀ body : RawTerm (targetScope + 1), subject ≠ lamCell body)
    (subjectSize : subject.size ≤ budget)
    (targetWellFormed : WfContextDescPi targetContext)
    {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (rhoInjective : Function.Injective rho)
    (condition : ContextReflectsRename profile rho sourceContext targetContext)
    (wellFormed : WfContextDescPi sourceContext)
    {sourceSubject : RawTerm sourceScope}
    (subjectInImage : subject = RawTerm.rename rho sourceSubject) :
    ∃ base : RawTerm sourceScope,
      Conv classifier (RawTerm.rename rho base) ∧
      IsTypeDescPi profile sourceContext base :=
  match derivation with
  | .ofFormation formationTyped =>
      pinExtractFormationClassifier formationTyped rho sourceContext condition
        wellFormed subjectInImage
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      let ⟨base, pinConv, baseTyped⟩ :=
        pinExtractNeutralClassifier residualBelow typedPremise subjectNormal hNotLam
          subjectSize targetWellFormed rho sourceContext rhoInjective condition
          wellFormed subjectInImage
      ⟨base, converts.sym.trans pinConv, baseTyped⟩
  | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
      (hNotLam _ rfl).elim
  | @HasTypeDescPi.piElim _ _ _ nestedFunction nestedArgument _ _
      nestedFunctionTyped nestedArgumentTyped => by
      have nestedFunctionNormal := appNormal_functionNormal _ _ subjectNormal
      have nestedArgumentNormal := appNormal_argumentNormal _ _ subjectNormal
      have hNotLamNested : ∀ body, nestedFunction ≠ lamCell body := by
        intro body hEq
        rw [hEq] at subjectNormal
        exact RawTerm.not_isStepNormalForm_beta_smoke body _ subjectNormal
      obtain ⟨sourceNestedFunction, sourceNestedArgument, hSourceSubject,
          hNestedFunction, hNestedArgument⟩ :=
        renameEqAppCellInversion rho subjectInImage.symm
      have nestedFunctionSize : _ ≤ budget :=
        Nat.le_of_lt
          (Nat.lt_of_lt_of_le (RawTerm.size_lt_appCell_function _ _) subjectSize)
      obtain ⟨piBase, piPinned, piBaseTyped⟩ :=
        pinExtractNeutralClassifier residualBelow nestedFunctionTyped
          nestedFunctionNormal hNotLamNested nestedFunctionSize targetWellFormed rho
          sourceContext rhoInjective condition wellFormed hNestedFunction
      obtain ⟨domainBase, codomainBase, sourceChain, domainConv, codomainConv⟩ :=
        Conv.pinnedPiComponentsWithSourceChain rho piPinned
      obtain ⟨piLevel, piFlag, piBaseAt⟩ := piBaseTyped
      have piReductTyped :=
        HasTypeDescPi.subjectReductionStar wellFormed piBaseAt sourceChain
      obtain ⟨domainLevel, codomainLevel, componentFlag, domainTyped, codomainTyped,
          _convToOutput⟩ := HasTypeDescPi.invertPiTyCode piReductTyped
      have nestedArgumentSize : _ ≤ budget :=
        Nat.le_of_lt
          (Nat.lt_of_lt_of_le (RawTerm.size_lt_appCell_argument _ _) subjectSize)
      obtain ⟨argumentReflClassifier, argumentClassConv, sourceArgumentTyped⟩ :=
        HasTypeDescPi.pinnedReflectionGuarded (residualBelow nestedArgumentSize)
          nestedArgumentTyped (Nat.le_refl _) nestedArgumentNormal
          targetWellFormed rho sourceContext rhoInjective condition wellFormed
          hNestedArgument domainConv ⟨domainLevel, componentFlag, domainTyped⟩
      have sourceArgumentAtDomain :
          HasTypeDescPi profile sourceContext sourceNestedArgument domainBase :=
        HasTypeDescPi.conv domainLevel componentFlag sourceArgumentTyped
          (Conv.reflectRenameOfFinInjective rho rhoInjective
            (argumentClassConv.sym.trans domainConv)) domainTyped
      refine ⟨RawTerm.subst0 codomainBase sourceNestedArgument, ?_, ?_⟩
      · rw [RawTerm.rename_subst0_commute, ← hNestedArgument]
        exact Conv.subst _ codomainConv
      · refine ⟨codomainLevel, componentFlag, ?_⟩
        exact HasTypeDescPi.substituteUnderBinding sourceNestedArgument
          codomainTyped sourceArgumentAtDomain
  | .genFormationPi _targetContext generator payload children levels flag rule
      isFormation _premises => by
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        formationRuleIsUniverseFormer isFormation
      refine ⟨universeCodeCell (lmaxAll levels) flag, ?_, ?_⟩
      · show Conv (universeCodeCell (lmaxAll levels) flag)
          (RawTerm.rename rho (universeCodeCell (lmaxAll levels) flag))
        rw [rename_universeCodeCell]
        exact Conv.refl _
      · exact ⟨(lmaxAll levels).lsucc, flag,
          .ofFormation (.universeFormation sourceContext (lmaxAll levels) flag)⟩

/-- **The plateau induction**: the guarded piElim residual holds at every bound within a budget,
by structural induction on the budget — the spine pin-extraction's master calls land at strictly
smaller bounds, supplied by the induction hypothesis. -/
theorem plateauResidualGuardedUpTo (profile : PolyProfile) :
    ∀ (budget : Nat) (bound : Nat), bound ≤ budget →
      PinnedReflectionPiElimResidualGuarded profile bound
  | 0 => by
      intro bound hBound
      intro targetScope targetContext functionTerm argument domainCode codomainCode
        _functionTyped _argumentTyped sizeBound _appNormal _functionIH _argumentIH
      exact absurd (Nat.le_trans sizeBound hBound) (Nat.not_succ_le_zero _)
  | budget + 1 => by
      intro bound hBound
      intro targetScope targetContext functionTerm argument domainCode codomainCode
        functionTyped argumentTyped sizeBound appNormal functionIH argumentIH
      intro targetWellFormed sourceScope rho sourceContext rhoInjective condition
        wellFormed sourceSubject pinBase subjectInImage _pinned _pinBaseTyped
      obtain ⟨sourceFunction, sourceArgument, hSubject, hFunction, hArgument⟩ :=
        renameEqAppCellInversion rho subjectInImage.symm
      subst hSubject
      have functionNormal := appNormal_functionNormal _ _ appNormal
      have hNotLamF : ∀ body, functionTerm ≠ lamCell body := by
        intro body hEq
        rw [hEq] at appNormal
        exact RawTerm.not_isStepNormalForm_beta_smoke body argument appNormal
      have functionSize : functionTerm.size ≤ budget :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (RawTerm.size_lt_appCell_function _ _) sizeBound) hBound)
      obtain ⟨piBase', piPinned', piBaseTyped'⟩ :=
        pinExtractNeutralClassifier
          (fun {smallBound} h => plateauResidualGuardedUpTo profile budget smallBound h)
          functionTyped functionNormal hNotLamF functionSize targetWellFormed rho
          sourceContext rhoInjective condition wellFormed hFunction
      exact pinnedReflectionPiElimCore profile functionIH argumentIH rho sourceContext
        targetWellFormed rhoInjective condition wellFormed hFunction hArgument
        piPinned' piBaseTyped'

/-- The guarded residual holds at EVERY bound. -/
theorem plateauResidualGuarded (profile : PolyProfile) (bound : Nat) :
    PinnedReflectionPiElimResidualGuarded profile bound :=
  plateauResidualGuardedUpTo profile bound bound (Nat.le_refl bound)

/-- **THE PLATEAU MASTER**: the full pinned reflection for every NORMAL grown-typed subject —
the guarded master at the subject's own size, with the plateau-induction residual. -/
theorem HasTypeDescPi.pinnedReflectionNormal {profile : PolyProfile}
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier)
    (subjectNormal : RawTerm.isStepNormalForm subject) :
    PinnedReflectionConclusion profile targetContext subject classifier :=
  HasTypeDescPi.pinnedReflectionGuarded (plateauResidualGuarded profile subject.size)
    derivation (Nat.le_refl _) subjectNormal

end FX1Poly.Typed

#print axioms FX1Poly.Typed.pinExtractFormationClassifier
#print axioms FX1Poly.Typed.pinExtractNeutralClassifier
#print axioms FX1Poly.Typed.plateauResidualGuarded
#print axioms FX1Poly.Typed.HasTypeDescPi.pinnedReflectionNormal
