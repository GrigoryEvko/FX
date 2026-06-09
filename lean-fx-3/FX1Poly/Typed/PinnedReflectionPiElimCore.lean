import FX1Poly.Typed.GrownPinnedReflection
import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Core.RawTermFresh

/-! # FX1Poly/Typed/PinnedReflectionPiElimCore — the pinned-function piElim discharge
     (route-H reflection, the residual's core + first concrete instance)

The conditional grown pinned-reflection master (`GrownPinnedReflection`) isolates ONE open arm:
`PinnedReflectionPiElimResidual` — the application case, where the conclusion's pin
(`subst0 codomainCode argument`) says nothing about the FUNCTION's Π classifier.  This file
factors the residual's discharge:

  * `pinnedReflectionPiElimCore` — the residual conclusion holds whenever the function's Π
    classifier IS pinned (Conv to a `ρ`-image of a source-typed base).  The proof is the
    full reflection pipeline: the pinning analysis exposes exact image components with a
    source chain (`pinnedPiComponentsWithSourceChain`); source subject reduction + Π-formation
    inversion type the source components; the premise IHs reflect the function and the
    argument at their respective pins; injective Conv reflection re-pins both to the exact
    source Π/domain; `piElim` rebuilds; `rename_subst0_commute` + `Conv.subst` close the
    output Conv.  This is the CONSUMER SHAPE for every head analysis — whatever produces a
    function-Π pin finishes through here.

  * `pinnedReflectionPiElimVarArm` — the first concrete producer: a VARIABLE-headed function's
    Π pin comes for free from `invertVar` (the classifier converts to the target lookup) +
    the Kripke context condition (the target lookup converts to the image of the source
    lookup) + `WfContextDescPi.lookupIsType` (the source lookup is source-typed).  Note the
    motive's OUTPUT pin hypotheses are unused here — the application's classifier regenerates
    from the spine, which is exactly why the residual was open.

The remaining open head shapes (λ-headed after whnf, nested applications) route through the
whnf analysis; each new head analysis is one more producer feeding `pinnedReflectionPiElimCore`.

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The pinned-function piElim core**: the residual conclusion, given a pin for the FUNCTION's Π
classifier.  This is the consumer shape for every head analysis: whatever pins the function's Π
(context condition for var heads, spine recursion for neutrals, ...) finishes through here. -/
theorem pinnedReflectionPiElimCore (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)}
    (functionIH : PinnedReflectionConclusion profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode))
    (argumentIH : PinnedReflectionConclusion profile targetContext argument domainCode)
    {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetWellFormed : WfContextDescPi targetContext)
    (rhoInjective : Function.Injective rho)
    (condition : ContextReflectsRename profile rho sourceContext targetContext)
    (wellFormed : WfContextDescPi sourceContext)
    {sourceFunction sourceArgument piBase : RawTerm sourceScope}
    (functionInImage : functionTerm = RawTerm.rename rho sourceFunction)
    (argumentInImage : argument = RawTerm.rename rho sourceArgument)
    (piPinned :
      Conv (piTyCodeCell domainCode codomainCode) (RawTerm.rename rho piBase))
    (piBaseTyped : IsTypeDescPi profile sourceContext piBase) :
    ∃ reflectedClassifier : RawTerm sourceScope,
      Conv (RawTerm.subst0 codomainCode argument)
        (RawTerm.rename rho reflectedClassifier) ∧
      HasTypeDescPi profile sourceContext (appCell sourceFunction sourceArgument)
        reflectedClassifier := by
  obtain ⟨domainBase, codomainBase, sourceChain, domainConv, codomainConv⟩ :=
    Conv.pinnedPiComponentsWithSourceChain rho piPinned
  obtain ⟨piLevel, piFlag, piBaseTypedAt⟩ := piBaseTyped
  have piTyped : HasTypeDescPi profile sourceContext
      (piTyCodeCell domainBase codomainBase) (universeCodeCell piLevel piFlag) :=
    HasTypeDescPi.subjectReductionStar wellFormed piBaseTypedAt sourceChain
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, _convToOutput⟩ :=
    HasTypeDescPi.invertPiTyCode piTyped
  obtain ⟨reflectedFunctionClassifier, functionClassifierConv, functionReflected⟩ :=
    functionIH targetWellFormed rho sourceContext rhoInjective condition wellFormed
      functionInImage piPinned ⟨piLevel, piFlag, piBaseTypedAt⟩
  have piImagesConv :
      Conv (RawTerm.rename rho reflectedFunctionClassifier)
        (RawTerm.rename rho piBase) :=
    functionClassifierConv.sym.trans piPinned
  have reflectedToPiBase : Conv reflectedFunctionClassifier piBase :=
    Conv.reflectRenameOfFinInjective rho rhoInjective piImagesConv
  have piBaseToPiCell : Conv piBase (piTyCodeCell domainBase codomainBase) :=
    ⟨piTyCodeCell domainBase codomainBase, sourceChain, StepStar.refl _⟩
  have functionAtSourcePi :
      HasTypeDescPi profile sourceContext sourceFunction
        (piTyCodeCell domainBase codomainBase) :=
    HasTypeDescPi.conv piLevel piFlag functionReflected
      (reflectedToPiBase.trans piBaseToPiCell) piTyped
  obtain ⟨reflectedArgumentClassifier, argumentClassifierConv, argumentReflected⟩ :=
    argumentIH targetWellFormed rho sourceContext rhoInjective condition wellFormed
      argumentInImage domainConv ⟨domainLevel, flag, domainTyped⟩
  have domainImagesConv :
      Conv (RawTerm.rename rho reflectedArgumentClassifier)
        (RawTerm.rename rho domainBase) :=
    argumentClassifierConv.sym.trans domainConv
  have argumentAtDomainBase :
      HasTypeDescPi profile sourceContext sourceArgument domainBase :=
    HasTypeDescPi.conv domainLevel flag argumentReflected
      (Conv.reflectRenameOfFinInjective rho rhoInjective domainImagesConv) domainTyped
  refine ⟨RawTerm.subst0 codomainBase sourceArgument, ?_, ?_⟩
  · rw [RawTerm.rename_subst0_commute, ← argumentInImage]
    exact Conv.subst _ codomainConv
  · exact HasTypeDescPi.piElim functionAtSourcePi argumentAtDomainBase

/-- **The variable-function instance of the piElim residual** — the first concrete fragment: a
var-headed function's Π classifier pins from `invertVar` + the Kripke context condition, with the
pin base source-typed by `lookupIsType`.  The OUTPUT pin is unused (the conclusion classifier
regenerates from the spine). -/
theorem pinnedReflectionPiElimVarArm (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {index : Fin targetScope} {argument domainCode : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)}
    (functionTyped : HasTypeDescPi profile targetContext (variableCell index)
      (piTyCodeCell domainCode codomainCode))
    (functionIH : PinnedReflectionConclusion profile targetContext (variableCell index)
      (piTyCodeCell domainCode codomainCode))
    (argumentIH : PinnedReflectionConclusion profile targetContext argument domainCode) :
    PinnedReflectionConclusion profile targetContext
      (appCell (variableCell index) argument)
      (RawTerm.subst0 codomainCode argument) := by
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage _pinned _pinBaseTyped
  obtain ⟨sourceFunction, sourceArgument, hSubject, hFunction, hArgument⟩ :=
    renameEqAppCellInversion rho subjectInImage.symm
  subst hSubject
  obtain ⟨sourceIndex, hSourceFunction, hIndex⟩ :=
    renameEqVariableCellInversion rho hFunction.symm
  subst hSourceFunction
  subst hIndex
  have piPinned :
      Conv (piTyCodeCell domainCode codomainCode)
        (RawTerm.rename rho (sourceContext.lookup sourceIndex)) :=
    (HasTypeDescPi.invertVar functionTyped).trans (condition sourceIndex)
  have piBaseTyped :
      IsTypeDescPi profile sourceContext (sourceContext.lookup sourceIndex) :=
    WfContextDescPi.lookupIsType sourceContext wellFormed sourceIndex
  exact pinnedReflectionPiElimCore profile functionIH argumentIH rho sourceContext
    targetWellFormed rhoInjective condition wellFormed rfl hArgument piPinned piBaseTyped

/-- **The reduces-to-variable producer** — the first whnf-route case, strictly generalizing the
var arm: a function that `StepStar`-REDUCES to a variable pins its Π through target-side subject
reduction (the exact consumer of the motive's target-wf premise) + `invertVar` on the reduct + the
Kripke context condition.  The reduct is automatically in-image (`StepStar.reflectRename` on the
in-image function), so the source index exists; the core then finishes with the ORIGINAL premise
IHs — the reduction only serves to REVEAL the pin, which is a property of the shared classifier. -/
theorem pinnedReflectionPiElimReducesToVarArm (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)} {index : Fin targetScope}
    (functionTyped : HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode))
    (functionReduces : StepStar functionTerm (variableCell index))
    (functionIH : PinnedReflectionConclusion profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode))
    (argumentIH : PinnedReflectionConclusion profile targetContext argument domainCode) :
    PinnedReflectionConclusion profile targetContext
      (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument) := by
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage _pinned _pinBaseTyped
  obtain ⟨sourceFunction, sourceArgument, hSubject, hFunction, hArgument⟩ :=
    renameEqAppCellInversion rho subjectInImage.symm
  subst hSubject
  rw [hFunction] at functionReduces
  obtain ⟨sourceReduct, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename rho functionReduces
  obtain ⟨sourceIndex, _hSourceReduct, hIndex⟩ :=
    renameEqVariableCellInversion rho imageEq
  subst hIndex
  have varTyped : HasTypeDescPi profile targetContext (variableCell (rho sourceIndex))
      (piTyCodeCell domainCode codomainCode) := by
    rw [hFunction] at functionTyped
    exact HasTypeDescPi.subjectReductionStar targetWellFormed functionTyped functionReduces
  have piPinned :
      Conv (piTyCodeCell domainCode codomainCode)
        (RawTerm.rename rho (sourceContext.lookup sourceIndex)) :=
    (HasTypeDescPi.invertVar varTyped).trans (condition sourceIndex)
  have piBaseTyped :
      IsTypeDescPi profile sourceContext (sourceContext.lookup sourceIndex) :=
    WfContextDescPi.lookupIsType sourceContext wellFormed sourceIndex
  exact pinnedReflectionPiElimCore profile functionIH argumentIH rho sourceContext
    targetWellFormed rhoInjective condition wellFormed hFunction hArgument piPinned piBaseTyped

end FX1Poly.Typed
