import FX1Poly.Typed.GrownPinnedReflection
import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Core.RawTermFresh

/-! Probe: STR-8b core — the PINNED-FUNCTION piElim discharge.  If the function's Π classifier IS
pinned (Conv to an image of a source-typed base), the residual conclusion follows from the premise
IHs: pin analysis → source Π components typed via SR + inversion → reflect function and argument →
re-pin both via injective Conv reflection → rebuild piElim → output Conv via rename_subst0_commute.
Plus the FIRST concrete instance: variable-headed functions, whose Π pin comes from `invertVar` +
the Kripke context condition + `lookupIsType`. -/

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

end FX1Poly.Typed

#print axioms FX1Poly.Typed.pinnedReflectionPiElimCore
#print axioms FX1Poly.Typed.pinnedReflectionPiElimVarArm
