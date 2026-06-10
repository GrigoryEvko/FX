import FX1Poly.Typed.PinnedReflectionPiElimCore

/-! Probe: STR-8b second producer — functions that StepStar-REDUCE to a variable.  Strictly
generalizes the var arm; the first whnf-route case, exercising target-side SR-star (the exact
consumer of the motive's target-wf premise). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

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
  obtain ⟨sourceIndex, hSourceReduct, hIndex⟩ :=
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

#print axioms FX1Poly.Typed.pinnedReflectionPiElimReducesToVarArm
