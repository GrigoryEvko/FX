import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimUnderWf
import FX1Poly.Typed.HasTypeDescPiClassifierValidity

/-! Probe: the FLEXIBLE grown context-conversion mutual, UNCONDITIONAL under target well-formedness.
    A faithful transform of `convContextOfPiElimArm ⋈ convTelescopeOfPiElimArm` with the `piElimArm`
    hypothesis DROPPED, `WfContextDescPi targetContext` threaded (extended at piIntro + telescope-cons via
    `WfContextDescPi.cons`), and the piElim case discharged by the brick `piElimArmUnderWfTarget`
    (functionFlexible derived from functionConverted via `classifierIsTypeDescPi`). Closes GrownCtxConv-5/#842
    as "grown context conversion under target wf". -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

theorem HasTypeDescPi.convContextFlexibleUnderWfProbe {profile : PolyProfile}
    {scope : Nat} {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      WfContextDescPi targetContext →
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      ∃ classifier', Conv classifier classifier' ∧
        HasTypeDescPi profile targetContext subject classifier' :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext _targetWf contextConv =>
      HasTypeDescPi.convContextOfFormation formationTyped targetContext contextConv
  | .conv levelExpr flag typed converts _reclassifierTyped =>
      fun targetContext targetWf contextConv => by
      obtain ⟨classifier', convClassifierToClassifier', typedAtClassifier'⟩ :=
        HasTypeDescPi.convContextFlexibleUnderWfProbe typed targetContext targetWf contextConv
      exact ⟨classifier', Conv.trans converts.sym convClassifierToClassifier', typedAtClassifier'⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext targetWf contextConv => by
      obtain ⟨_clsD, convD, domainAtClsD⟩ :=
        HasTypeDescPi.convContextFlexibleUnderWfProbe domainTyped targetContext targetWf contextConv
      have domainTyped' : HasTypeDescPi profile targetContext domainCode
          (universeCodeCell domainLevel flag) := domainAtClsD.convBackToUniverseCode convD
      have extendedWf : WfContextDescPi (targetContext.cons domainCode) :=
        WfContextDescPi.cons targetWf ⟨domainLevel, flag, domainTyped'⟩
      obtain ⟨_clsC, convC, codomainAtClsC⟩ :=
        HasTypeDescPi.convContextFlexibleUnderWfProbe codomainTyped (targetContext.cons domainCode)
          extendedWf (convContextCondition_cons domainCode contextConv)
      have codomainTyped' : HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := codomainAtClsC.convBackToUniverseCode convC
      obtain ⟨_clsBody, convBody, bodyAtClsBody⟩ :=
        HasTypeDescPi.convContextFlexibleUnderWfProbe bodyTyped (targetContext.cons domainCode)
          extendedWf (convContextCondition_cons domainCode contextConv)
      have bodyTyped' : HasTypeDescPi profile (targetContext.cons domainCode) body codomainCode :=
        HasTypeDescPi.conv codomainLevel flag bodyAtClsBody convBody.sym codomainTyped'
      exact ⟨piTyCodeCell domainCode codomainCode, Conv.refl _,
        HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped' codomainTyped' bodyTyped'⟩
  | .piElim functionTyped argumentTyped => fun targetContext targetWf contextConv => by
      obtain ⟨functionClassifier, convToFunctionClassifier, functionAtClassifier⟩ :=
        HasTypeDescPi.convContextFlexibleUnderWfProbe functionTyped targetContext targetWf contextConv
      exact HasTypeDescPi.piElimArmUnderWfTarget targetWf
        ⟨functionClassifier, convToFunctionClassifier,
          HasTypeDescPi.classifierIsTypeDescPi targetWf functionAtClassifier⟩
        ⟨functionClassifier, convToFunctionClassifier, functionAtClassifier⟩
        (HasTypeDescPi.convContextFlexibleUnderWfProbe argumentTyped targetContext targetWf contextConv)
  | .genFormationPi _formerContext generator payload children levels flag rule isFormation premises =>
      fun targetContext targetWf contextConv =>
      ⟨rule.outputType scope levels flag, Conv.refl _,
        HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule
          isFormation
          (DescTelescopePi.convTelescopeFlexibleUnderWfProbe premises targetContext targetWf contextConv)⟩

theorem DescTelescopePi.convTelescopeFlexibleUnderWfProbe {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      WfContextDescPi targetContext →
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _targetWf _contextConv =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext targetWf contextConv => by
        obtain ⟨_headClassifier, headConv, headAtClassifier⟩ :=
          HasTypeDescPi.convContextFlexibleUnderWfProbe headTyped targetContext targetWf contextConv
        have headTyped' : HasTypeDescPi profile targetContext head (universeCodeCell headLevel flag) :=
          headAtClassifier.convBackToUniverseCode headConv
        have extendedWf : WfContextDescPi (targetContext.cons head) :=
          WfContextDescPi.cons targetWf ⟨headLevel, flag, headTyped'⟩
        refine DescTelescopePi.cons targetContext head headLevel restLevels flag rest headTyped' ?_
        exact DescTelescopePi.convTelescopeFlexibleUnderWfProbe restTyped (targetContext.cons head)
          extendedWf (convContextCondition_cons head contextConv)

end

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.convContextFlexibleUnderWfProbe
#print axioms FX1Poly.Typed.DescTelescopePi.convTelescopeFlexibleUnderWfProbe
