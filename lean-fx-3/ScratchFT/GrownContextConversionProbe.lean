import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescContextConversion

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- The grown context-conversion mutual pair, conditional on the lone hard piElim arm.
mutual

theorem HasTypeDescPi.convContextOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {scope : Nat} {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      ∃ classifier', Conv classifier classifier' ∧
        HasTypeDescPi profile targetContext subject classifier' :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext contextConv =>
      HasTypeDescPi.convContextOfFormation formationTyped targetContext contextConv
  | .conv levelExpr flag typed converts _reclassifierTyped => fun targetContext contextConv => by
      obtain ⟨classifier', convClassifierToClassifier', typedAtClassifier'⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm typed targetContext contextConv
      exact ⟨classifier', Conv.trans converts.sym convClassifierToClassifier', typedAtClassifier'⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext contextConv => by
      obtain ⟨_clsD, convD, domainAtClsD⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm domainTyped targetContext contextConv
      have domainTyped' : HasTypeDescPi profile targetContext domainCode
          (universeCodeCell domainLevel flag) := domainAtClsD.convBackToUniverseCode convD
      obtain ⟨_clsC, convC, codomainAtClsC⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm codomainTyped (targetContext.cons domainCode)
          (convContextCondition_cons domainCode contextConv)
      have codomainTyped' : HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := codomainAtClsC.convBackToUniverseCode convC
      obtain ⟨_clsBody, convBody, bodyAtClsBody⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm bodyTyped (targetContext.cons domainCode)
          (convContextCondition_cons domainCode contextConv)
      have bodyTyped' : HasTypeDescPi profile (targetContext.cons domainCode) body codomainCode :=
        HasTypeDescPi.conv codomainLevel flag bodyAtClsBody convBody.sym codomainTyped'
      exact ⟨piTyCodeCell domainCode codomainCode, Conv.refl _,
        HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped' codomainTyped' bodyTyped'⟩
  | .piElim functionTyped argumentTyped => fun targetContext contextConv =>
      piElimArm functionTyped argumentTyped targetContext contextConv
  | .genFormationPi _formerContext generator payload children levels flag rule isFormation premises =>
      fun targetContext contextConv =>
      ⟨rule.outputType scope levels flag, Conv.refl _,
        HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule
          isFormation
          (DescTelescopePi.convTelescopeOfPiElimArm piElimArm premises targetContext contextConv)⟩

theorem DescTelescopePi.convTelescopeOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _contextConv =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext contextConv => by
        obtain ⟨_headClassifier, headConv, headAtClassifier⟩ :=
          HasTypeDescPi.convContextOfPiElimArm piElimArm headTyped targetContext contextConv
        have headTyped' : HasTypeDescPi profile targetContext head (universeCodeCell headLevel flag) :=
          headAtClassifier.convBackToUniverseCode headConv
        refine DescTelescopePi.cons targetContext head headLevel restLevels flag rest headTyped' ?_
        exact DescTelescopePi.convTelescopeOfPiElimArm piElimArm restTyped (targetContext.cons head)
          (convContextCondition_cons head contextConv)

end

#print axioms HasTypeDescPi.convContextOfPiElimArm
#print axioms DescTelescopePi.convTelescopeOfPiElimArm

end FX1Poly.Typed
