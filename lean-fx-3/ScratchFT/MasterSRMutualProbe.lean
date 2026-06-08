import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiContextConversionConditional

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

theorem HasTypeDescPi.subjectReductionOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescPi profile context reduct classifier :=
  match derivation with
  | .ofFormation formationTyped => fun reduct step =>
      absurd step (formationTyped.subjectAdmitsNoStep reduct)
  | .conv levelExpr flag typed converts reclassifierTyped => fun reduct step =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.subjectReductionOfPiElimArm piElimArm typed wellFormed reduct step)
        converts reclassifierTyped
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
        (fun {bodyReduct} bodyStep =>
          HasTypeDescPi.subjectReductionOfPiElimArm piElimArm bodyTyped
            (WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩) bodyReduct bodyStep)
  | .piElim functionTyped argumentTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiElimArmDescPi functionTyped argumentTyped step
        (fun {functionReduct} functionStep =>
          HasTypeDescPi.subjectReductionOfPiElimArm piElimArm functionTyped wellFormed
            functionReduct functionStep)
        (fun {argumentReduct} argumentStep =>
          HasTypeDescPi.subjectReductionOfPiElimArm piElimArm argumentTyped wellFormed
            argumentReduct argumentStep)
        wellFormed
  | .genFormationPi formerContext generator payload children levels flag rule isFormation premises =>
      fun reduct step => by
      obtain ⟨children', reductEq, stepChildren⟩ := former_step_inv isFormation step
      subst reductEq
      exact HasTypeDescPi.genFormationPi formerContext generator payload children' levels flag rule
        isFormation
        (DescTelescopePi.subjectReductionOfPiElimArm piElimArm premises wellFormed children'
          stepChildren)

theorem DescTelescopePi.subjectReductionOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children)
    (wellFormed : WfContextDescPi context) :
    ∀ (children' : RawTermChildren binderShifts baseScope),
      StepChildren children children' → DescTelescopePi profile context levels flag children' :=
  match telescope with
  | .nil _context _flag => fun _children' stepChildren =>
      (StepChildren.no_step_at_empty_spine stepChildren).elim
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      fun _children' stepChildren => by
        cases stepChildren with
        | here _rest headStep =>
            rename_i headAfter
            refine DescTelescopePi.cons context headAfter headLevel restLevels flag rest
              (HasTypeDescPi.subjectReductionOfPiElimArm piElimArm headTyped wellFormed headAfter
                headStep) ?_
            exact DescTelescopePi.convTelescopeOfPiElimArm piElimArm restTyped
              (context.cons headAfter)
              (convContextCondition_consStep ⟨headAfter, StepStar.single headStep, StepStar.refl _⟩)
        | there _head restStep =>
            rename_i restAfter
            exact DescTelescopePi.cons context head headLevel restLevels flag restAfter headTyped
              (DescTelescopePi.subjectReductionOfPiElimArm piElimArm restTyped
                (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩) restAfter restStep)

end

#print axioms HasTypeDescPi.subjectReductionOfPiElimArm
#print axioms DescTelescopePi.subjectReductionOfPiElimArm

end FX1Poly.Typed
