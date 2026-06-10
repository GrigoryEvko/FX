import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiContextStepConversion

/-! Probe: the UNCONDITIONAL grown master subject reduction ⋈ grown telescope SR (SR-U4).
    A faithful copy of the conditional `subjectReductionOfPiElimArm` mutual with the `piElimArm`
    parameter DROPPED and the telescope `here` arm's tail re-typing routed through the
    UNCONDITIONAL `contextConversionTelescopeExact` (SR-U2) + `ofHeadStep` (SR-U3). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

theorem HasTypeDescPi.subjectReductionProbe {profile : PolyProfile}
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
        (HasTypeDescPi.subjectReductionProbe typed wellFormed reduct step)
        converts reclassifierTyped
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
        (fun {bodyReduct} bodyStep =>
          HasTypeDescPi.subjectReductionProbe bodyTyped
            (WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩) bodyReduct bodyStep)
  | .piElim functionTyped argumentTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiElimArmDescPi functionTyped argumentTyped step
        (fun {functionReduct} functionStep =>
          HasTypeDescPi.subjectReductionProbe functionTyped wellFormed
            functionReduct functionStep)
        (fun {argumentReduct} argumentStep =>
          HasTypeDescPi.subjectReductionProbe argumentTyped wellFormed
            argumentReduct argumentStep)
        wellFormed
  | .genFormationPi formerContext generator payload children levels flag rule isFormation premises =>
      fun reduct step => by
      obtain ⟨children', reductEq, stepChildren⟩ := former_step_inv isFormation step
      subst reductEq
      exact HasTypeDescPi.genFormationPi formerContext generator payload children' levels flag rule
        isFormation
        (DescTelescopePi.subjectReductionProbe premises wellFormed children' stepChildren)

theorem DescTelescopePi.subjectReductionProbe {profile : PolyProfile}
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
              (HasTypeDescPi.subjectReductionProbe headTyped wellFormed headAfter headStep) ?_
            exact DescTelescopePi.contextConversionTelescopeExact restTyped
              (context.cons headAfter)
              (ConvContextWithOldValid.ofHeadStep
                (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩) headStep)
        | there _head restStep =>
            rename_i restAfter
            exact DescTelescopePi.cons context head headLevel restLevels flag restAfter headTyped
              (DescTelescopePi.subjectReductionProbe restTyped
                (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩) restAfter restStep)

end

end FX1Poly.Typed

-- Axiom audit
#print axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionProbe
#print axioms FX1Poly.Typed.DescTelescopePi.subjectReductionProbe
