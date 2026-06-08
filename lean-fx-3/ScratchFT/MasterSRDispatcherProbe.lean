import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.HasTypeDescSubjectReduction

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- The conditional master SR dispatcher over WfContextDescPi, with the grown telescope SR as the explicit
-- hypothesis (the genFormationPi residual = the GCC bundle). All other arms are shipped.
theorem HasTypeDescPi.subjectReductionOfGrownTelescopeSR {profile : PolyProfile}
    (telescopeSR : ∀ {baseScope currentDepth : Nat} {binderShifts : List Nat}
        {telescopeContext : TypingContext profile (baseScope + currentDepth)}
        {levels : List LevelExpr} {flag : UniverseFlag}
        {children : RawTermChildren binderShifts baseScope},
        DescTelescopePi profile telescopeContext levels flag children →
        ∀ children' : RawTermChildren binderShifts baseScope,
          StepChildren children children' →
          DescTelescopePi profile telescopeContext levels flag children')
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (derivation : HasTypeDescPi profile context subject classifier) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescPi profile context reduct classifier :=
  match derivation with
  | .ofFormation formationTyped => fun reduct step =>
      absurd step (formationTyped.subjectAdmitsNoStep reduct)
  | .conv levelExpr flag typed converts reclassifierTyped => fun reduct step =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR wellFormed typed reduct step)
        converts reclassifierTyped
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
        (fun {bodyReduct} bodyStep =>
          HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR
            (WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩)
            bodyTyped bodyReduct bodyStep)
  | .piElim functionTyped argumentTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiElimArmDescPi functionTyped argumentTyped step
        (fun {functionReduct} functionStep =>
          HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR wellFormed functionTyped
            functionReduct functionStep)
        (fun {argumentReduct} argumentStep =>
          HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR wellFormed argumentTyped
            argumentReduct argumentStep)
        wellFormed
  | .genFormationPi formerContext generator payload children levels flag rule isFormation premises =>
      fun reduct step => by
      obtain ⟨children', reductEq, stepChildren⟩ := former_step_inv isFormation step
      subst reductEq
      exact HasTypeDescPi.genFormationPi formerContext generator payload children' levels flag rule
        isFormation (telescopeSR premises children' stepChildren)

#print axioms HasTypeDescPi.subjectReductionOfGrownTelescopeSR

end FX1Poly.Typed
