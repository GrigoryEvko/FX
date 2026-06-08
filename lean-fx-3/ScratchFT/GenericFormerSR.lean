import FX1Poly.Typed.FormerStepInversionGeneric
import FX1Poly.Typed.HasTypeDescPi

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe: cascade-free generic former SR. A step out of a genFormationPi-typed former is a child congruence
(TG-1); re-type the premise telescope via the mutual-partner telescope SR and reassemble via the generic
genFormationPi at the SAME output type. One arm for the WHOLE formation family — no enumeration, no per-arity
hard-coding; a new formation row is absorbed zero-touch. -/
theorem HasTypeDescPi.subjectReductionAtFormerGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
    {target : RawTerm scope}
    (isFormation : typingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target)
    (telescopeSR : ∀ {childrenAfter : RawTermChildren generator.binderShifts scope},
      StepChildren children childrenAfter →
        DescTelescopePi profile (currentDepth := 0) context levels flag childrenAfter) :
    HasTypeDescPi profile context target (rule.outputType scope levels flag) := by
  obtain ⟨childrenAfter, targetEq, stepChildren⟩ := formerCellStepIsChildCongruence isFormation step
  subst targetEq
  exact HasTypeDescPi.genFormationPi context generator payload childrenAfter levels flag rule isFormation
    (telescopeSR stepChildren)

#print axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtFormerGeneric

end FX1Poly.Typed
