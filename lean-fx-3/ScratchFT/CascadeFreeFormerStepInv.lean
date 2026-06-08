import FX1Poly.Typed.HasTypeDescSubjectReduction

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe: cascade-free `former_step_inv` — no enumeration of formation generators.  A step out of any
formation-rule cell is a child congruence; each ROOT-redex case forces the head to a redex generator whose
`typingRuleDescOf = none`, refuted against `isFormation`.  Survives every future formation row (zero-touch). -/
theorem former_step_inv_cascadeFree {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} {target : RawTerm scope}
    (isFormation : typingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' := by
  cases step with
  | cong _ _ childStep => exact ⟨_, rfl, childStep⟩
  | beta => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaBoolTrue => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaBoolFalse => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaFstPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaSndPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatElimZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatRecZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaListElimNil => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaOptionMatchNone => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaOptionMatchSome => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaEitherMatchInl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaEitherMatchInr => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatElimSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaNatRecSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaListElimCons => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaIdJRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | iotaIdStrictRecRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)

#print axioms FX1Poly.Typed.former_step_inv_cascadeFree

end FX1Poly.Typed
