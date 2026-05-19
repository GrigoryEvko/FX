import LeanFX2.Tools.Tactics.Choreography

/-! # Smoke/AuditTacticsChoreography

Smoke checks for the project-wide tactic choreography helpers.
-/

namespace LeanFX2.Smoke.AuditTacticsChoreography

#print axioms LeanFX2.optionSomeContradictsNone
#print axioms LeanFX2.optionSomePayloadEq_of_sameOptionSuccess
#print axioms LeanFX2.optionNoneIsSomeContradictsTrue

example {someType : Type} {someValue : someType}
    {optionValue : Option someType}
    (someSuccess : optionValue = some someValue)
    (noneSuccess : optionValue = none) : False := by
  fx_contradict_none someSuccess with noneSuccess

example {someType : Type} {leftValue rightValue : someType}
    {optionValue : Option someType}
    (leftSuccess : optionValue = some leftValue)
    (rightSuccess : optionValue = some rightValue) :
    leftValue = rightValue := by
  fx_some_payload_eq payloadEq from leftSuccess and rightSuccess
  exact payloadEq

example {someType : Type} {leftValue rightValue : someType}
    {optionValue : Option someType}
    (leftSuccess : optionValue = some leftValue)
    (rightSuccess : optionValue = some rightValue)
    (payloadConsumer : leftValue = rightValue → True) : True := by
  fx_subst_some_payload payloadEq from leftSuccess and rightSuccess
  exact payloadConsumer rfl

example {someType : Type}
    (isSomeNone : Option.isSome (none : Option someType) = true) :
    False := by
  fx_contradict_none_isSome isSomeNone

example {firstType secondType : Type} (typeEq : firstType = secondType)
    (someValue : firstType) :
    HEq (typeEq ▸ someValue) someValue := by
  fx_heq_cast

example {someValue : Nat} : someValue = someValue := by
  fx_rfl

example {someValue : Nat} (valueEq : someValue = someValue) :
    someValue = someValue := by
  fx_cases_rfl valueEq

example {firstValue secondValue : Nat}
    (valueHEq : HEq firstValue secondValue) :
    HEq secondValue firstValue := by
  fx_heq_symm valueHEq

example {firstValue secondValue thirdValue : Nat}
    (firstHEq : HEq firstValue secondValue)
    (secondHEq : HEq secondValue thirdValue) :
    HEq firstValue thirdValue := by
  fx_heq_trans firstHEq then secondHEq

example {firstValue secondValue thirdValue fourthValue : Nat}
    (firstHEq : HEq firstValue secondValue)
    (secondHEq : HEq secondValue thirdValue)
    (thirdHEq : HEq thirdValue fourthValue) :
    HEq firstValue fourthValue := by
  fx_heq_trans3 firstHEq then secondHEq then thirdHEq

example
    {firstValue secondValue thirdValue fourthValue fifthValue : Nat}
    (firstHEq : HEq firstValue secondValue)
    (secondHEq : HEq secondValue thirdValue)
    (thirdHEq : HEq thirdValue fourthValue)
    (fourthHEq : HEq fourthValue fifthValue) :
    HEq firstValue fifthValue := by
  fx_heq_trans4 firstHEq then secondHEq then thirdHEq then fourthHEq

example {firstValue secondValue thirdValue : Nat}
    (firstHEq : HEq firstValue secondValue)
    (secondHEq : HEq secondValue thirdValue) :
    HEq firstValue thirdValue := by
  fx_have_heq_trans resultHEq from firstHEq then secondHEq
  exact resultHEq

example {firstValue secondValue : Nat}
    (valueHEq : HEq firstValue secondValue) :
    HEq secondValue firstValue := by
  fx_have_heq_symm resultHEq from valueHEq
  exact resultHEq

end LeanFX2.Smoke.AuditTacticsChoreography
