import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Core.WeakHeadStep

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe: cascade-free formationGenerator_noWeakHeadStep — a formation former cell admits no weak-head step,
proven WITHOUT enumerating pi/sigma (TG-1 idiom: refute each redex arm via isFormation's none=some). -/
theorem formationGenerator_noWeakHeadStep_generic {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} (isFormation : typingRuleDescOf generator = some rule) :
    ∀ reduct : RawTerm scope,
      ¬ WeakHeadStep (.mkGen generator payload children) reduct := by
  intro _reduct weakHeadStep
  cases weakHeadStep with
  | beta => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | appCongruence _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | rootIota iotaStep =>
      cases iotaStep <;> nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeBoolElim _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeFst _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeSnd _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeNatElim _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeNatRec _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeListElim _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeOptionMatch _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeEitherMatch _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeIdJ _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)
  | scrutineeIdStrictRec _ => nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)

#print axioms FX1Poly.Typed.formationGenerator_noWeakHeadStep_generic

end FX1Poly.Typed
