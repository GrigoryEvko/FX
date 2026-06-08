import FX1Poly.Typed.WfContextDescPi
import FX1Poly.Typed.HasTypeDescPiWeakening

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- IsTypeDescPi survives a binding extension (grown weakening). -/
theorem IsTypeDescPi.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsTypeDescPi profile context classifier) (newBinding : RawTerm scope) :
    IsTypeDescPi profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken classifier) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, typed.weakenUnderBinding newBinding⟩

/-- Lookup in a grown-well-formed context yields a grown type. -/
theorem WfContextDescPi.lookupIsType {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContextDescPi context →
      ∀ index : Fin scope, IsTypeDescPi profile context (context.lookup index) := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          exact (WfContextDescPi.headIsType wellFormed).weakenUnderBinding bindingType
      | succ k =>
          exact (ih (WfContextDescPi.tailWellFormed wellFormed)
            ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding bindingType

#print axioms FX1Poly.Typed.IsTypeDescPi.weakenUnderBinding
#print axioms FX1Poly.Typed.WfContextDescPi.lookupIsType

end FX1Poly.Typed
