import FX1Poly.Typed.WfContextDescPi
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Probe: IsTypeDescPi survives single-substitution (subst dual of weakenUnderBinding). -/
theorem IsTypeDescPi.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {classifier : RawTerm (scope + 1)}
    (isType : IsTypeDescPi profile (context.cons argType) classifier)
    (argument : RawTerm scope)
    (argumentTyped : HasTypeDescPi profile context argument argType) :
    IsTypeDescPi profile context (RawTerm.subst0 classifier argument) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, typed.substituteUnderBinding argument argumentTyped⟩

#print axioms FX1Poly.Typed.IsTypeDescPi.substituteUnderBinding

end FX1Poly.Typed
