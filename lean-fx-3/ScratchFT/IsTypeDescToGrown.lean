import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.HasTypeDescValidity

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe: the IsType-level functoriality of the formation→grown embedding (the type-level mirror of the
shipped term-level HasTypeDesc.toHasTypeDescPi): a formation type is a grown type. -/
theorem IsTypeDesc.toIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsTypeDesc profile context classifier) :
    IsTypeDescPi profile context classifier := by
  obtain ⟨levelExpr, flag, universeTyped⟩ := isType
  exact ⟨levelExpr, flag, HasTypeDescPi.ofFormation universeTyped⟩

#print axioms FX1Poly.Typed.IsTypeDesc.toIsTypeDescPi

end FX1Poly.Typed
