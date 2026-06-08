import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.HasTypeDescValidity

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe: a FORMATION-typed cell's classifier is a GROWN type (IsTypeDescPi) under grown well-formedness.
The var arm uses WfContextDescPi.lookupIsType (concluding IsTypeDescPi directly); the others lift the formation
universe-typing via ofFormation. The formation-engine var-arm engine of grown classifier-validity. -/
theorem HasTypeDesc.classifierIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (derivation : HasTypeDesc profile context subject classifier) :
    IsTypeDescPi profile context classifier :=
  match derivation with
  | .var context index => WfContextDescPi.lookupIsType context wellFormed index
  | .conv levelExpr flag _typed _converts reclassifierTyped =>
      ⟨levelExpr, flag, HasTypeDescPi.ofFormation reclassifierTyped⟩
  | .universeFormation context levelExpr flag =>
      ⟨_, _, HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context levelExpr.lsucc flag)⟩
  | .genFormation context generator _payload _children levels flag rule isFormation _premises => by
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context (lmaxAll levels) flag)⟩

#print axioms FX1Poly.Typed.HasTypeDesc.classifierIsTypeDescPi

end FX1Poly.Typed
