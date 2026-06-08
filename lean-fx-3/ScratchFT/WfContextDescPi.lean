import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.WfContext

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Grown context well-formedness: every binding is a GROWN type (IsTypeDescPi) in its prefix. The structural
-- parity twin of WfContext (which is HasType-based, hence not extendable at a grown binder). -/
def WfContextDescPi {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext bindingType =>
      WfContextDescPi restContext ∧ IsTypeDescPi profile restContext bindingType

theorem WfContextDescPi.emptyIsWellFormed {profile : PolyProfile} :
    WfContextDescPi (profile := profile) .empty :=
  trivial

theorem WfContextDescPi.tailWellFormed {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextDescPi (restContext.cons bindingType)) :
    WfContextDescPi restContext :=
  wellFormed.1

theorem WfContextDescPi.headIsType {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextDescPi (restContext.cons bindingType)) :
    IsTypeDescPi profile restContext bindingType :=
  wellFormed.2

theorem WfContextDescPi.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextDescPi restContext)
    (bindingIsType : IsTypeDescPi profile restContext bindingType) :
    WfContextDescPi (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingIsType⟩

/-- Every HasType-well-formed context is grown-well-formed: each HasType binding embeds via ofFormation. The
-- easy bridge (IsType → IsTypeDescPi); lets grown metatheory consume the shipped WfContext hypotheses. -/
theorem WfContextDescPi.ofWfContext {profile : PolyProfile} :
    {scope : Nat} → {context : TypingContext profile scope} →
      WfContext context → WfContextDescPi context
  | _, .empty, _ => trivial
  | _, .cons restContext bindingType, wellFormed =>
      ⟨WfContextDescPi.ofWfContext wellFormed.tailWellFormed,
        let ⟨levelExpr, flag, hasTypeDeriv⟩ := wellFormed.headIsType
        ⟨levelExpr, flag, HasTypeDescPi.ofFormation hasTypeDeriv.toHasTypeDesc⟩⟩

theorem wfContextDescPi_universeBinding {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    WfContextDescPi (profile := profile)
      ((TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag)) :=
  ⟨trivial,
    ⟨levelExpr.lsucc, flag,
      HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0)
          levelExpr flag)⟩⟩

#print axioms FX1Poly.Typed.WfContextDescPi
#print axioms FX1Poly.Typed.WfContextDescPi.cons
#print axioms FX1Poly.Typed.WfContextDescPi.ofWfContext
#print axioms FX1Poly.Typed.wfContextDescPi_universeBinding

end FX1Poly.Typed
