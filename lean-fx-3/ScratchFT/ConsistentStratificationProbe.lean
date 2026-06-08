import FX1Poly.Typed.ValidTyping

/-! SCRATCH: #662 ConsistentStratification foundational brick. Verify here, then move to library. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

def ConsistentStratification {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) : Prop :=
  ∀ (termIndex typeIndex : Fin scope),
    context.lookup termIndex = variableCell typeIndex →
    contextLevels typeIndex = contextLevels termIndex + 1

theorem consistentStratification_empty {profile : PolyProfile}
    (contextLevels : Fin 0 → Nat) :
    ConsistentStratification contextLevels (TypingContext.empty : TypingContext profile 0) :=
  fun termIndex _typeIndex _ => termIndex.elim0

theorem ConsistentStratification.strictlyBelowType {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context)
    {termIndex typeIndex : Fin scope}
    (isVarType : context.lookup termIndex = variableCell typeIndex) :
    contextLevels termIndex < contextLevels typeIndex := by
  rw [consistent termIndex typeIndex isVarType]
  exact Nat.lt_succ_self _

theorem ConsistentStratification.noSelfType {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context) (index : Fin scope) :
    context.lookup index ≠ variableCell index := by
  intro isSelfType
  exact absurd (consistent.strictlyBelowType isSelfType) (Nat.lt_irrefl _)

end FX1Poly.Typed
