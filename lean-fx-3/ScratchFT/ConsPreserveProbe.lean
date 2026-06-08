import FX1Poly.Typed.ConsistentStratification
import FX1Poly.Typed.ReducibleEnvVec

/-! SCRATCH: #662 binder-extension preservation ConsistentStratification.cons. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- Does levelCons compute on a weakened index by rfl?
theorem levelCons_weaken_probe {scope : Nat} (headLevel : Nat)
    (tailLevels : Fin scope → Nat) (index : Fin scope) :
    levelCons headLevel tailLevels (RawRenaming.weaken index) = tailLevels index := rfl

-- Does levelCons at 0 = headLevel by rfl?
theorem levelCons_zero_probe {scope : Nat} (headLevel : Nat)
    (tailLevels : Fin scope → Nat) (isLt : 0 < scope + 1) :
    levelCons headLevel tailLevels ⟨0, isLt⟩ = headLevel := rfl

-- the binder-extension preservation
theorem consPreserveProbe {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context)
    {headLevel : Nat} {domainCode : RawTerm scope}
    (domainConstraint : ∀ sourceIndex : Fin scope,
      domainCode = variableCell sourceIndex → contextLevels sourceIndex = headLevel + 1) :
    ConsistentStratification (levelCons headLevel contextLevels) (context.cons domainCode) := by
  intro termIndex typeIndex isVarType
  match termIndex with
  | ⟨0, isLt⟩ =>
      rw [TypingContext.lookup_cons_zero context domainCode isLt] at isVarType
      obtain ⟨sourceIndex, domEq, weakenEq⟩ :=
        rename_eq_variableCell_inversion RawRenaming.weaken isVarType
      rw [← weakenEq]
      show levelCons headLevel contextLevels (RawRenaming.weaken sourceIndex) = headLevel + 1
      rw [levelCons_weaken_probe]
      exact domainConstraint sourceIndex domEq
  | ⟨position + 1, isLtSucc⟩ =>
      rw [TypingContext.lookup_cons_succ context domainCode position isLtSucc] at isVarType
      obtain ⟨sourceIndex, lookupEq, weakenEq⟩ :=
        rename_eq_variableCell_inversion RawRenaming.weaken isVarType
      rw [← weakenEq]
      show levelCons headLevel contextLevels (RawRenaming.weaken sourceIndex)
        = contextLevels ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ + 1
      rw [levelCons_weaken_probe]
      exact consistent ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ sourceIndex lookupEq

end FX1Poly.Typed

#print axioms FX1Poly.Typed.consPreserveProbe
#print axioms FX1Poly.Typed.levelCons_weaken_probe
