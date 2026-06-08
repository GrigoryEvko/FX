import FX1Poly.Typed.DenoteKeyedReducibleEnv
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.HasTypeDescPi

/-! Scratch SN-D5d first brick: the denote-keyed telescope-reducibility predicate (the genFormationPi premise's
return type, single-level denote analogue of the fuel `TelescopeReducible`). Each head is a denote-reducible
member of its universe code at the ambient `level`; the tail is reducible under the cons-extended substitution by
any denote-reducible argument. Reuses the shipped `consecutiveShifts` index. SIMPLER than fuel: single ambient
level (no multi-level dispatch), `RawTermSubst … targetScope` (no +1). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

def TelescopeReducibleAtDenote {baseScope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    (flag : UniverseFlag) :
    (currentDepth : Nat) → (count : Nat) →
    RawTermSubst (baseScope + currentDepth) targetScope →
    List LevelExpr →
    RawTermChildren (consecutiveShifts currentDepth count) baseScope → Prop
  | _, 0, _, _, _ => True
  | _, _ + 1, _, [], _ => True
  | currentDepth, _ + 1, substitution, headLevel :: restLevels, .childCons head tail =>
      IsReducibleMemberAtDenote env level (universeCodeCell headLevel flag)
        (RawTerm.subst substitution head) ∧
      (∀ argument : RawTerm targetScope,
        IsReducibleMemberAtDenote env level (RawTerm.subst substitution head) argument →
        TelescopeReducibleAtDenote env level flag (currentDepth + 1) _
          (RawTermSubst.cons argument substitution) restLevels tail)

/-- The empty telescope (count 0) is reducible (vacuously). -/
theorem TelescopeReducibleAtDenote.nil {baseScope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    (flag : UniverseFlag) (currentDepth : Nat)
    (substitution : RawTermSubst (baseScope + currentDepth) targetScope)
    (children : RawTermChildren (consecutiveShifts currentDepth 0) baseScope) :
    TelescopeReducibleAtDenote env level flag currentDepth 0 substitution [] children :=
  True.intro

/-- A two-child former spine (`gen_piTyCode.binderShifts = [0,1] = consecutiveShifts 0 2`) reducibility unfolds
to: head reducible member of its universe, and per reducible argument the one-child tail reducible. -/
theorem TelescopeReducibleAtDenote.twoChild {baseScope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    (flag : UniverseFlag) (substitution : RawTermSubst baseScope targetScope)
    (headLevel restLevel : LevelExpr)
    (head : RawTerm baseScope) (tail : RawTermChildren (consecutiveShifts 1 1) baseScope)
    (headMember : IsReducibleMemberAtDenote env level (universeCodeCell headLevel flag)
      (RawTerm.subst substitution head))
    (tailReducible : ∀ argument : RawTerm targetScope,
      IsReducibleMemberAtDenote env level (RawTerm.subst substitution head) argument →
      TelescopeReducibleAtDenote env level flag 1 1 (RawTermSubst.cons argument substitution)
        [restLevel] tail) :
    TelescopeReducibleAtDenote env level flag 0 2 substitution [headLevel, restLevel]
      (.childCons head tail) :=
  ⟨headMember, tailReducible⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.TelescopeReducibleAtDenote.nil
#print axioms FX1Poly.Typed.TelescopeReducibleAtDenote.twoChild
