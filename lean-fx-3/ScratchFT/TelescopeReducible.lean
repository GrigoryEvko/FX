import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Core.RawTermSubstConsCommute

/-! Scratch experiment v3: index the children by `consecutiveShifts currentDepth count` so the head sits at
`baseScope + currentDepth` by construction AND the recursive substitution `cons arg substitution :
RawTermSubst (baseScope + currentDepth + 1)` matches `baseScope + (currentDepth + 1)` definitionally. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The consecutive shift list `[d, d+1, …, d+count-1]` — the `binderShifts` a depth-`d` telescope of `count`
children carries (each child binds one more variable than the previous).  Definitionally
`consecutiveShifts d (n+1) = d :: consecutiveShifts (d+1) n`, so a `count+1` children spine is a `childCons`
with head at `baseScope + d`. -/
def consecutiveShifts : Nat → Nat → List Nat
  | _, 0 => []
  | depth, count + 1 => depth :: consecutiveShifts (depth + 1) count

/-- The reducibility relation for a former's premise telescope, indexed by `currentDepth` and the child
`count`.  Each child head is a reducible member of its universe at every level; the tail is reducible under
the substitution extended by any reducible argument at variable 0. -/
def TelescopeReducible {baseScope targetScope : Nat} (flag : UniverseFlag) :
    (currentDepth : Nat) → (count : Nat) →
    RawTermSubst (baseScope + currentDepth) (targetScope + 1) →
    List LevelExpr →
    RawTermChildren (consecutiveShifts currentDepth count) baseScope → Prop
  | _, 0, _, _, _ => True
  | _, _ + 1, _, [], _ => True
  | currentDepth, _ + 1, substitution, headLevel :: restLevels, .childCons head tail =>
      (∀ level : Nat, IsReducibleMemberAt (level + 1) (universeCodeCell headLevel flag)
        (RawTerm.subst substitution head)) ∧
      (∀ {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt memberLevel (RawTerm.subst substitution head) argument →
        TelescopeReducible flag (currentDepth + 1) _ (RawTermSubst.cons argument substitution)
          restLevels tail)

end FX1Poly.Typed
