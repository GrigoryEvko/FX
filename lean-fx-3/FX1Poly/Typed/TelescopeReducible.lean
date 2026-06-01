import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Core.RawTermSubstConsCommute

/-! # FX1Poly/Typed/TelescopeReducible
    — the reducibility logical relation for a former's premise telescope

The fundamental theorem's `genFormationPi` arm receives the children's typing as a `DescTelescopePi`
telescope and must obtain each child's reducibility under the appropriately binder-extended substitution.
This file defines the RETURN TYPE the (mutual) `fundamentalTelescope` companion produces: a logical relation
`TelescopeReducible` over the telescope's child spine.

## The consecutive-shift indexing (the keystone of this file)

A depth-`d` telescope of `count` children carries `binderShifts = [d, d+1, …, d+count-1]` — each child binds
one more variable than the previous.  Indexing the children by `consecutiveShifts currentDepth count` (rather
than a generic `binderShifts`) makes BOTH scope obligations definitional at once:

  * the head sits at `RawTerm (baseScope + currentDepth)` (the first element of `consecutiveShifts
    currentDepth (count+1)`), so the closing `RawTerm.subst substitution head` typechecks against
    `substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)`; and
  * the recursive call's extended substitution `RawTermSubst.cons argument substitution :
    RawTermSubst (baseScope + currentDepth + 1) (targetScope + 1)` matches the recursive expectation
    `RawTermSubst (baseScope + (currentDepth + 1)) (targetScope + 1)` definitionally (`Nat`'s `+1` is `succ`,
    `a + b + 1` is defeq to `a + (b + 1)`).

A generic-`binderShifts` formulation fails one obligation or the other (deriving the substitution scope from
the head shift breaks the recursive call; tracking `currentDepth` separately breaks the head); the
`consecutiveShifts` index ties them together.  Former telescopes (Π / Σ) carry `binderShifts = [0,1]`, which
is `consecutiveShifts 0 2` definitionally — so the companion produces this relation at no extra cost.

## Zero-axiom verification

Two `def`s (a structural recursion on `count`); no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The consecutive shift list `[depth, depth+1, …, depth+count-1]` — the `binderShifts` a depth-`depth`
telescope of `count` children carries.  Definitionally `consecutiveShifts depth (count+1) = depth ::
consecutiveShifts (depth+1) count`, so a `count+1` children spine over it is a `childCons` with head at
`baseScope + depth`. -/
def consecutiveShifts : Nat → Nat → List Nat
  | _, 0 => []
  | depth, count + 1 => depth :: consecutiveShifts (depth + 1) count

/-- **The reducibility relation for a former's premise telescope.**  Indexed by `currentDepth` and the child
`count`: every child head is a reducible member of its universe code at every level (`headMember`-style), and
the tail is reducible under the substitution extended (`RawTermSubst.cons`) by any reducible argument at
variable 0 (`tailReducible`-style).  The `consecutiveShifts` child index keeps the head and recursive
substitution scopes definitional (see the module docstring).  This is exactly the structure the mutual
`fundamentalTelescope` companion produces and the `genFormationPi` arm reads its `FormerChildrenReducible`
bundle off (head at `predLevel`/`predLevel+1`, tail's head for the codomain). -/
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
