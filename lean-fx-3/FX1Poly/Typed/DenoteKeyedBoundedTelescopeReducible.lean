import FX1Poly.Typed.DenoteKeyedBoundedReducibleEnv
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DenoteKeyedBoundedTelescopeReducible
    — the bound-carrying telescope-reducibility relation (motive_2 shape for the grown-FT recursor dispatch)

The bounded grown-engine fundamental theorem's `genFormationPi` arm receives a former's children as a
`DescTelescopePi` telescope and must obtain each child's bound-reducibility under the appropriately
binder-extended substitution.  This file defines the RETURN TYPE the (future, mutual) bounded
`fundamentalTelescope` companion will produce — the `motive_2` of the `HasTypeDescPi.rec` dispatch — the
logical relation `TelescopeReducibleAtBounded` over the former's child spine.

It is the bound-carrying analogue of the single-level `TelescopeReducibleAtDenote`
(`DenoteKeyedTelescopeReducible.lean`).  The one structural difference: where the denote relation keys both
the head MEMBERSHIP and the tail ARGUMENT quantification on a single ambient `level`, the bounded relation
carries TWO nat levels:

  * `bound` — the level at which each child head is a bound-reducible MEMBER of its universe code.  Matches the
    `IsReducibleMemberAtBounded env bound (universeCodeCell …) …` shape the discharge
    `piReducibleAsTypeFromNonUniformLevelMemberBounded` consumes for `domainMember` / `codomainMember`.
  * `argLevel` — the level at which the tail's domain ARGUMENT is quantified.  In the Π/Σ dispatch this is the
    former's decoded OUTPUT level `denote levelExpr env` (the discharge's argument premise
    `IsReducibleMemberAtBounded env (denote levelExpr env) (subst domain) argument`), which is strictly below
    `bound` by gate-extraction (`universeCodeReducibleAtBounded_belowBound`).  The denote relation collapses
    these two because it has no separate `bound`; the bounded relation must keep them distinct.

The `consecutiveShifts currentDepth count` child index (shipped, reused from `TelescopeReducible`) ties the
head scope and the recursive-call substitution scope together definitionally — a depth-`d` telescope of
`count` children carries `binderShifts = [d, d+1, …, d+count-1]`, so the head sits at `baseScope +
currentDepth` and the `cons`-extended recursive substitution lands at `baseScope + (currentDepth + 1)` (see
`TelescopeReducible`'s module docstring for why the generic-`binderShifts` formulation fails).

`twoChild` is the Π/Σ-former unfolder: `gen_piTyCode.binderShifts = [0,1] = consecutiveShifts 0 2`, so a
Π/Σ former's two-child premise spine is exactly a `TelescopeReducibleAtBounded … 0 2` — the shape the bounded
`genFormationPi` arm reads its domain/codomain reducibility off, then lifts to the former's output level via
free bounded cumulativity in `piReducibleAsTypeFromNonUniformLevelMemberBounded`.

## Zero-axiom verification

A structural-recursion `def` on `count` plus two unfolders (the `nil` base case is `True.intro`; `twoChild` is
the anonymous constructor of the two-clause conjunction).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The bound-carrying telescope-reducibility relation.**  Indexed by `currentDepth` and child `count`:
every child head is a bound-reducible member of its universe code at `bound`, and the tail is reducible under
the substitution extended (`RawTermSubst.cons`) by any bound-reducible argument at variable 0 — that argument
quantified at `argLevel` (the former's output level), matching the discharge premise shape.  The bound-carrying
analogue of `TelescopeReducibleAtDenote`; the `consecutiveShifts` index keeps the head and recursive
substitution scopes definitional. -/
def TelescopeReducibleAtBounded {baseScope targetScope : Nat} (env : Nat → Nat) (bound argLevel : Nat)
    (flag : UniverseFlag) :
    (currentDepth : Nat) → (count : Nat) →
    RawTermSubst (baseScope + currentDepth) targetScope →
    List LevelExpr →
    RawTermChildren (consecutiveShifts currentDepth count) baseScope → Prop
  | _, 0, _, _, _ => True
  | _, _ + 1, _, [], _ => True
  | currentDepth, _ + 1, substitution, headLevel :: restLevels, .childCons head tail =>
      IsReducibleMemberAtBounded env bound (universeCodeCell headLevel flag)
        (RawTerm.subst substitution head) ∧
      (∀ argument : RawTerm targetScope,
        IsReducibleMemberAtBounded env argLevel (RawTerm.subst substitution head) argument →
        TelescopeReducibleAtBounded env bound argLevel flag (currentDepth + 1) _
          (RawTermSubst.cons argument substitution) restLevels tail)

/-- The empty telescope (child count `0`) is bound-telescope-reducible vacuously. -/
theorem TelescopeReducibleAtBounded.nil {baseScope targetScope : Nat} (env : Nat → Nat)
    (bound argLevel : Nat) (flag : UniverseFlag) (currentDepth : Nat)
    (substitution : RawTermSubst (baseScope + currentDepth) targetScope)
    (children : RawTermChildren (consecutiveShifts currentDepth 0) baseScope) :
    TelescopeReducibleAtBounded env bound argLevel flag currentDepth 0 substitution [] children :=
  True.intro

/-- **The Π/Σ-former two-child unfolder.**  A two-child former spine (`gen_piTyCode.binderShifts =
[0,1] = consecutiveShifts 0 2`) is bound-telescope-reducible exactly when the head is a bound-reducible member
of its universe code at `bound` and, per bound-reducible argument at `argLevel`, the one-child tail is
bound-telescope-reducible under the `cons`-extended substitution.  The shape the bounded `genFormationPi` arm
reads the domain/codomain reducibility off. -/
theorem TelescopeReducibleAtBounded.twoChild {baseScope targetScope : Nat} (env : Nat → Nat)
    (bound argLevel : Nat) (flag : UniverseFlag) (substitution : RawTermSubst baseScope targetScope)
    (headLevel restLevel : LevelExpr)
    (head : RawTerm baseScope) (tail : RawTermChildren (consecutiveShifts 1 1) baseScope)
    (headMember : IsReducibleMemberAtBounded env bound (universeCodeCell headLevel flag)
      (RawTerm.subst substitution head))
    (tailReducible : ∀ argument : RawTerm targetScope,
      IsReducibleMemberAtBounded env argLevel (RawTerm.subst substitution head) argument →
      TelescopeReducibleAtBounded env bound argLevel flag 1 1 (RawTermSubst.cons argument substitution)
        [restLevel] tail) :
    TelescopeReducibleAtBounded env bound argLevel flag 0 2 substitution [headLevel, restLevel]
      (.childCons head tail) :=
  ⟨headMember, tailReducible⟩

end FX1Poly.Typed
