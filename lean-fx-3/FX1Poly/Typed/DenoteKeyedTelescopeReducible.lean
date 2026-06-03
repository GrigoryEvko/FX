import FX1Poly.Typed.DenoteKeyedReducibleEnv
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DenoteKeyedTelescopeReducible
    — the denote-keyed telescope-reducibility relation (first brick of the genFormationPi arm, SN-D5d toward SN-043)

The denote fundamental theorem's `genFormationPi` arm receives a former's children as a `DescTelescopePi`
telescope and must obtain each child's denote-reducibility under the appropriately binder-extended substitution.
This file defines the RETURN TYPE the (future, mutual) denote `fundamentalTelescope` companion will produce: the
logical relation `TelescopeReducibleAtDenote` over the former's child spine.

It is the single-level denote analogue of the fuel `TelescopeReducible` (`TelescopeReducible.lean`), and is
SIMPLER than the fuel original on two counts:
  * each child head is a denote-reducible member of its universe code at the SINGLE ambient `level` (the fuel
    version tracks `∀ level, IsReducibleMemberAt (level+1) …` — the multi-level dispatch the fuel route needs);
  * the closing substitution is `RawTermSubst (baseScope + currentDepth) targetScope` (no `+1` — the denote
    `ReducibleEnvAtDenote` rides on `RawTermSubst scope targetScope`, unlike the fuel `ReducibleEnvVec`'s
    successor scope).

The `consecutiveShifts currentDepth count` child index (shipped, reused from `TelescopeReducible`) ties the head
scope and the recursive-call substitution scope together definitionally — a depth-`d` telescope of `count`
children carries `binderShifts = [d, d+1, …, d+count-1]`, so the head sits at `baseScope + currentDepth` and the
`cons`-extended recursive substitution lands at `baseScope + (currentDepth + 1)` (see `TelescopeReducible`'s
module docstring for why the generic-`binderShifts` formulation fails).

`twoChild` is the Π/Σ-former unfolder: `gen_piTyCode.binderShifts = [0,1] = consecutiveShifts 0 2`, so a Π/Σ
former's two-child premise spine is exactly a `TelescopeReducibleAtDenote … 0 2` — the shape the genFormationPi
arm reads its domain/codomain reducibility off.

## Zero-axiom verification

A structural-recursion `def` on `count` plus two unfolders (the `nil` base case is `True.intro`; `twoChild` is
the anonymous constructor of the two-clause conjunction).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The denote-keyed telescope-reducibility relation.**  Indexed by `currentDepth` and child `count`: every
child head is a denote-reducible member of its universe code at the ambient `level`, and the tail is reducible
under the substitution extended (`RawTermSubst.cons`) by any denote-reducible argument at variable 0.  The
single-level denote analogue of `TelescopeReducible`; the `consecutiveShifts` index keeps the head and recursive
substitution scopes definitional. -/
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

/-- The empty telescope (child count `0`) is denote-telescope-reducible vacuously. -/
theorem TelescopeReducibleAtDenote.nil {baseScope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    (flag : UniverseFlag) (currentDepth : Nat)
    (substitution : RawTermSubst (baseScope + currentDepth) targetScope)
    (children : RawTermChildren (consecutiveShifts currentDepth 0) baseScope) :
    TelescopeReducibleAtDenote env level flag currentDepth 0 substitution [] children :=
  True.intro

/-- **The Π/Σ-former two-child unfolder.**  A two-child former spine (`gen_piTyCode.binderShifts =
[0,1] = consecutiveShifts 0 2`) is denote-telescope-reducible exactly when the head is a denote-reducible member
of its universe code and, per denote-reducible argument, the one-child tail is denote-telescope-reducible under
the `cons`-extended substitution.  The shape the genFormationPi arm reads the domain/codomain reducibility off. -/
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
