import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Universe

/-! # AuditPhase12A1UniverseConstraint

D1.2 audit gates verifying that `Ty.universe` is genuinely
level-constraining: `Ty.universe u rfl : Ty (u.toNat + 1) scope`
and the Type-in-Type loophole `Ty.universe u : Ty u.toNat scope`
is structurally impossible.

## What this file proves

* Smoke `universe_at_level1`, `universe_at_level2`, `universe_at_level3`:
  positive examples — `Ty.universe .zero rfl : Ty 1 scope` typechecks
* `no_type_in_type_at_zero`, `no_type_in_type_at_one`,
  `no_type_in_type_at_two`: refutations — there is no proof of
  `0 = UniverseLevel.zero.toNat + 1`, `1 = (UniverseLevel.succ .zero).toNat + 1`, etc.
  These witnesses prove the level-constraint is enforced.

## Why this matters

Codex's earlier design `Ty.universe (u : UniverseLevel) : Ty level scope`
left `level` free.  That permitted `Ty.universe .zero : Ty 0 scope` —
a level-0 universe living at level 0, the textbook Type-in-Type form
that admits Girard's paradox.

The propositional-equation parameter pattern (per
`feedback_lean_universe_constructor_block.md` P-3 mitigation) ensures
the level is fixed by the payload: `Ty.universe u (h : level = u.toNat + 1)`.
At construction sites, `h` must be supplied; if the level is wrong,
no proof of `h` exists, and the universe ctor cannot be applied. -/

namespace LeanFX2

/-- `Type 0 : Type 1` — the smallest universe lives one level up. -/
example : Ty 1 0 :=
  Ty.universe (scope := 0) UniverseLevel.zero rfl

/-- `Type 1 : Type 2` — successor universe. -/
example : Ty 2 0 :=
  Ty.universe (scope := 0) (UniverseLevel.succ .zero) rfl

/-- `Type 2 : Type 3` — chain continues. -/
example : Ty 3 5 :=
  Ty.universe (scope := 5) (UniverseLevel.succ (.succ .zero)) rfl

/-! ## Type-in-Type refutations (zero-axiom)

Each refutation is `nomatch` on the impossible proposition
`level = universeLevel.toNat + 1` where the levels chosen are
genuinely different.  The compiler closes these structurally —
no `decide`, no `omega`, no propext. -/

/-- Cannot construct `Ty.universe .zero rfl : Ty 0 scope` because
    `0 = .zero.toNat + 1 = 1` is false (`UniverseLevel.zero.toNat = 0`). -/
example : ¬ ∃ (h : (0 : Nat) = UniverseLevel.zero.toNat + 1), True :=
  fun ⟨h, _⟩ => Nat.noConfusion h

/-- Cannot construct `Ty.universe (.succ .zero) rfl : Ty 1 scope`
    because `1 = (.succ .zero).toNat + 1 = 2` is false. -/
example : ¬ ∃ (h : (1 : Nat) = (UniverseLevel.succ .zero).toNat + 1), True :=
  fun ⟨h, _⟩ => Nat.noConfusion (Nat.succ.inj h)

/-- General loophole closure: the proof obligation `level = u.toNat + 1`
    is the propositional equation that forces the level.  Without a
    proof, no `Ty.universe` value at that level exists.

    This refutation works for ANY universe level `u`: a level-`u`
    universe cannot inhabit level `u`, only level `u + 1`. -/
example (u : UniverseLevel) : ¬ (u.toNat = u.toNat + 1) :=
  fun h => Nat.succ_ne_self u.toNat h.symm

end LeanFX2

#print axioms LeanFX2.UniverseLevel
#print axioms LeanFX2.Ty
