import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Universe

/-! # AuditPhase12A1UniverseConstraint

D1.2 audit gates verifying that `Ty.universe` is genuinely
level-constraining: `Ty.universe u h : Ty level scope` requires
`h : u.toNat + 1 ≤ level`, so the Type-in-Type loophole
`Ty.universe u : Ty u.toNat scope` is structurally impossible
(`u + 1 ≤ u` has no proof).

Phase 12.A.B1.1 changed the propositional-equation parameter
`levelEq : level = u.toNat + 1` to a propositional-inequality
`levelLe : u.toNat + 1 ≤ level`.  This makes cumulativity intrinsic:
a level-`u` universe inhabits any `Ty l scope` for `l ≥ u + 1`.
The paradox-blocking property is preserved: `u + 1 ≤ u` is never
provable.

## What this file proves

* Smoke `universe_at_level1`, `universe_at_level2`, `universe_at_level3`:
  positive examples — `Ty.universe .zero (Nat.le_refl _) : Ty 1 scope`
  typechecks.  Cumul examples: `Ty.universe .zero h : Ty 5 scope` with
  `h : 1 ≤ 5` typechecks (intrinsic cumulativity).
* `no_type_in_type_at_zero`, etc.: refutations — there is no proof of
  `.zero.toNat + 1 ≤ 0`, `(.succ .zero).toNat + 1 ≤ 1`, etc.
  These witnesses prove the level-constraint is enforced.

## Why this matters

Codex's earlier design `Ty.universe (u : UniverseLevel) : Ty level scope`
left `level` free.  That permitted `Ty.universe .zero : Ty 0 scope` —
a level-0 universe living at level 0, the textbook Type-in-Type form
that admits Girard's paradox.

The propositional-inequality parameter `Ty.universe u (h : u.toNat + 1 ≤ level)`
forces `level ≥ u + 1`.  At construction sites, `h` must be supplied;
if `level < u + 1`, no proof of `h` exists, and the universe ctor
cannot be applied. -/

namespace LeanFX2

/-- `Type 0 : Type 1` — the smallest universe lives one level up. -/
example : Ty 1 0 :=
  Ty.universe (scope := 0) UniverseLevel.zero (Nat.le_refl _)

/-- `Type 1 : Type 2` — successor universe. -/
example : Ty 2 0 :=
  Ty.universe (scope := 0) (UniverseLevel.succ .zero) (Nat.le_refl _)

/-- `Type 2 : Type 3` — chain continues. -/
example : Ty 3 5 :=
  Ty.universe (scope := 5) (UniverseLevel.succ (.succ .zero)) (Nat.le_refl _)

/-- `Type 0 : Type 5` — intrinsic cumulativity (Phase 12.A.B1.1):
    a level-0 universe inhabits any `Ty l scope` for `l ≥ 1`. -/
example : Ty 5 0 :=
  Ty.universe (scope := 0) UniverseLevel.zero (by decide)

/-- `Type 1 : Type 7` — chain example showing intrinsic level-jumping. -/
example : Ty 7 3 :=
  Ty.universe (scope := 3) (UniverseLevel.succ .zero) (by decide)

/-! ## Type-in-Type refutations (zero-axiom)

Each refutation closes the impossible proposition
`u.toNat + 1 ≤ level` where the levels chosen are genuinely too small.
The compiler closes these structurally — `Nat.not_succ_le_self` for
`u + 1 ≤ u`. -/

/-- Cannot construct `Ty.universe .zero h : Ty 0 scope` because
    `.zero.toNat + 1 ≤ 0` is `1 ≤ 0`, which has no proof. -/
example : ¬ ∃ (_ : UniverseLevel.zero.toNat + 1 ≤ (0 : Nat)), True :=
  fun ⟨badProof, _⟩ => Nat.not_succ_le_zero 0 badProof

/-- Cannot construct `Ty.universe (.succ .zero) h : Ty 1 scope`
    because `(.succ .zero).toNat + 1 ≤ 1` is `2 ≤ 1`, no proof. -/
example : ¬ ∃ (_ : (UniverseLevel.succ .zero).toNat + 1 ≤ (1 : Nat)), True :=
  fun ⟨badProof, _⟩ => Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ badProof)

/-- General loophole closure: a level-`u` universe cannot inhabit
    level `u`.  `u.toNat + 1 ≤ u.toNat` is `Nat.not_succ_le_self`. -/
example (u : UniverseLevel) : ¬ (u.toNat + 1 ≤ u.toNat) :=
  fun h => Nat.not_succ_le_self u.toNat h

end LeanFX2

#print axioms LeanFX2.UniverseLevel
#print axioms LeanFX2.Ty
