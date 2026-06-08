import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/TypedUniverseTower — the predicative universe hierarchy is an infinite non-collapsing tower

`L1-GIRARD-ACYCLIC` (#941) proved the universe classification relation is irreflexive at every chain length:
no `Type@e₀ : Type@e₁ : … : Type@e₀` cycle exists, so FX's predicative hierarchy never collapses the way an
impredicative `Type : Type` does (which would re-enable Girard's paradox).  That was the NEGATIVE half — the
hierarchy does not fold back on itself.  This file ships the POSITIVE half: the hierarchy genuinely ASCENDS, an
infinite tower whose levels are all pairwise distinct up to definitional equality.

  **`universeHierarchy_isInfiniteNonCollapsingTower` (★)** — there is a family `tower : ℕ → RawTerm 0` (the
  closed universe codes `Type@0, Type@1, Type@2, …`) such that (a) every rung is typed at the next,
  `tower n : tower (n+1)` via the `universeFormation` rule (`Type@n : Type@(n+1)`), and (b) distinct rungs are
  non-convertible, `m ≠ n → tower m ≢ tower n`.  So the closed-term model carries an injection from ℕ into a
  strictly-ascending classification chain — the predicative tower is infinite and never collapses.

The two structural pieces:

  * `universeLevelOfNat` — the n-fold-`lsucc` family `ℕ → LevelExpr` (`Type@n`'s level), with
    `universeLevelOfNat_injective` (the level algebra carries an injection from ℕ: `lzero`/`lsucc` are distinct
    and `lsucc` is injective, so the n-fold tower has no collisions).
  * `universeLevelTower` — `Type@n` as a closed raw term, with `_hasTypeDescPi` (each rung types at the next via
    the formation rule — the `.lsucc` output is DEFEQ to `universeLevelOfNat (n+1)`, no coercion) and
    `_notConvertible_of_ne` (distinct rungs are non-convertible: universe codes are conv-rigid step-normal-forms,
    so `universeCodeCell_inj_of_conv` reduces convertibility to level equality, refuted by level injectivity).

This complements `L1-GIRARD-ACYCLIC` (irreflexivity / no collapse) and contrasts the impredicative `Type:Type`
that the predicativity guards (`LevelExpr.ne_lsucc_self`, `ne_lsuccLsucc_self`) reject: the ascent is real,
proper, and infinite, exactly because each level is strictly below its successor.

## Zero-axiom verification

`universeLevelOfNat_injective` is a clean `induction … generalizing` with `cases` on the cross-constructor
contradictions (the propext-free idiom already used in `LevelExpr.ne_lsucc_self`) and `injection` +
`congrArg Nat.succ` on the matching case.  `_hasTypeDescPi` is `HasTypeDescPi.ofFormation` of the
`universeFormation` rule with the successor level handled by `rfl`-level defeq.  `_notConvertible_of_ne` consumes
the propext-free `universeCodeCell_inj_of_conv` (global confluence over step-normal universe codes).  The
capstone bundles them.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated
per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The level expression `Type@n`: `n`-fold `lsucc` over `lzero`.  Structural recursion on the `Nat`, so
`universeLevelOfNat (n+1)` reduces definitionally to `LevelExpr.lsucc (universeLevelOfNat n)`. -/
def universeLevelOfNat : Nat → LevelExpr
  | 0 => LevelExpr.lzero
  | (k + 1) => LevelExpr.lsucc (universeLevelOfNat k)

/-- The n-fold-`lsucc` family injects ℕ into the level algebra: distinct natural numbers name distinct levels.
By `induction … generalizing`: the cross-constructor `lzero`-vs-`lsucc` cases close by `cases` (no-confusion,
propext-free), and the `lsucc`-vs-`lsucc` case strips one successor by `injection` and recurses.  This is the
level-side injectivity that makes the universe tower non-collapsing. -/
theorem universeLevelOfNat_injective {m n : Nat}
    (sameLevels : universeLevelOfNat m = universeLevelOfNat n) : m = n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ priorRight => cases sameLevels
  | succ priorLeft inductiveHypothesis =>
      cases n with
      | zero => cases sameLevels
      | succ priorRight =>
          injection sameLevels with innerLevelsEq
          exact congrArg Nat.succ (inductiveHypothesis innerLevelsEq)

/-- `Type@n` as a closed raw term: the universe code at level `universeLevelOfNat n` (the `flag` selects the
hierarchy mode).  Profile-free — universe codes carry no profile. -/
def universeLevelTower (flag : UniverseFlag) (n : Nat) : RawTerm 0 :=
  universeCodeCell (universeLevelOfNat n) flag

/-- **Each rung is typed at the next: `Type@n : Type@(n+1)`.**  Directly the `universeFormation` rule
(`Type@e : Type@(e.lsucc)`) wrapped by `ofFormation`; the rule's `.lsucc` output level is DEFINITIONALLY EQUAL
to `universeLevelOfNat (n+1)` (both are `LevelExpr.lsucc (universeLevelOfNat n)`), so no coercion is needed.
This is the ascending half of the tower. -/
theorem universeLevelTower_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) (n : Nat) :
    HasTypeDescPi profile TypingContext.empty
      (universeLevelTower flag n) (universeLevelTower flag (n + 1)) :=
  HasTypeDescPi.ofFormation
    (HasTypeDesc.universeFormation TypingContext.empty (universeLevelOfNat n) flag)

/-- **Distinct rungs are non-convertible: `m ≠ n → Type@m ≢ Type@n`.**  Universe codes are conv-rigid step
normal forms, so `universeCodeCell_inj_of_conv` (global confluence, no SN premise) reduces a convertibility of
two rungs to equality of their levels, which `universeLevelOfNat_injective` then refutes when the indices
differ.  This is the non-collapsing half — the tower's levels never coincide. -/
theorem universeLevelTower_notConvertible_of_ne (flag : UniverseFlag)
    {m n : Nat} (depthsDiffer : m ≠ n) :
    ¬ Conv (universeLevelTower flag m) (universeLevelTower flag n) := by
  intro conv
  have levelsEq : universeLevelOfNat m = universeLevelOfNat n :=
    (universeCodeCell_inj_of_conv conv).left
  exact depthsDiffer (universeLevelOfNat_injective levelsEq)

/-- ★ **The predicative universe hierarchy is an infinite, non-collapsing tower.**  The closed universe codes
`Type@0, Type@1, Type@2, …` form a family `ℕ → RawTerm 0` in which (a) every rung is typed at the next
(`tower n : tower (n+1)`, the formation rule) and (b) distinct rungs are non-convertible
(`m ≠ n → tower m ≢ tower n`).  So a single closed-term model carries an injection from ℕ into a strictly
ascending classification chain: the hierarchy genuinely ascends and never collapses — the positive complement of
the `L1-GIRARD-ACYCLIC` (#941) irreflexivity, and the antithesis of an impredicative `Type:Type`. -/
theorem universeHierarchy_isInfiniteNonCollapsingTower {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ tower : Nat → RawTerm 0,
      (∀ n, HasTypeDescPi profile TypingContext.empty (tower n) (tower (n + 1)))
      ∧ (∀ m n, m ≠ n → ¬ Conv (tower m) (tower n)) :=
  ⟨universeLevelTower flag,
    fun n => universeLevelTower_hasTypeDescPi flag n,
    fun _ _ depthsDiffer => universeLevelTower_notConvertible_of_ne flag depthsDiffer⟩

end FX1Poly.Typed
