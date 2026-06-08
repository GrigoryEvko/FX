import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.UniverseCodeConversion

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- n-fold `lsucc` over `lzero`: the level expression `Type@n`. -/
def universeLevelOfNat : Nat → LevelExpr
  | 0 => LevelExpr.lzero
  | (k + 1) => LevelExpr.lsucc (universeLevelOfNat k)

/-- The n-fold-lsucc family injects ℕ into the level algebra. -/
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

/-- `Type@n` as a closed raw term: the universe code at level `universeLevelOfNat n`. -/
def universeLevelTower (flag : UniverseFlag) (n : Nat) : RawTerm 0 :=
  universeCodeCell (universeLevelOfNat n) flag

/-- `Type@n : Type@(n+1)` via the formation rule (the `.lsucc` output is defeq to `universeLevelOfNat (n+1)`). -/
theorem universeLevelTower_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) (n : Nat) :
    HasTypeDescPi profile TypingContext.empty
      (universeLevelTower flag n) (universeLevelTower flag (n + 1)) :=
  HasTypeDescPi.ofFormation
    (HasTypeDesc.universeFormation TypingContext.empty (universeLevelOfNat n) flag)

/-- Distinct tower levels are non-convertible: `universeCodeCell_inj_of_conv` then level injectivity. -/
theorem universeLevelTower_notConvertible_of_ne (flag : UniverseFlag)
    {m n : Nat} (depthsDiffer : m ≠ n) :
    ¬ Conv (universeLevelTower flag m) (universeLevelTower flag n) := by
  intro conv
  have levelsEq : universeLevelOfNat m = universeLevelOfNat n :=
    (universeCodeCell_inj_of_conv conv).left
  exact depthsDiffer (universeLevelOfNat_injective levelsEq)

/-- ★ The predicative universe hierarchy is an infinite non-collapsing tower. -/
theorem universeHierarchy_isInfiniteNonCollapsingTower {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ tower : Nat → RawTerm 0,
      (∀ n, HasTypeDescPi profile TypingContext.empty (tower n) (tower (n + 1)))
      ∧ (∀ m n, m ≠ n → ¬ Conv (tower m) (tower n)) :=
  ⟨universeLevelTower flag,
    fun n => universeLevelTower_hasTypeDescPi flag n,
    fun _ _ depthsDiffer => universeLevelTower_notConvertible_of_ne flag depthsDiffer⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeLevelOfNat_injective
#print axioms FX1Poly.Typed.universeLevelTower_hasTypeDescPi
#print axioms FX1Poly.Typed.universeLevelTower_notConvertible_of_ne
#print axioms FX1Poly.Typed.universeHierarchy_isInfiniteNonCollapsingTower
