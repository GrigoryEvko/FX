import FX1Poly.Core.NormalizeSteps
import FX1Poly.Typed.IdentityTowerFamily

/-! # FX1Poly/Typed/NormalizeStepsTower
   — the identity-tower family realizes the normalizer's step counter EXACTLY (SN-145 boundary)

`Core/NormalizeSteps` ships the normalizer's exact cost instrumentation; this file makes it
NON-VACUOUS and pins the honest boundary of the STRICT-COMPLEXITY story for the term normalizer:

  * `RawTerm.reduceOnce_idTower_succ` / `_zero` — the reducer's behavior on the tower computes by
    `rfl` at EVERY height (including symbolic): each tower member fires exactly its root β.
  * `normalizeSteps_idTower` — the counter is EXACT on the family: normalizing
    `(λx.x)ⁿ (Type@e)` costs exactly `n` reduceOnce firings, for every `n`.
  * `normalizeSteps_unbounded` — the boundary brick: the counter is NOT bounded by any constant
    (every bound is exceeded by a tower member, whose SN witness is the TYPED SN theorem SN-043
    via `idTower_stronglyNormalizing`).

HONESTY: the family's step count is LINEAR in its size, so it does NOT refute a degree-≥1
polynomial bound; what it establishes is exactness + unboundedness.  The non-elementary lower
bound for β-normalization (Statman 1979) — which would refute EVERY size-polynomial — is
literature-cited in `Core/NormalizeSteps` and remains a named open formalization target.

## Zero-axiom verification

The reducer equations close by `rfl` (root-β with the innermost-var-0 body computes on symbolic
tails); the exact count is structural induction on the height over `normalizeSteps_unfold`; the
unboundedness witness instantiates the tower at `bound + 1` with the SN-043-derived accessibility.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The reducer fires exactly the root β on every successor tower member — by `rfl`, height
symbolic. -/
theorem RawTerm.reduceOnce_idTower_succ (levelExpr : LevelExpr) (flag : UniverseFlag)
    (towerHeight : Nat) :
    RawTerm.reduceOnce (idTower levelExpr flag (towerHeight + 1)) =
      some (idTower levelExpr flag towerHeight) := rfl

/-- The reducer halts at the tower's base (the universe-code value) — by `rfl`. -/
theorem RawTerm.reduceOnce_idTower_zero (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.reduceOnce (idTower levelExpr flag 0) = none := rfl

/-- **The counter is EXACT on the identity tower**: normalizing `(λx.x)ⁿ (Type@e)` costs exactly
`n` reducer firings, for every height and every accessibility witness (the witness is
proof-irrelevant).  Structural induction on the height; each step is the `rfl`-computing root β
plus the unfold equation. -/
theorem normalizeSteps_idTower (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∀ (towerHeight : Nat)
      (accessible : Acc StepStar.StepSuccessor (idTower levelExpr flag towerHeight)),
      RawTerm.normalizeSteps (idTower levelExpr flag towerHeight) accessible = towerHeight
  | 0, accessible => by
      rw [RawTerm.normalizeSteps_eq]
      rfl
  | towerHeight + 1, accessible => by
      rw [RawTerm.normalizeSteps_eq]
      show RawTerm.normalizeSteps (idTower levelExpr flag towerHeight) _ + 1 =
        towerHeight + 1
      exact congrArg (· + 1) (normalizeSteps_idTower levelExpr flag towerHeight _)

/-- **The normalizer's step counter is not bounded by any constant** — every proposed bound is
exceeded by the tower member one taller, whose accessibility is supplied by the TYPED SN theorem
(SN-043 through `idTower_stronglyNormalizing`).  The honest boundary brick for SN-145: exactness
+ unboundedness are machine-checked; no size-polynomial claim is made in either direction. -/
theorem normalizeSteps_unbounded (bound : Nat) :
    ∃ (term : RawTerm 0) (accessible : Acc StepStar.StepSuccessor term),
      bound < RawTerm.normalizeSteps term accessible :=
  ⟨idTower LevelExpr.lzero UniverseFlag.standard (bound + 1),
   idTower_stronglyNormalizing (profile := fxProfile) LevelExpr.lzero UniverseFlag.standard
     (bound + 1),
   by
     rw [normalizeSteps_idTower LevelExpr.lzero UniverseFlag.standard (bound + 1)]
     exact Nat.lt_succ_self bound⟩

/-- Harvest: the tower's normalizer run is a counted chain of length exactly its height —
`normalizeSteps_chainExact` instantiated through the exact count. -/
theorem idTower_normalizeChainExact (levelExpr : LevelExpr) (flag : UniverseFlag)
    (towerHeight : Nat)
    (accessible : Acc StepStar.StepSuccessor (idTower levelExpr flag towerHeight)) :
    StepStarN towerHeight (idTower levelExpr flag towerHeight)
      (RawTerm.normalize (idTower levelExpr flag towerHeight) accessible) := by
  have hChain :=
    RawTerm.normalizeSteps_chainExact (idTower levelExpr flag towerHeight) accessible
  rw [normalizeSteps_idTower levelExpr flag towerHeight accessible] at hChain
  exact hChain

end FX1Poly.Typed
