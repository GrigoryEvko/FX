import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Universe.LevelExprSimplify

/-! # FX1Poly/Typed/FormerOutputLevelBounds
    — each Π/Σ-former child level is ≤ the former's output level (the genFormationPi `belowOutput` premises)

The dependent type-former output level is `lmaxAll levels` (`universeFormerOutput = universeCodeCell (lmaxAll
levels) flag`, `HasTypeDesc.lean`).  The bounded `genFormationPi` recursor arm feeds the non-uniform discharge
`piReducibleAsTypeFromNonUniformLevelMemberBounded`, whose `domainBelowOutput` / `codomainBelowOutput` premises
require each child's decoded level to sit at or below the former's decoded output level.  For the two-child Π/Σ
formers (`levels = [domainLevel, codomainLevel]`) the fold collapses definitionally —
`lmaxAll [a, b] = LevelExpr.lmax a b` — and `LevelExpr.denote_lmax` denotes that to the structural `levelMax`,
whose component bounds are elementary Nat inductions.

## The declarations

  * `levelMax_le_left` / `levelMax_le_right` — `valueA ≤ levelMax valueA valueB` and the dual, by structural
    induction mirroring `LevelExpr.levelMax`'s three clauses.  (The `ClassifierLevelMeasure` versions are
    file-private, so these are re-derived here for cross-file use.)
  * `lmaxAll_pair` — the two-element fold collapse `lmaxAll [a, b] = LevelExpr.lmax a b` (definitional).
  * `denote_domainLevel_le_lmaxAll_pair` / `denote_codomainLevel_le_lmaxAll_pair` — the two `belowOutput`
    facts the discharge consumes, each `rw [lmaxAll_pair, denote_lmax]` then the matching `levelMax` bound.

## Zero-axiom verification

The `levelMax` bounds are propext-clean structural Nat inductions (full three-clause coverage, `Nat.zero_le` /
`Nat.le_refl` / `Nat.succ_le_succ`); `lmaxAll_pair` is `rfl`; the denote bounds are two rewrites by `rfl`-lemmas
then a `levelMax` bound.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Universe

/-- `valueA ≤ levelMax valueA valueB`, by structural induction mirroring `LevelExpr.levelMax`'s three clauses.
Re-derived locally because the `ClassifierLevelMeasure` version is file-private. -/
theorem levelMax_le_left : ∀ (valueA valueB : Nat), valueA ≤ LevelExpr.levelMax valueA valueB
  | 0, _ => Nat.zero_le _
  | _ + 1, 0 => Nat.le_refl _
  | valueA + 1, valueB + 1 => Nat.succ_le_succ (levelMax_le_left valueA valueB)

/-- `valueB ≤ levelMax valueA valueB` — the right-component bound, dual of `levelMax_le_left`. -/
theorem levelMax_le_right : ∀ (valueA valueB : Nat), valueB ≤ LevelExpr.levelMax valueA valueB
  | 0, _ => Nat.le_refl _
  | _ + 1, 0 => Nat.zero_le _
  | valueA + 1, valueB + 1 => Nat.succ_le_succ (levelMax_le_right valueA valueB)

/-- The two-element fold collapse: a Π/Σ former's `lmaxAll [domainLevel, codomainLevel]` is exactly
`LevelExpr.lmax domainLevel codomainLevel` (definitional, via `lmaxFold`). -/
theorem lmaxAll_pair (domainLevel codomainLevel : LevelExpr) :
    lmaxAll [domainLevel, codomainLevel] = LevelExpr.lmax domainLevel codomainLevel := rfl

/-- **The domain `belowOutput` fact.**  A Π/Σ former's domain level is at or below the former's output level:
`denote domainLevel env ≤ denote (lmaxAll [domainLevel, codomainLevel]) env`.  The discharge's
`domainBelowOutput` premise. -/
theorem denote_domainLevel_le_lmaxAll_pair (domainLevel codomainLevel : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote domainLevel env ≤ LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env := by
  rw [lmaxAll_pair, LevelExpr.denote_lmax]
  exact levelMax_le_left _ _

/-- **The codomain `belowOutput` fact.**  A Π/Σ former's codomain level is at or below the former's output
level.  The discharge's `codomainBelowOutput` premise. -/
theorem denote_codomainLevel_le_lmaxAll_pair (domainLevel codomainLevel : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote codomainLevel env ≤ LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env := by
  rw [lmaxAll_pair, LevelExpr.denote_lmax]
  exact levelMax_le_right _ _

end FX1Poly.Typed
