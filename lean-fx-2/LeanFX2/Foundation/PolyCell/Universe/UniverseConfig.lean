/-!
# Universe Configuration (Axis 10 — Polynomial Universes)

The universe cell as a FullPolynomialUniverse instance. Step.eqType
gives operational univalence; Aberlé-Spivak subterminality gives
structural univalence. Both paths converge on the same Conv theorem.

Reference: arXiv:2409.19176, arXiv:1802.00997, arXiv:1904.07004.
-/

namespace LeanFX2.Foundation.PolyCell.Universe

/-- Universe level structure: how levels are organized. -/
inductive LevelStructure where
  | cumulativeNat
  | predicative
  | impredicative
  deriving DecidableEq, Repr

/-- Universe configuration for a PolyProfile. -/
structure UniverseConfig where
  levelStructure : LevelStructure
  hasUnivalence : Bool
  hasCumulativity : Bool

/-- FX's universe config: cumulative Nat-indexed, univalent, cumulative. -/
def fxUniverseConfig : UniverseConfig where
  levelStructure := .cumulativeNat
  hasUnivalence := true
  hasCumulativity := true

theorem fxUniverseConfig_univalent :
    fxUniverseConfig.hasUnivalence = true := rfl

theorem fxUniverseConfig_cumulative :
    fxUniverseConfig.hasCumulativity = true := rfl

end LeanFX2.Foundation.PolyCell.Universe
