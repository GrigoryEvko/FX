/-!
# Universe Configuration (Axis 10 — Polynomial Universes)

The universe cell target is a FullPolynomialUniverse instance.  This file
only records the level structure and an explicit construction ledger.  It
does not claim operational univalence, polynomial subterminality, or
cumulativity until the corresponding theorem packages are supplied.

Reference: arXiv:2409.19176, arXiv:1802.00997, arXiv:1904.07004.
-/

namespace FX1Poly.Universe

/-- Universe level structure: how levels are organized. -/
inductive LevelStructure where
  | cumulativeNat
  | predicative
  | impredicative
  deriving DecidableEq, Repr

/-- How much of Axis 10 has actually been constructed.

Operational univalence and polynomial subterminality are independent proof
paths, while cumulativity is a separate universe-level theorem package.  The
ledger records exactly which packages are present. -/
inductive UniverseConstructionLevel where
  /-- Only the level structure has been recorded. -/
  | levelStructureOnly
  /-- `Step.eqType`-style operational univalence has been constructed. -/
  | operationalUnivalence
  /-- Aberle-Spivak polynomial subterminality has been constructed. -/
  | polynomialSubterminality
  /-- Both univalence routes have been constructed. -/
  | operationalAndPolynomialUnivalence
  /-- Operational univalence plus universe cumulativity have been constructed. -/
  | cumulativeOperationalUnivalence
  /-- Polynomial subterminality plus universe cumulativity have been constructed. -/
  | cumulativePolynomialSubterminality
  /-- Both univalence routes and universe cumulativity have been constructed. -/
  | cumulativeOperationalAndPolynomial
  deriving DecidableEq, Repr

/-- Whether this Axis 10 level includes operational univalence. -/
def UniverseConstructionLevel.hasOperationalUnivalence :
    UniverseConstructionLevel → Bool
  | .levelStructureOnly => false
  | .operationalUnivalence => true
  | .polynomialSubterminality => false
  | .operationalAndPolynomialUnivalence => true
  | .cumulativeOperationalUnivalence => true
  | .cumulativePolynomialSubterminality => false
  | .cumulativeOperationalAndPolynomial => true

/-- Whether this Axis 10 level includes polynomial subterminality. -/
def UniverseConstructionLevel.hasPolynomialSubterminality :
    UniverseConstructionLevel → Bool
  | .levelStructureOnly => false
  | .operationalUnivalence => false
  | .polynomialSubterminality => true
  | .operationalAndPolynomialUnivalence => true
  | .cumulativeOperationalUnivalence => false
  | .cumulativePolynomialSubterminality => true
  | .cumulativeOperationalAndPolynomial => true

/-- Whether this Axis 10 level includes universe cumulativity. -/
def UniverseConstructionLevel.hasCumulativity :
    UniverseConstructionLevel → Bool
  | .levelStructureOnly => false
  | .operationalUnivalence => false
  | .polynomialSubterminality => false
  | .operationalAndPolynomialUnivalence => false
  | .cumulativeOperationalUnivalence => true
  | .cumulativePolynomialSubterminality => true
  | .cumulativeOperationalAndPolynomial => true

/-- Universe configuration for a PolyProfile. -/
structure UniverseConfig where
  levelStructure : LevelStructure
  constructionLevel : UniverseConstructionLevel

/-- FX's universe config currently records only the cumulative Nat-indexed
level structure.  It does not claim Axis 10 univalence or cumulativity. -/
def fxUniverseConfig : UniverseConfig where
  levelStructure := .cumulativeNat
  constructionLevel := .levelStructureOnly

/-- FX universes are configured with Nat-indexed levels. -/
theorem fxUniverseConfig_levelStructure :
    fxUniverseConfig.levelStructure = LevelStructure.cumulativeNat := rfl

/-- FX Axis 10 currently has only a level-structure ledger. -/
theorem fxUniverseConfig_constructionLevel :
    fxUniverseConfig.constructionLevel =
      UniverseConstructionLevel.levelStructureOnly := rfl

/-- FX Axis 10 currently has no constructed operational univalence theorem. -/
theorem fxUniverseConfig_hasNoOperationalUnivalence :
    fxUniverseConfig.constructionLevel.hasOperationalUnivalence = false := rfl

/-- FX Axis 10 currently has no constructed polynomial-subterminality theorem. -/
theorem fxUniverseConfig_hasNoPolynomialSubterminality :
    fxUniverseConfig.constructionLevel.hasPolynomialSubterminality = false := rfl

/-- FX Axis 10 currently has no constructed universe-cumulativity theorem. -/
theorem fxUniverseConfig_hasNoCumulativity :
    fxUniverseConfig.constructionLevel.hasCumulativity = false := rfl

end FX1Poly.Universe
