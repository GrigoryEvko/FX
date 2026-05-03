import LeanFX2.Foundation.Universe

/-! Phase 1.F zero-axiom audit — universe hierarchy scaffolding.

These declarations form the structural foundation for `Ty.universe` /
`Conv.cumul` integration. -/

#print axioms LeanFX2.UniverseLevel
#print axioms LeanFX2.UniverseLevel.toNat
#print axioms LeanFX2.UniverseLevel.le
#print axioms LeanFX2.UniverseLevel.leDecidable
#print axioms LeanFX2.UniverseLevel.le_refl
#print axioms LeanFX2.UniverseLevel.le_trans
#print axioms LeanFX2.UniverseLevel.le_succ

#print axioms LeanFX2.Ty.universeLe
#print axioms LeanFX2.Ty.universeLe_refl
#print axioms LeanFX2.Ty.universeLe_trans
#print axioms LeanFX2.Ty.universeLe_decidable
#print axioms LeanFX2.Ty.universeLe_succ
#print axioms LeanFX2.Ty.universeLe_succ_iff_le
