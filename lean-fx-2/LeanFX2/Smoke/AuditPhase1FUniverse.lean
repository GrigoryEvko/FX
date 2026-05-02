import LeanFX2.Foundation.Universe

/-! Phase 1.F zero-axiom audit — universe preorder scaffolding.

These five declarations form the structural foundation for the future
`Ty.universe` / `Conv.cumul` integration.  All zero-axiom because the
preorder is just `Nat.le` (decidable, structural). -/

#print axioms LeanFX2.Ty.universeLe
#print axioms LeanFX2.Ty.universeLe_refl
#print axioms LeanFX2.Ty.universeLe_trans
#print axioms LeanFX2.Ty.universeLe_decidable
#print axioms LeanFX2.Ty.universeLe_succ
#print axioms LeanFX2.Ty.universeLe_succ_iff_le
