import FX1Poly.Core.Eliminators.Nat.NatShapedRecursorCellStrongNormalization
import FX1Poly.Core.Eliminators.Nat.NatElimNumeralStrongNormalization
import FX1Poly.Core.Eliminators.Nat.NatElimReductTrackingStrongNormalization

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatShapedRecursorCellStrongNormalizationAxiomWitness —
    independent #print axioms

An INDEPENDENT `#print axioms` cross-check — a separate mechanism in a separate file from the fuel-based
`#assert_no_axioms` gates of the per-file twins — over the generator-agnostic nat-shaped recursor cell-SN
engines AND every `natElim` / `natRec` twin derived from them.

The engines carry the `Acc` towers once; the ten twins below instantiate them at their own spine, inversion,
and contractum congruence.  Each must print "does not depend on any axioms" — so the collapse cannot have
smuggled an axiom into the shared argument, and no derived twin picks one up through its instantiation.

Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Core.StepStar.NatShapedSpineInversion
#print axioms FX1Poly.Core.StepStar.NatShapedContractumCongruence
#print axioms FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee
#print axioms FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
#print axioms
  FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN
#print axioms FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_natValueScrutinee

#print axioms FX1Poly.Core.StepStar.natSuccCell_inj
#print axioms FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_normalScrutinee
#print axioms FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_normalScrutinee
#print axioms FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_natValueScrutinee
#print axioms FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_natValueScrutinee

#print axioms FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
#print axioms FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
#print axioms
  FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN
#print axioms
  FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN
#print axioms
  FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN
#print axioms
  FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN

end FX1PolyAudit
