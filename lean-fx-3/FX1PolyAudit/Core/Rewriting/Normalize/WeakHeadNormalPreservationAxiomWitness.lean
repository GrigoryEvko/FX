import FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalPreservation

/-! # FX1PolyAudit.Core.Rewriting.Normalize.WeakHeadNormalPreservationAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the weak-head
normal-form preservation module: the step-into-a-cell packaging inversion, the backward weak-head
reflection, and the normality-preservation corollary.  Each must print "does not depend on any
axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Core.Step.weakHeadOrSpineStepIntoCell
#print axioms FX1Poly.Core.WeakHeadStep.reflectAlongStep
#print axioms FX1Poly.Core.WeakHeadStep.weakHeadNormalPreservedByStep

end FX1PolyAudit
