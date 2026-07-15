import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.StepInversionAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over the two-child spine slot
decomposition and every root inversion rewired onto it.  Each must print "does not depend on any
axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Core.StepChildren.no_step_at_empty_spine
#print axioms FX1Poly.Core.StepChildren.invertTwoChildSpine

#print axioms FX1Poly.Core.Step.from_lam
#print axioms FX1Poly.Core.Step.from_pair
#print axioms FX1Poly.Core.Step.from_listCons
#print axioms FX1Poly.Core.Step.from_glueIntro
#print axioms FX1Poly.Core.Step.from_arrowCode
#print axioms FX1Poly.Core.Step.from_productCode
#print axioms FX1Poly.Core.Step.from_sumCode
#print axioms FX1Poly.Core.Step.from_eitherCode
#print axioms FX1Poly.Core.Step.from_equivCode
#print axioms FX1Poly.Core.Step.from_piTyCode
#print axioms FX1Poly.Core.Step.from_sigmaTyCode
#print axioms FX1Poly.Core.Step.from_polyFunctor
#print axioms FX1Poly.Core.Step.from_app
#print axioms FX1Poly.Core.Step.from_pathApp

#print axioms FX1Poly.Core.Step.from_boolElim
#print axioms FX1Poly.Core.Step.from_natElim
#print axioms FX1Poly.Core.Step.from_natRec
#print axioms FX1Poly.Core.Step.from_listElim
#print axioms FX1Poly.Core.Step.from_optionMatch
#print axioms FX1Poly.Core.Step.from_eitherMatch

end FX1PolyAudit
