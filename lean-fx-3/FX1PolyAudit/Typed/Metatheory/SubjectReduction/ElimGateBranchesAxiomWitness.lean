import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateBranches

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.ElimGateBranchesAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over all eleven per-generator rows of the eliminator-congruence
gate.

The rows split by provenance:

  * SEVEN rows (`fst` / `snd` / `app` / `pathApp` / `boolElim` / `natElim` / `natRec`) are single applications of
    their `ElimGateBranchesBounded` twins at `UnionChildSubjectReduction.toBelow`, so this witness also
    independently certifies the flavor-forgetting step and the bounded twins those rows fire;
  * FOUR rows (`optionMatch` / `eitherMatch` / `idJ` / `listElim`) have NO bounded twin and are proved in full
    here — genuine unbounded-only content.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Typed.fstElimGateBranchCloses
#print axioms FX1Poly.Typed.sndElimGateBranchCloses
#print axioms FX1Poly.Typed.appElimGateBranchCloses
#print axioms FX1Poly.Typed.pathAppElimGateBranchCloses
#print axioms FX1Poly.Typed.boolElimGateBranchCloses
#print axioms FX1Poly.Typed.natElimGateBranchCloses
#print axioms FX1Poly.Typed.natRecGateBranchCloses

#print axioms FX1Poly.Typed.optionMatchGateBranchCloses
#print axioms FX1Poly.Typed.eitherMatchGateBranchCloses
#print axioms FX1Poly.Typed.idJGateBranchCloses
#print axioms FX1Poly.Typed.listElimGateBranchCloses

end FX1PolyAudit
