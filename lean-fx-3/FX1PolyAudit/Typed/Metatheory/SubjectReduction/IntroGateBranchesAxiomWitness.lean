import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranches

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.IntroGateBranchesAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every declaration of the introducer-congruence branch module:
the two head-refutation helpers and the sixteen per-generator branch rows.

Each branch row is a single application of its `IntroGateBranchesBounded` twin at
`UnionChildSubjectReduction.toBelow`, so this witness also independently certifies that the flavor-forgetting
step (`Nat` order only) and every bounded twin it fires carry no axiom.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Typed.intervalTypeCell_not_conv_natTypeCell
#print axioms FX1Poly.Typed.intervalTypeCell_not_conv_listTypeCell

#print axioms FX1Poly.Typed.boolTrueIntroGateBranchCloses
#print axioms FX1Poly.Typed.boolFalseIntroGateBranchCloses
#print axioms FX1Poly.Typed.unitIntroGateBranchCloses
#print axioms FX1Poly.Typed.interval0IntroGateBranchCloses
#print axioms FX1Poly.Typed.interval1IntroGateBranchCloses
#print axioms FX1Poly.Typed.natZeroIntroGateBranchCloses
#print axioms FX1Poly.Typed.optionNoneIntroGateBranchCloses
#print axioms FX1Poly.Typed.listNilIntroGateBranchCloses
#print axioms FX1Poly.Typed.natSuccIntroGateBranchCloses
#print axioms FX1Poly.Typed.optionSomeIntroGateBranchCloses
#print axioms FX1Poly.Typed.eitherInlIntroGateBranchCloses
#print axioms FX1Poly.Typed.eitherInrIntroGateBranchCloses
#print axioms FX1Poly.Typed.pairIntroGateBranchCloses
#print axioms FX1Poly.Typed.listConsIntroGateBranchCloses
#print axioms FX1Poly.Typed.reflIntroGateBranchCloses
#print axioms FX1Poly.Typed.lamIntroGateBranchCloses

end FX1PolyAudit
