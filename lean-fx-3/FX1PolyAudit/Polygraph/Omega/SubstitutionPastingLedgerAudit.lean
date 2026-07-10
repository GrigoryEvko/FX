import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.SubstitutionPastingLedger

/-! # FX1PolyAudit.Polygraph.Omega.SubstitutionPastingLedgerAudit — zero-axiom gate for the OMEGA-7 r1 ledger
(OMEGA-7 r1, B4).

Per-declaration `#assert_no_axioms` on the four shipped-piece markers (anchor / pasting arithmetic / tuple
seed / admission chain seed), the r1-anchor-round-complete marker, the three surviving-jam markers (total
model / fragment substCell=pasteAlong / kernel-as-value tuple), the permanent general-familiality wall, and
the staircase-closure criteria marker. -/

namespace FX1PolyAudit

-- SubstitutionPastingLedger.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_substCompositionAnchored
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_pastingArithmeticShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_presentedKernelTupleSeeded
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_admissionChainSeeded
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_r1AnchorRoundComplete
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_totalTermToCellModelReached
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_fragmentSubstCellEqPasteAlongReached
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_kernelAsValueTuple
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_generalFamilialityDecidable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega7_staircaseClosureCriteriaRecorded

end FX1PolyAudit
