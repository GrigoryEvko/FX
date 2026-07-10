import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WeakDirectedCeilingLedger

/-! # FX1PolyAudit.Polygraph.Omega.WeakDirectedCeilingLedgerAudit — zero-axiom gate for the OMEGA-6 ceiling ledger
(OMEGA-6 r1, B4).

Per-declaration `#assert_no_axioms` on the six checking-vs-deciding markers (ps-check / coh-admission /
free-strict decidable; weak-ω coherence equality / general presented word problem / weak-ω operad model NOT
decidable), the four deferred-item markers (fullness / typed telescope / genuine reverse / SN-subset-folk
shipped), the r1-checking-shipped marker, the OMEGA-7 pasting-shape signature, and the handoff-recorded
marker. -/

namespace FX1PolyAudit

-- WeakDirectedCeilingLedger.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_psContextCheckDecidable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_cohCellCheckable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_freeStrictWordProblemDecidable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_weakOmegaCoherenceEqualityDecidable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_generalPresentedWordProblemDecidable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_weakOmegaModelAsOperadAlgebra
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_cohFullnessChecked
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_psContextTypedTelescope
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_genuineOmegaReverseModelled
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_snInvertibleSubsetFolkShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_r1CheckingShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.OmegaSevenPastingShape
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega6_omegaSevenHandoffRecorded

end FX1PolyAudit
