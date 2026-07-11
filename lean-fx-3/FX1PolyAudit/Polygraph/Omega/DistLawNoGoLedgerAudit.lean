import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.DistLawNoGoLedger

/-! # FX1PolyAudit.Polygraph.Omega.DistLawNoGoLedgerAudit — zero-axiom gate for the distributive-law no-go
ledger and census feed (WP-DISTLAW r1, B4 + B5).

Per-declaration `#assert_no_axioms` on the model-law status sum, the ledger-entry structure, the three
populated entries, the ledger and its free-theory-side / count lemmas, the walker-grounded free-theory
presentation statement, and the census-feed / inheritance / jam / #2187-state markers. -/

namespace FX1PolyAudit

-- the ledger interface
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawModelStatus
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawLedgerEntry

-- the three populated entries
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawLedgerReaderReader
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawLedgerPowersetPowerset
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawLedgerIdempotentCounterexample

-- the ledger and its grounded lemmas
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawNoGoLedger
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawNoGoLedger_allFreeTheoryPresented
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawNoGoLedger_countIsThree

-- the walker-grounded free-theory presentation
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawWalkerFreeTheoryPresentedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawWalkerFreeTheoryPresented

-- the census feed, downstream inheritance, jams, and #2187 state markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_censusFeedNewSingleObjectWalker
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_downstreamInheritanceRecorded
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_jamFullTwoCellDecisionAtMonadPathNormalForm
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_jamMechanizedFiniteNoGoDeferredOnCarrierBound
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_jamFullHomotopyBasisOmegaFiveHandoff
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_wpDistLawR1StateRecorded

end FX1PolyAudit
