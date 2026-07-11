import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AcyclicObstructionTruncationCertificate

/-! # FX1PolyAudit/Polygraph/Homology/AcyclicObstructionTruncationCertificate — zero-axiom gate (the
    decidable Ufnarovski-graph acyclicity checker, the conditional vanishing `census 0 ==> exact`, and the
    `{xy}` finite eventual-exactness certificate)

Per-declaration zero-axiom gate for TOWER-ANICK r6 (#2144 / #2145): the fuel-structural acyclicity checker
(`obstructionOutNeighbours`, `obstructionFrontierStep`, `obstructionReachableWithin`, `natListContains`,
`obstructionSources`, `obstructionSourceReachesItself`, `anyObstructionSourceOnCycle`,
`isAcyclicUfnarovskiGraph`, `hasSelfLoop`) with its three-graph classification, the conditional vanishing
(`multiObstructionHomologyDataAtDegree`, `multiObstructionHomologyInvariantIsFreeOnCensus`,
`censusZeroImpliesExact`), the `{xy}` finite certificate (`AcyclicTruncationCertificate`,
`linearSystemTruncationCertificate`, `linearSystemEventuallyExact`), and the ledger markers.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B1: the decidable acyclicity checker
#assert_no_axioms FX1Poly.Polygraph.Homology.obstructionOutNeighbours
#assert_no_axioms FX1Poly.Polygraph.Homology.obstructionFrontierStep
#assert_no_axioms FX1Poly.Polygraph.Homology.obstructionReachableWithin
#assert_no_axioms FX1Poly.Polygraph.Homology.natListContains
#assert_no_axioms FX1Poly.Polygraph.Homology.obstructionSources
#assert_no_axioms FX1Poly.Polygraph.Homology.obstructionSourceReachesItself
#assert_no_axioms FX1Poly.Polygraph.Homology.anyObstructionSourceOnCycle
#assert_no_axioms FX1Poly.Polygraph.Homology.isAcyclicUfnarovskiGraph
#assert_no_axioms FX1Poly.Polygraph.Homology.hasSelfLoop
#assert_no_axioms FX1Poly.Polygraph.Homology.linearGraphIsAcyclic
#assert_no_axioms FX1Poly.Polygraph.Homology.selfLoopGraphIsNotAcyclic
#assert_no_axioms FX1Poly.Polygraph.Homology.fibGraphIsNotAcyclic
#assert_no_axioms FX1Poly.Polygraph.Homology.linearGraphHasNoSelfLoop
#assert_no_axioms FX1Poly.Polygraph.Homology.selfLoopGraphHasSelfLoop
#assert_no_axioms FX1Poly.Polygraph.Homology.fibGraphHasSelfLoop

-- B2: the conditional vanishing
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionHomologyDataAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionHomologyInvariantIsFreeOnCensus
#assert_no_axioms FX1Poly.Polygraph.Homology.censusZeroImpliesExact

-- B3: the {xy} finite certificate
#assert_no_axioms FX1Poly.Polygraph.Homology.AcyclicTruncationCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.linearSystemTruncationCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.linearSystemEventuallyExact

-- B4: the named node and the ledger marker
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicToCensusZeroIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicObstructionTruncationCertificateIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.isAcyclicUfnarovskiGraph
#print axioms FX1Poly.Polygraph.Homology.linearGraphIsAcyclic
#print axioms FX1Poly.Polygraph.Homology.selfLoopGraphIsNotAcyclic
#print axioms FX1Poly.Polygraph.Homology.fibGraphIsNotAcyclic
#print axioms FX1Poly.Polygraph.Homology.multiObstructionHomologyInvariantIsFreeOnCensus
#print axioms FX1Poly.Polygraph.Homology.censusZeroImpliesExact
#print axioms FX1Poly.Polygraph.Homology.linearSystemEventuallyExact
#print axioms FX1Poly.Polygraph.Homology.linearSystemTruncationCertificate

end FX1PolyAudit
