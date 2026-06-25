import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Lattice.ClockDomainLatticeDimension

/-! # FX1PolyAudit.Dimensions.Lattice.ClockDomainLatticeDimension — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.natBeqReflexive
#assert_no_axioms FX1Poly.Modal.natEqOfBeqTrue
#assert_no_axioms FX1Poly.Modal.natBeqCommutes
#assert_no_axioms FX1Poly.Modal.ClockGrade.join
#assert_no_axioms FX1Poly.Modal.clockJoinSyncWithSelf
#assert_no_axioms FX1Poly.Modal.clockLattice
#assert_no_axioms FX1Poly.Modal.clockJoinCommutes
#assert_no_axioms FX1Poly.Modal.clockJoinAssociates
#assert_no_axioms FX1Poly.Modal.clockIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.clockSyncIncomparableOfDistinct
#assert_no_axioms FX1Poly.Modal.clockSyncJoinDistinctIsCrossDomain
#assert_no_axioms FX1Poly.Modal.clockSync01Incomparable
#assert_no_axioms FX1Poly.Modal.clockCombinationalIsLeast
#assert_no_axioms FX1Poly.Modal.clockCrossDomainIsGreatest
#assert_no_axioms FX1Poly.Modal.clockOverflowProductIsLawful

end FX1PolyAudit
