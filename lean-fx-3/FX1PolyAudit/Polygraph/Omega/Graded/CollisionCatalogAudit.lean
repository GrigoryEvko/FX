import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Graded.CollisionCatalog

/-! # FX1PolyAudit.Polygraph.Omega.Graded.CollisionCatalogAudit — zero-axiom gate for the §6.8
soundness-collision catalog as data (OMEGA-5 r1, B4).

Per-declaration `#assert_no_axioms` on the collision-row record, the nine collision rows, the catalog,
the non-free predicate, and the non-vacuity witnesses (length, all-non-free, the contradictory `E044`
locus, the 3-way `I004`). -/

namespace FX1PolyAudit

-- CollisionCatalog.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.CollisionRow
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionClassifiedFail
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionBorrowAsync
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionCtAsync
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionCtFailSecret
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionMonotonicConcurrent
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionGhostRuntime
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionClassifiedAsyncSession
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionDecimalOverflowWrap
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionBorrowUnscopedSpawn
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.sixEightCatalog
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.allCollisionsNonFree
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.sixEightCatalog_length
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.sixEightCatalog_allNonFree
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionCtAsync_isContradictoryNonFree
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.collisionClassifiedAsyncSession_isThreeWay

end FX1PolyAudit
