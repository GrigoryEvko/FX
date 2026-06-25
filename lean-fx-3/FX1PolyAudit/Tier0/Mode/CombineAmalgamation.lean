import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.CombineAmalgamation

/-! # FX1PolyAudit/AuditTier0ModeCombineAmalgamation — zero-axiom gate for mode-18

Per-declaration zero-axiom gate for `mode-18` (`FX1Poly/Tier0/Mode/CombineAmalgamation.lean`): the doctrine
feature profile + §6.8 collision catalogue, the pushout/combine + its universal property + symmetry, the
decidable combinability + the H² obstruction shadow + the blocking theorem, the witnesses, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Doctrines + the §6.8 collision catalogue
#assert_no_axioms FX1Poly.Tier0.Doctrine
#assert_no_axioms FX1Poly.Tier0.Doctrine.hasCollision
#assert_no_axioms FX1Poly.Tier0.Doctrine.isAdmissible

-- The pushout / amalgamation + universal property
#assert_no_axioms FX1Poly.Tier0.Doctrine.combine
#assert_no_axioms FX1Poly.Tier0.Doctrine.Refines
#assert_no_axioms FX1Poly.Tier0.Doctrine.combine_refines_left
#assert_no_axioms FX1Poly.Tier0.Doctrine.combine_refines_right
#assert_no_axioms FX1Poly.Tier0.Doctrine.combine_universal
#assert_no_axioms FX1Poly.Tier0.Doctrine.combine_comm

-- Decidable combinability + the H² obstruction
#assert_no_axioms FX1Poly.Tier0.Doctrine.combinesOrthogonally
#assert_no_axioms FX1Poly.Tier0.Doctrine.combinationObstruction
#assert_no_axioms FX1Poly.Tier0.Doctrine.combinesOrthogonally_eq
#assert_no_axioms FX1Poly.Tier0.Doctrine.combinationObstruction_blocks

-- Witnesses
#assert_no_axioms FX1Poly.Tier0.emptyDoctrine
#assert_no_axioms FX1Poly.Tier0.emptyDoctrine_combine
#assert_no_axioms FX1Poly.Tier0.classifiedDoctrine
#assert_no_axioms FX1Poly.Tier0.failDoctrine
#assert_no_axioms FX1Poly.Tier0.borrowDoctrine
#assert_no_axioms FX1Poly.Tier0.classified_fail_no_combine
#assert_no_axioms FX1Poly.Tier0.classified_fail_obstructed
#assert_no_axioms FX1Poly.Tier0.classified_borrow_combines

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohomologicalH2
#assert_no_axioms FX1Poly.Tier0.fxMode_hasDistributiveLawPushout
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFull21DimCollisionMatrix
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelCombineConnection

end FX1PolyAudit
