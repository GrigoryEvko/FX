import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.TypeAxis.TypeSix

/-! # FX1PolyAudit/AuditTier0TypeSix — zero-axiom gate for type-6 (HITs: cubical computation + canonicity)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Ledger/TypeAxis/TypeSix.lean`: the four backed flips (path
β computation, cubical path typing, the truncation recursor, HIT-row structural safety) and the three
deferral honesty markers (cubical Kan operations, HIT path constructors, HIT canonicity).  Gating
`fxType_pathComputation_isBacked` / `fxType_truncationRecursor_isBacked` transitively certifies the path-β
and truncation iota rows zero-axiom; gating `fxType_cubicalPathTyping_isBacked` certifies the interval/bridge
typing rows and the affine path-introduction.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The four backed flips
#assert_no_axioms FX1Poly.Tier0.fxType_hasPathComputation
#assert_no_axioms FX1Poly.Tier0.fxType_pathComputation_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasCubicalPathTyping
#assert_no_axioms FX1Poly.Tier0.fxType_cubicalPathTyping_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasTruncationRecursor
#assert_no_axioms FX1Poly.Tier0.fxType_truncationRecursor_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasHitRowStructuralSafety
#assert_no_axioms FX1Poly.Tier0.fxType_hitRowStructuralSafety_isBacked

-- The deferral honesty markers
#assert_no_axioms FX1Poly.Tier0.fxType_hasCubicalKanOperations
#assert_no_axioms FX1Poly.Tier0.fxType_hasHitPathConstructors
#assert_no_axioms FX1Poly.Tier0.fxType_hasHitCanonicity

end FX1PolyAudit
