import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Parametricity.AffineBoundaryStructural

/-! # FX1PolyAudit/AuditAffineBoundaryStructural — zero-axiom gate for the affine boundary predicate

Per-declaration zero-axiom gate for
`FX1Poly/Typed/Dimensions/Parametricity/AffineBoundaryStructural.lean`: the structural boundary predicate
(`isAffineEndpointHead` / `isOnAffineBoundary`), the endpoint/interior computations
(`interval0_isOnAffineBoundary` / `interval1_isOnAffineBoundary` / `var_isNotOnAffineBoundary`), the
classifier (`affineEndpoint_classifies`), and the QF_BV-moot theorems
(`affineBoundary_needsNoConnectionSolver` / `deMorganBoundary_wouldNeedConnectionSolver`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — demonstrating that deciding the affine boundary predicate (Nuyts hurdle 4)
requires NO SMT / QF_BV / cofibration solver, only `DecidableEq`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.isAffineEndpointHead
#assert_no_axioms FX1Poly.Typed.isOnAffineBoundary
#assert_no_axioms FX1Poly.Typed.interval0_isOnAffineBoundary
#assert_no_axioms FX1Poly.Typed.interval1_isOnAffineBoundary
#assert_no_axioms FX1Poly.Typed.var_isNotOnAffineBoundary
#assert_no_axioms FX1Poly.Typed.affineEndpoint_classifies
#assert_no_axioms FX1Poly.Typed.affineBoundary_needsNoConnectionSolver
#assert_no_axioms FX1Poly.Typed.deMorganBoundary_wouldNeedConnectionSolver
#assert_no_axioms FX1Poly.Typed.connectionHeadedDimension_notStructurallyDetected

end FX1PolyAudit
