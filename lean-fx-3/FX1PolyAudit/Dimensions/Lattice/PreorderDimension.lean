import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Lattice.PreorderDimension

/-! # FX1PolyAudit.Dimensions.Lattice.PreorderDimension — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_refl
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_symm
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_trans
#assert_no_axioms FX1Poly.Modal.PreorderDimension.IsAntisymmetric
#assert_no_axioms FX1Poly.Modal.PreorderDimension.product
#assert_no_axioms FX1Poly.Modal.boundedJoinSemilatticeToPreorder
#assert_no_axioms FX1Poly.Modal.latticePreorderIsAntisymmetric
#assert_no_axioms FX1Poly.Modal.effectInducedPreorderIsAntisymmetric
#assert_no_axioms FX1Poly.Modal.LifetimeGrade.outlives
#assert_no_axioms FX1Poly.Modal.lifetimeOutlivesRefl
#assert_no_axioms FX1Poly.Modal.lifetimeOutlivesTrans
#assert_no_axioms FX1Poly.Modal.lifetimePreorder
#assert_no_axioms FX1Poly.Modal.lifetimeStaticOutlivesAll
#assert_no_axioms FX1Poly.Modal.lifetimeRegionsEquivalentButDistinct
#assert_no_axioms FX1Poly.Modal.lifetimeIsNotAntisymmetric
#assert_no_axioms FX1Poly.Modal.lifetimeProductPreorder

end FX1PolyAudit
