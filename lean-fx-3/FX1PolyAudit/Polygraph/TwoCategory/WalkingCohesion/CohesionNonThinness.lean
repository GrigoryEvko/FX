import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionNonThinness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCohesion.CohesionNonThinness — zero-axiom gate (thinness REFUTED)

Per-declaration zero-axiom gate for the r2 non-thinness refutation: the generic `ℤ/2`-parity homomorphism and its
soundness over `TwoCellStep` / `TwoCellConv` / `TwoCellConvFull` / `castBoundary`, the cohesion instantiation and
its saturated-congruence soundness, the separating parallel pair at the hom `id ⇒ shape`, the refutation of
`CohesionThinness` / `CohesionLocalPosetality`, the non-vacuity witnesses, and the honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.genParity
#assert_no_axioms FX1Poly.Polygraph.genParity_castBoundary
#assert_no_axioms FX1Poly.Polygraph.genParity_step
#assert_no_axioms FX1Poly.Polygraph.genParity_conv
#assert_no_axioms FX1Poly.Polygraph.genParity_convFull
#assert_no_axioms FX1Poly.Polygraph.cohesionGeneratorParity
#assert_no_axioms FX1Poly.Polygraph.cohesionParity
#assert_no_axioms FX1Poly.Polygraph.cohesionParity_satConv
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeUnitViaLowerAdjunctionCell
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeUnit_parity
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeUnitViaLowerAdjunction_parity
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeUnit_notConvertibleToLowerAdjunctionRoute
#assert_no_axioms FX1Poly.Polygraph.cohesionNotLocallyPosetal
#assert_no_axioms FX1Poly.Polygraph.cohesionLocalPosetality_uninhabited
#assert_no_axioms FX1Poly.Polygraph.cohesionParity_agreesOnGenuineIdentification
#assert_no_axioms FX1Poly.Polygraph.cohesionNonThinness_isNonVacuous
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_isLocallyPosetal
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasThinnessRefutation

end FX1PolyAudit
