import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleReflectionStraddleJoins

/-! # FX1PolyAudit.…WalkingCohesionQuadruple.QuadrupleReflectionStraddleJoins — zero-axiom gate

Per-declaration zero-axiom gate for the extended thin fragment: the two new ff-round-trip whisker collapses
(`coDisc`-ff-upper, `Disc`-ff-middle), the two new reflection straddle joins (upper on `codisc`, middle on
`disc`), their bundle, the non-degeneracy size checks, and the two honesty markers (the complete reflection-join
suite + the sharper free-word-normalizer wall).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.quadCodiscWhiskeredUpperRoundCollapses
#assert_no_axioms FX1Poly.Polygraph.quadStraddleCodiscUnitInvCounitJoin
#assert_no_axioms FX1Poly.Polygraph.quadDiscWhiskeredMiddleRoundLeftCollapses
#assert_no_axioms FX1Poly.Polygraph.quadStraddleDiscCounitMiddleInvUnitJoin
#assert_no_axioms FX1Poly.Polygraph.quadAllReflectionStraddleJoins
#assert_no_axioms FX1Poly.Polygraph.quadStraddleMiddleJoin_sidesAreDistinct
#assert_no_axioms FX1Poly.Polygraph.quadStraddleUpperJoin_sidesAreDistinct
#assert_no_axioms FX1Poly.Polygraph.fxQuadCohesion_hasReflectionStraddleJoinSuite
#assert_no_axioms FX1Poly.Polygraph.fxQuadCohesion_hasFreeWordNormalizerForThinness

end FX1PolyAudit
