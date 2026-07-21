import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleWellPointedCollapse

/-! # FX1PolyAudit.…WalkingCohesionQuadruple.QuadrupleWellPointedCollapse — zero-axiom gate

Per-declaration zero-axiom gate for the Δ-separator collapse suite: the two split-iso inverse-uniqueness
engines, the three modality multiplication/comultiplication cells with their round-trip collapses and
unit/counit laws, the three well-pointedness agreements (`ʃ`/`♭`/`♯`), the three remaining leg straddle joins,
the bundles, the head-constructor probe with the three non-degeneracy distinctness witnesses, and the two
honesty markers.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.quadCohesionRightInverseOfSplitIsoUnique
#assert_no_axioms FX1Poly.Polygraph.quadCohesionLeftInverseOfSplitIsoUnique
#assert_no_axioms FX1Poly.Polygraph.quadShapeLeftUnitWhiskerCell
#assert_no_axioms FX1Poly.Polygraph.quadShapeRightUnitWhiskerCell
#assert_no_axioms FX1Poly.Polygraph.quadShapeMulCell
#assert_no_axioms FX1Poly.Polygraph.quadShapeMulInvCell
#assert_no_axioms FX1Poly.Polygraph.quadShapeMulRoundCollapses
#assert_no_axioms FX1Poly.Polygraph.quadShapeMonadLeftUnitLaw
#assert_no_axioms FX1Poly.Polygraph.quadShapeMonadRightUnitLaw
#assert_no_axioms FX1Poly.Polygraph.quadShapeUnitWhiskersAgree
#assert_no_axioms FX1Poly.Polygraph.quadFlatLeftCounitWhiskerCell
#assert_no_axioms FX1Poly.Polygraph.quadFlatRightCounitWhiskerCell
#assert_no_axioms FX1Poly.Polygraph.quadFlatComulCell
#assert_no_axioms FX1Poly.Polygraph.quadFlatComulInvCell
#assert_no_axioms FX1Poly.Polygraph.quadFlatComulRoundCollapses
#assert_no_axioms FX1Poly.Polygraph.quadFlatComonadLeftCounitLaw
#assert_no_axioms FX1Poly.Polygraph.quadFlatComonadRightCounitLaw
#assert_no_axioms FX1Poly.Polygraph.quadFlatCounitWhiskersAgree
#assert_no_axioms FX1Poly.Polygraph.quadSharpLeftUnitWhiskerCell
#assert_no_axioms FX1Poly.Polygraph.quadSharpRightUnitWhiskerCell
#assert_no_axioms FX1Poly.Polygraph.quadSharpMulCell
#assert_no_axioms FX1Poly.Polygraph.quadSharpMulInvCell
#assert_no_axioms FX1Poly.Polygraph.quadSharpMulRoundCollapses
#assert_no_axioms FX1Poly.Polygraph.quadSharpMonadLeftUnitLaw
#assert_no_axioms FX1Poly.Polygraph.quadSharpMonadRightUnitLaw
#assert_no_axioms FX1Poly.Polygraph.quadSharpUnitWhiskersAgree
#assert_no_axioms FX1Poly.Polygraph.quadStraddlePi0UnitInvCounitJoin
#assert_no_axioms FX1Poly.Polygraph.quadStraddleGammaCounitMiddleInvUnitJoin
#assert_no_axioms FX1Poly.Polygraph.quadStraddleGammaUnitUpperInvCounitJoin
#assert_no_axioms FX1Poly.Polygraph.quadAllModalityDeltaSeparatorsCollapse
#assert_no_axioms FX1Poly.Polygraph.quadRemainingLegStraddleJoins
#assert_no_axioms FX1Poly.Polygraph.quadIsWhiskerLeftHeadedCell
#assert_no_axioms FX1Poly.Polygraph.quadShapeUnitWhiskers_sidesAreDistinct
#assert_no_axioms FX1Poly.Polygraph.quadFlatCounitWhiskers_sidesAreDistinct
#assert_no_axioms FX1Poly.Polygraph.quadSharpUnitWhiskers_sidesAreDistinct
#assert_no_axioms FX1Poly.Polygraph.fxQuadCohesion_hasDeltaSeparatorCollapseAtAllThreeModalities
#assert_no_axioms FX1Poly.Polygraph.fxQuadCohesion_hasAllSixLegStraddleJoins

end FX1PolyAudit
