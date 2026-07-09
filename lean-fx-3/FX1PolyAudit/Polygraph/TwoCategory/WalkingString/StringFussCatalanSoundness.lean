import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanSoundness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanSoundness — zero-axiom gate (FC-1 B/C/D)

Per-declaration zero-axiom gate for the FC-1 colour-faithfulness (B), FC soundness (C), and one-colour regression
(D) layers.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- (B) wire-level chirality + colour faithfulness
#assert_no_axioms FX1Poly.Polygraph.isCupWordOrdered
#assert_no_axioms FX1Poly.Polygraph.isCapWordOrdered
#assert_no_axioms FX1Poly.Polygraph.stringCapWord_not_cupWord
#assert_no_axioms FX1Poly.Polygraph.stringCupWord_not_capWord
#assert_no_axioms FX1Poly.Polygraph.stringCupCapWord_hasExactlyOneGEnd
#assert_no_axioms FX1Poly.Polygraph.stringGeneratorArcColour_ne_gWire
#assert_no_axioms FX1Poly.Polygraph.stringGeneratorArcColours
#assert_no_axioms FX1Poly.Polygraph.fxString_hasFcColourFaithful

-- (C) FC soundness
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_fcDiagramOf_eq
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_ne_notSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringSnakeF_eq_identityF
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringSnakeGlo_eq_identityG
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringSnakeGhi_eq_identityG
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringSnakeH_eq_identityH
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringSnakeGlo_eq_stringSnakeGhi
#assert_no_axioms FX1Poly.Polygraph.fcDiagramOf_stringCrossLevel_ne_identityG
#assert_no_axioms FX1Poly.Polygraph.fxString_hasFcSoundness

-- (D) one-colour regression
#assert_no_axioms FX1Poly.Polygraph.fcDiagramForgetColour
#assert_no_axioms FX1Poly.Polygraph.fcDiagramForgetColour_fcDiagramOf
#assert_no_axioms FX1Poly.Polygraph.IsMonochromaticFc
#assert_no_axioms FX1Poly.Polygraph.monochromaticFc_reduces_toMatchingOf
#assert_no_axioms FX1Poly.Polygraph.stringUnitLower_isMonochromaticFc
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMonochromaticRegression

end FX1PolyAudit
