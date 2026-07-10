import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRightImageReflect

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutRightImageReflect — zero-axiom gate for the right-image
isFalse reflection (conservativity, semantic half) via the arity fold

Per-declaration zero-axiom gate for the fold-preservation infrastructure (`mapPath_length`,
`arityFoldStepAtom_congr`, the joint spine recursion `arityFold_foldl_mapCellAlong`, and its corollary
`arityMonotoneMapOf_mapCellAlong`), the semantic reflection (`pushoutRightImage_arityFoldEq`), the separation isFalse
(`pushoutRightImage_notConv_of_arityDiffer`), the non-vacuity witness, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the fold-preservation infrastructure
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFoldStepAtom_congr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFold_foldl_mapCellAlong
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_mapCellAlong

-- the semantic reflection + separation isFalse + non-vacuity
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImage_arityFoldEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImage_notConv_of_arityDiffer
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconFaces_arityMapsDiffer
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageFaces_notConv

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRightImageArityReflection
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_fullRightImageReflectionStaysWalled

end FX1PolyAudit
