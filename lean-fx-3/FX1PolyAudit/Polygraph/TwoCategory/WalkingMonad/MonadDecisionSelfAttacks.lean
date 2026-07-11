import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDecisionSelfAttacks

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadDecisionSelfAttacks — zero-axiom gate

Per-declaration zero-axiom gate for the concrete-word truth-probes of the closed saturated decision (the block-sum
re-sort smokes, the width-4 associativity combs, and their folds) plus the B2 self-attack verdicts.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadComposeCounts_probe_twoOne
#assert_no_axioms FX1Poly.Polygraph.monadComposeCounts_probe_mixed
#assert_no_axioms FX1Poly.Polygraph.monadComposeCounts_probe_single
#assert_no_axioms FX1Poly.Polygraph.monadAssocCombLeftFour
#assert_no_axioms FX1Poly.Polygraph.monadAssocCombRightFour
#assert_no_axioms FX1Poly.Polygraph.monadFold_assocCombLeftFour
#assert_no_axioms FX1Poly.Polygraph.monadFold_assocCombRightFour
#assert_no_axioms FX1Poly.Polygraph.monadDecision_yes_assocFour
#assert_no_axioms FX1Poly.Polygraph.monadFaceInsertPortZero
#assert_no_axioms FX1Poly.Polygraph.monadFaceInsertPortTwo
#assert_no_axioms FX1Poly.Polygraph.monadFold_faceInsertPortZero
#assert_no_axioms FX1Poly.Polygraph.monadFold_faceInsertPortTwo
#assert_no_axioms FX1Poly.Polygraph.monadDecision_no_facePorts

end FX1PolyAudit
