import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaTableStar

/-! # FX1PolyAudit/AuditEtaTableStar — ETA-T5 inc-4.1 shard

Per-declaration zero-axiom gate for the table eta star and its
substitution diagonals: the stars with concatenation and position
lifts, the renaming closure, the pointwise-star substitution
machinery, the ★ term-monotone substitution star, and the
`subst0`/`substPair` diagonals.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Stars and lifts -/

#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.single
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.concat
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildrenStar.concat
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.congLift
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildrenStar.hereLift
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildrenStar.thereLift

/-! ## Renaming closure -/

#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.rename
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.weaken

/-! ## Pointwise substitution machinery -/

#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_pointwiseEtaStar
#assert_no_axioms FX1Poly.Core.RawTermSubst.iterateLift_pointwiseEtaStar
#assert_no_axioms FX1Poly.Core.RawTerm.subst_pointwiseEtaStar
#assert_no_axioms FX1Poly.Core.RawTermChildren.subst_pointwiseEtaStar

/-! ## The diagonals -/

#assert_no_axioms FX1Poly.Core.RawTermSubst.singleton_pointwiseEtaStar
#assert_no_axioms FX1Poly.Core.RawTermSubst.pair_pointwiseEtaStar
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.subst0_argDiagonal
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.substPair_argDiagonal
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.subst0_diagonal

end FX1PolyAudit
