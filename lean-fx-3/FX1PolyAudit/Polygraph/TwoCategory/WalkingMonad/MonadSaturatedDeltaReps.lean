import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps — zero-axiom gate (the deep bridge)

Per-declaration zero-axiom gate for the bespoke-free DEEP saturated-Δ representatives bridge: the unit /
multiplication free 2-cells and the three law composites, and the retuned monotone-map fold with its generator
smokes, structural-fragment soundness leg, and three monad-law fold-soundness theorems, relocated VERBATIM from the
pure-bespoke Δ chain so the survivor lane can consume the walking-monad skeleton conv-decoupled.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadUnitTwoCell
#assert_no_axioms FX1Poly.Polygraph.monadMulTwoCell
#assert_no_axioms FX1Poly.Polygraph.monadLeftUnitCell
#assert_no_axioms FX1Poly.Polygraph.monadRightUnitCell
#assert_no_axioms FX1Poly.Polygraph.monadAssocLeftCell
#assert_no_axioms FX1Poly.Polygraph.monadAssocRightCell
#assert_no_axioms FX1Poly.Polygraph.monadIdTCell
#assert_no_axioms FX1Poly.Polygraph.monadMonoStepAtom
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_unit
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_mul
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_congr_of_spine_eq
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_eq_of_interchangeFreeStep
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_leftUnit_eq_id
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_rightUnit_eq_id
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_assoc_eq
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredLeftUnit_via_simplicialIdentity
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredIdT_eq
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredLeftUnit
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_rightUnit_via_succSimplicialIdentity
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_assoc_via_degenCommute

end FX1PolyAudit
