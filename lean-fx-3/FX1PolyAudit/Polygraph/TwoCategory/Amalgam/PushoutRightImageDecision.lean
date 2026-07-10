import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadBespokeFreeWalk
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRightImageDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutRightImageDecision — zero-axiom + bespoke-free gate for the
TWO-SIDED right-image decider

Per-declaration zero-axiom gate for the two-sided decider, its Bool observability, the two live verdicts, and the
honesty markers.  PLUS the constant-closure META-WALK certifying the decider inherits the B5 re-founding: its full
transitive closure has NO bespoke `monadSaturatedTwoCellDecision`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageTwoSidedDecision
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesTwoSided
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesTwoSided_assoc
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesTwoSided_faces
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRightImageTwoSidedDecision
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_fullPushoutDispatchStaysWalledAfterRightImage

/-! ## The two-sided decider is bespoke-free (inherits the B5 re-founding) -/

#assert_constant_free_of FX1Poly.Polygraph.Amalgam.pushoutRightImageTwoSidedDecision
  needle FX1Poly.Polygraph.monadSaturatedTwoCellDecision

end FX1PolyAudit
