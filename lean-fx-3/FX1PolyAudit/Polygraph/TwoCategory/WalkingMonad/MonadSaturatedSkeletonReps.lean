import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedSkeletonReps

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedSkeletonReps — zero-axiom gate (the bridge)

Per-declaration zero-axiom gate for the bespoke-free SKELETON-REPS bridge: the cons-only prepend primitives
(`ascendingPrepend` / `shiftPrepend`) and the ordinal-sum whisker embedding (`embedLocalMap`) with their length +
region-wise value characterizations and the three-region position split (`embedRegionSplit`), relocated VERBATIM
from `MonadWhiskerEmbedding` so the KZ order model can consume them conv-decoupled.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ascendingPrepend_length
#assert_no_axioms FX1Poly.Polygraph.ascendingPrepend_get_lt
#assert_no_axioms FX1Poly.Polygraph.ascendingPrepend_get_add
#assert_no_axioms FX1Poly.Polygraph.shiftPrepend_length
#assert_no_axioms FX1Poly.Polygraph.shiftPrepend_get_lt
#assert_no_axioms FX1Poly.Polygraph.shiftPrepend_get_add
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_length
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_get_left
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_get_mid
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_get_right
#assert_no_axioms FX1Poly.Polygraph.embedRegionSplit

end FX1PolyAudit
