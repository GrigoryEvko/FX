import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDeltaDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadDeltaDecision — zero-axiom gate (the Δ decision)

Per-declaration zero-axiom gate for the walking-monad Δ decision: the Godement / `ofFull` residual discharged by the
disjoint-window two-block commute (`embedLocalMap_disjointCommute`, `monadMonotoneMapOf_interchange`) and the
COMPLETE soundness leg `monadMonotoneMapOf_mapEqOfConv`.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mapsInto_mono
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_mapsInto
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_hcomp
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.composeMap_middleSwap
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_interchange
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_eqOfStep
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_eqOfConv
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_eqOfConvFull
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_mapEqOfConv
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasMapEqOfConvComplete

end FX1PolyAudit
