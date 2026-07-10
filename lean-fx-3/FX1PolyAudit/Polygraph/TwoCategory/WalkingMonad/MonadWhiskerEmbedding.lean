import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerEmbedding

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerEmbedding — zero-axiom gate (the whisker embedding)

Per-declaration zero-axiom gate for the walking-monad whisker-embedding: the fold of a whiskered free 2-cell run
at any context is the ordinal-sum embedding of the cell's local map (`monadRunMonoCell_localEmbed`), so the two
top-level whiskerings embed the body's map, discharging the two WHISKER-congruence cases of `mapEqOfConv`
(`monadMonotoneMapOf_whiskerLeftCongr` / `_whiskerRightCongr`).  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_idMap
#assert_no_axioms FX1Poly.Polygraph.faceMap_eq_embedLocalMap
#assert_no_axioms FX1Poly.Polygraph.degenMap_eq_embedLocalMap
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_composeMap
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_nest
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_length
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_mapsInto
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_localEmbed_gen
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_localEmbed
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskerLeftCongr
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskerRightCongr
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWhiskerEmbeddingAndCongruence

end FX1PolyAudit
