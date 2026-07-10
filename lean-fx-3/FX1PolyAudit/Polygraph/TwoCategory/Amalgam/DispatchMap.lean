import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchMap

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DispatchMap — zero-axiom gate for the block factorization +
dispatch map assembly (WP-AMALG-2 r1, B1)

Per-declaration zero-axiom gate: the dispatch routing map (`blockTags`) with its soundness, the block-purity of a
dispatch-map image (`wordAllComponentTwo` / `monoFalseBlocks` / `monoBlockDecompose` /
`monoBlockDecompose_lengthLeOne`), the dispatch map firing on the real monad unit (`dispatchedMonadUnit` /
`dispatchedMonadUnit_isGen` / `dispatchedMonadUnit_index`), and the non-vacuity contrast on the witness pushout.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the dispatch routing map
#assert_no_axioms FX1Poly.Polygraph.Amalgam.blockTags
#assert_no_axioms FX1Poly.Polygraph.Amalgam.blockTags_recompose_sound

-- block-purity of a dispatch-map image
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordAllComponentTwo
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monoFalseBlocks
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monoBlockDecompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monoBlockDecompose_lengthLeOne

-- the dispatch map firing on a real component generator
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchedMonadUnit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchedMonadUnit_isGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchedMonadUnit_index

-- the non-vacuity contrast (routing of a real combined cell vs a dispatch-map image)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairDomainRouting
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessWordRouting
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairDomain_multiBlock
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadTailWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadTailWord_allTwo
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadTailWord_singleBlock
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadTailWord_monoBlockGeneral

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasBlockDispatchMap

end FX1PolyAudit
