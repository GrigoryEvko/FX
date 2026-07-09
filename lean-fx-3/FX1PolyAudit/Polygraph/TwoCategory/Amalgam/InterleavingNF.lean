import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.InterleavingNF

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.InterleavingNF — zero-axiom gate for the free-product NF

Per-declaration zero-axiom gate for the interleaving normal form: the tag / block machinery, the alternating
factorisation `blockDecompose`, and its three invariants (soundness, alternation, non-degeneracy).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.letterTag
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tagsDiffer
#assert_no_axioms FX1Poly.Polygraph.Amalgam.prependLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.blockDecompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.recompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.prependLetter_recompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.blockDecompose_sound
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isAlternating
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isAlternating_headLettersIrrelevant
#assert_no_axioms FX1Poly.Polygraph.Amalgam.prependLetter_preserves_alternating
#assert_no_axioms FX1Poly.Polygraph.Amalgam.blockDecompose_alternates
#assert_no_axioms FX1Poly.Polygraph.Amalgam.allBlocksNonempty
#assert_no_axioms FX1Poly.Polygraph.Amalgam.allBlocksNonempty_tail
#assert_no_axioms FX1Poly.Polygraph.Amalgam.prependLetter_preserves_nonempty
#assert_no_axioms FX1Poly.Polygraph.Amalgam.blockDecompose_blocksNonempty
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasInterleavingNF

end FX1PolyAudit
