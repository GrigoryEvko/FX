import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.SPrefixRefutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.SPrefixRefutation — zero-axiom gate for the s-prefix normal form
REFUTATION (WP-AMALG-2 r3, B1)

Per-declaration zero-axiom gate: the exact non-commuting word `t·s`, its block decomposition (involution block
non-initial), the `s`-to-front reordering being a DIFFERENT word, the `s`-prefix-split predicate, the REFUTATION
that `t·s` has no `s`-prefix split, the non-vacuity anchor cell, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the exact non-commuting word + its block structure
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairTSWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairSTWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairTSWord_blockDecompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairSTWord_blockDecompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairTSWord_ne_STWord

-- the s-prefix-split predicate + the refutation
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isAllComponentOne
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isAllComponentTwo
#assert_no_axioms FX1Poly.Polygraph.Amalgam.hasSPrefixSplit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairTSWord_not_sPrefixForm

-- the non-vacuity anchor + the honesty marker
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairTSPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairTSIdentityCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_sPrefixNormalFormRefuted

end FX1PolyAudit
